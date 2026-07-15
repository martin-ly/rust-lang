#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""check_stub_purity.py — 检查非 concept/ 目录中的 stub/redirect 纯度。

依据 AGENTS.md §2 Canonical 规则与 §3.3 重定向 stub 模板：
  - `knowledge/` 文件应只保留摘要、速查与链接（≤20 行或明确 stub）。
  - `docs/` 中标记为 stub/archive redirect 的文件不应保留通用概念完整正文。
  - `content/` 专题入口 stub 同理。
  - `crates/*/docs/` 不应复制通用概念解释，应链接到 `concept/`。

检测两类违规：
  (a) 文件顶部或元数据声明为 stub/redirect/archive，但正文明显过长
      （行数 > MAX_STUB_LINES 且字节数 > MAX_STUB_BYTES）。
  (b) 文件未声明为 stub，但正文极短（< MIN_SUBSTANTIVE_LINES）且不含
      独立操作步骤/决策树/项目特定内容，疑似空壳页。
  (c) 文件含大量指向 concept/ 的链接但仍保留与 concept/ 权威页高度
      重复的通用概念正文（正文重复度 > SIMILARITY_THRESHOLD）。

退出码：
  默认：输出报告，exit 0
  --strict：存在 (a) 类伪 stub 或 (c) 类高重复正文时 exit 1

输出：
  reports/STUB_PURITY_BASELINE_<date>.md
  reports/STUB_PURITY_BASELINE_<date>.json
"""
from __future__ import annotations

import argparse
import datetime as _dt
import json
import os
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# 扫描目录（相对 ROOT）
SCAN_DIRS = [
    "knowledge",
    "docs",
    "content",
    "crates",
]

# 排除路径片段
EXCLUDE_DIR_PARTS = {"archive", "sources", "tmp", "target", "book", "vendor"}
EXCLUDE_NAME_KEYWORDS = ("summary.md", "index.md", "readme.md")

# 严格的伪 stub 检测标记：文件明确声明自己是重定向/合并/archive stub，
# 但仍保留大量正文，即构成 pseudo-stub。注意：
#   - 单独的“redirect”或“权威来源”字样不够（大量 legitimate 索引 stub 也会用）。
#   - 以下标记必须成对或成句出现，才视为“声明为 stub”。
STUB_MARKERS = (
    "本文件保留为重定向",
    "本文件为重定向",
    "stub/archive redirect",
    "archive redirect",
    "本主题已合并至",
    "内容已整合至",
    "已迁移至",
    "已合并至",
)

# 文件顶部元数据块通常占用的行数上限；若正文在元数据之后仍很长，则判定为伪 stub
MAX_STUB_LINES = 25
MAX_STUB_BYTES = 2000

# 空壳页判定：正文行数低于此值且不属于明确 stub
MIN_SUBSTANTIVE_LINES = 5

# 与 concept/ 权威页正文重复度阈值（ difflib SequenceMatcher ratio ）
SIMILARITY_THRESHOLD = 0.25

TITLE_RE = re.compile(r"^#\s+(.+?)\s*$", re.MULTILINE)
EN_RE = re.compile(r"\*\*EN\*\*\s*[:：]\s*(.+?)$", re.MULTILINE)
LINK_RE = re.compile(r"\]\(([^)]+)\)")

# 这些目录/文件属于合法长索引或研究报告，不参与伪 stub 判定
# （它们可能含“权威来源”等字样，但本身是 legitimate 内容页）
LEGITIMATE_LONG_INDEX_DIRS = {
    "docs/00_meta",
    "docs/12_research_notes",
    "docs/03_reference/quick_reference",
    "content/safety_critical",
}
LEGITIMATE_LONG_INDEX_FILES = {
    "docs/15_rust_formal_engineering_system/README.md",
    "docs/15_rust_formal_engineering_system/00_master_index.md",
}


def is_excluded(path: Path) -> bool:
    parts = set(path.parts)
    if parts & EXCLUDE_DIR_PARTS:
        return True
    name = path.name.lower()
    if name in EXCLUDE_NAME_KEYWORDS:
        return True
    return False


def declared_stub(text: str) -> bool:
    return any(marker in text for marker in STUB_MARKERS)


def extract_body(text: str) -> str:
    """去掉顶部元数据引用块（> ...）和标题，返回正文。"""
    lines = text.splitlines()
    body_lines = []
    in_frontmatter = False
    for line in lines:
        stripped = line.strip()
        if stripped.startswith(">"):
            continue
        if stripped == "---":
            in_frontmatter = not in_frontmatter
            continue
        if in_frontmatter:
            continue
        body_lines.append(line)
    return "\n".join(body_lines)


def body_lines_and_bytes(text: str) -> tuple[int, int]:
    body = extract_body(text)
    non_empty = [ln for ln in body.splitlines() if ln.strip()]
    return len(non_empty), len(body.encode("utf-8"))


def find_concept_authority(topic: str, concept_dir: Path) -> Path | None:
    """按标题或文件名粗略匹配 concept/ 权威页，用于重复度检查。"""
    topic_norm = re.sub(r"[^\w]", "", topic.lower())
    candidates = []
    for p in concept_dir.rglob("*.md"):
        if is_excluded(p):
            continue
        text = p.read_text(encoding="utf-8", errors="replace")
        title_m = TITLE_RE.search(text)
        en_m = EN_RE.search(text)
        title = title_m.group(1) if title_m else ""
        en = en_m.group(1) if en_m else ""
        combined = re.sub(r"[^\w]", "", (title + " " + en).lower())
        if topic_norm and (topic_norm in combined or combined in topic_norm):
            candidates.append(p)
    # 取路径最短（最核心）的匹配
    return min(candidates, key=lambda x: len(str(x))) if candidates else None


def similarity(a: str, b: str) -> float:
    try:
        import difflib

        return difflib.SequenceMatcher(None, a, b).ratio()
    except Exception:
        return 0.0


def collect_pages() -> list[dict]:
    pages = []
    for scan_dir in SCAN_DIRS:
        base = ROOT / scan_dir
        if not base.exists():
            continue
        if scan_dir == "crates":
            # 只扫描 crates/*/docs/
            for docs_dir in base.glob("*/docs"):
                for path in docs_dir.rglob("*.md"):
                    if is_excluded(path):
                        continue
                    pages.append(parse_page(path))
        else:
            for path in base.rglob("*.md"):
                if is_excluded(path):
                    continue
                pages.append(parse_page(path))
    return [p for p in pages if p]


def parse_page(path: Path) -> dict | None:
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except Exception:
        return None
    title_m = TITLE_RE.search(text)
    title = title_m.group(1).strip() if title_m else ""
    en_m = EN_RE.search(text)
    en = en_m.group(1).strip() if en_m else ""
    is_stub = declared_stub(text)
    body_line_count, body_byte_count = body_lines_and_bytes(text)

    # 提取指向 concept/ 的链接
    concept_links = []
    for m in LINK_RE.finditer(text):
        link = m.group(1)
        if "concept/" in link or link.startswith("../../concept"):
            concept_links.append(link)

    return {
        "path": str(path.relative_to(ROOT)).replace("\\", "/"),
        "title": title,
        "en": en,
        "is_stub": is_stub,
        "body_lines": body_line_count,
        "body_bytes": body_byte_count,
        "concept_links": concept_links,
        "text": text,
    }


def is_whitelisted_long_index(path_str: str) -> bool:
    if path_str in LEGITIMATE_LONG_INDEX_FILES:
        return True
    for prefix in LEGITIMATE_LONG_INDEX_DIRS:
        if path_str.startswith(prefix):
            return True
    return False


def evaluate(pages: list[dict]) -> dict:
    pseudo_stubs = []
    empty_shells = []
    high_dup = []

    concept_dir = ROOT / "concept"
    authority_cache: dict[str, tuple[Path, str] | None] = {}

    for p in pages:
        path_str = p["path"]

        # (a) 声明为 stub 但正文过长；合法长索引目录/文件除外
        if p["is_stub"] and not is_whitelisted_long_index(path_str):
            if p["body_lines"] > MAX_STUB_LINES or p["body_bytes"] > MAX_STUB_BYTES:
                pseudo_stubs.append(p)
                continue

        # (b) 未声明 stub 但正文过短（排除已声明 stub 的短文件）
        if not p["is_stub"] and p["body_lines"] < MIN_SUBSTANTIVE_LINES:
            empty_shells.append(p)
            continue

        # (c) 非 stub 或伪 stub 中含通用概念正文：与 concept/ 权威页相似度
        # 仅对 body 较大且含 concept/ 链接的文件做此检查，控制开销
        if p["body_bytes"] > 2000 and p["concept_links"] and not is_whitelisted_long_index(path_str):
            topic = p["en"] or p["title"]
            if topic:
                cache_key = topic.lower()
                if cache_key not in authority_cache:
                    authority = find_concept_authority(topic, concept_dir)
                    if authority:
                        authority_cache[cache_key] = (authority, authority.read_text(encoding="utf-8", errors="replace"))
                    else:
                        authority_cache[cache_key] = None
                cached = authority_cache[cache_key]
                if cached:
                    auth_text = cached[1]
                    body = extract_body(p["text"])
                    # 去掉代码块、链接、标题后比较
                    clean_body = re.sub(r"```[\s\S]*?```", "", body)
                    clean_body = re.sub(r"\[([^\]]+)\]\([^)]+\)", r"\1", clean_body)
                    clean_auth = re.sub(r"```[\s\S]*?```", "", auth_text)
                    clean_auth = re.sub(r"\[([^\]]+)\]\([^)]+\)", r"\1", clean_auth)
                    sim = similarity(clean_body, clean_auth)
                    if sim > SIMILARITY_THRESHOLD:
                        high_dup.append({**p, "similarity": round(sim, 3), "authority": str(cached[0].relative_to(ROOT)).replace("\\", "/")})

    return {
        "total": len(pages),
        "pseudo_stubs": pseudo_stubs,
        "empty_shells": empty_shells,
        "high_duplicates": high_dup,
    }


def format_report(result: dict, date_str: str) -> str:
    lines = [
        f"# Stub Purity Baseline Report ({date_str})",
        "",
        "> 依据 AGENTS.md §2 Canonical 规则与 §3.3 重定向 stub 模板：",
        "> knowledge/docs/content/crates docs 中的 stub/redirect 文件不应保留通用概念完整正文。",
        "",
        "## 汇总",
        "",
        f"- 扫描页数：{result['total']}",
        f"- 伪 stub（声明为 stub 但正文过长）：{len(result['pseudo_stubs'])}",
        f"- 空壳页（未声明 stub 但正文极短）：{len(result['empty_shells'])}",
        f"- 高重复正文（vs concept/ 权威页相似度 > {SIMILARITY_THRESHOLD}）：{len(result['high_duplicates'])}",
        "",
    ]

    def section(name: str, items: list[dict], extra_cols: tuple = ()):
        lines.append(f"## {name} ({len(items)})")
        lines.append("")
        if not items:
            lines.append("未发现。")
            lines.append("")
            return
        for item in items:
            line = f"- `{item['path']}` — 正文 {item['body_lines']} 行 / {item['body_bytes']} 字节"
            for col in extra_cols:
                line += f", {col}: {item.get(col, '')}"
            lines.append(line)
        lines.append("")

    section("伪 stub", result["pseudo_stubs"])
    section("空壳页", result["empty_shells"])
    section("高重复正文", result["high_duplicates"], ("similarity", "authority"))

    lines.extend([
        "## 判定标准",
        "",
        f"- 声明为 stub：正文含任一标记（如『本文件为学习入口 stub』、『redirect』等）。",
        f"- 伪 stub：声明为 stub，但去元数据后正文 > {MAX_STUB_LINES} 行 或 > {MAX_STUB_BYTES} 字节。",
        f"- 空壳页：未声明 stub，但去元数据后正文 < {MIN_SUBSTANTIVE_LINES} 行。",
        f"- 高重复正文：去代码块后与 concept/ 权威页相似度 > {SIMILARITY_THRESHOLD}。",
        "",
    ])

    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description="检查非 concept/ 目录中的 stub/redirect 纯度")
    parser.add_argument("--strict", action="store_true", help="存在伪 stub 或高重复正文时 exit 1")
    parser.add_argument("--json", action="store_true", help="仅输出 JSON 到 stdout")
    parser.add_argument("--report", action="store_true", help="写入 reports/ 文件")
    args = parser.parse_args()

    pages = collect_pages()
    result = evaluate(pages)
    date_str = _dt.datetime.now().strftime("%Y_%m_%d")

    if args.json:
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return 0

    report = format_report(result, date_str)
    print(report)

    if args.report:
        reports_dir = ROOT / "reports"
        reports_dir.mkdir(exist_ok=True)
        md_path = reports_dir / f"STUB_PURITY_BASELINE_{date_str}.md"
        json_path = reports_dir / f"STUB_PURITY_BASELINE_{date_str}.json"
        md_path.write_text(report, encoding="utf-8")
        json_path.write_text(json.dumps(result, ensure_ascii=False, indent=2), encoding="utf-8")
        print(f"\n报告已写入：\n  {md_path}\n  {json_path}", file=sys.stderr)

    fail_count = len(result["pseudo_stubs"]) + len(result["high_duplicates"])
    if args.strict and fail_count > 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
