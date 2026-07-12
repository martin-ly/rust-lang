#!/usr/bin/env python3
"""内容完整性审计：量化 concept/ 中的 TODO 类标记与空章节。

背景：2026-07-09 CONTENT_COMPLETENESS_AUDIT 基线（reports/CONTENT_COMPLETENESS_AUDIT_2026_07_09.md）
标记 126 个文件含 TODO/待补充/占位标记、420 个文件含空章节。本脚本以可机器复核的方式
重新量化，并与基线对比，用于 2026-07-12 清零整改（reports/CONTENT_COMPLETENESS_CLEANUP_2026_07_12.md）。

口径：
- 扫描 concept/**/*.md，排除 archive/、sources/、placeholders/ 与重定向 stub
  （前 30 行含 "Redirect stub" 或 "重定向" 且正文 < 40 行）。
- 标记：TODO|TBD|FIXME|待补充|待完善|占位符|placeholder（大小写不敏感），
  跳过代码块（``` 围栏）内命中；按上下文分类：heading/toc/meta/version_log/body。
- 空章节：标题（任意级别）与下一个标题之间无实质内容（仅空行）。
  - empty_leaf：下一个标题级别 <= 当前级别（或为文件末尾）——真正无内容的叶子章节。
  - empty_parent：下一个标题级别更深——父章节无引导语，仅有子章节。

用法：
    python scripts/audit_content_completeness.py            # 终端摘要
    python scripts/audit_content_completeness.py --json tmp/completeness.json
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CONCEPT = ROOT / "concept"

EXCLUDE_PARTS = {"archive", "sources", "placeholders", "deprecated"}

MARKER_RE = re.compile(
    r"TODO|TBD|FIXME|待补充|待完善|占位符|placeholder", re.IGNORECASE
)
HEADING_RE = re.compile(r"^(#{1,6})\s+(.*\S)\s*$")
FENCE_RE = re.compile(r"^\s*```")
TOC_LINE_RE = re.compile(r"^\s*[-*]\s+\[.*\]\(#.*\)\s*$")
META_LINE_RE = re.compile(r"^>\s*\*\*")
VERSION_LOG_RE = re.compile(r"^\s*[-*]\s*v?\d+\.\d+")

# 占位性引导语（2026-07-12 空父章节填充脚本 tmp/fill_empty_sections.py 的 9 种句式开头；
# 见 reports/TEMPLATE_BACKFILL_QUALITY_2026_07_12.md）。单节正文 <2 句且全为引导句式
# 记为 PLACEHOLDER_SECTION（观察指标，默认不阻断）。
GUIDE_RE = re.compile(
    r"^(本节围绕「.*」展开|「.*」部分(按|包含)|本节将「.*」分解|理解「.*」需要把握|"
    r"本节从.*切入|「.*」涉及|本节聚焦「.*」|「.*」部分的核心主题|本节专门讨论「|"
    r"本节从.*两个层面剖析)"
)


def iter_files() -> list[Path]:
    out = []
    for p in sorted(CONCEPT.rglob("*.md")):
        rel = p.relative_to(CONCEPT)
        if any(part in EXCLUDE_PARTS for part in rel.parts):
            continue
        out.append(p)
    return out


def is_redirect_stub(lines: list[str]) -> bool:
    head = "\n".join(lines[:30])
    if len(lines) <= 40 and ("Redirect stub" in head or "重定向" in head):
        return True
    return False


def classify_line(line: str) -> str:
    if HEADING_RE.match(line):
        return "heading"
    if TOC_LINE_RE.match(line):
        return "toc"
    if META_LINE_RE.match(line):
        return "meta"
    if VERSION_LOG_RE.match(line):
        return "version_log"
    return "body"


def audit_file(path: Path) -> dict:
    lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    result = {
        "path": str(path.relative_to(ROOT)).replace("\\", "/"),
        "redirect_stub": is_redirect_stub(lines),
        "markers": [],          # (lineno, kind, text)
        "empty_leaf": [],       # (lineno, heading)
        "empty_parent": [],     # (lineno, heading)
        "placeholder_sections": [],  # (lineno, heading, guide_text)
    }
    # --- markers (skip code fences) ---
    in_code = False
    for i, line in enumerate(lines, start=1):
        if FENCE_RE.match(line):
            in_code = not in_code
            continue
        if in_code:
            continue
        if MARKER_RE.search(line):
            result["markers"].append((i, classify_line(line), line.strip()[:120]))
    if result["redirect_stub"]:
        return result
    # --- empty sections ---
    headings = []  # (index_of_line, level, text)
    in_code = False
    for i, line in enumerate(lines):
        if FENCE_RE.match(line):
            in_code = not in_code
            continue
        if in_code:
            continue
        m = HEADING_RE.match(line)
        if m:
            headings.append((i, len(m.group(1)), m.group(2)))
    for k, (idx, level, text) in enumerate(headings):
        nxt = headings[k + 1] if k + 1 < len(headings) else None
        end = nxt[0] if nxt else len(lines)
        body = [ln for ln in lines[idx + 1 : end] if ln.strip()]
        if body:
            # PLACEHOLDER_SECTION：本节正文（子标题前）<2 句且全为引导句式
            own = []
            for ln in body:
                if HEADING_RE.match(ln):
                    break
                s = ln.strip()
                if s == "---" or META_LINE_RE.match(ln) or TOC_LINE_RE.match(ln):
                    continue
                own.append(s)
            if own and all(GUIDE_RE.match(s) for s in own):
                nsent = sum(len(re.findall(r"[。！？]", s)) for s in own)
                if nsent < 2:
                    result["placeholder_sections"].append((idx + 1, text, own[0][:80]))
            continue
        if nxt is None or nxt[1] <= level:
            result["empty_leaf"].append((idx + 1, text))
        else:
            result["empty_parent"].append((idx + 1, text))
    return result


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--json", help="输出 JSON 明细到指定路径")
    ap.add_argument("--strict", help="存在 PLACEHOLDER_SECTION 时 exit 1（默认仅观察）", action="store_true")
    args = ap.parse_args()

    records = [audit_file(p) for p in iter_files()]
    active = [r for r in records if not r["redirect_stub"]]

    marker_files = [r for r in active if r["markers"]]
    leaf_files = [r for r in active if r["empty_leaf"]]
    parent_files = [r for r in active if r["empty_parent"]]

    n_markers = sum(len(r["markers"]) for r in marker_files)
    n_leaf = sum(len(r["empty_leaf"]) for r in leaf_files)
    n_parent = sum(len(r["empty_parent"]) for r in parent_files)

    print(f"扫描文件: {len(records)}（其中重定向 stub {len(records) - len(active)}，有效 {len(active)}）")
    print(f"① 标记命中: {n_markers} 处 / {len(marker_files)} 文件")
    by_kind: dict[str, int] = {}
    for r in marker_files:
        for _, kind, _ in r["markers"]:
            by_kind[kind] = by_kind.get(kind, 0) + 1
    for k, v in sorted(by_kind.items()):
        print(f"   - {k}: {v}")
    print(f"② 空章节(真叶子): {n_leaf} 处 / {len(leaf_files)} 文件")
    print(f"② 空章节(父容器无引导语): {n_parent} 处 / {len(parent_files)} 文件")
    ph_files = [r for r in active if r["placeholder_sections"]]
    n_ph = sum(len(r["placeholder_sections"]) for r in ph_files)
    print(f"③ 占位引导章节(PLACEHOLDER_SECTION，观察): {n_ph} 处 / {len(ph_files)} 文件")
    print()
    print("基线对比（2026-07-09）: 标记文件 126 →", len(marker_files),
          "；空章节文件 420 →", len(set(id(r) for r in leaf_files) | set(id(r) for r in parent_files)))

    if args.json:
        out = Path(args.json)
        out.write_text(
            json.dumps(records, ensure_ascii=False, indent=1), encoding="utf-8"
        )
        print(f"JSON 明细: {out}")
    if args.strict and n_ph:
        print("--strict: 存在 PLACEHOLDER_SECTION，exit 1")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
