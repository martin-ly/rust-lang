#!/usr/bin/env python3
"""扫描 knowledge/ 和 docs/ 下 Markdown 文件的 EN/Summary 元数据覆盖率，并支持自动补全。

用法:
    python scripts/check_knowledge_docs_i18n.py          # 只检查并输出报告
    python scripts/check_knowledge_docs_i18n.py --fix    # 自动为缺失文件补全 EN/Summary
    python scripts/check_knowledge_docs_i18n.py --report # 同时写入 reports/knowledge_docs_i18n_report.md
"""

from __future__ import annotations

import argparse
import re
import string
import sys
from pathlib import Path
from typing import Iterable

ROOT = Path(__file__).resolve().parent.parent
TARGET_DIRS = [ROOT / "knowledge", ROOT / "docs"]
EN_RE = re.compile(r"^>\s*\*\*EN\*\*:\s*(.+)$", re.MULTILINE)
SUMMARY_RE = re.compile(r"^>\s*\*\*Summary\*\*:\s*(.+)$", re.MULTILINE)
TITLE_RE = re.compile(r"^#\s+(.+?)(?:\s+\{#.*?\})?\s*$", re.MULTILINE)
PARENS_EN_RE = re.compile(r"[\(（]([^（）\(\)]+)[\)）]")

# 用于判断文件是否为 stub / archive redirect 的特征词
STUB_MARKERS = [
    "stub",
    "redirect",
    "重定向",
    "archive",
    "已归档",
    "历史版本存档",
    "精简知识卡片",
    "本主题深度解释见",
    "详见 concept",
    "权威来源.*concept/",
]
STUB_PATTERN = re.compile(
    "|".join(STUB_MARKERS),
    re.IGNORECASE | re.MULTILINE | re.DOTALL,
)

ACRONYMS = {
    "ffi": "FFI",
    "asm": "ASM",
    "mir": "MIR",
    "llvm": "LLVM",
    "ub": "UB",
    "api": "API",
    "url": "URL",
    "cli": "CLI",
    "gui": "GUI",
    "http": "HTTP",
    "https": "HTTPS",
    "tcp": "TCP",
    "udp": "UDP",
    "cpu": "CPU",
    "gpu": "GPU",
    "ram": "RAM",
    "ssd": "SSD",
    "json": "JSON",
    "yaml": "YAML",
    "toml": "TOML",
    "sql": "SQL",
    "orm": "ORM",
    "crc": "CRC",
}


def iter_md_files(dirs: Iterable[Path]) -> Iterable[Path]:
    for d in dirs:
        if not d.exists():
            continue
        for p in sorted(d.rglob("*.md")):
            if not p.is_file():
                continue
            # 排除任何层级名为 archive/Archive 的子目录
            if any(part.lower() == "archive" for part in p.parts):
                continue
            yield p


def read_text(path: Path) -> str:
    raw = path.read_bytes()
    return raw.decode("utf-8-sig")


def write_text(path: Path, text: str) -> None:
    path.write_bytes(text.encode("utf-8"))


def strip_markdown(text: str) -> str:
    """去除 markdown 行内格式，用于生成元数据。"""
    text = re.sub(r"\*\*([^*]+)\*\*", r"\1", text)
    text = re.sub(r"__([^_]+)__", r"\1", text)
    text = re.sub(r"`([^`]+)`", r"\1", text)
    text = re.sub(r"\{#.*?\}", "", text)
    return text.strip()


def split_title(title: str) -> tuple[str, str | None]:
    """从标题中提取中文部分与英文部分。

    支持括号、斜杠、冒号分隔的中英标题。返回 (chinese_title, english_title_or_none)。
    """
    title = strip_markdown(title)

    # 1. 括号片段：按语言分类，而非简单把括号内当英文
    segments: list[tuple[str, str]] = []  # (kind, text)
    last_end = 0
    has_parens = False
    for m in PARENS_EN_RE.finditer(title):
        has_parens = True
        text_before = title[last_end:m.start()].strip()
        if text_before:
            segments.append(("text", text_before))
        segments.append(("parens", m.group(1).strip()))
        last_end = m.end()
    tail = title[last_end:].strip()
    if tail:
        segments.append(("text", tail))

    if has_parens:
        chinese_parts: list[str] = []
        english_parts: list[str] = []
        for kind, text in segments:
            if not text:
                continue
            if is_mostly_english(text):
                english_parts.append(text)
            else:
                chinese_parts.append(text)
        zh = " ".join(chinese_parts).strip()
        en = " ".join(english_parts).strip() if english_parts else None
        zh = re.sub(r"[\(\)（）]", "", zh).strip()
        return zh or title, en

    # 2. 斜杠分隔的双语标题（仅当一侧为英文、另一侧为中文时拆分）
    if " / " in title:
        parts = [p.strip() for p in title.split(" / ")]
        if len(parts) == 2:
            a, b = parts
            a_en = is_mostly_english(a)
            b_en = is_mostly_english(b)
            if a_en and not b_en:
                return b, a
            if b_en and not a_en:
                return a, b
            # 同语言：左侧作为中文标题，不提取英文
            return title, None

    # 3. 冒号分隔（仅当一侧为英文、另一侧为中文时拆分）
    if "：" in title or ":" in title:
        sep = "：" if "：" in title else ":"
        parts = [p.strip() for p in title.split(sep, 1)]
        if len(parts) == 2:
            a, b = parts
            a_en = is_mostly_english(a)
            b_en = is_mostly_english(b)
            if a_en and not b_en:
                return b, a
            if b_en and not a_en:
                return a, b
            # 同语言：左侧作为中文标题，不提取英文
            return a, None

    return title, None


def is_mostly_english(text: str) -> bool:
    """判断文本是否以英文为主（存在 CJK 字符时认为不是纯英文）。"""
    text = strip_markdown(text)
    cjk = sum(1 for c in text if "\u4e00" <= c <= "\u9fff")
    if cjk > 0:
        return False
    letters = sum(1 for c in text if c.isalpha())
    ascii_chars = sum(1 for c in text if ord(c) < 128 and c.isalpha())
    if letters == 0:
        return False
    return ascii_chars / letters >= 0.7


def title_case_words(words: Iterable[str]) -> str:
    out = []
    for w in words:
        w = w.strip()
        if not w:
            continue
        lower = w.lower()
        if lower in ACRONYMS:
            out.append(ACRONYMS[lower])
        elif len(w) == 1:
            out.append(w.upper())
        else:
            out.append(w[0].upper() + w[1:].lower())
    return " ".join(out)


def filename_to_en(stem: str) -> str:
    """从文件名生成英文标题。"""
    # 去掉前导数字与分隔符，例如 00_master_index -> master_index
    stem = re.sub(r"^\d+[-_]?", "", stem)
    # 拆分 _ 与 -
    words = re.split(r"[_\-]+", stem)
    return title_case_words(words)


def parent_dir_to_en(path: Path) -> str:
    """从父目录名生成英文标题。"""
    parent = path.parent.name
    parent = re.sub(r"^\d+[-_]", "", parent)
    words = re.split(r"[_\-]+", parent)
    return title_case_words(words)


def generate_en(title: str, path: Path) -> str:
    """基于标题和路径生成英文名称。"""
    _, en = split_title(title)
    if en:
        en = strip_markdown(en)
        en = re.sub(r"[\n\r]+", " ", en)
        en = en.strip(string.whitespace + "\\/：:")
        if en and len(en) >= 2:
            return en

    # 标题本身以英文为主
    if is_mostly_english(title):
        cleaned = strip_markdown(title)
        cleaned = re.sub(r"[\n\r]+", " ", cleaned)
        cleaned = cleaned.strip(string.whitespace + "\\/：:")
        if cleaned and len(cleaned) >= 2:
            return cleaned

    # README 文件：取父目录名 + Index/Overview
    if path.name.lower() == "readme.md":
        parent_en = parent_dir_to_en(path)
        if parent_en and parent_en.lower() not in {"knowledge", "docs", "content"}:
            return f"{parent_en} Index"
        return "Index"

    # 普通文件：从文件名生成
    en = filename_to_en(path.stem)
    if en and len(en) >= 2:
        # 若文件名太泛化，尝试补上前缀
        if en.lower() in {"readme", "index", "guide"}:
            parent_en = parent_dir_to_en(path)
            if parent_en:
                return f"{parent_en} {en}".strip()
        return en

    parent_en = parent_dir_to_en(path)
    return parent_en or "Untitled"


def generate_summary(title: str, path: Path, en: str) -> str:
    """生成一句话双语摘要。"""
    zh, extracted_en = split_title(title)
    zh = strip_markdown(zh) if zh else ""

    # 纯英文标题：直接复用
    if not zh or is_mostly_english(zh):
        base = zh or en
        return f"{base} {en}."

    # 生成英文翻译：优先使用提取的英文，否则使用生成的 EN
    eng = extracted_en or en
    return f"{zh} {eng}."


def is_stub(content: str) -> bool:
    """判断文件内容是否表明这是一个 stub / archive redirect。"""
    return bool(STUB_PATTERN.search(content))


def find_title_line(lines: list[str]) -> int | None:
    """返回首个 # 标题的行索引（跳过可选的 YAML frontmatter）。"""
    if lines and lines[0].strip() == "---":
        # 跳过 frontmatter
        for i in range(1, len(lines)):
            if lines[i].strip() == "---":
                start = i + 1
                break
        else:
            start = 0
    else:
        start = 0

    for i in range(start, len(lines)):
        if TITLE_RE.match(lines[i]):
            return i
    return None


def find_quote_block(lines: list[str], after: int) -> tuple[int, int] | None:
    """查找标题后的第一个引用块，返回 (start, end)（end 为不包含）。"""
    i = after + 1
    # 跳过标题后的空行
    while i < len(lines) and lines[i].strip() == "":
        i += 1
    if i >= len(lines) or not lines[i].lstrip().startswith(">"):
        return None
    start = i
    while i < len(lines):
        line = lines[i]
        if line.strip() == "":
            # 空行可能结束块；继续看下一行是否仍为引用
            if i + 1 < len(lines) and lines[i + 1].lstrip().startswith(">"):
                i += 1
                continue
            break
        if not line.lstrip().startswith(">"):
            break
        i += 1
    return start, i


def _find_line_starting_with(lines: list[str], prefix: str, after: int) -> int | None:
    for i in range(after, len(lines)):
        if lines[i].lstrip().startswith(prefix):
            return i
    return None


def insert_metadata(content: str, path: Path) -> str | None:
    """为文件内容插入 EN/Summary 元数据。返回修改后的内容；无需修改时返回 None。"""
    lines = content.splitlines(keepends=True)
    title_idx = find_title_line(lines)

    if title_idx is None:
        # 没有 # 标题：根据路径生成一个标题并插入到文件开头
        en = generate_en("", path)
        summary = generate_summary("", path, en)
        if is_stub(content):
            summary += " (stub/archive redirect)"
        title_text = en
        if " " not in title_text:
            title_text = filename_to_en(path.stem) or en
        new_content = f"# {title_text}\n\n"
        new_content += f"> **EN**: {en}\n"
        new_content += f"> **Summary**: {summary}\n\n"
        new_content += content
        return new_content

    title_match = TITLE_RE.match(lines[title_idx])
    assert title_match is not None
    raw_title = title_match.group(1)

    en = generate_en(raw_title, path)
    summary = generate_summary(raw_title, path, en)
    if is_stub(content):
        summary += " (stub/archive redirect)"

    en_line = f"> **EN**: {en}\n"
    summary_line = f"> **Summary**: {summary}\n"

    existing_en_match = EN_RE.search(content)
    existing_summary_match = SUMMARY_RE.search(content)
    has_en = existing_en_match is not None
    has_summary = existing_summary_match is not None
    if has_en and has_summary:
        return None

    block = find_quote_block(lines, title_idx)
    if block:
        start, end = block
        if not has_en and not has_summary:
            # 两者都缺失：插入到引用块开头
            new_lines = lines[:start]
            new_lines.append(en_line)
            new_lines.append(summary_line)
            new_lines.extend(lines[start:])
            return "".join(new_lines)
        # 仅缺失一项：在已有项的相邻位置插入
        new_lines = list(lines)
        if has_en and not has_summary:
            en_line_idx = _find_line_starting_with(lines, "> **EN**:", start)
            if en_line_idx is not None:
                insert_at = en_line_idx + 1
                new_lines.insert(insert_at, summary_line)
                return "".join(new_lines)
        if has_summary and not has_en:
            summary_line_idx = _find_line_starting_with(lines, "> **Summary**:", start)
            if summary_line_idx is not None:
                insert_at = summary_line_idx
                new_lines.insert(insert_at, en_line)
                return "".join(new_lines)
        # 兜底：插入块首
        new_lines = lines[:start]
        new_lines.append(en_line)
        new_lines.append(summary_line)
        new_lines.extend(lines[start:])
        return "".join(new_lines)
    else:
        # 标题后没有引用块，新建一个
        new_lines = lines[: title_idx + 1]
        new_lines.append("\n")
        if not has_en:
            new_lines.append(en_line)
        if not has_summary:
            new_lines.append(summary_line)
        new_lines.append("\n")
        new_lines.extend(lines[title_idx + 1 :])
        return "".join(new_lines)


def process_file(path: Path, fix: bool = False) -> dict:
    content = read_text(path)
    has_en = bool(EN_RE.search(content))
    has_summary = bool(SUMMARY_RE.search(content))
    result = {
        "path": path,
        "rel": path.relative_to(ROOT).as_posix(),
        "has_en": has_en,
        "has_summary": has_summary,
        "fixed": False,
    }
    if fix and not (has_en and has_summary):
        new_content = insert_metadata(content, path)
        if new_content is not None and new_content != content:
            write_text(path, new_content)
            result["fixed"] = True
            result["has_en"] = True
            result["has_summary"] = True
    return result


def main() -> int:
    parser = argparse.ArgumentParser(
        description="检查并补全 knowledge/ 和 docs/ 的 EN/Summary 元数据。"
    )
    parser.add_argument(
        "--fix",
        action="store_true",
        help="自动为缺失文件补全 EN/Summary（默认只检查）。",
    )
    parser.add_argument(
        "--report",
        action="store_true",
        help="将结果写入 reports/knowledge_docs_i18n_report.md。",
    )
    args = parser.parse_args()

    files = list(iter_md_files(TARGET_DIRS))
    results = [process_file(p, fix=args.fix) for p in files]

    total = len(results)
    en_count = sum(1 for r in results if r["has_en"])
    summary_count = sum(1 for r in results if r["has_summary"])
    fixed_count = sum(1 for r in results if r["fixed"])
    missing_en = [r["rel"] for r in results if not r["has_en"]]
    missing_summary = [r["rel"] for r in results if not r["has_summary"]]

    en_rate = en_count / total * 100 if total else 0
    summary_rate = summary_count / total * 100 if total else 0

    lines = []
    lines.append("# knowledge/ 与 docs/ 国际化元数据覆盖率报告\n")
    lines.append(f"扫描文件数: {total}\n")
    lines.append("\n| 指标 | 覆盖数 | 覆盖率 |")
    lines.append("|------|-------:|-------:|")
    lines.append(f"| EN 标题 | {en_count} / {total} | {en_rate:.1f}% |")
    lines.append(f"| Summary | {summary_count} / {total} | {summary_rate:.1f}% |")
    if args.fix:
        lines.append(f"| 本次修改文件数 | {fixed_count} | - |")
    lines.append("")

    if missing_en:
        lines.append(f"## 缺失 EN 标题（{len(missing_en)} 个）\n")
        for f in missing_en[:50]:
            lines.append(f"- {f}")
        lines.append("")
    if missing_summary:
        lines.append(f"## 缺失 Summary（{len(missing_summary)} 个）\n")
        for f in missing_summary[:50]:
            lines.append(f"- {f}")
        lines.append("")

    if args.fix and fixed_count:
        lines.append(f"## 已修改文件示例（前 20 个）\n")
        for r in results:
            if r["fixed"]:
                lines.append(f"- {r['rel']}")
                if len([x for x in lines if x.startswith("- ")]) >= 20:
                    break
        lines.append("")

    report_text = "\n".join(lines)
    print(report_text)

    if args.report:
        report_path = ROOT / "reports" / "knowledge_docs_i18n_report.md"
        report_path.parent.mkdir(parents=True, exist_ok=True)
        report_path.write_text(report_text, encoding="utf-8")
        print(f"\n报告已写入: {report_path}")

    return 0 if not missing_en and not missing_summary else 1


if __name__ == "__main__":
    sys.exit(main())
