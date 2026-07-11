#!/usr/bin/env python3
"""
修正 docs/ 中同文件锚点链接，使其与标题实际锚点一致。

本脚本不修改标题本身，仅：
1. 解析每个标题的显式锚点（{#...}）或按 GitHub 风格计算锚点。
2. 对同文件链接（#...）根据链接文本匹配到对应标题。
3. 清除链接文本中混入的 {#...}，并将 URL 更新为标题的正确锚点。

匹配规则：链接文本清除显式锚点和内联格式后，与标题显示文本（同样清除内联格式）一致。
"""
import re
from pathlib import Path
from collections import Counter

DOCS_DIR = Path("docs")

HEADING_RE = re.compile(r"^(#{1,6})\s+(.+)$")
EXPLICIT_ANCHOR_RE = re.compile(r"\s*\{#[^}]+\}\s*$")
LINK_RE = re.compile(r"\[([^\]]+)\]\((#[^)]+)\)")


def strip_explicit_anchor(text: str) -> str:
    return EXPLICIT_ANCHOR_RE.sub("", text).rstrip()


def normalize_anchor(text: str) -> str:
    text = EXPLICIT_ANCHOR_RE.sub("", text)
    text = text.strip().lower()
    text = re.sub(r"[^\w\s-]", "", text, flags=re.UNICODE)
    text = re.sub(r"\s+", "-", text)
    text = text.strip("-")
    return text


def strip_inline_formatting(text: str) -> str:
    text = re.sub(r"`+[^`]*`+", "", text)
    for marker in ("**", "*", "__", "_"):
        text = re.sub(re.escape(marker) + r"(.*?)" + re.escape(marker), r"\1", text)
    return text.strip()


def unescape_md(text: str) -> str:
    return re.sub(r"\\(.)", r"\1", text)


def parse_headings(content: str):
    headings = []
    seen = Counter()
    for line in content.splitlines():
        m = HEADING_RE.match(line)
        if not m:
            continue
        raw = m.group(2).rstrip()
        display = strip_explicit_anchor(raw)
        explicit = EXPLICIT_ANCHOR_RE.search(raw)
        if explicit:
            anchor = explicit.group(0).strip()[2:-1].strip()
        else:
            base = normalize_anchor(raw)
            if base in seen:
                anchor = f"{base}-{seen[base]}"
            else:
                anchor = base
            seen[base] += 1
        headings.append((display, anchor))
    return headings


def fix_file(path: Path) -> int:
    content = path.read_text(encoding="utf-8")
    original = content

    headings = parse_headings(content)
    display_to_anchors = {}
    for display, anchor in headings:
        display_to_anchors.setdefault(display, []).append(anchor)

    anchor_usage = Counter()

    def replace_link(m):
        text = m.group(1)
        url = m.group(2)
        clean_text = strip_explicit_anchor(text).strip()
        key = strip_inline_formatting(unescape_md(clean_text))
        target = None
        for display, anchors in display_to_anchors.items():
            disp_key = strip_inline_formatting(unescape_md(display))
            if disp_key == key:
                idx = anchor_usage[key]
                target = anchors[idx] if idx < len(anchors) else anchors[-1]
                anchor_usage[key] += 1
                break
        if target is None:
            return m.group(0)
        return f"[{clean_text}](#{target})"

    content = LINK_RE.sub(replace_link, content)

    if content != original:
        path.write_text(content, encoding="utf-8")
        return 1
    return 0


def main():
    files = sorted(DOCS_DIR.rglob("*.md"))
    modified = 0
    for path in files:
        if fix_file(path):
            modified += 1
    print(f"已修改文件: {modified}")


if __name__ == "__main__":
    main()
