#!/usr/bin/env python3
"""
修复 docs/ 目录下 Markdown 文件的同文件锚点链接。

策略：
1. 为每个标题计算规范显式锚点（GitHub 风格，移除 emoji/标点，空格折叠为单连字符）。
2. 为所有标题统一添加/重写显式锚点 `{#anchor}`。
3. 更新同文件锚点链接（`#...`）使其指向对应标题的显式锚点。
4. 链接文本中混入的 `{#...}` 会被清除。

用法：
    python scripts/fix_docs_anchor_links.py [directory] [--dry-run]
    默认 directory 为 docs/
"""

import re
import sys
from pathlib import Path
from collections import Counter

DEFAULT_DIR = Path("docs")

HEADING_RE = re.compile(r"^(#{1,6})\s+(.+)$")
EXPLICIT_ANCHOR_RE = re.compile(r"\s*\{#[^}]+\}\s*$")
LINK_RE = re.compile(r"\[([^\]]+)\]\(([^)]+)\)")


def normalize_anchor(text: str) -> str:
    """GitHub 风格锚点：小写、移除 emoji/标点、空格折叠为单连字符。"""
    text = EXPLICIT_ANCHOR_RE.sub("", text)
    text = text.strip().lower()
    # 保留 \w（含 CJK）、空格、连字符
    text = re.sub(r"[^\w\s-]", "", text, flags=re.UNICODE)
    # 折叠空白为单连字符
    text = re.sub(r"\s+", "-", text)
    text = text.strip("-")
    return text


def strip_explicit_anchor(text: str) -> str:
    return EXPLICIT_ANCHOR_RE.sub("", text).rstrip()


def unescape_markdown(text: str) -> str:
    return re.sub(r"\\(.)", r"\1", text)


def strip_inline_formatting(text: str) -> str:
    text = re.sub(r"`+[^`]*`+", "", text)
    for marker in ("**", "*", "__", "_"):
        text = re.sub(re.escape(marker) + r"(.*?)" + re.escape(marker), r"\1", text)
    return text.strip()


def parse_headings(content: str):
    headings = []
    seen = Counter()
    for line in content.splitlines():
        m = HEADING_RE.match(line)
        if not m:
            continue
        level = len(m.group(1))
        raw = m.group(2).rstrip()
        display = strip_explicit_anchor(raw)
        base = normalize_anchor(raw)
        if base in seen:
            anchor = f"{base}-{seen[base]}"
        else:
            anchor = base
        seen[base] += 1
        headings.append((level, raw, display, anchor))
    return headings


def fix_file(path: Path, dry_run: bool = False):
    content = path.read_text(encoding="utf-8")
    original_lines = content.splitlines()
    headings = parse_headings(content)

    display_to_anchors = {}
    anchor_usage = Counter()
    for idx, (_, _, display, anchor) in enumerate(headings):
        display_to_anchors.setdefault(display, []).append(anchor)

    heading_raw_to_anchor = {raw: anchor for _, raw, _, anchor in headings}

    new_lines = []
    changed_headings = 0
    for line in original_lines:
        m = HEADING_RE.match(line)
        if m:
            raw = m.group(2).rstrip()
            if raw in heading_raw_to_anchor:
                anchor = heading_raw_to_anchor[raw]
                display = strip_explicit_anchor(raw)
                new_text = f"{display} {{#{anchor}}}"
                explicit = EXPLICIT_ANCHOR_RE.search(raw)
                if not explicit or anchor != explicit.group(0).strip()[2:-1].strip():
                    changed_headings += 1
                new_lines.append(f"{m.group(1)} {new_text}")
                continue
        new_lines.append(line)

    fixed_links = 0
    unfixed_links = []
    top_anchor_updated = False

    in_code_block = False
    for i, line in enumerate(new_lines):
        stripped = line.strip()
        if stripped.startswith("```"):
            in_code_block = not in_code_block
            continue
        if in_code_block:
            continue

        def replace_link(match):
            nonlocal fixed_links
            text = match.group(1)
            url = match.group(2)
            if not url.startswith("#"):
                return match.group(0)
            stripped_text = strip_explicit_anchor(text).strip()
            match_key = strip_inline_formatting(unescape_markdown(stripped_text))
            target = None
            for display_text, anchors in display_to_anchors.items():
                clean_display = strip_inline_formatting(unescape_markdown(display_text))
                if clean_display == match_key:
                    idx = anchor_usage[match_key]
                    target = anchors[idx] if idx < len(anchors) else anchors[-1]
                    anchor_usage[match_key] += 1
                    break
            if target:
                fixed_links += 1
                clean_text = strip_explicit_anchor(text)
                return f"[{clean_text}](#{target})"
            else:
                unfixed_links.append((i + 1, text, url))
                return match.group(0)

        new_lines[i] = LINK_RE.sub(replace_link, line)

    if new_lines and new_lines[0].startswith("<a id="):
        first_heading = next((h for h in headings if h[0] == 1), None)
        if first_heading:
            _, _, _, anchor = first_heading
            new_lines[0] = f'<a id="{anchor}"></a>'
            top_anchor_updated = True

    new_content = "\n".join(new_lines)
    if new_content != content and not dry_run:
        path.write_text(new_content, encoding="utf-8")

    return {
        "changed_headings": changed_headings,
        "fixed_links": fixed_links,
        "unfixed_links": unfixed_links,
        "top_anchor_updated": top_anchor_updated,
        "modified": new_content != content,
    }


def main():
    args = sys.argv[1:]
    dry_run = "--dry-run" in args
    target_dir = DEFAULT_DIR
    for arg in args:
        if arg == "--dry-run":
            continue
        target_dir = Path(arg)

    if not target_dir.exists():
        print(f"目录不存在: {target_dir}")
        sys.exit(1)

    md_files = sorted(target_dir.rglob("*.md"))
    print(f"发现 {len(md_files)} 个 Markdown 文件 in {target_dir}")
    if dry_run:
        print("(当前为预览模式，不会写入文件)\n")

    total_fixed = 0
    total_unfixed = []
    modified_files = []

    for path in md_files:
        stats = fix_file(path, dry_run=dry_run)
        if stats["modified"]:
            modified_files.append(str(path.relative_to(target_dir)))
        total_fixed += stats["fixed_links"]
        total_unfixed.extend((path.name, line, text, url) for line, text, url in stats["unfixed_links"])
        if stats["modified"] or stats["unfixed_links"]:
            print(f"  {path.name}: 规范化标题 {stats['changed_headings']} 个, 修复链接 {stats['fixed_links']} 个, 未修复 {len(stats['unfixed_links'])} 个")

    print(f"\n总计: 修改文件 {len(modified_files)} 个, 修复链接 {total_fixed} 个, 未修复 {len(total_unfixed)} 个")

    if total_unfixed:
        print("\n未修复的同文件锚点链接（无对应标题）:")
        for fname, line, text, url in total_unfixed:
            print(f"  {fname}:{line} [{text}]({url})")


if __name__ == "__main__":
    main()
