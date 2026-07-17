#!/usr/bin/env python3
"""
Fix malformed TOC anchors in docs/ Markdown files.

Pattern: [text {#id}](#<slug>-<id>)
Fix:     [text](#unescaped_id)

Also fixes the simple duplicate: [#id-id] -> [#id]
"""
import re
from pathlib import Path
from urllib.parse import quote

DOCS_BASE = Path('e:/_src/rust-lang/docs')

def unescape_markdown(s: str) -> str:
    """Unescape markdown special characters in a string."""
    return s.replace(r'\_', '_').replace(r'\\', '\\').replace(r'\[', '[').replace(r'\]', ']').replace(r'\*', '*').replace(r'\`', '`')

def fix_toc_links(content: str) -> str:
    """Replace malformed TOC link anchors with clean explicit IDs."""
    # Pattern: [text { #id }](url)
    # We need a non-greedy match for text, then an explicit {#id}, then the URL.
    # The link text may contain escaped brackets/underscores.
    link_re = re.compile(r'\[([^\]]+\{#[^}]+\})\]\(([^)]+)\)')

    def replacer(match):
        text_part = match.group(1)
        url = match.group(2)

        # Extract the explicit ID
        id_match = re.search(r'\{#([^}]+)\}\s*$', text_part)
        if not id_match:
            return match.group(0)

        raw_id = id_match.group(1)
        clean_id = unescape_markdown(raw_id)

        # Remove the explicit ID from the link text
        clean_text = re.sub(r'\s*\{#[^}]+\}\s*$', '', text_part)

        # Build new URL
        if url.startswith('#'):
            new_url = f'#{clean_id}'
        else:
            # If URL contains #, keep the path and fix the anchor
            if '#' in url:
                path, _ = url.split('#', 1)
                new_url = f'{path}#{clean_id}'
            else:
                # No anchor to fix, shouldn't happen for this pattern
                return match.group(0)

        return f'[{clean_text}]({new_url})'

    return link_re.sub(replacer, content)

def main():
    md_files = list(DOCS_BASE.rglob('*.md'))
    changed_files = []

    for md_file in md_files:
        try:
            content = md_file.read_text(encoding='utf-8')
        except Exception as e:
            print(f'警告: 无法读取 {md_file}: {e}')
            continue

        new_content = fix_toc_links(content)
        if new_content != content:
            md_file.write_text(new_content, encoding='utf-8')
            changed_files.append(str(md_file))

    print(f'已处理 {len(md_files)} 个文件，修改 {len(changed_files)} 个文件')
    if changed_files:
        print(f'前 10 个修改文件:')
        for f in changed_files[:10]:
            print(f'  - {f}')

if __name__ == '__main__':
    main()
