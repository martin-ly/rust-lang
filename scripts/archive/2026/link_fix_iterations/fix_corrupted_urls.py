#!/usr/bin/env python3
"""修复误替换导致的 rust-lang.github.io URL 损坏."""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent / "concept"


def main():
    changed = 0
    for p in sorted(ROOT.rglob('*.md')):
        text = p.read_text(encoding='utf-8')
        # 将 https://github.com/rust-lang<project> 恢复为 https://rust-lang.github.io/<project>
        new_text = re.sub(
            r'https://github\.com/rust-lang([a-zA-Z0-9_-])',
            r'https://rust-lang.github.io/\1',
            text,
        )
        # 恢复缺失的斜杠形式（如 rust-langapi-guidelines）
        new_text = re.sub(
            r'https://rust-lang\.github\.io/([a-zA-Z0-9_-]+)([a-zA-Z0-9_/-]+\.html)',
            r'https://rust-lang.github.io/\1/\2',
            new_text,
        )
        # 恢复 rust-lang.github.io/<project>/ 结尾的斜杠
        new_text = re.sub(
            r'https://rust-lang\.github\.io/([a-zA-Z0-9_-]+)/([a-zA-Z0-9_/-]+?[^/])\.html',
            r'https://rust-lang.github.io/\1/\2.html',
            new_text,
        )
        if new_text != text:
            p.write_text(new_text, encoding='utf-8')
            changed += 1
    print(f'updated {changed} files')


if __name__ == '__main__':
    main()
