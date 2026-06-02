#!/usr/bin/env python3
"""为 docs/archive/ 下没有归档标记的 .md 文件添加归档头部"""
import os
from pathlib import Path

ARCHIVE_MARKER = "> **归档说明**: 本文档为历史归档文件，内容可能已过时。最新信息请参考对应活跃文档。\n\n"

def needs_marking(filepath):
    content = filepath.read_text(encoding='utf-8')
    markers = ['归档说明', 'ARCHIVED', '已归档', '历史保留', '历史归档', 'archive notice']
    return not any(m.lower() in content.lower()[:500] for m in markers)

def add_archive_mark(filepath):
    content = filepath.read_text(encoding='utf-8')
    new_content = ARCHIVE_MARKER + content
    filepath.write_text(new_content, encoding='utf-8')

def main():
    marked = 0
    skipped = 0
    for root, dirs, files in os.walk('docs/archive'):
        for f in files:
            if f.endswith('.md'):
                path = Path(root) / f
                if needs_marking(path):
                    add_archive_mark(path)
                    marked += 1
                else:
                    skipped += 1
    print(f"Marked {marked} files, skipped {skipped} files")

if __name__ == '__main__':
    main()
