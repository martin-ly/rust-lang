#!/usr/bin/env python3
"""为 concept/07_future/ 中无状态头部的预览特性文件添加标准状态头部"""
import os
from pathlib import Path

STATUS_HEADER = """> **状态**: 🧪 Nightly 实验性
> **跟踪版本**: nightly 1.98.0 (2026-05-31)
> **预计稳定**: 待定（需等待 RFC / MCP 完成）
>
"""

def has_status_header(content):
    """检查是否已有状态头部"""
    first_500 = content[:500]
    return '状态' in first_500 and ('Nightly' in first_500 or 'MCP' in first_500 or 'RFC' in first_500 or '实验性' in first_500)

def add_status_header(filepath):
    content = filepath.read_text(encoding='utf-8')
    
    if has_status_header(content):
        return False
    
    lines = content.split('\n')
    
    # 找到第一个标题行（# 开头）
    insert_idx = 0
    for i, line in enumerate(lines):
        if line.strip().startswith('# '):
            insert_idx = i + 1
            # 如果下一个是空行，再往后移
            if insert_idx < len(lines) and lines[insert_idx].strip() == '>':
                # 已经有引用块，跳过
                while insert_idx < len(lines) and (lines[insert_idx].strip() == '>' or lines[insert_idx].strip() == ''):
                    insert_idx += 1
            break
    
    lines.insert(insert_idx, STATUS_HEADER.rstrip())
    new_content = '\n'.join(lines)
    
    filepath.write_text(new_content, encoding='utf-8')
    return True

def main():
    modified = 0
    skipped = 0
    
    preview_dir = Path('concept/07_future')
    for f in sorted(preview_dir.glob('*_preview.md')):
        if add_status_header(f):
            modified += 1
            print(f'Added header: {f.name}')
        else:
            skipped += 1
    
    print(f'\nModified: {modified}, Skipped: {skipped}')

if __name__ == '__main__':
    main()
