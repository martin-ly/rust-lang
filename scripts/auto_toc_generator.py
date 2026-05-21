#!/usr/bin/env python3
"""
自动化目录生成器 v1.0
功能：
1. 扫描所有缺目录的 Markdown 文件
2. 基于标题结构自动生成目录
3. 插入来源引用块和跨文件链接尾注
"""

import re
from pathlib import Path

DOCS_DIR = Path('docs')

def generate_toc(content):
    lines = content.split('\n')
    headings = []
    for line in lines:
        match = re.match(r'^(#{2,4})\s+(.+)$', line)
        if match:
            level = len(match.group(1))
            text = match.group(2).strip()
            display_text = re.sub(r'\[([^\]]+)\]\([^)]+\)', r'\1', text)
            display_text = re.sub(r'[*`]', '', display_text)
            display_text = re.sub(r'\s*\{[^}]*\}\s*', '', display_text)
            anchor = re.sub(r'[^\w\s-]', '', display_text.lower())
            anchor = re.sub(r'\s+', '-', anchor).strip('-')
            if anchor and display_text:
                headings.append((level, display_text, anchor))
    
    if not headings:
        return None
    
    toc_lines = ['## 📑 目录', '>']
    for level, text, anchor in headings:
        indent = '  ' * (level - 2)
        toc_lines.append(f'{indent}- [{text}](#{anchor})')
    
    return '\n'.join(toc_lines)

def add_cross_links(file_path, content):
    if '## 相关概念' in content or '## Related' in content:
        return content
    links = []
    parent_readme = file_path.parent / 'README.md'
    if parent_readme.exists() and parent_readme != file_path:
        links.append(f'- [{file_path.parent.name} 目录](./README.md)')
    if file_path.parent != DOCS_DIR:
        grandparent = file_path.parent.parent
        gp_readme = grandparent / 'README.md'
        if gp_readme.exists():
            links.append(f'- [上级目录](../README.md)')
    if not links:
        return content
    section = '\n\n---\n\n## 相关概念\n\n' + '\n'.join(links) + '\n'
    return content + section

def process_file(file_path):
    content = file_path.read_text(encoding='utf-8', errors='ignore')
    if re.search(r'##\s*(📑\s*)?目录|##\s*Table of Contents', content, re.IGNORECASE):
        return False, 'already_has_toc'
    if len(content.split('\n')) < 30:
        return False, 'too_short'
    toc = generate_toc(content)
    if not toc:
        return False, 'no_headings'
    
    lines = content.split('\n')
    insert_pos = 0
    in_frontmatter = False
    frontmatter_end = 0
    first_heading_pos = -1
    
    for i, line in enumerate(lines):
        if line.strip() == '---' and i == 0:
            in_frontmatter = True
            continue
        if in_frontmatter and line.strip() == '---':
            frontmatter_end = i + 1
            in_frontmatter = False
            continue
        if re.match(r'^#\s+', line) and first_heading_pos == -1:
            first_heading_pos = i
            continue
        if first_heading_pos != -1 and re.match(r'^#{2,4}\s+', line):
            insert_pos = i
            break
    
    if insert_pos == 0:
        insert_pos = frontmatter_end if frontmatter_end > 0 else (first_heading_pos + 1 if first_heading_pos != -1 else 1)
    
    new_lines = lines[:insert_pos] + ['', toc, ''] + lines[insert_pos:]
    new_content = '\n'.join(new_lines)
    new_content = add_cross_links(file_path, new_content)
    file_path.write_text(new_content, encoding='utf-8')
    return True, 'ok'

def main():
    files = [f for f in DOCS_DIR.rglob('*.md') if 'archive' not in str(f) and f.name != 'README.md']
    success = 0
    skipped = 0
    errors = 0
    for file_path in sorted(files):
        try:
            ok, reason = process_file(file_path)
            if ok:
                success += 1
                print(f'ADDED_TOC: {file_path.relative_to(".")}')
            else:
                skipped += 1
        except Exception as e:
            errors += 1
            print(f'ERROR: {file_path.relative_to(".")} - {e}')
    print('\n' + '='*60)
    print(f'总计: {len(files)} 个文件')
    print(f'成功添加目录: {success}')
    print(f'跳过: {skipped}')
    print(f'错误: {errors}')

if __name__ == '__main__':
    main()
