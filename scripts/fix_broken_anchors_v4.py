#!/usr/bin/env python3
"""修复指向不存在标题的锚点链接：降级为纯文本 (v4)"""
import re
import os
from pathlib import Path

def github_slug(text):
    text = text.strip()
    text = re.sub(r'\s*\{#[^}]+\}\s*$', '', text)
    text = re.sub(r'\\(.)', r'\1', text)
    text = re.sub(r'\*\*(.+?)\*\*', r'\1', text)
    text = re.sub(r'\*(.+?)\*', r'\1', text)
    text = re.sub(r'`(.+?)`', r'\1', text)
    text = text.lower()
    text = re.sub(r'[^\w\s-]', '', text, flags=re.UNICODE)
    text = re.sub(r' ', '-', text.strip())
    text = text.strip('-')
    return text

def fix_file(filepath):
    content = filepath.read_text(encoding='utf-8')
    original = content
    
    headers = re.findall(r'^#{1,6}\s+(.+)$', content, re.MULTILINE)
    header_slugs = {github_slug(h) for h in headers}
    
    def replace_link(match):
        link_text = match.group(1)
        anchor = match.group(2).lower().strip()
        
        if anchor in header_slugs:
            return match.group(0)
        
        link_slug = github_slug(link_text)
        if link_slug in header_slugs:
            return f'[{link_text}](#{link_slug})'
        
        # 标题不存在，降级为纯文本
        return link_text
    
    new_content = re.sub(r'\[(.*?)\]\(#([^)]+)\)', replace_link, content)
    if new_content != original:
        filepath.write_text(new_content, encoding='utf-8')
        return True
    return False

def main():
    fixed_files = 0
    for root, dirs, files in os.walk('docs'):
        if any(x in root for x in ['archive', 'research_notes', 'rust-ownership-decidability']):
            continue
        dirs[:] = [d for d in dirs if not d.startswith('.')]
        for f in files:
            if f.endswith('.md'):
                if fix_file(Path(root) / f):
                    fixed_files += 1
    print(f'Fixed broken anchors in {fixed_files} files')

if __name__ == '__main__':
    main()
