#!/usr/bin/env python3
"""批量修复 Markdown 文件中的损坏锚点链接 (v2 - 多种 slug 策略)"""
import re
import os
from pathlib import Path

def github_slug(text):
    """GitHub 风格锚点 slug"""
    text = text.strip()
    text = re.sub(r'\s*\{#[^}]+\}\s*$', '', text)
    text = re.sub(r'\\(.)', r'\1', text)
    text = re.sub(r'\*\*(.+?)\*\*', r'\1', text)
    text = re.sub(r'\*(.+?)\*', r'\1', text)
    text = re.sub(r'`(.+?)`', r'\1', text)
    text = text.lower()
    text = re.sub(r'[^\w\s-]', '', text, flags=re.UNICODE)
    text = re.sub(r'\s+', '-', text.strip())
    text = text.strip('-')
    return text

def toc_slug(text):
    """TOC 生成器风格锚点 slug（某些生成器把 → 替换为 -）"""
    text = text.strip()
    text = re.sub(r'\s*\{#[^}]+\}\s*$', '', text)
    text = re.sub(r'\\(.)', r'\1', text)
    text = re.sub(r'\*\*(.+?)\*\*', r'\1', text)
    text = re.sub(r'\*(.+?)\*', r'\1', text)
    text = re.sub(r'`(.+?)`', r'\1', text)
    text = text.lower()
    # Replace specific chars with hyphen instead of removing
    text = re.sub(r'[→~—]', '-', text)
    text = re.sub(r'[^\w\s-]', '', text, flags=re.UNICODE)
    text = re.sub(r'\s+', '-', text.strip())
    # Collapse multiple hyphens
    text = re.sub(r'-+', '-', text)
    text = text.strip('-')
    return text

def fix_anchors_in_file(filepath):
    content = filepath.read_text(encoding='utf-8')
    original = content
    
    headers = re.findall(r'^#{1,6}\s+(.+)$', content, re.MULTILINE)
    header_slugs_github = {github_slug(h): h for h in headers}
    header_slugs_toc = {toc_slug(h): h for h in headers}
    
    link_pattern = re.compile(r'\[(.*?)\]\(#([^)]+)\)')
    
    def replace_link(match):
        link_text = match.group(1)
        anchor = match.group(2)
        anchor_clean = anchor.lower().strip()
        
        if anchor_clean in header_slugs_github or anchor_clean in header_slugs_toc:
            return match.group(0)
        
        # Try link text with both slug styles
        link_slug_gh = github_slug(link_text)
        if link_slug_gh in header_slugs_github:
            return f'[{link_text}](#{link_slug_gh})'
        if link_slug_gh in header_slugs_toc:
            return f'[{link_text}](#{link_slug_gh})'
        
        link_slug_toc = toc_slug(link_text)
        if link_slug_toc in header_slugs_toc:
            return f'[{link_text}](#{link_slug_toc})'
        if link_slug_toc in header_slugs_github:
            return f'[{link_text}](#{link_slug_toc})'
        
        # Try cleaning the anchor itself
        cleaned = re.sub(r'[\uFE00-\uFE0F\u200B-\u200F]', '', anchor_clean)
        if cleaned in header_slugs_github or cleaned in header_slugs_toc:
            return f'[{link_text}](#{cleaned})'
        
        # Try collapsing multiple hyphens in anchor
        collapsed = re.sub(r'-+', '-', anchor_clean).strip('-')
        if collapsed in header_slugs_github or collapsed in header_slugs_toc:
            return f'[{link_text}](#{collapsed})'
        
        return match.group(0)
    
    new_content = link_pattern.sub(replace_link, content)
    if new_content != original:
        filepath.write_text(new_content, encoding='utf-8')
        return True
    return False

def main():
    fixed_files = 0
    for root, dirs, files in os.walk('docs'):
        dirs[:] = [d for d in dirs if not d.startswith('.')]
        for f in files:
            if f.endswith('.md'):
                if fix_anchors_in_file(Path(root) / f):
                    fixed_files += 1
    print(f'Fixed anchors in {fixed_files} files')

if __name__ == '__main__':
    main()
