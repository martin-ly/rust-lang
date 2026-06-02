#!/usr/bin/env python3
"""修复剩余的损坏链接"""
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
    
    same_file_pattern = re.compile(r'\[(.*?)\]\(#([^)]+)\)')
    
    def replace_same_file(match):
        link_text = match.group(1)
        anchor = match.group(2).lower().strip()
        
        if anchor in header_slugs:
            return match.group(0)
        
        link_slug = github_slug(link_text)
        if link_slug in header_slugs:
            return f'[{link_text}](#{link_slug})'
        
        # Anchor doesn't exist - downgrade to plain text
        return link_text
    
    new_content = same_file_pattern.sub(replace_same_file, content)
    
    # Cross-file links
    cross_file_pattern = re.compile(r'\[(.*?)\]\(([^)]+\.md)(?:#([^)]+))?\)')
    
    def replace_cross_file(match):
        link_text = match.group(1)
        target_file = match.group(2)
        anchor = match.group(3)
        
        source_dir = filepath.parent
        resolved = source_dir / target_file
        
        if not resolved.exists():
            return link_text
        
        if anchor:
            target_content = resolved.read_text(encoding='utf-8')
            target_headers = re.findall(r'^#{1,6}\s+(.+)$', target_content, re.MULTILINE)
            target_slugs = {github_slug(h) for h in target_headers}
            anchor_clean = anchor.lower().strip()
            
            if anchor_clean in target_slugs:
                return match.group(0)
            
            link_slug = github_slug(link_text)
            if link_slug in target_slugs:
                return f'[{link_text}]({target_file}#{link_slug})'
            
            return f'[{link_text}]({target_file})'
        
        return match.group(0)
    
    new_content = cross_file_pattern.sub(replace_cross_file, new_content)
    
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
                if fix_file(Path(root) / f):
                    fixed_files += 1
    print(f'Fixed links in {fixed_files} files')

if __name__ == '__main__':
    main()
