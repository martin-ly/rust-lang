#!/usr/bin/env python3
"""批量修复 Markdown 文件中的损坏锚点链接"""
import re
import os
from pathlib import Path

def github_slug(text):
    text = text.strip()
    # Remove explicit {#id}
    text = re.sub(r'\s*\{#[^}]+\}\s*$', '', text)
    # Unescape backslash sequences
    text = re.sub(r'\\(.)', r'\1', text)
    # Remove markdown formatting
    text = re.sub(r'\*\*(.+?)\*\*', r'\1', text)
    text = re.sub(r'\*(.+?)\*', r'\1', text)
    text = re.sub(r'`(.+?)`', r'\1', text)
    text = text.lower()
    # Remove all non-word, non-space, non-hyphen characters (including emojis)
    text = re.sub(r'[^\w\s-]', '', text, flags=re.UNICODE)
    # Replace spaces with hyphens
    text = re.sub(r'\s+', '-', text.strip())
    # Remove leading/trailing hyphens
    text = text.strip('-')
    return text

def fix_anchors_in_file(filepath):
    content = filepath.read_text(encoding='utf-8')
    original = content
    
    headers = re.findall(r'^#{1,6}\s+(.+)$', content, re.MULTILINE)
    header_slugs = {github_slug(h): h for h in headers}
    link_pattern = re.compile(r'\[(.*?)\]\(#([^)]+)\)')
    
    def replace_link(match):
        link_text = match.group(1)
        anchor = match.group(2)
        anchor_clean = anchor.lower().strip()
        
        if anchor_clean in header_slugs:
            return match.group(0)
        
        link_slug = github_slug(link_text)
        if link_slug in header_slugs:
            return f'[{link_text}](#{link_slug})'
        
        if anchor_clean.startswith('-'):
            without_leading = anchor_clean.lstrip('-')
            if without_leading in header_slugs:
                return f'[{link_text}](#{without_leading})'
        
        cleaned_anchor = re.sub(r'[\uFE00-\uFE0F\u200B-\u200F]', '', anchor_clean)
        if cleaned_anchor in header_slugs:
            return f'[{link_text}](#{cleaned_anchor})'
        
        stripped = re.sub(r'[^\w\s-]', '', anchor_clean, flags=re.UNICODE).strip().strip('-')
        stripped = re.sub(r'\s+', '-', stripped)
        if stripped in header_slugs:
            return f'[{link_text}](#{stripped})'
        
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
