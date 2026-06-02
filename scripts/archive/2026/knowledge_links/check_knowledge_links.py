import re
import os
from pathlib import Path

knowledge_dir = Path('knowledge')
md_files = list(knowledge_dir.rglob('*.md'))

def is_in_code_block(lines, line_idx):
    in_code = False
    for i in range(line_idx + 1):
        stripped = lines[i].strip()
        if stripped.startswith('```') or stripped.startswith('~~~'):
            in_code = not in_code
    return in_code

def find_broken_links(md_file):
    content = md_file.read_text(encoding='utf-8')
    lines = content.split('\n')
    broken = []
    
    # Pattern for markdown links [text](url)
    link_pattern = re.compile(r'(?<!!)\[([^\]]+)\]\(([^)]+)\)')
    
    for line_idx, line in enumerate(lines):
        if is_in_code_block(lines, line_idx):
            continue
        
        for match in link_pattern.finditer(line):
            text = match.group(1)
            url = match.group(2).strip()
            
            # Skip pure anchors
            if url.startswith('#'):
                continue
            
            # Skip external URLs
            if url.startswith('http://') or url.startswith('https://'):
                continue

            # Skip mailto links
            if url.startswith('mailto:'):
                continue
            
            # Skip directory links
            if url.endswith('/'):
                continue
            
            # Skip other subsystems (starting with ../ and not pointing within knowledge)
            if url.startswith('../'):
                # Check if it stays within knowledge
                parts = url.split('/')
                if len(parts) > 1 and parts[1] not in ['00_start', '01_fundamentals', '02_intermediate', '03_advanced', '04_expert', '05_reference', '06_ecosystem', '99_archive']:
                    continue
            
            # Resolve the path
            src_dir = md_file.parent
            target = src_dir / url
            target_str = str(target.resolve()).replace('\\', '/')
            
            # Also check if target exists as a file
            exists = target.exists()
            if not exists and not url.endswith('.md'):
                target_md = src_dir / (url + '.md')
                if target_md.exists():
                    exists = True
            
            if not exists:
                broken.append({
                    'line': line_idx + 1,
                    'text': text,
                    'url': url,
                    'resolved': target_str
                })
    
    return broken

all_broken = {}
for md_file in md_files:
    broken = find_broken_links(md_file)
    if broken:
        rel_path = str(md_file).replace('\\', '/')
        all_broken[rel_path] = broken

if all_broken:
    for src_file, links in sorted(all_broken.items()):
        print(f'\n{src_file}')
        for link in links:
            print(f'  行 {link["line"]}: "{link["text"]}" -> {link["url"]}')
else:
    print('未发现断裂链接。')
