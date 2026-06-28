#!/usr/bin/env python3
"""检查 concept/knowledge/book 中的同文件锚点问题"""
import re
import os
from pathlib import Path

def github_slug(text):
    text = text.strip()
    text = re.sub(r'\s*\{#[^}]+\}\s*$', '', text)
    # 剥离 Markdown 链接，保留链接文本（GitHub 锚点基于渲染后的纯文本）
    text = re.sub(r'\[([^\]]+)\]\([^)]+\)', r'\1', text)
    text = re.sub(r'\\(.)', r'\1', text)
    text = re.sub(r'\*\*(.+?)\*\*', r'\1', text)
    text = re.sub(r'\*(.+?)\*', r'\1', text)
    text = re.sub(r'`(.+?)`', r'\1', text)
    text = text.lower()
    text = re.sub(r'[^\w\s-]', '', text, flags=re.UNICODE)
    text = re.sub(r' ', '-', text.strip())
    text = text.strip('-')
    return text

def check_dir(base_dir):
    issues = []
    for root, dirs, files in os.walk(base_dir):
        if any(x in root for x in ['archive', 'research_notes', 'rust-ownership-decidability', '99_archive']):
            continue
        for f in files:
            if not f.endswith('.md'):
                continue
            path = Path(root) / f
            content = path.read_text(encoding='utf-8')
            headers = set(github_slug(h) for h in re.findall(r'^#{1,6}\s+(.+)$', content, re.MULTILINE))
            for m in re.finditer(r'\[([^\]]*)\]\(#([^)]+)\)', content):
                anchor = m.group(2).lower().strip()
                if anchor not in headers and github_slug(m.group(1)) not in headers:
                    issues.append((str(path), m.group(0)))
    return issues

def main():
    total = 0
    for d in ['concept', 'knowledge', 'book']:
        issues = check_dir(d)
        total += len(issues)
        print(f'{d}: {len(issues)} broken same-file anchors')
        for path, link in issues[:3]:
            print(f'  {path}: {link[:80]}')
    print(f'\nTotal active anchor issues: {total}')

if __name__ == '__main__':
    main()
