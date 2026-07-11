#!/usr/bin/env python3
"""应用外部链接替换映射到 concept/ 下的 Markdown 文件。"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CONCEPT_DIR = ROOT / "concept"

def apply_replacements(mapping):
    files = set()
    # 支持 dict {old: new} 或 list[{"old_url": ..., "new_url": ...}]
    if isinstance(mapping, list):
        items = [(entry['old_url'], entry['new_url']) for entry in mapping if entry.get('status') == 'replaced']
    else:
        items = list(mapping.items())
    # 按 old_url 长度降序，避免短 URL 误替换长 URL 的前缀
    items = sorted(items, key=lambda kv: len(kv[0]), reverse=True)
    for p in CONCEPT_DIR.rglob('*.md'):
        text = p.read_text(encoding='utf-8')
        original = text
        for old, new in items:
            text = text.replace(old, new)
        if text != original:
            p.write_text(text, encoding='utf-8')
            files.add(p)
    print(f'已修改 {len(files)} 个文件')

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print('Usage: apply_link_replacements.py <mapping.json>')
        sys.exit(1)
    data = json.loads(Path(sys.argv[1]).read_text(encoding='utf-8'))
    apply_replacements(data)
