#!/usr/bin/env python3
"""修正 concept/ 中失效或 slug 错误的 RFC 链接."""
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent / "concept"
MAP_PATH = Path(__file__).resolve().parent / "rfcs_slug_map.json"

RFC_RE = re.compile(r'https://rust-lang\.github\.io/rfcs/(\d+)(?:-[^/\s]*)?\.html')


def main():
    slug_map = json.loads(MAP_PATH.read_text(encoding='utf-8'))
    changed = 0
    for p in sorted(ROOT.rglob('*.md')):
        text = p.read_text(encoding='utf-8')
        new_text = text
        for m in RFC_RE.finditer(text):
            url = m.group(0)
            num = int(m.group(1))
            slug = slug_map.get(str(num))
            if slug:
                new_url = f'https://rust-lang.github.io/rfcs/{num:04d}-{slug}.html'
            else:
                new_url = f'https://github.com/rust-lang/rfcs/pull/{num}'
            new_text = new_text.replace(url, new_url)
        if new_text != text:
            p.write_text(new_text, encoding='utf-8')
            changed += 1
    print(f'updated {changed} files')


if __name__ == '__main__':
    main()
