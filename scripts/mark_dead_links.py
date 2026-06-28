#!/usr/bin/env python3
"""将指定的失效外链在 Markdown 中标记为 [已失效]，并保留原 URL 为 HTML 注释。"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CONCEPT = ROOT / "concept"

LINK_RE = re.compile(r'\[([^\]]+)\]\((https?://[^\s)]+)\)')


def mark_in_file(path: Path, dead_urls: set[str]) -> int:
    text = path.read_text(encoding='utf-8')
    original = text

    def repl(m):
        label, url = m.group(1), m.group(2)
        if url in dead_urls:
            return f"[{label} [已失效]]<!-- 原链接: {url} -->"
        return m.group(0)

    text = LINK_RE.sub(repl, text)
    if text != original:
        path.write_text(text, encoding='utf-8')
        return original.count('\n') - text.count('\n')  # placeholder
    return 0


def main(urls):
    dead = set(urls)
    for p in CONCEPT.rglob('*.md'):
        mark_in_file(p, dead)


if __name__ == '__main__':
    main(sys.argv[1:])
