import json
import re

cache = json.load(open('google_translation_cache.json'))

with open('crates/c10_networks/src/p2p/mod.rs', 'r', encoding='utf-8') as f:
    lines = f.readlines()

i = 0
while i < len(lines):
    line = lines[i]
    if line.startswith('///') or line.startswith('//!'):
        block_type = '///' if line.startswith('///') else '//!'
        block_lines = []
        while i < len(lines) and lines[i].startswith(block_type):
            block_lines.append(lines[i])
            i += 1
        block_text = ''.join(block_lines)
        if re.search(r'[\u4e00-\u9fff]', block_text):
            print(f"Found Chinese block:")
            print(repr(block_text))
            print(f"In cache: {block_text in cache}")
            if block_text in cache:
                print(f"Translation: {repr(cache[block_text])}")
            print()
    else:
        i += 1
