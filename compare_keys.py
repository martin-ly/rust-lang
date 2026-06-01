import json
import re

cache = json.load(open('google_translation_cache.json'))

with open('crates/c10_networks/src/p2p/mod.rs', 'r', encoding='utf-8') as f:
    lines = f.readlines()

i = 0
while i < len(lines):
    if lines[i].startswith('///') or lines[i].startswith('//!'):
        block_type = '///' if lines[i].startswith('///') else '//!'
        block_lines = []
        while i < len(lines) and lines[i].startswith(block_type):
            block_lines.append(lines[i])
            i += 1
        block_text = ''.join(block_lines).rstrip('\n')
        if re.search(r'[\u4e00-\u9fff]', block_text):
            print(f"Extracted block:")
            print(repr(block_text))
            print(f"In cache: {block_text in cache}")
            if block_text in cache:
                print(f"Translation: {repr(cache[block_text])}")
            else:
                # Try to find a similar key
                for k in list(cache.keys())[:5]:
                    print(f"  Cache key: {repr(k)}")
            break
    else:
        i += 1
