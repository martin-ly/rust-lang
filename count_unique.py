import os
import re

def extract_blocks(filepath):
    with open(filepath, 'r', encoding='utf-8') as f:
        lines = f.readlines()
    blocks = []
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
                blocks.append(block_text)
        else:
            i += 1
    return blocks

directories = [
    'crates/c10_networks/src',
    'crates/c11_macro_system/src',
    'crates/c11_macro_system_proc/src',
    'crates/c12_wasm/src',
    'crates/c13_embedded/src',
    'exercises/src',
]

all_blocks = set()
for d in directories:
    if not os.path.exists(d):
        continue
    for root, _, files in os.walk(d):
        for fname in files:
            if fname.endswith('.rs'):
                filepath = os.path.join(root, fname)
                blocks = extract_blocks(filepath)
                for b in blocks:
                    all_blocks.add(b)

print(f"Unique blocks in files: {len(all_blocks)}")

import json
cache = json.load(open('google_translation_cache.json'))
print(f"Cache entries: {len(cache)}")

missing = [b for b in all_blocks if b not in cache]
print(f"Missing translations: {len(missing)}")
for b in missing[:10]:
    print(f"  {repr(b[:80])}")
