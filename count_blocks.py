import os
import re

def extract_chinese_blocks(filepath):
    with open(filepath, 'r', encoding='utf-8') as f:
        lines = f.readlines()
    blocks = []
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

file_info = []
for d in directories:
    if not os.path.exists(d):
        continue
    for root, _, files in os.walk(d):
        for fname in files:
            if fname.endswith('.rs'):
                filepath = os.path.join(root, fname)
                blocks = extract_chinese_blocks(filepath)
                if blocks:
                    file_info.append((filepath, len(blocks), sum(len(b.split('\n')) for b in blocks)))

file_info.sort(key=lambda x: -x[1])
print(f"Total files: {len(file_info)}")
print("Top 50 by block count:")
for f, bc, lc in file_info[:50]:
    print(f"  {bc:3d} blocks ({lc:4d} lines): {f}")

# Group by directory
from collections import defaultdict
by_dir = defaultdict(int)
for f, bc, lc in file_info:
    d = f.split('/')[1]  # e.g., c10_networks
    by_dir[d] += bc

print("\nBlocks by directory:")
for d, c in sorted(by_dir.items(), key=lambda x: -x[1]):
    print(f"  {d}: {c} blocks")
