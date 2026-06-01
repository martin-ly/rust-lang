import os
import re
import json

def extract_chinese_blocks(filepath):
    with open(filepath, 'r', encoding='utf-8') as f:
        lines = f.readlines()
    
    blocks = []
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith('///') or line.startswith('//!'):
            block = []
            while i < len(lines) and (lines[i].startswith('///') or lines[i].startswith('//!')):
                block.append(lines[i])
                i += 1
            text = ''.join(block)
            if re.search(r'[\u4e00-\u9fff]', text):
                blocks.append(''.join(block))
        else:
            i += 1
    return blocks

directories = [
    'crates/c10_networks/src',
    'crates/c11_macro_system/src',
    'crates/c11_macro_system_proc/src',
    'crates/c12_wasm/src',
    'crates/c13_embedded/src',
    'exercises/src'
]

all_blocks = set()
file_count = 0
for d in directories:
    if not os.path.exists(d):
        continue
    for root, _, files in os.walk(d):
        for fname in files:
            if fname.endswith('.rs'):
                filepath = os.path.join(root, fname)
                blocks = extract_chinese_blocks(filepath)
                if blocks:
                    file_count += 1
                for b in blocks:
                    all_blocks.add(b)

print(f"Files with Chinese comments: {file_count}")
print(f"Unique Chinese comment blocks: {len(all_blocks)}")

# Save to file for analysis
with open('chinese_blocks.txt', 'w', encoding='utf-8') as f:
    for b in sorted(all_blocks):
        f.write('---BLOCK---\n')
        f.write(b)
        f.write('\n')
