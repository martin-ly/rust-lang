import os
import re

def extract_blocks(filepath):
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
            text = ''.join(block_lines)
            has_chinese = bool(re.search(r'[\u4e00-\u9fff]', text))
            has_english = bool(re.search(r'[a-zA-Z]', text))
            if has_chinese and not has_english:
                blocks.append(''.join(block_lines))
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

all_blocks = []
for d in directories:
    if not os.path.exists(d):
        continue
    for root, _, files in os.walk(d):
        for fname in files:
            if fname.endswith('.rs'):
                filepath = os.path.join(root, fname)
                blocks = extract_blocks(filepath)
                for b in blocks:
                    all_blocks.append((filepath, b))

print(f"Total pure Chinese blocks: {len(all_blocks)}\n")
for fp, b in all_blocks:
    print(f"File: {fp}")
    print(f"Block:\n{b}")
    print("-" * 40)
