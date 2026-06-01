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
                blocks.append((filepath, len(block_lines), block_text))
        else:
            i += 1
    return blocks

all_blocks = []
for root, _, files in os.walk('exercises/src'):
    for fname in files:
        if fname.endswith('.rs'):
            filepath = os.path.join(root, fname)
            blocks = extract_chinese_blocks(filepath)
            all_blocks.extend(blocks)

print(f"Total blocks in exercises: {len(all_blocks)}")
all_blocks.sort(key=lambda x: -x[1])
print("Largest blocks:")
for filepath, size, text in all_blocks[:20]:
    print(f"  {size:3d} lines: {filepath}")
    print(f"    Preview: {text[:120].replace(chr(10), ' | ')}")
