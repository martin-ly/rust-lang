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
            block_lines = [lines[i]]
            i += 1
            # Continue while same type AND same language pattern
            while i < len(lines) and lines[i].startswith(block_type):
                block_lines.append(lines[i])
                i += 1
            blocks.append((block_type, block_lines))
        else:
            i += 1
    return blocks

def analyze_file(filepath):
    blocks = extract_blocks(filepath)
    chinese_blocks = []
    english_blocks = []
    mixed_blocks = []
    
    for block_type, lines in blocks:
        text = ''.join(lines)
        has_chinese = bool(re.search(r'[\u4e00-\u9fff]', text))
        has_english = bool(re.search(r'[a-zA-Z]', text))
        
        if has_chinese and has_english:
            mixed_blocks.append(lines)
        elif has_chinese:
            chinese_blocks.append(lines)
        elif has_english:
            english_blocks.append(lines)
    
    return chinese_blocks, english_blocks, mixed_blocks

directories = [
    'crates/c10_networks/src',
    'crates/c11_macro_system/src',
    'crates/c11_macro_system_proc/src',
    'crates/c12_wasm/src',
    'crates/c13_embedded/src',
    'exercises/src',
]

total_chinese = 0
total_mixed = 0
files_with_chinese = []
files_with_mixed = []

for d in directories:
    if not os.path.exists(d):
        continue
    for root, _, files in os.walk(d):
        for fname in files:
            if fname.endswith('.rs'):
                filepath = os.path.join(root, fname)
                chinese, english, mixed = analyze_file(filepath)
                if chinese:
                    total_chinese += len(chinese)
                    files_with_chinese.append((filepath, len(chinese)))
                if mixed:
                    total_mixed += len(mixed)
                    files_with_mixed.append((filepath, len(mixed)))

print(f"Files with pure Chinese blocks: {len(files_with_chinese)}")
print(f"Total pure Chinese blocks: {total_chinese}")
print(f"Files with mixed Chinese+English blocks: {len(files_with_mixed)}")
print(f"Total mixed blocks: {total_mixed}")

print("\nTop files with pure Chinese blocks:")
for f, c in sorted(files_with_chinese, key=lambda x: -x[1])[:20]:
    print(f"  {c:3d} {f}")
