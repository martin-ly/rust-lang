import os
import re

def check_file(filepath):
    with open(filepath, 'r', encoding='utf-8') as f:
        lines = f.readlines()
    
    patterns = []
    for i, line in enumerate(lines):
        if line.startswith('///') or line.startswith('//!'):
            text = line[4:].strip() if line.startswith('/// ') else line[4:].strip() if line.startswith('//! ') else line[3:].strip()
            if text and not re.search(r'[\u4e00-\u9fff]', text):
                # Check if previous line is Chinese doc comment
                if i > 0 and (lines[i-1].startswith('///') or lines[i-1].startswith('//!')):
                    prev_text = lines[i-1][4:].strip() if lines[i-1].startswith('/// ') else lines[i-1][4:].strip() if lines[i-1].startswith('//! ') else lines[i-1][3:].strip()
                    if re.search(r'[\u4e00-\u9fff]', prev_text):
                        patterns.append((i, lines[i-1].strip(), line.strip()))
    return patterns

directories = [
    'crates/c10_networks/src',
    'crates/c11_macro_system/src',
    'crates/c11_macro_system_proc/src',
    'crates/c12_wasm/src',
    'crates/c13_embedded/src',
    'exercises/src',
]

files_with_broken = []
for d in directories:
    if not os.path.exists(d):
        continue
    for root, _, files in os.walk(d):
        for fname in files:
            if fname.endswith('.rs'):
                filepath = os.path.join(root, fname)
                patterns = check_file(filepath)
                if patterns:
                    files_with_broken.append((filepath, patterns))

print(f"Files with English following Chinese on consecutive lines: {len(files_with_broken)}")
for fp, pats in files_with_broken[:20]:
    print(f"\n{fp}:")
    for _, ch, en in pats[:3]:
        print(f"  {ch}")
        print(f"  {en}")
