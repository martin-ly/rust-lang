import os
import re

def analyze_file(filepath):
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    doc_lines = re.findall(r'^\s*(///|//!).*$', content, re.MULTILINE)
    chinese_doc_lines = [l for l in doc_lines if re.search(r'[\u4e00-\u9fff]', l)]
    
    if not chinese_doc_lines:
        return None
    
    # Check if file already has English translations
    # A simple heuristic: for each Chinese doc line, check if next non-empty line is an English doc line
    lines = content.split('\n')
    has_english_pair = False
    for i, line in enumerate(lines):
        if re.match(r'^\s*(///|//!)', line) and re.search(r'[\u4e00-\u9fff]', line):
            # Check next few lines for English doc comment without Chinese
            for j in range(i+1, min(i+5, len(lines))):
                next_line = lines[j].strip()
                if next_line.startswith('///') or next_line.startswith('//!'):
                    if not re.search(r'[\u4e00-\u9fff]', next_line) and re.search(r'[a-zA-Z]{3,}', next_line):
                        has_english_pair = True
                        break
                elif next_line and not next_line.startswith('//'):
                    break
    
    if has_english_pair:
        return None
    
    return len(chinese_doc_lines)

target_dirs = [
    'crates/c02_type_system', 'crates/c03_control_fn', 'crates/c04_generic',
    'crates/c05_threads', 'crates/c06_async', 'crates/c07_process',
    'crates/c08_algorithms', 'crates/c09_design_pattern', 'crates/c10_networks',
    'crates/c11_macro_system', 'crates/c11_macro_system_proc', 'crates/c12_wasm',
    'crates/c13_embedded', 'crates/exercises', 'examples',
]

candidates = []
for target in target_dirs:
    if not os.path.exists(target):
        continue
    for root, dirs, files in os.walk(target):
        dirs[:] = [d for d in dirs if d != 'target']
        for file in files:
            if file.endswith('.rs'):
                filepath = os.path.join(root, file)
                count = analyze_file(filepath)
                if count:
                    candidates.append((filepath, count))

candidates.sort(key=lambda x: x[1])
print(f"Found {len(candidates)} files needing translation:")
for f, c in candidates:
    print(f"  {c:3d} | {f}")
