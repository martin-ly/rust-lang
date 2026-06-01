import os
import re

def analyze_file(filepath):
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    doc_lines = re.findall(r'^\s*(///|//!).*$', content, re.MULTILINE)
    chinese_doc_lines = [l for l in doc_lines if re.search(r'[\u4e00-\u9fff]', l)]
    
    if not chinese_doc_lines:
        return 0
    
    # Count how many Chinese doc lines exist
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
                if count > 0:
                    candidates.append((filepath, count))

candidates.sort(key=lambda x: x[1])
print(f"Found {len(candidates)} files with Chinese doc comments:")
for f, c in candidates:
    print(f"  {c:3d} | {f}")
