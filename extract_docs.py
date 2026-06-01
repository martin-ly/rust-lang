import os
import re

target_dirs = [
    'crates/c02_type_system', 'crates/c03_control_fn', 'crates/c04_generic',
    'crates/c05_threads', 'crates/c06_async', 'crates/c07_process',
    'crates/c08_algorithms', 'crates/c09_design_pattern', 'crates/c10_networks',
    'crates/c11_macro_system', 'crates/c11_macro_system_proc', 'crates/c12_wasm',
    'crates/c13_embedded', 'crates/exercises', 'examples',
]

lines = set()
for target in target_dirs:
    if not os.path.exists(target):
        continue
    for root, dirs, files in os.walk(target):
        dirs[:] = [d for d in dirs if d != 'target']
        for file in files:
            if file.endswith('.rs'):
                filepath = os.path.join(root, file)
                with open(filepath, 'r', encoding='utf-8') as f:
                    content = f.read()
                doc_lines = re.findall(r'^\s*(?:///|//!)\s*(.*)$', content, re.MULTILINE)
                for line in doc_lines:
                    if re.search(r'[\u4e00-\u9fff]', line):
                        lines.add(line.strip())

# Sort by length descending
lines = sorted(lines, key=len, reverse=True)
print(f"Total unique Chinese doc lines: {len(lines)}")
for line in lines[:200]:
    print(repr(line))
