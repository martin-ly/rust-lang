import os
import re

directories = [
    'crates/c10_networks/src',
    'crates/c11_macro_system/src',
    'crates/c11_macro_system_proc/src',
    'crates/c12_wasm/src',
    'crates/c13_embedded/src',
    'exercises/src',
]

lines = set()
for d in directories:
    if not os.path.exists(d):
        continue
    for root, _, files in os.walk(d):
        for fname in files:
            if fname.endswith('.rs'):
                filepath = os.path.join(root, fname)
                with open(filepath, 'r', encoding='utf-8') as f:
                    for line in f:
                        line = line.rstrip('\n')
                        if line.startswith('///') or line.startswith('//!'):
                            text = line[4:] if line.startswith('/// ') else line[4:] if line.startswith('//! ') else line[3:]
                            if re.search(r'[\u4e00-\u9fff]', text) and not re.search(r'[a-zA-Z]', text):
                                lines.add(line.strip())

print(f"Unique pure Chinese lines: {len(lines)}")
for l in sorted(lines):
    print(repr(l))
