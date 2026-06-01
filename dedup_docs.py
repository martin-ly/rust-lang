#!/usr/bin/env python3
"""Remove duplicate consecutive doc comment lines from Rust files."""

import os
import re

def dedup_file(filepath):
    with open(filepath, 'r', encoding='utf-8') as f:
        lines = f.readlines()
    
    new_lines = []
    prev_doc = None
    modified = False
    
    for line in lines:
        stripped = line.rstrip('\n')
        match = re.match(r'^(\s*(?:///|//!)\s*)(.*)$', stripped)
        
        if match:
            prefix = match.group(1)
            text = match.group(2)
            # Check if this is a duplicate of the previous doc comment (same text)
            if prev_doc is not None and text == prev_doc:
                modified = True
                continue  # Skip duplicate
            prev_doc = text
        else:
            prev_doc = None
        
        new_lines.append(line)
    
    if modified:
        with open(filepath, 'w', encoding='utf-8') as f:
            f.writelines(new_lines)
    
    return modified


def main():
    target_dirs = [
        'crates/c02_type_system', 'crates/c03_control_fn', 'crates/c04_generic',
        'crates/c05_threads', 'crates/c06_async', 'crates/c07_process',
        'crates/c08_algorithms', 'crates/c09_design_pattern', 'crates/c10_networks',
        'crates/c11_macro_system', 'crates/c11_macro_system_proc', 'crates/c12_wasm',
        'crates/c13_embedded', 'crates/exercises', 'examples',
    ]
    
    modified_files = []
    for target in target_dirs:
        if not os.path.exists(target):
            continue
        for root, dirs, files in os.walk(target):
            dirs[:] = [d for d in dirs if d != 'target']
            for file in files:
                if file.endswith('.rs'):
                    filepath = os.path.join(root, file)
                    if dedup_file(filepath):
                        modified_files.append(filepath)
    
    print(f"Deduped {len(modified_files)} files")


if __name__ == '__main__':
    main()
