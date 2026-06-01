#!/usr/bin/env python3
"""Strip auto-generated English translations that follow Chinese doc comments."""

import os
import re

def strip_file(filepath):
    with open(filepath, 'r', encoding='utf-8') as f:
        lines = f.readlines()
    
    new_lines = []
    modified = False
    
    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.rstrip('\n')
        
        # Check if current line is a doc comment with Chinese
        match_curr = re.match(r'^(\s*(?:///|//!)\s*)(.*)$', stripped)
        if match_curr and re.search(r'[\u4e00-\u9fff]', match_curr.group(2)):
            # Look ahead: if next line is a doc comment without Chinese, skip it
            if i + 1 < len(lines):
                next_line = lines[i + 1].rstrip('\n')
                match_next = re.match(r'^\s*(?:///|//!)\s*(.*)$', next_line)
                if match_next:
                    next_text = match_next.group(1)
                    # If next line has no Chinese, it's likely our auto-translation
                    if not re.search(r'[\u4e00-\u9fff]', next_text):
                        # Check if next-next line is also a doc comment without Chinese
                        # (in case of duplicates that dedup missed)
                        if i + 2 < len(lines):
                            next_next = lines[i + 2].rstrip('\n')
                            match_nn = re.match(r'^\s*(?:///|//!)\s*(.*)$', next_next)
                            if match_nn and not re.search(r'[\u4e00-\u9fff]', match_nn.group(1)):
                                # Skip two English lines
                                new_lines.append(line)
                                i += 3
                                modified = True
                                continue
                        # Skip one English line
                        new_lines.append(line)
                        i += 2
                        modified = True
                        continue
        
        new_lines.append(line)
        i += 1
    
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
                    if strip_file(filepath):
                        modified_files.append(filepath)
    
    print(f"Stripped translations from {len(modified_files)} files")


if __name__ == '__main__':
    main()
