#!/usr/bin/env python3
"""Strip auto-generated mixed Chinese-English doc comment lines."""

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
        
        match = re.match(r'^(\s*(?:///|//!)\s*)(.*)$', stripped)
        if not match:
            new_lines.append(line)
            i += 1
            continue
        
        text = match.group(2)
        has_chinese = bool(re.search(r'[\u4e00-\u9fff]', text))
        has_english = bool(re.search(r'[a-zA-Z]{4,}', text))
        
        # If a doc comment line has BOTH Chinese and substantial English,
        # and the English looks like a bad auto-translation (no spaces between
        # words, or Chinese particles like 了/的/和 mixed in),
        # then it's likely a bad translation - remove it.
        if has_chinese and has_english:
            # Check for Chinese particles that indicate bad word-by-word translation
            chinese_particles = re.search(r'[了的是与为将]', text)
            # Check for concatenated English words (lowercase followed immediately by uppercase)
            concatenated = re.search(r'[a-z][A-Z]', text)
            # Check for all-lowercase English followed immediately by Chinese
            mixed_boundary = re.search(r'[a-z]{3,}[\u4e00-\u9fff]', text)
            
            if chinese_particles or concatenated or mixed_boundary:
                modified = True
                i += 1
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
    
    print(f"Stripped mixed translations from {len(modified_files)} files")


if __name__ == '__main__':
    main()
