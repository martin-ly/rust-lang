import os
import re

def needs_translation(filepath):
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    doc_lines = re.findall(r'^\s*(///|//!).*$', content, re.MULTILINE)
    if not doc_lines:
        return False, 0
    
    chinese_only = []
    for line in doc_lines:
        has_chinese = re.search(r'[\u4e00-\u9fff]', line)
        # Skip lines that already have substantial English text mixed in
        # Allow some English words like Rust, API names, version numbers
        english_words = re.findall(r'[a-zA-Z]{4,}', line)
        chinese_chars = len(re.findall(r'[\u4e00-\u9fff]', line))
        
        if has_chinese:
            # If there are substantial English words alongside Chinese, it might already be bilingual
            # But we need to check if it's truly bilingual or just has English terms
            if len(english_words) >= 3 and chinese_chars < len(english_words) * 2:
                # Likely already has English, skip
                continue
            chinese_only.append(line)
    
    return len(chinese_only) > 0, len(chinese_only)

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
                needs, count = needs_translation(filepath)
                if needs:
                    candidates.append((filepath, count))

candidates.sort(key=lambda x: x[1], reverse=True)
print(f"Found {len(candidates)} files needing translation:")
for f, c in candidates:
    print(f"  {c:3d} | {f}")
