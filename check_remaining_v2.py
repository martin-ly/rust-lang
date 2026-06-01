import os
import re

target_dirs = [
    'crates/c02_type_system', 'crates/c03_control_fn', 'crates/c04_generic',
    'crates/c05_threads', 'crates/c06_async', 'crates/c07_process',
    'crates/c08_algorithms', 'crates/c09_design_pattern', 'crates/c10_networks',
    'crates/c11_macro_system', 'crates/c11_macro_system_proc', 'crates/c12_wasm',
    'crates/c13_embedded', 'crates/exercises', 'examples',
]

remaining = []
for target in target_dirs:
    if not os.path.exists(target):
        continue
    for root, dirs, files in os.walk(target):
        dirs[:] = [d for d in dirs if d != 'target']
        for file in files:
            if file.endswith('.rs'):
                filepath = os.path.join(root, file)
                with open(filepath, 'r', encoding='utf-8') as f:
                    lines = f.readlines()
                
                for i, line in enumerate(lines):
                    stripped = line.rstrip('\n')
                    match = re.match(r'^\s*(?:///|//!)(?!/)\s*(.*)$', stripped)
                    if match:
                        text = match.group(1)
                        if not re.search(r'[\u4e00-\u9fff]', text):
                            continue
                        
                        # Check if line already has substantial English (bilingual inline)
                        english_words = re.findall(r'[a-zA-Z]{4,}', text)
                        chinese_chars = len(re.findall(r'[\u4e00-\u9fff]', text))
                        if len(english_words) >= 2 and chinese_chars < len(english_words) * 3:
                            continue  # Already bilingual enough
                        
                        # Check if next line is English translation
                        has_translation = False
                        for j in range(i+1, min(i+5, len(lines))):
                            next_line = lines[j].rstrip('\n')
                            next_match = re.match(r'^\s*(?:///|//!)(?!/)\s*(.*)$', next_line)
                            if next_match:
                                next_text = next_match.group(1)
                                if not re.search(r'[\u4e00-\u9fff]', next_text) and re.search(r'[a-zA-Z]{3,}', next_text):
                                    has_translation = True
                                    break
                            elif next_line.strip() and not next_line.strip().startswith('//'):
                                break
                        
                        if not has_translation:
                            remaining.append((filepath, i+1, text))

print(f"Remaining truly untranslated Chinese doc lines: {len(remaining)}")
for filepath, line_no, text in remaining[:30]:
    print(f"  {filepath}:{line_no} | {text[:80]}")
