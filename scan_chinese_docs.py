import os
import re

def has_chinese_doc_comments(filepath):
    """Check if file has Chinese //! or /// doc comments."""
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Find all doc comment lines
    doc_comments = re.findall(r'^\s*///.*$', content, re.MULTILINE)
    mod_docs = re.findall(r'^\s*//!.*$', content, re.MULTILINE)
    all_docs = doc_comments + mod_docs
    
    if not all_docs:
        return False, False, []
    
    # Check if any doc comment contains Chinese characters
    has_chinese = any(re.search(r'[\u4e00-\u9fff]', line) for line in all_docs)
    
    # Check if any doc comment contains English words (simple heuristic)
    has_english = any(re.search(r'[a-zA-Z]{3,}', line) for line in all_docs)
    
    return has_chinese, has_english, all_docs[:10]

def main():
    target_dirs = [
        'crates/c02_type_system',
        'crates/c03_control_fn',
        'crates/c04_generic',
        'crates/c05_threads',
        'crates/c06_async',
        'crates/c07_process',
        'crates/c08_algorithms',
        'crates/c09_design_pattern',
        'crates/c10_networks',
        'crates/c11_macro_system',
        'crates/c11_macro_system_proc',
        'crates/c12_wasm',
        'crates/c13_embedded',
        'crates/exercises',
        'examples',
    ]
    
    candidates = []
    for target in target_dirs:
        if not os.path.exists(target):
            continue
        for root, dirs, files in os.walk(target):
            # Skip target directories
            dirs[:] = [d for d in dirs if d != 'target']
            for file in files:
                if file.endswith('.rs'):
                    filepath = os.path.join(root, file)
                    has_chinese, has_english, samples = has_chinese_doc_comments(filepath)
                    if has_chinese and not has_english:
                        candidates.append(filepath)
    
    print(f"Found {len(candidates)} files with Chinese-only doc comments:")
    for f in candidates:
        print(f)

if __name__ == '__main__':
    main()
