import re

with open('chinese_blocks.txt', 'r', encoding='utf-8') as f:
    content = f.read()

blocks = [b.strip() for b in content.split('---BLOCK---\n')[1:] if b.strip()]

patterns = {
    'rust_feature_module': 0,
    'exercise_title': 0,
    'version_info': 0,
    'module_desc': 0,
    'trait_impl': 0,
    'other': 0,
}

examples = {}

for b in blocks:
    first_line = b.split('\n')[0].strip()
    if re.search(r'Rust \d+\.\d+.*新特性', first_line):
        patterns['rust_feature_module'] += 1
        examples.setdefault('rust_feature_module', b)
    elif re.search(r'# 练习 \d+:', first_line):
        patterns['exercise_title'] += 1
        examples.setdefault('exercise_title', b)
    elif re.search(r'# 版本信息', first_line):
        patterns['version_info'] += 1
        examples.setdefault('version_info', b)
    elif re.search(r'^(///|//!) (本模块|本库|本文件|本 crate)', first_line):
        patterns['module_desc'] += 1
        examples.setdefault('module_desc', b)
    elif 'trait' in b.lower() and 'impl' in b.lower():
        patterns['trait_impl'] += 1
        examples.setdefault('trait_impl', b)
    else:
        patterns['other'] += 1

for k, v in patterns.items():
    print(f"{k}: {v}")
    if k in examples:
        print(f"  Example: {examples[k][:100].replace(chr(10), ' | ')}")
        print()

# More detailed pattern analysis
print("\n=== First lines starting with specific patterns ===")
first_lines = [b.split('\n')[0].strip() for b in blocks]

print(f"\nStarts with '//! Rust': {sum(1 for l in first_lines if l.startswith('//! Rust'))}")
print(f"Starts with '//! # 练习': {sum(1 for l in first_lines if l.startswith('//! # 练习'))}")
print(f"Starts with '//! # C': {sum(1 for l in first_lines if l.startswith('//! # C'))}")
print(f"Starts with '/// # Trait': {sum(1 for l in first_lines if l.startswith('/// # Trait'))}")
print(f"Starts with '/// #': {sum(1 for l in first_lines if l.startswith('/// #'))}")
print(f"Starts with '//! #': {sum(1 for l in first_lines if l.startswith('//! #'))}")
print(f"Starts with '/// ```': {sum(1 for l in first_lines if l.startswith('/// ```'))}")
print(f"Starts with '//! ```': {sum(1 for l in first_lines if l.startswith('//! ```'))}")
print(f"Starts with '/// 本': {sum(1 for l in first_lines if l.startswith('/// 本'))}")
print(f"Starts with '//! 本': {sum(1 for l in first_lines if l.startswith('//! 本'))}")
print(f"Starts with '/// ' and no #: {sum(1 for l in first_lines if l.startswith('/// ') and '#' not in l and '```' not in l)}")
print(f"Starts with '//! ' and no #: {sum(1 for l in first_lines if l.startswith('//! ') and '#' not in l and '```' not in l)}")
