#!/usr/bin/env python3
import re

# Fix 1: rust_195_features.rs - add ``` before code blocks
with open('crates/c02_type_system/src/rust_195_features.rs', 'r', encoding='utf-8') as f:
    lines = f.read().split('\n')

new_lines = []
for i, line in enumerate(lines):
    m = re.match(r'^(\s*)/// let mut ', line)
    if m:
        indent = m.group(1)
        if i > 0 and lines[i-1].strip() != '/// ```':
            new_lines.append(indent + '/// ```')
    new_lines.append(line)

with open('crates/c02_type_system/src/rust_195_features.rs', 'w', encoding='utf-8') as f:
    f.write('\n'.join(new_lines))
print('Fixed rust_195_features.rs')

# Fix 2: precise_capturing_guide.rs - convert doc comments to regular comments
with open('crates/c02_type_system/src/precise_capturing_guide.rs', 'r', encoding='utf-8') as f:
    content = f.read()

content = content.replace('//! ', '// ')
content = content.replace('/// ', '// ')

with open('crates/c02_type_system/src/precise_capturing_guide.rs', 'w', encoding='utf-8') as f:
    f.write(content)
print('Fixed precise_capturing_guide.rs')

# Fix 3: rust_191_features.rs - fix fullwidth parentheses in doc comments
with open('crates/c02_type_system/src/rust_191_features.rs', 'r', encoding='utf-8') as f:
    content = f.read()

# Replace fullwidth parentheses with halfwidth in doc comments
content = content.replace('（如', '(如')
content = content.replace('）', ')')
content = content.replace('（', '(')
content = content.replace('）', ')')

with open('crates/c02_type_system/src/rust_191_features.rs', 'w', encoding='utf-8') as f:
    f.write(content)
print('Fixed rust_191_features.rs')
