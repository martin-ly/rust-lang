#!/usr/bin/env python3
import re

with open('crates/c02_type_system/src/rust_195_features.rs', 'r', encoding='utf-8') as f:
    content = f.read()

# For each code block starting with ``` followed by let mut dq/let mut list,
# add the appropriate use statement after the opening ```
lines = content.split('\n')
new_lines = []
i = 0
while i < len(lines):
    line = lines[i]
    new_lines.append(line)
    # Check if this is an opening ``` in a doc comment
    if line.strip() == '/// ```':
        # Look ahead to determine what type is used
        j = i + 1
        while j < len(lines) and lines[j].strip() != '/// ```':
            if 'VecDeque' in lines[j]:
                new_lines.append(line.replace('```', 'use std::collections::VecDeque;'))
                break
            elif 'LinkedList' in lines[j]:
                new_lines.append(line.replace('```', 'use std::collections::LinkedList;'))
                break
            j += 1
    i += 1

with open('crates/c02_type_system/src/rust_195_features.rs', 'w', encoding='utf-8') as f:
    f.write('\n'.join(new_lines))

print('Done')
