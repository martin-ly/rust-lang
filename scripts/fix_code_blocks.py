#!/usr/bin/env python3
"""为不完整片段添加 ignore 标记"""

import os, re

for root, dirs, files in os.walk('concept'):
    for f in files:
        if not f.endswith('.md'):
            continue
        path = os.path.join(root, f)
        with open(path, 'r', encoding='utf-8') as fh:
            content = fh.read()
        
        original = content
        pattern = r'```rust\n(.*?)\n```'
        
        def replace_block(m):
            code = m.group(1).strip()
            has_main = 'fn main' in code
            has_fn = code.startswith('fn ') or '\nfn ' in code
            has_impl = code.startswith('impl ') or '\nimpl ' in code
            has_struct = code.startswith('struct ') or '\nstruct ' in code
            has_trait = code.startswith('trait ') or '\ntrait ' in code
            is_single_line = code.count('\n') < 1
            is_short = len(code) < 80
            
            if not has_main and not has_fn and not has_impl and not has_struct and not has_trait and (is_single_line or is_short):
                return f'```rust,ignore\n{m.group(1)}\n```'
            return m.group(0)
        
        content = re.sub(pattern, replace_block, content, flags=re.DOTALL)
        
        if content != original:
            with open(path, 'w', encoding='utf-8') as fh:
                fh.write(content)
            print(f'Fixed: {path}')

print('Done.')
