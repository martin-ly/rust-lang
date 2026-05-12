#!/usr/bin/env python3
"""代码块标记审计：为不完整片段添加 ignore 标记"""

import os, re

FRAGMENT_FILES = []

for root, dirs, files in os.walk('concept'):
    for f in files:
        if not f.endswith('.md'):
            continue
        path = os.path.join(root, f)
        with open(path, 'r', encoding='utf-8') as fh:
            content = fh.read()
        
        # Find ```rust blocks without modifiers
        pattern = r'```rust\n(.*?)\n```'
        matches = list(re.finditer(pattern, content, re.DOTALL))
        
        fragments = []
        for m in matches:
            code = m.group(1).strip()
            has_main = 'fn main' in code
            has_fn = code.startswith('fn ') or '\nfn ' in code
            has_impl = code.startswith('impl ') or '\nimpl ' in code
            has_struct = code.startswith('struct ') or '\nstruct ' in code
            has_trait = code.startswith('trait ') or '\ntrait ' in code
            is_single_line = code.count('\n') < 1
            is_short = len(code) < 80
            
            # Fragment criteria: no main, no function/struct/trait/impl, short
            if not has_main and not has_fn and not has_impl and not has_struct and not has_trait and (is_single_line or is_short):
                fragments.append((m.start(), m.group(0), code[:60]))
        
        if fragments:
            FRAGMENT_FILES.append((path, len(fragments)))
            print(f'{path}: {len(fragments)} fragments')
            for _, _, preview in fragments:
                print(f'  -> {preview}...')

print(f'\nTotal files with fragments: {len(FRAGMENT_FILES)}')
