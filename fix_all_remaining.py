#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""批量修复所有剩余断链"""

import json
import re
from pathlib import Path

def main():
    docs_path = Path('e:/_src/rust-lang/docs')
    
    with open(docs_path / 'link_check_report.json', 'r', encoding='utf-8') as f:
        data = json.load(f)
    
    fixed_total = 0
    
    for file_path_str, broken_links in data['broken_by_file'].items():
        full_path = docs_path / file_path_str
        if not full_path.exists():
            continue
        
        try:
            with open(full_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            original_content = content
            
            for link in broken_links:
                target = link['link_target']
                text = link['link_text']
                
                # 跳过代码语法误报
                if any(x in target for x in [' T', 'a, b', 'item T', 'x T']) and 'T ' in text:
                    continue
                if text.startswith('\\'):  # LaTeX
                    continue
                if '{}' in target:  # 模板
                    continue
                if target == 'path' or target == '(.*)' or target == 'path/to/doc.md':
                    # 占位符链接，移除
                    pattern = rf'\[{re.escape(text)}\]\({re.escape(target)}\)'
                    content = re.sub(pattern, text, content)
                    continue
                
                # 修复特定模式
                # 1. 目录链接 -> README.md
                if target.endswith('/') and not target.startswith('http'):
                    old = f']({target})'
                    new = f']({target}README.md)'
                    content = content.replace(old, new)
                
                # 2. archive/process_reports 链接
                if '../archive/process_reports/2026_02/' in target:
                    content = content.replace(
                        '](../archive/process_reports/2026_02/)',
                        '](../archive/process_reports/)'
                    )
                
                # 3. coq_skeleton 链接
                if 'coq_skeleton/' in target and '../' in target:
                    content = content.replace(
                        '../coq_skeleton/',
                        './coq_skeleton/'
                    )
                
                # 4. 修复 software_design_theory 链接
                for subdir in ['01_design_patterns_formal', '02_workflow', '03_execution_models', 
                               '04_compositional_engineering', '05_boundary_system']:
                    if f'{subdir}/' in target and 'README.md' not in target:
                        content = content.replace(
                            f']({subdir}/)',
                            f']({subdir}/README.md)'
                        )
            
            if content != original_content:
                with open(full_path, 'w', encoding='utf-8') as f:
                    f.write(content)
                fixed_total += len(broken_links)
                print(f'Fixed: {file_path_str} ({len(broken_links)} links)')
        
        except Exception as e:
            print(f'Error: {file_path_str}: {e}')
    
    print(f'\nTotal links fixed: {fixed_total}')

if __name__ == '__main__':
    main()
