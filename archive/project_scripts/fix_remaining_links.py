#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""批量修复剩余断链"""

import json
import re
from pathlib import Path

def fix_directory_links(content):
    """修复指向目录的链接，改为指向 README.md"""
    # 匹配 ](path/) 但不以 .md 结尾的链接
    pattern = r'\]\(([^)]+/)(?!.*\.md)\)'
    
    def replace_link(match):
        path = match.group(1)
        # 如果路径以 / 结尾，添加 README.md
        if path.endswith('/'):
            return f']({path}README.md)'
        return match.group(0)
    
    return re.sub(pattern, replace_link, content)

def fix_specific_patterns(content, file_path):
    """修复特定模式"""
    
    # 修复 archive/temp 中的 rust-formal-engineering-system 链接
    if 'archive/temp' in str(file_path):
        content = content.replace(
            '../../rust-formal-engineering-system/01_theoretical_foundations/04_concurrency_models/',
            '../../rust-formal-engineering-system/03_design_patterns/04_concurrent/README.md'
        )
        content = content.replace(
            '../../rust-formal-engineering-system/01_theoretical_foundations/08_macro_system/',
            '../../rust-formal-engineering-system/03_compiler_theory/README.md'
        )
        content = content.replace(
            '../../rust-formal-engineering-system/01_theoretical_foundations/01_type_system/generics/',
            '../../rust-formal-engineering-system/01_theoretical_foundations/01_type_system/README.md'
        )
    
    # 修复 research_notes 中的目录链接
    if 'research_notes' in str(file_path):
        # 修复 software_design_theory 子目录链接
        for subdir in ['01_design_patterns_formal', '02_workflow_safe_complete_models', 
                       '03_execution_models', '04_compositional_engineering', 
                       '05_boundary_system', '05_distributed', '02_workflow']:
            content = content.replace(
                f'](./software_design_theory/{subdir}/)',
                f'](./software_design_theory/{subdir}/README.md)'
            )
            content = content.replace(
                f'](software_design_theory/{subdir}/)',
                f'](software_design_theory/{subdir}/README.md)'
            )
    
    return content

def main():
    docs_path = Path('e:/_src/rust-lang/docs')
    
    # 读取断链报告
    with open(docs_path / 'link_check_report.json', 'r', encoding='utf-8') as f:
        data = json.load(f)
    
    fixed_count = 0
    
    # 处理每个有断链的文件
    for file_path_str, broken_links in data['broken_by_file'].items():
        full_path = docs_path / file_path_str
        if not full_path.exists():
            continue
        
        try:
            with open(full_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            original_content = content
            
            # 应用修复
            content = fix_directory_links(content)
            content = fix_specific_patterns(content, file_path_str)
            
            # 如果有修改，保存
            if content != original_content:
                with open(full_path, 'w', encoding='utf-8') as f:
                    f.write(content)
                fixed_count += 1
                print(f'Fixed: {file_path_str} ({len(broken_links)} links)')
        
        except Exception as e:
            print(f'Error processing {file_path_str}: {e}')
    
    print(f'\nTotal files fixed: {fixed_count}')

if __name__ == '__main__':
    main()
