#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""最终批量修复断链"""

import json
import re
from pathlib import Path

def fix_file(filepath, docs_path):
    """修复单个文件的断链"""
    full_path = docs_path / filepath
    if not full_path.exists():
        return 0
    
    with open(full_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    original = content
    
    # 通用修复规则
    replacements = [
        # 修复 archive/deprecated 中的研究笔记链接
        (r'\.\./\.\./research_notes/', '../../../research_notes/'),
        (r'\.\./\.\./\.\./research_notes/', '../../../../research_notes/'),
        
        # 修复形式化方法链接
        (r'\.\./formal_methods/', '../../research_notes/formal_methods/'),
        (r'\.\./type_theory/', '../../research_notes/type_theory/'),
        
        # 修复 coq_skeleton 链接
        (r'\.\./coq_skeleton/', './coq_skeleton/'),
        
        # 修复 software_design_theory 子目录链接
        (r'\(\./software_design_theory/(\w+)/\)', r'(./software_design_theory/\1/README.md)'),
        
        # 修复 archive/process_reports 链接
        (r'\.\./\.\./archive/process_reports/2026_02/', '../../archive/process_reports/'),
        
        # 修复占位符链接
        (r'\[文档名\]\(path\)', '文档名'),
        (r'\[研究路线图\]\(wrong/absolute/path/RESEARCH_ROADMAP\.md\)', '研究路线图'),
        (r'\[xx\]\(path/to/doc\.md\)', 'xx'),
        (r'\[矩阵文档 §节名\]\(path\)', '矩阵文档 §节名'),
        (r'\[\.\*\\\]\(\(\.\*\)\)', '正则表达式'),
    ]
    
    for pattern, replacement in replacements:
        content = re.sub(pattern, replacement, content)
    
    if content != original:
        with open(full_path, 'w', encoding='utf-8') as f:
            f.write(content)
        return 1
    return 0

def main():
    docs_path = Path('e:/_src/rust-lang/docs')
    
    with open(docs_path / 'link_check_report.json', 'r', encoding='utf-8') as f:
        data = json.load(f)
    
    fixed_files = 0
    for file_path in data['broken_by_file'].keys():
        if fix_file(file_path, docs_path):
            fixed_files += 1
            print(f'Fixed: {file_path}')
    
    print(f'\nTotal files fixed: {fixed_files}')

if __name__ == '__main__':
    main()
