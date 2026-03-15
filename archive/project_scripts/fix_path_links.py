#!/usr/bin/env python3
"""修复常见的路径错误"""

import os
import re
from pathlib import Path

def find_markdown_files(root_dir):
    """递归查找所有 Markdown 文件"""
    md_files = []
    for root, dirs, files in os.walk(root_dir):
        dirs[:] = [d for d in dirs if d not in ['.git', 'node_modules']]
        for file in files:
            if file.endswith('.md'):
                md_files.append(os.path.join(root, file))
    return md_files

def fix_common_path_issues(filepath):
    """修复常见的路径问题"""
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    original_content = content
    fixes = []
    
    # 1. 修复 docs/docs/ 双重路径问题
    new_content = re.sub(r'\]\((\.\.?/?)docs/docs/', r'](\1docs/', content)
    if new_content != content:
        fixes.append("docs/docs/ -> docs/")
        content = new_content
    
    # 2. 修复从 docs/ 文件到 research_notes/ 的错误相对路径
    # 如果文件在 docs/ 目录下，research_notes 应该是 ./research_notes/ 而不是 ../../research_notes/
    if filepath.startswith('.\\docs\\') or filepath.startswith('./docs/'):
        # 修复过多的 ../
        new_content = re.sub(r'\]\(\.\./\.\./research_notes/', r'](./research_notes/', content)
        if new_content != content:
            fixes.append("../../research_notes/ -> ./research_notes/")
            content = new_content
    
    # 3. 修复从 docs/01_learning/ 到 research_notes/ 的路径
    if 'docs\\01_learning' in filepath or 'docs/01_learning' in filepath:
        new_content = re.sub(r'\]\(\.\./\.\./research_notes/', r'](./research_notes/', content)
        if new_content != content:
            fixes.append("../../research_notes/ -> ./research_notes/")
            content = new_content
    
    # 4. 修复从 docs/ 到 crates/ 的错误路径
    if filepath.startswith('.\\docs\\') or filepath.startswith('./docs/'):
        new_content = re.sub(r'\]\(\.\./\.\./crates/', r'](./crates/', content)
        if new_content != content:
            fixes.append("../../crates/ -> ./crates/")
            content = new_content
    
    # 5. 修复 docs/ 到 docs/ 的双重路径
    new_content = re.sub(r'\.\./docs/docs/', r'../docs/', content)
    if new_content != content:
        fixes.append("../docs/docs/ -> ../docs/")
        content = new_content
    
    if content != original_content:
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(content)
        return fixes
    
    return []

def main():
    root_dir = '.'
    md_files = find_markdown_files(root_dir)
    
    total_fixes = 0
    fixed_files = []
    
    print(f"扫描 {len(md_files)} 个 Markdown 文件...")
    
    for filepath in md_files:
        try:
            fixes = fix_common_path_issues(filepath)
            if fixes:
                fixed_files.append((filepath, fixes))
                total_fixes += len(fixes)
        except Exception as e:
            print(f"处理 {filepath} 时出错: {e}")
    
    print(f"\n修复完成!")
    print(f"修复文件数: {len(fixed_files)}")
    print(f"修复链接数: {total_fixes}")
    
    if fixed_files:
        print("\n修复详情 (前20个):")
        for filepath, fixes in fixed_files[:20]:
            print(f"\n{filepath}:")
            for fix in fixes:
                print(f"  - {fix}")

if __name__ == '__main__':
    main()
