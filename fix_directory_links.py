#!/usr/bin/env python3
"""修复 Markdown 中的目录链接，将其改为指向 README.md"""

import os
import re
from pathlib import Path

def find_markdown_files(root_dir):
    """递归查找所有 Markdown 文件"""
    md_files = []
    for root, dirs, files in os.walk(root_dir):
        # 跳过 archive 和 .git 目录
        dirs[:] = [d for d in dirs if d not in ['.git', 'archive', 'node_modules']]
        for file in files:
            if file.endswith('.md'):
                md_files.append(os.path.join(root, file))
    return md_files

def fix_directory_links_in_file(filepath):
    """修复文件中的目录链接"""
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    original_content = content
    fixes = []
    
    # 匹配 Markdown 链接: [text](./path/)
    # 捕获以 / 结尾的相对路径链接
    pattern = r'\[([^\]]+)\]\((\.?[^)]+)\/\)'
    
    def replace_link(match):
        link_text = match.group(1)
        link_path = match.group(2)
        
        # 跳过已经是 .md 结尾的链接
        if link_path.endswith('.md'):
            return match.group(0)
        
        # 构建可能的 README 路径
        base_dir = os.path.dirname(filepath)
        target_dir = os.path.normpath(os.path.join(base_dir, link_path))
        
        # 检查目标目录是否存在
        if os.path.isdir(target_dir):
            # 检查 README.md 是否存在
            readme_path = os.path.join(target_dir, 'README.md')
            if os.path.exists(readme_path):
                new_link = f'[{link_text}]({link_path}/README.md)'
                fixes.append(f"{link_path}/ -> {link_path}/README.md")
                return new_link
        
        return match.group(0)
    
    new_content = re.sub(pattern, replace_link, content)
    
    if new_content != original_content:
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(new_content)
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
            fixes = fix_directory_links_in_file(filepath)
            if fixes:
                fixed_files.append((filepath, fixes))
                total_fixes += len(fixes)
        except Exception as e:
            print(f"处理 {filepath} 时出错: {e}")
    
    print(f"\n修复完成!")
    print(f"修复文件数: {len(fixed_files)}")
    print(f"修复链接数: {total_fixes}")
    
    if fixed_files:
        print("\n修复详情:")
        for filepath, fixes in fixed_files[:10]:  # 只显示前10个
            print(f"\n{filepath}:")
            for fix in fixes:
                print(f"  - {fix}")

if __name__ == '__main__':
    main()
