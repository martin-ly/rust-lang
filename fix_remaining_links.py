#!/usr/bin/env python3
"""修复剩余的路径问题"""

import os
import re

def find_markdown_files(root_dir):
    md_files = []
    for root, dirs, files in os.walk(root_dir):
        dirs[:] = [d for d in dirs if d not in ['.git', 'node_modules']]
        for file in files:
            if file.endswith('.md'):
                md_files.append(os.path.join(root, file))
    return md_files

def fix_file(filepath):
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    original = content
    fixes = []
    
    # 1. 修复 docs/crates/ 路径错误
    if 'docs/crates/' in content:
        content = content.replace('docs/crates/', '../crates/')
        fixes.append('docs/crates/ -> ../crates/')
    
    # 2. 修复 xxx 占位符链接
    if 'crates/xxx/' in content or 'xxx/docs' in content or 'xxx/examples' in content:
        # 这些通常是示例链接，保留或替换为通用说明
        pass
    
    # 3. 修复相对路径文本
    if '[相对路径]' in content or '](相对路径)' in content:
        content = content.replace('](相对路径)', '](./docs/)')
        fixes.append('相对路径 -> ./docs/')
    
    # 4. 修复其他.md链接
    if 'other.md' in content:
        content = content.replace('other.md', 'README.md')
        fixes.append('other.md -> README.md')
    
    if content != original:
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(content)
        return fixes
    return []

def main():
    md_files = find_markdown_files('.')
    total_fixes = 0
    fixed_files = []
    
    print(f"扫描 {len(md_files)} 个文件...")
    
    for filepath in md_files:
        try:
            fixes = fix_file(filepath)
            if fixes:
                fixed_files.append((filepath, fixes))
                total_fixes += len(fixes)
        except Exception as e:
            pass
    
    print(f"修复了 {len(fixed_files)} 个文件，{total_fixes} 处链接")
    for fp, fixes in fixed_files[:10]:
        print(f"  {fp}: {fixes}")

if __name__ == '__main__':
    main()
