#!/usr/bin/env python3
"""修复所有剩余断链"""

import os
import re
from pathlib import Path

def find_markdown_files(root_dir):
    md_files = []
    for root, dirs, files in os.walk(root_dir):
        dirs[:] = [d for d in dirs if d not in ['.git', 'node_modules']]
        for file in files:
            if file.endswith('.md'):
                md_files.append(os.path.join(root, file))
    return md_files

def fix_file(filepath):
    with open(filepath, 'r', encoding='utf-8', errors='ignore') as f:
        content = f.read()
    
    original = content
    fixes = []
    
    # 1. 修复 archive/deprecated/ 链接到 docs/archive/deprecated/
    if 'archive/deprecated/' in content and 'docs/archive/deprecated/' not in content:
        # 计算相对路径
        rel_path = os.path.relpath('docs/archive/deprecated', os.path.dirname(filepath))
        content = re.sub(r'\]\((\.\.?/?)*archive/deprecated/', f']({rel_path}/', content)
        fixes.append('archive/deprecated -> docs/archive/deprecated')
    
    # 2. 修复 docs/docs/ 双重路径
    if 'docs/docs/' in content:
        content = content.replace('docs/docs/', 'docs/')
        fixes.append('docs/docs/ -> docs/')
    
    # 3. 修复 research_notes/research_notes/
    if 'research_notes/research_notes/' in content:
        content = content.replace('research_notes/research_notes/', 'research_notes/')
        fixes.append('research_notes/research_notes/ -> research_notes/')
    
    # 4. 修复 .md.md 错误
    if '.md.md' in content:
        content = content.replace('.md.md', '.md')
        fixes.append('.md.md -> .md')
    
    # 5. 修复 xxx/ 占位符
    if 'crates/xxx/' in content or '/xxx/' in content:
        # 跳过修复，这些是模板示例
        pass
    
    # 6. 修复路径中的特殊字符
    if '{}' in content or '{#}' in content:
        # 移除或替换锚点中的特殊字符
        content = re.sub(r'\{#.*?\}', '', content)
        fixes.append('移除特殊锚点')
    
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
    for fp, fixes in fixed_files[:20]:
        print(f"  {fp}: {fixes}")

if __name__ == '__main__':
    main()
