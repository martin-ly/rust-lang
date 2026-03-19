#!/usr/bin/env python3
"""分析文档结构，识别缺少目录/主题的文件"""

import os
import re
from pathlib import Path

def find_markdown_files(root_dir):
    """递归查找所有 Markdown 文件"""
    md_files = []
    for root, dirs, files in os.walk(root_dir):
        # 跳过的目录
        skip_dirs = {'.git', 'node_modules', 'target', 'archive'}
        dirs[:] = [d for d in dirs if d not in skip_dirs]
        
        for file in files:
            if file.endswith('.md'):
                md_files.append(os.path.join(root, file))
    return md_files

def analyze_file_structure(filepath):
    """分析文件结构"""
    try:
        with open(filepath, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
    except Exception as e:
        return None
    
    lines = content.split('\n')
    
    # 检查是否有目录
    has_toc = False
    toc_patterns = [
        r'^## 目录',
        r'^## 目錄',
        r'^## Table of Contents',
        r'^## Contents',
        r'^\- \[',  # 简单的目录链接
        r'^\* \[',
    ]
    
    for line in lines[:50]:  # 检查前50行
        for pattern in toc_patterns:
            if re.search(pattern, line, re.IGNORECASE):
                has_toc = True
                break
    
    # 检查标题层级
    h1_count = len(re.findall(r'^# ', content, re.MULTILINE))
    h2_count = len(re.findall(r'^## ', content, re.MULTILINE))
    h3_count = len(re.findall(r'^### ', content, re.MULTILINE))
    
    # 检查元信息
    has_meta = bool(re.search(r'^> \*\*', content, re.MULTILINE))
    
    # 检查内容实质度
    content_lines = [l for l in lines if l.strip() and not l.startswith('#')]
    code_blocks = len(re.findall(r'```', content)) // 2
    
    # 判断是否有实质内容
    has_substance = len(content_lines) > 10 or code_blocks > 0
    
    return {
        'filepath': filepath,
        'size': len(content),
        'lines': len(lines),
        'has_toc': has_toc,
        'h1_count': h1_count,
        'h2_count': h2_count,
        'h3_count': h3_count,
        'has_meta': has_meta,
        'has_substance': has_substance,
        'code_blocks': code_blocks,
    }

def main():
    root_dir = '.'
    md_files = find_markdown_files(root_dir)
    
    print(f"扫描 {len(md_files)} 个 Markdown 文件...\n")
    
    no_toc_files = []
    no_meta_files = []
    no_substance_files = []
    
    for filepath in md_files:
        result = analyze_file_structure(filepath)
        if not result:
            continue
        
        if not result['has_toc'] and result['lines'] > 20:
            no_toc_files.append(result)
        
        if not result['has_meta'] and result['size'] > 500:
            no_meta_files.append(result)
        
        if not result['has_substance'] and result['size'] < 2000:
            no_substance_files.append(result)
    
    # 输出结果
    print("=" * 60)
    print(f"📊 统计结果")
    print("=" * 60)
    print(f"\n📝 缺少目录的文件: {len(no_toc_files)}")
    print(f"📝 缺少元信息的文件: {len(no_meta_files)}")
    print(f"⚠️  可能无实质内容的文件: {len(no_substance_files)}")
    
    print(f"\n{'='*60}")
    print("📋 缺少目录的文件 (Top 20):")
    print("=" * 60)
    for f in sorted(no_toc_files, key=lambda x: x['size'], reverse=True)[:20]:
        print(f"  {f['filepath']} ({f['lines']}行)")
    
    print(f"\n{'='*60}")
    print("📋 缺少元信息的文件 (Top 20):")
    print("=" * 60)
    for f in sorted(no_meta_files, key=lambda x: x['size'], reverse=True)[:20]:
        print(f"  {f['filepath']}")
    
    print(f"\n{'='*60}")
    print("⚠️  可能无实质内容的文件 (Top 20):")
    print("=" * 60)
    for f in no_substance_files[:20]:
        print(f"  {f['filepath']} ({f['size']} bytes)")
    
    # 保存详细报告
    with open('DOC_STRUCTURE_ANALYSIS.md', 'w', encoding='utf-8') as f:
        f.write("# 文档结构分析报告\n\n")
        f.write(f"生成时间: 2026-03-10\n\n")
        f.write(f"## 统计摘要\n\n")
        f.write(f"- 总文件数: {len(md_files)}\n")
        f.write(f"- 缺少目录: {len(no_toc_files)}\n")
        f.write(f"- 缺少元信息: {len(no_meta_files)}\n")
        f.write(f"- 可能无实质内容: {len(no_substance_files)}\n\n")
        
        f.write("## 需要添加目录的文件\n\n")
        for item in no_toc_files:
            f.write(f"- [ ] `{item['filepath']}` ({item['lines']}行)\n")
    
    print(f"\n📄 详细报告已保存到: DOC_STRUCTURE_ANALYSIS.md")

if __name__ == '__main__':
    main()
