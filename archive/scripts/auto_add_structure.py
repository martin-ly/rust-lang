#!/usr/bin/env python3
"""自动为 Markdown 文件添加目录和元信息"""

import os
import re
from pathlib import Path

def extract_headings(content):
    """提取所有标题"""
    headings = []
    for match in re.finditer(r'^(#{1,4})\s+(.+)$', content, re.MULTILINE):
        level = len(match.group(1))
        title = match.group(2).strip()
        # 清理标题中的 markdown 链接
        title = re.sub(r'\[([^\]]+)\]\([^)]+\)', r'\1', title)
        headings.append((level, title))
    return headings

def generate_toc(headings, max_depth=3):
    """生成目录"""
    if len(headings) <= 1:
        return ""
    
    toc_lines = ["## 目录", ""]
    
    # 找到最小层级作为基准
    min_level = min(h[0] for h in headings)
    
    for level, title in headings:
        if level > max_depth:
            continue
        # 生成锚点
        anchor = title.lower()
        anchor = re.sub(r'[^\w\s-]', '', anchor)
        anchor = re.sub(r'\s+', '-', anchor)
        
        indent = "  " * (level - min_level)
        toc_lines.append(f"{indent}- [{title}](#{anchor})")
    
    return "\n".join(toc_lines) + "\n"

def generate_meta(filename):
    """生成元信息"""
    return f"""> **最后更新**: 2026-03-10
> **状态**: 持续更新
> **文档类型**: 技术文档

---

"""

def add_structure_to_file(filepath):
    """为单个文件添加结构"""
    try:
        with open(filepath, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
    except Exception as e:
        return False, str(e)
    
    original_content = content
    modified = False
    
    # 提取标题
    headings = extract_headings(content)
    
    # 检查是否已有目录
    has_toc = bool(re.search(r'^## 目录', content, re.MULTILINE))
    
    # 检查是否已有元信息
    has_meta = bool(re.search(r'^> \*\*', content, re.MULTILINE))
    
    lines = content.split('\n')
    
    # 找到第一个标题的位置
    first_heading_idx = None
    for i, line in enumerate(lines):
        if re.match(r'^#\s+', line):
            first_heading_idx = i
            break
    
    if first_heading_idx is None:
        return False, "No heading found"
    
    # 插入元信息（如果没有）
    if not has_meta:
        meta = generate_meta(os.path.basename(filepath))
        lines.insert(first_heading_idx + 1, '')
        lines.insert(first_heading_idx + 2, meta)
        modified = True
    
    # 重新计算第一个标题位置（可能已改变）
    for i, line in enumerate(lines):
        if re.match(r'^#\s+', line):
            first_heading_idx = i
            break
    
    # 插入目录（如果没有且标题足够多）
    if not has_toc and len(headings) >= 3:
        toc = generate_toc(headings)
        if toc:
            # 找到元信息后或标题后的位置
            insert_idx = first_heading_idx + 1
            
            # 跳过已有的空行
            while insert_idx < len(lines) and lines[insert_idx].strip() == '':
                insert_idx += 1
            
            # 如果有元信息，跳过元信息块
            if has_meta or re.search(r'^> \*\*', '\n'.join(lines[insert_idx:insert_idx+5]), re.MULTILINE):
                while insert_idx < len(lines) and not lines[insert_idx].startswith('---'):
                    insert_idx += 1
                insert_idx += 1  # 跳过分隔线
            
            lines.insert(insert_idx, '')
            lines.insert(insert_idx + 1, toc)
            lines.insert(insert_idx + 2, '---')
            lines.insert(insert_idx + 3, '')
            modified = True
    
    if modified:
        new_content = '\n'.join(lines)
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(new_content)
        return True, "Updated"
    
    return False, "No changes needed"

def main():
    # 优先处理 crates/docs 下的文件
    priority_dirs = [
        'crates',
        'docs',
    ]
    
    updated_count = 0
    error_count = 0
    
    for priority_dir in priority_dirs:
        if not os.path.exists(priority_dir):
            continue
        
        for root, dirs, files in os.walk(priority_dir):
            # 跳过 archive 和 node_modules
            dirs[:] = [d for d in dirs if d not in ['archive', 'node_modules', 'target']]
            
            for file in files:
                if file.endswith('.md'):
                    filepath = os.path.join(root, file)
                    
                    # 检查文件大小（跳过太小的文件）
                    size = os.path.getsize(filepath)
                    if size < 200:
                        continue
                    
                    success, msg = add_structure_to_file(filepath)
                    if success:
                        updated_count += 1
                        print(f"✅ {filepath}")
                    elif "No changes" not in msg:
                        error_count += 1
    
    print(f"\n{'='*60}")
    print(f"更新完成: {updated_count} 个文件")
    print(f"错误: {error_count} 个文件")

if __name__ == '__main__':
    main()
