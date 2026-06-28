#!/usr/bin/env python3
"""
批量为 RFC 引用添加链接。
将 "RFC XXXX" 替换为 "[RFC XXXX](https://rust-lang.github.io/rfcs/XXXX.html)"，
但跳过已存在于链接文本或代码块中的情况。
"""

import os
import re
from pathlib import Path

RFC_PATTERN = re.compile(r'(?<!\[)RFC\s+(\d{4})(?!\])')

def process_file(filepath: str) -> int:
    """处理单个文件，返回修改次数。"""
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    original = content
    lines = content.split('\n')
    new_lines = []
    in_code_block = False
    modified = 0
    
    for line in lines:
        stripped = line.strip()
        
        # 检测代码块边界
        if stripped.startswith('```'):
            in_code_block = not in_code_block
            new_lines.append(line)
            continue
        
        if in_code_block:
            new_lines.append(line)
            continue
        
        # 替换不在链接中的 RFC 引用
        def replace_rfc(match):
            rfc_num = match.group(1)
            return f'[RFC {rfc_num}](https://rust-lang.github.io/rfcs/{rfc_num}.html)'
        
        new_line = RFC_PATTERN.sub(replace_rfc, line)
        if new_line != line:
            modified += 1
        new_lines.append(new_line)
    
    new_content = '\n'.join(new_lines)
    
    if new_content != original:
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(new_content)
    
    return modified

def main():
    total_modified = 0
    files_changed = 0
    
    for root, dirs, files in os.walk('concept'):
        for filename in files:
            if not filename.endswith('.md'):
                continue
            filepath = os.path.join(root, filename)
            try:
                modified = process_file(filepath)
                if modified > 0:
                    print(f"  ✅ {filepath}: {modified} 处")
                    total_modified += modified
                    files_changed += 1
            except Exception as e:
                print(f"  ❌ {filepath}: {e}")
    
    print(f"\n完成: 修改 {total_modified} 处 RFC 引用, 涉及 {files_changed} 个文件")

if __name__ == '__main__':
    main()
