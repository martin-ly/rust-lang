#!/usr/bin/env python3
"""
批量修复 concept/ 目录下的死链。
问题模式: [text](../../XX_category/file.md) 应改为 [text](../XX_category/file.md)
"""

import re
from pathlib import Path

CONCEPT_DIR = Path("concept")


def fix_links_in_file(filepath: Path) -> int:
    """修复单个文件中的死链，返回修复数量"""
    content = filepath.read_text(encoding="utf-8")
    # 正则: 匹配 []( 后面跟着 ../../
    # 替换为 []( 后面跟着 ../
    new_content, count = re.subn(r'\]\(\.\./\.\./', '](../', content)
    if count > 0:
        filepath.write_text(new_content, encoding="utf-8")
    return count


def main():
    files = sorted(CONCEPT_DIR.rglob("*.md"))
    total_fixes = 0
    fixed_files = 0
    for filepath in files:
        count = fix_links_in_file(filepath)
        if count > 0:
            print(f"  修复 {count} 个死链: {filepath}")
            total_fixes += count
            fixed_files += 1
    print(f"\n总计: 修复了 {total_fixes} 个死链，涉及 {fixed_files} 个文件")


if __name__ == "__main__":
    main()
