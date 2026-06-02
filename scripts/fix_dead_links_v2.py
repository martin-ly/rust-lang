#!/usr/bin/env python3
"""
修复剩余的 dead links（v2）。
处理以下模式：
1. concept/xx/ -> ../knowledge/   改为 ../../knowledge/
2. concept/xx/ -> ../reports/     改为 ../../reports/
3. concept/xx/ -> ../docs/        改为 ../../docs/
4. concept/xx/ -> ../concept/     改为 ../
5. concept/xx/archive/ -> ../yy/  改为 ../../yy/
"""

import re
from pathlib import Path

CONCEPT_DIR = Path("concept")
PROJECT_ROOT = Path(".")


def fix_links_in_file(filepath: Path) -> int:
    """修复单个文件中的死链，返回修复数量"""
    content = filepath.read_text(encoding="utf-8")
    original = content
    rel = filepath.relative_to(PROJECT_ROOT)
    parts = list(rel.parts)

    # 模式1-3: concept/xx/ 下的文件引用 ../knowledge/ ../reports/ ../docs/
    if len(parts) >= 2 and parts[0] == "concept":
        # knowledge/, reports/, docs/ 在项目根目录
        content = re.sub(r'\]\(\.\./(knowledge|reports|docs)/', r'](../../\1/', content)
        # 多余的 ../concept/ -> ../
        content = re.sub(r'\]\(\.\./concept/', r'](../', content)

    # 模式5: concept/xx/archive/ 下的文件引用 ../yy/ (yy 是 concept 的子目录)
    if len(parts) >= 3 and parts[0] == "concept" and parts[2] == "archive":
        # 00_meta/, 01_foundation/ 等 concept 子目录
        content = re.sub(
            r'\]\(\.\./(00_meta|0[1-7]_\w+)/',
            r'](../../\1/',
            content
        )

    if content != original:
        filepath.write_text(content, encoding="utf-8")
        # 计算修改数量（粗略）
        return 1
    return 0


def main():
    files = sorted(CONCEPT_DIR.rglob("*.md"))
    fixed_files = 0
    for filepath in files:
        if fix_links_in_file(filepath):
            print(f"  已修复: {filepath}")
            fixed_files += 1
    print(f"\n总计: 修复了 {fixed_files} 个文件")


if __name__ == "__main__":
    main()
