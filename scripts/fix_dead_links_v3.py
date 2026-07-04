#!/usr/bin/env python3
"""
修复剩余的死链（v3）。
处理以下模式：
1. concept/xx/ -> ../knowledge/   改为 ../../knowledge/
2. concept/xx/ -> ../reports/     改为 ../../reports/
3. concept/xx/ -> ../docs/        改为 ../../docs/
4. concept/xx/ -> ../concept/     改为 ../
5. concept/xx/archive/ -> ../yy/  改为 ../../yy/

扩展：兼容 concept/xx/subdir/ 任意层级深度。
"""

import re
from pathlib import Path

CONCEPT_DIR = Path("concept")
PROJECT_ROOT = Path(".")


def depth_under_concept(filepath: Path) -> int:
    """返回文件在 concept/ 下的子目录深度。

    concept/01_foundation/foo.md          -> 1
    concept/01_foundation/items/foo.md    -> 2
    """
    rel = filepath.relative_to(PROJECT_ROOT)
    parts = list(rel.parts)
    if len(parts) < 2 or parts[0] != "concept":
        return 0
    # parts[0] == "concept", parts[1] == layer dir, actual file depth starts from parts[2]
    return max(0, len(parts) - 2)


def fix_links_in_file(filepath: Path) -> int:
    """修复单个文件中的死链，返回修复数量"""
    content = filepath.read_text(encoding="utf-8")
    original = content
    rel = filepath.relative_to(PROJECT_ROOT)
    parts = list(rel.parts)

    if len(parts) >= 2 and parts[0] == "concept":
        depth = depth_under_concept(filepath)
        if depth >= 1:
            # 模式1-3: concept/xx/(...)/ 下的文件引用 ../knowledge/ ../reports/ ../docs/
            # 需要 depth+1 个 ../ 才能到达项目根
            prefix_up = "../" * (depth + 1)
            content = re.sub(
                r'\]\(\.\./(knowledge|reports|docs)/',
                rf']({prefix_up}\1/',
                content,
            )
            # 模式4: 多余的 ../concept/ -> 根据深度调整
            # 在 depth=1 时：../concept/yy/ -> ../yy/
            # 在 depth=2 时：../concept/yy/ -> ../../yy/
            # 但跨子目录引用应使用相对路径而非 ../concept/；这里统一压缩为相对同层或上层
            content = re.sub(
                r'\]\(\.\./concept/',
                rf']({"../" * depth}',
                content,
            )

        # 模式5: concept/xx/archive/ 下的文件引用 ../yy/ (yy 是 concept 的子目录)
        if len(parts) >= 3 and parts[2] == "archive":
            content = re.sub(
                r'\]\(\.\./(00_meta|0[1-7]_\w+)/',
                r'](../../\1/',
                content,
            )

    if content != original:
        filepath.write_text(content, encoding="utf-8")
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
