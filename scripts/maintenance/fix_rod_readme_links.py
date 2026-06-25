#!/usr/bin/env python3
"""
修复 docs/rust-ownership-decidability/ 中指向缺失 ./README.md 的损坏链接。

策略：将文件内所有指向 ./README.md 的相对链接，替换为指向
 docs/rust-ownership-decidability/README.md 的正确相对路径。
"""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
ROD_ROOT = ROOT / "docs" / "rust-ownership-decidability"
TARGET_README = ROD_ROOT / "README.md"


def relative_to(from_file: Path, to_file: Path) -> str:
    """返回从 from_file 到 to_file 的相对路径（Markdown 风格）。"""
    return from_file.parent.relative_to(ROD_ROOT).as_posix() + "/" + to_file.name


def fix_links_in_file(path: Path) -> int:
    text = path.read_text(encoding="utf-8")
    # 匹配 [任意文本](./README.md)
    pattern = re.compile(r"\[(?P<text>[^\]]+)\]\(./README\.md\)")

    depth = len(path.relative_to(ROD_ROOT).parts) - 1  # 文件本身占一层
    if depth <= 0:
        return 0

    prefix = "../" * depth
    replacement = rf"[\g<text>]({prefix}README.md)"
    new_text, count = pattern.subn(replacement, text)

    if count:
        path.write_text(new_text, encoding="utf-8")
    return count


def main() -> int:
    if not TARGET_README.exists():
        print(f"❌ 目标 README 不存在: {TARGET_README}")
        return 1

    total = 0
    for path in ROD_ROOT.rglob("*.md"):
        if path == TARGET_README:
            continue
        count = fix_links_in_file(path)
        if count:
            print(f"  修复 {count} 处: {path.relative_to(ROOT)}")
            total += count

    print(f"\n✅ 共修复 {total} 处 ./README.md 链接")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
