#!/usr/bin/env python3
"""检查 concept/ 下同一目录内是否存在重复的 NN_ 编号前缀。

用法:
    python3 scripts/check_concept_numbering.py [path]

默认扫描 concept/ 目录。返回非零退出码表示发现冲突。
"""

from __future__ import annotations

import sys
from pathlib import Path

DEFAULT_ROOT = Path("concept")


EXCLUDED_DIRS = {"archive", "sources", "archive", "deprecated"}


def check_numbering(root: Path) -> int:
    conflicts = 0
    for dirpath in sorted(root.rglob("")):
        if not dirpath.is_dir():
            continue
        # 跳过归档目录，其文件名包含原始来源前缀，编号冲突不代表活跃内容问题
        if any(part in EXCLUDED_DIRS for part in dirpath.relative_to(root).parts):
            continue
        # 跳过 archive/sources 等非核心层级目录，但保留其检查输出可选
        prefix_map: dict[str, list[str]] = {}
        for f in sorted(dirpath.glob("[0-9][0-9]_*.md")):
            prefix = f.name[:2]
            prefix_map.setdefault(prefix, []).append(f.name)
        dups = {p: files for p, files in prefix_map.items() if len(files) > 1}
        if dups:
            conflicts += sum(len(files) for files in dups.values())
            rel = dirpath.relative_to(root)
            print(f"CONFLICT in {rel}:")
            for prefix, files in sorted(dups.items()):
                for fn in files:
                    print(f"  - {prefix} -> {fn}")
    return conflicts


def main() -> int:
    root = Path(sys.argv[1]) if len(sys.argv) > 1 else DEFAULT_ROOT
    if not root.is_dir():
        print(f"ERROR: {root} is not a directory", file=sys.stderr)
        return 2

    conflicts = check_numbering(root)
    if conflicts:
        print(f"\n❌ Found {conflicts} files with duplicate numbering prefixes.")
        return 1
    print("✅ No duplicate numbering prefixes found.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
