#!/usr/bin/env python3
"""检查 concept/ 中 markdown 文件的内部死链。

用法:
    python3 scripts/check_dead_links.py [path]

默认扫描 concept/ 目录。返回非零退出码表示发现死链。
"""

from __future__ import annotations

import sys
from pathlib import Path

# 复用 kb_auditor 的实现
sys.path.insert(0, str(Path(__file__).parent))
from kb_auditor import audit_file, check_link_validity  # noqa: E402

DEFAULT_ROOT = Path("concept")
EXCLUDED_DIRS = {"archive", "sources", "deprecated"}


def main() -> int:
    root = Path(sys.argv[1]) if len(sys.argv) > 1 else DEFAULT_ROOT
    if not root.is_dir():
        print(f"ERROR: {root} is not a directory", file=sys.stderr)
        return 2

    audits = [
        audit_file(p)
        for p in sorted(root.rglob("*.md"))
        if not any(part in EXCLUDED_DIRS for part in p.relative_to(root).parts)
    ]
    dead_links = check_link_validity(audits)
    if dead_links:
        print(f"❌ Found {len(dead_links)} dead links:")
        for dl in dead_links:
            print(f"  {dl['from']} -> {dl['to']}")
        return 1
    print("✅ No dead links found.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
