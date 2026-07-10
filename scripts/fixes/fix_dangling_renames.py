#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""修复去编号重命名未同步引用方导致的死链（P0/P3 闭环）。

背景：项目把 concept/00_meta 下 3 个文件从编号名改为去编号名
  03_bloom_taxonomy.md        -> bloom_taxonomy.md
  08_concept_audit_guide.md   -> concept_audit_guide.md
  05_cross_reference_matrix.md -> cross_reference_matrix.md
但引用方（md 链接、atlas 表）未同步，造成 kb_auditor --link-check 16 个死链。
本脚本在 concept/ 活跃 md（排除 archive）做文件名 token 全局替换，使 link-check 归零。
只改活跃 md，不动 archive/，不动 book/。
"""
from __future__ import annotations

import glob
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
CONCEPT = os.path.join(ROOT, "concept")

RENAMES = {
    "03_bloom_taxonomy.md": "bloom_taxonomy.md",
    "08_concept_audit_guide.md": "concept_audit_guide.md",
    "05_cross_reference_matrix.md": "cross_reference_matrix.md",
}


def main():
    dry = "--dry-run" in sys.argv
    files = [
        p for p in glob.glob(os.path.join(CONCEPT, "**", "*.md"), recursive=True)
        if (os.sep + "archive" + os.sep) not in p and "/archive/" not in p.replace("\\", "/")
    ]
    total_repl = 0
    changed = []
    for p in files:
        try:
            text = open(p, encoding="utf-8", errors="ignore").read()
        except Exception:
            continue
        new = text
        cnt = 0
        for old, nn in RENAMES.items():
            n = new.count(old)
            if n:
                new = new.replace(old, nn)
                cnt += n
        if cnt:
            total_repl += cnt
            rel = os.path.relpath(p, ROOT).replace("\\", "/")
            changed.append((rel, cnt))
            if not dry:
                open(p, "w", encoding="utf-8", newline="\n").write(new)
    print(f"[fix-dangling] files_changed={len(changed)} replacements={total_repl} dry={dry}")
    for rel, c in sorted(changed, key=lambda x: -x[1])[:30]:
        print(f"   {c:3d}  {rel}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
