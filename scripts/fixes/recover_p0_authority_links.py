#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""恢复 fix_p0_authority_links.py 因前缀替换导致的 URL 污染。"""
from __future__ import annotations

import glob
import os
import re

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
TARGET_DIRS = ("concept", "knowledge", "docs")

# 污染模式 -> 干净替换
FIXES = [
    # book-cn 重复替换
    (re.compile(r"https://github\.com/rust-lang-cn/book-cn[-cn]+(?=[\s)\]<>\"'`]|$)"),
     "https://github.com/rust-lang-cn/book-cn"),
    # overview.html 后面被拼接了原路径，截断回 overview.html
    (re.compile(r"https://rustc-dev-guide\.rust-lang\.org/overview\.html[^\s)\]<>\"'`]+"),
     "https://rustc-dev-guide.rust-lang.org/overview.html"),
]


def fix_file(path: str) -> tuple[int, list[str]]:
    with open(path, encoding="utf-8") as f:
        text = f.read()
    original = text
    changes = []
    for rx, repl in FIXES:
        if rx.search(text):
            text = rx.sub(repl, text)
            changes.append(f"recover: {rx.pattern[:60]}...")
    if text == original:
        return 0, []
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write(text)
    return 1, changes


def main() -> int:
    modified = 0
    for d in TARGET_DIRS:
        for p in glob.glob(os.path.join(ROOT, d, "**", "*.md"), recursive=True):
            if "/archive/" in p.replace("\\", "/"):
                continue
            changed, changes = fix_file(p)
            if changed:
                modified += 1
                print(f"[{p}]\n  " + "\n  ".join(changes))
    print(f"\n[recover-p0] modified {modified} files")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
