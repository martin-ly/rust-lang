#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""修复国际化权威来源中『确定无疑义』的占位/错误 URL（不臆测新址）。

映射表只包含：
  - 明显拼写/编号错误（如 RFC 2000-2000）
  - 已确认被移除旧资源的保守根页映射（async-book 旧章节 → async-book 根页）
  - 未来日期占位 blog → 真实 release notes（releases.rs）
  - std 模块错误路径修正（sync.html → sync/index.html）

不在表中的失效 URL（多数 TRPL/Reference/Nomicon 旧章节、单个 crate 404 等）标复核，不改。
--dry-run 预览。
"""
from __future__ import annotations

import glob
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DRY = "--dry-run" in sys.argv

# 精确 old_url -> new_url（确信）
EXACT = {
    "https://rust-lang.github.io/rfcs/2000-2000-const-generics.html":
        "https://rust-lang.github.io/rfcs/2000-const-generics.html",
    "https://blog.rust-lang.org/2026/01/xx/Rust-1.93.0/":
        "https://releases.rs/docs/1.93.0/",
    "https://rust-lang.github.io/async-book/02_execution/03_async_lifetimes.html":
        "https://rust-lang.github.io/async-book/",
    "https://rust-lang.github.io/async-book/04_pinning/01_chapter.html":
        "https://rust-lang.github.io/async-book/",
    "https://rust-lang.github.io/async-book/04_pinning/index.html":
        "https://rust-lang.github.io/async-book/",
    "https://doc.rust-lang.org/std/sync.html":
        "https://doc.rust-lang.org/std/sync/index.html",
}

# 谨慎 regex：async-book 任意旧具体章节 → 根页（仅当 async-book 子目录 html 失效时）
REGEX_REPLACEMENTS = [
    # 保守：只替换 rust-lang.github.io/async-book/ 下含至少两级子路径的 .html
    (re.compile(r"https://rust-lang\.github\.io/async-book/[^/]+/[^/]+\.html"),
     "https://rust-lang.github.io/async-book/"),
]


def main():
    changed = 0
    total = 0
    for d in ("concept", "knowledge", "docs", "crates"):
        for p in glob.glob(os.path.join(ROOT, d, "**", "*.md"), recursive=True):
            if "/archive/" in p.replace("\\", "/"):
                continue
            try:
                t = open(p, encoding="utf-8", errors="ignore").read()
            except Exception:
                continue
            new = t
            for old, nn in EXACT.items():
                n = new.count(old)
                if n:
                    new = new.replace(old, nn)
                    total += n
            for rx, repl in REGEX_REPLACEMENTS:
                n = len(rx.findall(new))
                if n:
                    new = rx.sub(repl, new)
                    total += n
            if new != t:
                changed += 1
                rel = os.path.relpath(p, ROOT).replace("\\", "/")
                print(f"  {'DRY ' if DRY else ''}{rel}")
                if not DRY:
                    open(p, "w", encoding="utf-8", newline="\n").write(new)
    print(f"[fix-url-placeholders] files_changed={changed} url_replacements={total} dry={DRY}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
