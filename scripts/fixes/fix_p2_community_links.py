#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""确定性修复 P2 社区/生态权威域中的已知失效/占位/typo URL。"""
from __future__ import annotations

import glob
import os
import re

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
TARGET_DIRS = ("concept", "knowledge", "docs")

# 精确替换（带边界）
URL_REPLACEMENTS = {
    # docs.rs 大小写错误
    "https://docs.rs/Axum/latest/Axum/": "https://docs.rs/axum/latest/axum/",
    "https://docs.rs/Serde/latest/Serde/": "https://docs.rs/serde/latest/serde/",
    "https://docs.rs/Tokio/latest/Tokio/": "https://docs.rs/tokio/latest/tokio/",
    "https://docs.rs/Warp/latest/Warp/": "https://docs.rs/warp/latest/warp/",
    # 子站根页回退
    "https://nnethercote.github.io/perf-book/dynamic-dispatch.html": "https://nnethercote.github.io/perf-book/",
    "https://nnethercote.github.io/perf-book/heap-alloc.html": "https://nnethercote.github.io/perf-book/",
    "https://nnethercote.github.io/perf-book/memory.html": "https://nnethercote.github.io/perf-book/",
    "https://nnethercote.github.io/perf-book/procedural-macros.html": "https://nnethercote.github.io/perf-book/",
    # verus URL 拼接错误
    "https://github.com/verus-lang/verusverus/": "https://github.com/verus-lang/verus/",
    "https://github.com/verus-lang/verusverus": "https://github.com/verus-lang/verus",
}

# 子站通用根页回退（前缀匹配）
FALLBACK_ROOTS = {
    "https://rust-unofficial.github.io/patterns/": "https://rust-unofficial.github.io/patterns/",
}

# 删除/注释链接：old_url -> 说明文本
REMOVE_LINKS = {
    "https://docs.rs/crate/latest/crate/": "docs.rs 占位 URL，待补充真实 crate 后替换",
    "https://mirrors.my-company.com/crates.io-index/": "企业镜像占位，需按实际部署替换",
}


def fix_file(path: str) -> tuple[int, list[str]]:
    with open(path, encoding="utf-8") as f:
        text = f.read()
    original = text
    changes = []

    for old, new in URL_REPLACEMENTS.items():
        rx = re.compile(re.escape(old) + r"(?![A-Za-z0-9\-_./#])")
        if rx.search(text):
            text = rx.sub(new, text)
            changes.append(f"url_replace: {old} -> {new}")

    for prefix, root in FALLBACK_ROOTS.items():
        # 将 prefix 开头的任意 URL 替换为根页（保留 markdown 链接语法）
        rx = re.compile(re.escape("](") + re.escape(prefix) + r"[^\s)\]]*")
        if rx.search(text):
            text = rx.sub(f"]({root})", text)
            changes.append(f"fallback_root: {prefix}* -> {root}")

    for old, note in REMOVE_LINKS.items():
        # 支持 [text](old) 和 <old>
        md_rx = re.compile(r"\[([^\]]+)\]" + re.escape(f"({old})"))
        if md_rx.search(text):
            text = md_rx.sub(rf"\1（{note}）", text)
            changes.append(f"remove_link_md: {old}")
        bare_rx = re.compile(re.escape(f"<{old}>"))
        if bare_rx.search(text):
            text = bare_rx.sub(note, text)
            changes.append(f"remove_link_bare: {old}")

    # 修复 blog 未来日期占位为 releases.rs 或说明
    # 先处理已知的未来版本链接：改为指向 github release tag（即使未来版本不存在，也保留官方 release 路径）
    blog_replacements = {
        "https://blog.rust-lang.org/2024/12/19/Rust-1.92.0.html": "https://github.com/rust-lang/rust/releases/tag/1.92.0",
        "https://blog.rust-lang.org/2025/12/04/Rust-1.96.1.html": "https://github.com/rust-lang/rust/releases/tag/1.96.1",
        "https://blog.rust-lang.org/2026/05/14/Rust-1.95.0.html": "https://github.com/rust-lang/rust/releases/tag/1.95.0",
        "https://blog.rust-lang.org/2026/05/28/Rust-1.96.0.html": "https://github.com/rust-lang/rust/releases/tag/1.96.0",
    }
    for old, new in blog_replacements.items():
        rx = re.compile(re.escape(old) + r"(?![A-Za-z0-9\-_./#])")
        if rx.search(text):
            text = rx.sub(new, text)
            changes.append(f"blog_future: {old} -> {new}")

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
    print(f"\n[fix-p2] modified {modified} files")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
