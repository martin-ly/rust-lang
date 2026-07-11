#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""修复剩余 P2 社区/生态失效链接（docs.rs 回退、blog 路径、verus 链接）。"""
from __future__ import annotations

import glob
import os
import re
from urllib.error import HTTPError, URLError
from urllib.request import Request, urlopen

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
TARGET_DIRS = ("concept", "knowledge", "docs")
UA = "Mozilla/5.0 (compatible; rust-lang-kb-health/1.0; +https://github.com/rust-lang)"


def head_status(u: str) -> int | None:
    try:
        req = Request(u, method="HEAD", headers={"User-Agent": UA})
        with urlopen(req, timeout=8) as r:
            return r.status
    except HTTPError as e:
        return e.code
    except Exception:
        return None


def docsrs_crate_root(u: str) -> str | None:
    """尝试找到一个可达的 docs.rs 根页；找不到返回 None。"""
    m = re.match(r"https://docs\.rs/([^/]+)/latest/", u)
    if not m:
        return None
    crate = m.group(1)
    candidates = [
        f"https://docs.rs/{crate}/latest/{crate}/",
        f"https://docs.rs/{crate}/latest/",
    ]
    for c in candidates:
        st = head_status(c)
        if st == 200:
            return c
    return None


URL_REPLACEMENTS = {
    "https://blog.rust-lang.org/inside-rust/2023/02/23/keyword-generics-progress-report.html":
        "https://blog.rust-lang.org/inside-rust/2023/02/23/keyword-generics-progress-report-feb-2023.html",
}

REMOVE_LINKS = {
    "https://blog.rust-lang.org/2023/06/01/": "该日期无对应官方博文",
}

VERUS_PREFIX_OLD = "https://github.com/verus-lang/verusverus/"
VERUS_PREFIX_NEW = "https://verus-lang.github.io/verus/"


def fix_file(path: str) -> tuple[int, list[str]]:
    with open(path, encoding="utf-8") as f:
        text = f.read()
    original = text
    changes = []

    # 1. 精确替换
    for old, new in URL_REPLACEMENTS.items():
        rx = re.compile(re.escape(old) + r"(?![A-Za-z0-9\-_./#])")
        if rx.search(text):
            text = rx.sub(new, text)
            changes.append(f"url_replace: {old} -> {new}")

    # 2. 删除占位/失效链接
    for old, note in REMOVE_LINKS.items():
        md_rx = re.compile(r"\[([^\]]+)\]" + re.escape(f"({old})"))
        if md_rx.search(text):
            text = md_rx.sub(rf"\1（{note}）", text)
            changes.append(f"remove_link_md: {old}")
        bare_rx = re.compile(re.escape(f"<{old}>"))
        if bare_rx.search(text):
            text = bare_rx.sub(note, text)
            changes.append(f"remove_link_bare: {old}")

    # 3. verusverus 前缀批量替换（保留后续路径）
    if VERUS_PREFIX_OLD in text:
        text = text.replace(VERUS_PREFIX_OLD, VERUS_PREFIX_NEW)
        changes.append(f"verus_prefix: {VERUS_PREFIX_OLD} -> {VERUS_PREFIX_NEW}")

    # 4. verus example 路径回退到仓库根
    verus_example = "https://github.com/verus-lang/verus/tree/main/source/rust_verify/example"
    verus_root = "https://github.com/verus-lang/verus"
    rx = re.compile(re.escape(verus_example) + r"(?![A-Za-z0-9\-_./#])")
    if rx.search(text):
        text = rx.sub(verus_root, text)
        changes.append(f"verus_example_fallback: {verus_example}")

    # 5. docs.rs 具体路径回退到可达根页
    docsrx = re.compile(r"https://docs\.rs/[^\s)\]<>\"'`]+")
    for m in docsrx.finditer(text):
        u = m.group(0)
        if u.endswith(")"):  # markdown 语法结尾
            u = u[:-1]
        # 仅处理已知失效模式：路径包含 /latest/ 且非根页
        if not re.search(r"/latest/[^/]+/?$", u):
            root = docsrs_crate_root(u)
            if root and root != u:
                # 边界替换，避免前缀污染
                rx2 = re.compile(re.escape(u) + r"(?![A-Za-z0-9\-_./#])")
                if rx2.search(text):
                    text = rx2.sub(root, text)
                    changes.append(f"docsrs_fallback: {u} -> {root}")

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
    print(f"\n[fix-p2-remaining] modified {modified} files")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
