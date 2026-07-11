#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""确定性修复 P1 学术权威域中的已知失效/占位 URL。"""
from __future__ import annotations

import glob
import os
import re

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
TARGET_DIRS = ("concept", "knowledge", "docs")

URL_REPLACEMENTS = {
    "https://aeneas-verification.github.io/": "https://aeneasverif.github.io/",
    "https://aeneas-verif.org/": "https://aeneasverif.github.io/",
    "https://plv.mpi-sws.org/rustbelt/rustbelt.pdf": "https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf",
    "https://plv.mpi-sws.org/semantics-of-memory-safety/": "https://plv.mpi-sws.org/",
}

# 将 [text](old_url) 替换为 text（说明），old_url 是占位 arXiv
REMOVE_LINKS = {
    "https://arxiv.org/abs/2026.05.08": "待正式 arXiv 编号",
    "https://arxiv.org/abs/2501.xxxxx": "待正式 arXiv 编号",
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

    for old, note in REMOVE_LINKS.items():
        rx = re.compile(r"\[([^\]]+)\]" + re.escape(f"({old})"))
        if rx.search(text):
            text = rx.sub(rf"\1（{note}）", text)
            changes.append(f"remove_link: {old}")

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
    print(f"\n[fix-p1] modified {modified} files")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
