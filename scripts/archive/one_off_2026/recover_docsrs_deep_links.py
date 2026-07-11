#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""撤销 fix_p2_remaining.py 对有效 docs.rs 深链的不必要回退。

对 git diff 中每个 docs.rs 单链替换（旧 URL 为深链、新 URL 为根页），
若旧 URL 仍可访问（HEAD 200），则恢复为旧 URL；否则保留根页。
"""
from __future__ import annotations

import os
import re
import subprocess
import sys
from urllib.error import HTTPError
from urllib.request import Request, urlopen

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
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


def path_depth(u: str) -> int:
    m = re.search(r"/latest/(.+)", u.rstrip("/"))
    if not m:
        return 0
    return len([s for s in m.group(1).split("/") if s])


def parse_diff():
    diff = subprocess.run(
        ["git", "diff", "--unified=0", "--", "*.md"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="ignore",
    ).stdout
    per_file = {}
    current_file = None
    for line in diff.splitlines():
        if line.startswith("diff --git a/"):
            m = re.match(r"diff --git a/(.+?) b/(.+?)$", line)
            if m:
                current_file = m.group(2)
        if current_file and line.startswith("--- a/"):
            current_file = line[6:]
        if current_file and line.startswith("+") and not line.startswith("+++"):
            new_url = re.search(r"(https://docs\.rs/[^\s)\]<>\"'`]+)", line)
            if new_url:
                per_file.setdefault(current_file, []).append((None, new_url.group(1)))
        if current_file and line.startswith("-") and not line.startswith("---"):
            old_url = re.search(r"(https://docs\.rs/[^\s)\]<>\"'`]+)", line)
            if old_url and per_file.get(current_file):
                # pair with last entry that has no old url
                entries = per_file[current_file]
                if entries and entries[-1][0] is None:
                    entries[-1] = (old_url.group(1), entries[-1][1])
    return per_file


def main() -> int:
    per_file = parse_diff()
    total_reverted = 0
    for rel, pairs in per_file.items():
        path = os.path.join(ROOT, rel)
        if not os.path.exists(path):
            continue
        with open(path, encoding="utf-8") as f:
            text = f.read()
        original = text
        for old, new in pairs:
            if not old or not new:
                continue
            if not old.startswith("https://docs.rs/") or not new.startswith("https://docs.rs/"):
                continue
            if path_depth(old) <= path_depth(new):
                continue
            st = head_status(old)
            if st == 200:
                rx = re.compile(re.escape(new) + r"(?![A-Za-z0-9\-_./#])")
                if rx.search(text):
                    text = rx.sub(old, text)
                    total_reverted += 1
                    print(f"revert {rel}: {new} -> {old}")
        if text != original:
            with open(path, "w", encoding="utf-8", newline="\n") as f:
                f.write(text)
    print(f"\n[recover-docsrs] reverted {total_reverted} deep links")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
