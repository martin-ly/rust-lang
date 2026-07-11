#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""P0 官方域『当前已 404 的具体 URL』保守回退到对应官方入口/根页。

只处理 `reports/AUTHORITY_LINK_HEALTH_*.json` 中 tier=P0、status=404 的具体 URL，
不误伤同域下仍然有效的精确子页。这是『100% 对齐有效性』与『精确章节』的折中，
映射在报告中标注为保守回退。
--dry-run 预览。
"""
from __future__ import annotations

import glob
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DRY = "--dry-run" in sys.argv


def fallback_for(url):
    if url.startswith("https://doc.rust-lang.org/book/ch") and url.endswith(".html"):
        return "https://doc.rust-lang.org/book/title-page.html"
    if re.match(r"https://doc\.rust-lang\.org/reference/[^/]+\.html", url):
        return "https://doc.rust-lang.org/reference/introduction.html"
    if re.match(r"https://doc\.rust-lang\.org/nomicon/[^/]+\.html", url):
        return "https://doc.rust-lang.org/nomicon/"
    if re.match(r"https://doc\.rust-lang\.org/rust-by-example/[^/]+\.html", url):
        return "https://doc.rust-lang.org/rust-by-example/"
    if re.match(r"https://rustc-dev-guide\.rust-lang\.org/[^/]+\.html", url):
        return "https://rustc-dev-guide.rust-lang.org/"
    if re.match(r"https://spec\.ferrocene\.dev/[^/]+\.html", url):
        return "https://spec.ferrocene.dev/"
    return None


def main():
    reports = sorted(glob.glob(os.path.join(ROOT, "reports", "AUTHORITY_LINK_HEALTH_*.json")))
    if not reports:
        print("no AUTHORITY_LINK_HEALTH report found")
        return 1
    data = json.load(open(reports[-1], encoding="utf-8"))
    mapping = {}
    for b in data.get("bad_list", []):
        if b.get("tier") == "P0" and b.get("status") == 404:
            new = fallback_for(b["url"])
            if new:
                mapping[b["url"]] = new
    if not mapping:
        print("[fix-p0-fallbacks] no P0 404 URLs eligible for root fallback")
        return 0
    print(f"[fix-p0-fallbacks] eligible P0 404 URLs: {len(mapping)}")
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
            local = 0
            for old, nn in mapping.items():
                n = new.count(old)
                if n:
                    new = new.replace(old, nn)
                    local += n
            if local:
                changed += 1
                total += local
                rel = os.path.relpath(p, ROOT).replace("\\", "/")
                print(f"  {'DRY ' if DRY else ''}{rel}: {local}")
                if not DRY:
                    open(p, "w", encoding="utf-8", newline="\n").write(new)
    print(f"[fix-p0-fallbacks] files_changed={changed} url_replacements={total} dry={DRY}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
