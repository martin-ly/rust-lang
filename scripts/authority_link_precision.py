#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""权威来源链接精确化检查器。

扫描 concept/（可选 knowledge/docs）中的 markdown 链接，发现指向
Reference / Nomicon / TRPL / Edition Guide / Async Book / rustc-dev-guide
等国际化权威来源「首页/introduction/index」而非具体章节的链接。

输出按严重度分级：
  S1: 链接文本声称具体章节（如 "Rust Reference — Lifetimes"），但 URL 是首页
  S2: 链接文本为泛称（如 "Rust Reference"），URL 是首页（建议在概念页中逐步精确化）

默认 exit 0（观察门）；--strict 时若有 S1 则 exit 1。
"""
from __future__ import annotations

import argparse
import glob
import os
import re
import sys
from dataclasses import dataclass, field
from typing import List

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# 被认定为「首页」的 URL 模式，以及对应的权威来源名称
HOMEPAGE_PATTERNS = [
    # (regex, authority_name, suggested_root_for_contextual_fixup)
    (re.compile(r"https?://doc\.rust-lang\.org/reference/introduction\.html$"), "Rust Reference", "https://doc.rust-lang.org/reference/"),
    (re.compile(r"https?://doc\.rust-lang\.org/reference/index\.html$"), "Rust Reference", "https://doc.rust-lang.org/reference/"),
    (re.compile(r"https?://doc\.rust-lang\.org/reference/?$"), "Rust Reference", "https://doc.rust-lang.org/reference/"),
    (re.compile(r"https?://doc\.rust-lang\.org/nomicon/index\.html$"), "Rustonomicon", "https://doc.rust-lang.org/nomicon/"),
    (re.compile(r"https?://doc\.rust-lang\.org/nomicon/?$"), "Rustonomicon", "https://doc.rust-lang.org/nomicon/"),
    (re.compile(r"https?://doc\.rust-lang\.org/book/title-page\.html$"), "TRPL", "https://doc.rust-lang.org/book/"),
    (re.compile(r"https?://doc\.rust-lang\.org/book/index\.html$"), "TRPL", "https://doc.rust-lang.org/book/"),
    (re.compile(r"https?://doc\.rust-lang\.org/edition-guide/index\.html$"), "Rust Edition Guide", "https://doc.rust-lang.org/edition-guide/"),
    (re.compile(r"https?://doc\.rust-lang\.org/edition-guide/?$"), "Rust Edition Guide", "https://doc.rust-lang.org/edition-guide/"),
    (re.compile(r"https?://doc\.rust-lang\.org/async-book/index\.html$"), "Async Book", "https://doc.rust-lang.org/async-book/"),
    (re.compile(r"https?://doc\.rust-lang\.org/async-book/?$"), "Async Book", "https://doc.rust-lang.org/async-book/"),
    (re.compile(r"https?://rust-lang\.github\.io/async-book/?$"), "Async Book", "https://rust-lang.github.io/async-book/"),
    (re.compile(r"https?://doc\.rust-lang\.org/rustc-dev-guide/index\.html$"), "rustc-dev-guide", "https://doc.rust-lang.org/rustc-dev-guide/"),
    (re.compile(r"https?://doc\.rust-lang\.org/rustc-dev-guide/introduction\.html$"), "rustc-dev-guide", "https://doc.rust-lang.org/rustc-dev-guide/"),
    (re.compile(r"https?://rustc-dev-guide\.rust-lang\.org/?$"), "rustc-dev-guide", "https://rustc-dev-guide.rust-lang.org/"),
    (re.compile(r"https?://doc\.rust-lang\.org/std/index\.html$"), "Rust Standard Library", "https://doc.rust-lang.org/std/"),
]

# markdown 内联链接 [text](url)
INLINE_LINK_RE = re.compile(r"\[([^\]]+)\]\((https?://[^\)]+)\)")
# 引用式链接 [text][ref] 暂不解析，因数量较少且上下文依赖 ref 定义

# S1 判定：链接文本中包含这些「具体章节暗示词」但 URL 为首页
SPECIFIC_HINTS = [
    "lifetimes", "lifetime", "elision", "borrowing", "ownership", "unsafe", "traits",
    "generics", "types", "type system", "patterns", "macros", "attributes",
    "modules", "crates", "functions", "enums", "structs", "references",
    "coercions", "subtyping", "variance", "async", "await", "pin",
    "ffi", "extern", "inline assembly", "allocators", "memory",
    "send", "sync", "concurrency", "atomics", "error", "panic", "testing",
    "const", "static", "mut", "references and borrowing",
]


@dataclass
class Finding:
    path: str
    line: int
    text: str
    url: str
    authority: str
    severity: str  # S1 or S2
    context: str = ""


def is_homepage_url(url: str) -> tuple[str, str] | None:
    """若 url 命中首页模式，返回 (authority_name, suggested_root)。"""
    for rx, name, root in HOMEPAGE_PATTERNS:
        if rx.search(url):
            return name, root
    return None


def severity_for(text: str) -> str:
    t = text.lower()
    for hint in SPECIFIC_HINTS:
        if hint in t:
            return "S1"
    return "S2"


def scan_file(path: str) -> List[Finding]:
    findings = []
    rel = os.path.relpath(path, ROOT).replace("\\", "/")
    try:
        with open(path, encoding="utf-8", errors="ignore") as f:
            lines = f.readlines()
    except Exception:
        return findings
    for i, line in enumerate(lines, 1):
        for text, url in INLINE_LINK_RE.findall(line):
            hit = is_homepage_url(url)
            if hit:
                authority, _ = hit
                sev = severity_for(text)
                ctx = line.strip()
                findings.append(Finding(rel, i, text, url, authority, sev, ctx))
    return findings


def main() -> int:
    parser = argparse.ArgumentParser(description="Check precision of authority source links")
    parser.add_argument("--dirs", default="concept", help="Comma-separated dirs to scan (default: concept)")
    parser.add_argument("--strict", action="store_true", help="Exit 1 if any S1 finding exists")
    parser.add_argument("--json", help="Write findings to JSON file")
    parser.add_argument("--exclude-readme", action="store_true", help="Skip README.md files")
    parser.add_argument("--exclude-archive", action="store_true", default=True, help="Skip paths containing /archive/")
    args = parser.parse_args()

    dirs = [d.strip() for d in args.dirs.split(",")]
    findings: List[Finding] = []
    for d in dirs:
        for path in glob.glob(os.path.join(ROOT, d, "**", "*.md"), recursive=True):
            rel = os.path.relpath(path, ROOT).replace("\\", "/")
            if args.exclude_archive and "/archive/" in rel:
                continue
            if args.exclude_readme and rel.endswith("README.md"):
                continue
            findings.extend(scan_file(path))

    s1 = [f for f in findings if f.severity == "S1"]
    s2 = [f for f in findings if f.severity == "S2"]

    print(f"[authority_link_precision] total={len(findings)} S1={len(s1)} S2={len(s2)}")
    if not findings:
        print("✅ 未发现指向权威来源首页的链接。")
        return 0

    print("\n=== S1: 文本声称具体章节但链接指向首页 ===")
    for f in s1:
        print(f"  {f.path}:{f.line} [{f.text}] -> {f.url}")
        print(f"    {f.context[:120]}")

    print("\n=== S2: 泛称链接指向首页（建议逐步精确化） ===")
    for f in s2[:200]:  # 限制输出避免刷屏
        print(f"  {f.path}:{f.line} [{f.text}] -> {f.url}")
    if len(s2) > 200:
        print(f"  ... 还有 {len(s2) - 200} 条 S2 未显示")

    if args.json:
        import json
        payload = [
            {"path": f.path, "line": f.line, "text": f.text, "url": f.url,
             "authority": f.authority, "severity": f.severity, "context": f.context}
            for f in findings
        ]
        with open(args.json, "w", encoding="utf-8") as jf:
            json.dump(payload, jf, ensure_ascii=False, indent=2)
        print(f"\n📝 JSON 报告: {args.json}")

    if args.strict and s1:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
