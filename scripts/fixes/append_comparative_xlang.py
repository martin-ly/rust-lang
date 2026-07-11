#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""对 concept/05_comparative 中『rust_vs_<lang>』单语言对比页，文末追加被对比语言的官方权威入口。

仅追加（idempotent：已含『## 权威来源』或已含对标域则跳过），不删/改正文。
对标官方 URL 取确信真实的语言官网（swift.org/ziglang.org/ruby-lang.org/kotlinlang.org/
scala-lang.org/learn.microsoft.com/elixir-lang.org 等）+ Rust P0 对照，不虚构。
综述页（README/paradigm_matrix/safety_boundaries）跳过（非单语言对比）。
"""
from __future__ import annotations

import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DRY = "--dry-run" in sys.argv

# lang 关键词 -> (被对比语言官方权威, ...)
XLANG = {
    "swift":   [("Swift 官方", "https://www.swift.org/"), ("Swift Docs", "https://www.swift.org/documentation/")],
    "zig":     [("Zig 官方", "https://ziglang.org/"), ("Zig Docs", "https://ziglang.org/documentation/master/")],
    "ruby":    [("Ruby 官方", "https://www.ruby-lang.org/"), ("Ruby Docs", "https://www.ruby-lang.org/en/documentation/")],
    "kotlin":  [("Kotlin 官方", "https://kotlinlang.org/"), ("Kotlin Docs", "https://kotlinlang.org/docs/home.html")],
    "scala":   [("Scala 官方", "https://www.scala-lang.org/"), ("Scala Docs", "https://docs.scala-lang.org/")],
    "csharp":  [("C# 官方 (Microsoft Learn)", "https://learn.microsoft.com/dotnet/csharp/"), (".NET 官方", "https://dotnet.microsoft.com/")],
    "elixir":  [("Elixir 官方", "https://elixir-lang.org/"), ("Elixir Docs", "https://elixir-lang.org/docs.html")],
    "java":    [("Java (Oracle Docs)", "https://docs.oracle.com/en/java/"), ("OpenJDK", "https://openjdk.org/")],
    "go":      [("Go Spec", "https://go.dev/ref/spec"), ("Effective Go", "https://go.dev/doc/effective_go")],
    "cpp":     [("cppreference", "https://en.cppreference.com/"), ("C++ Core Guidelines", "https://isocpp.github.io/CppCoreGuidelines/CppCoreGuidelines.html")],
    "haskell": [("GHC User Guide", "https://downloads.haskell.org/ghc/latest/docs/users_guide/"), ("Typeclassopedia", "https://wiki.haskell.org/Typeclassopedia")],
    "python":  [("Python 官方", "https://www.python.org/"), ("Python Docs", "https://docs.python.org/3/")],
    "javascript": [("MDN", "https://developer.mozilla.org/en-US/docs/Web/JavaScript"), ("TC39", "https://tc39.es/")],
}

RUST_P0 = [("Rust Reference（对照）", "https://doc.rust-lang.org/reference/"),
           ("TRPL（对照）", "https://doc.rust-lang.org/book/title-page.html")]

SKIP_NAMES = {"README.md", "03_paradigm_matrix.md", "04_safety_boundaries.md"}


def section(refs):
    lines = ["", "---", "", "## 权威来源（References · 跨语言国际权威对齐）", "",
             "> 仅追加被对比语言的官方权威入口与 Rust 对照，闭合跨语言对标覆盖；不改本文正文（AGENTS.md §2）。", ""]
    for label, url in refs:
        lines.append(f"- **{label}**: <{url}>")
    lines.append("")
    return "\n".join(lines)


def main():
    base = os.path.join(ROOT, "concept", "05_comparative")
    done = skipped = 0
    for dirpath, _, names in os.walk(base):
        if "/archive/" in dirpath.replace("\\", "/"):
            continue
        for nm in names:
            if not nm.endswith(".md") or nm in SKIP_NAMES:
                continue
            low = nm.lower()
            # 按关键词长度降序匹配，避免 'java' 误中 'javascript'（先匹配更长的 javascript）
            lang = next((k for k in sorted(XLANG, key=len, reverse=True) if k in low), None)
            if lang is None:
                continue
            p = os.path.join(dirpath, nm)
            t = open(p, encoding="utf-8", errors="ignore").read()
            # idempotent 按域判定：已含该对标语言任一官方域则 skip（避免重复/避免仅因已有 Rust References 而漏补）
            xlang_domains = [u.split("/")[2] for _, u in XLANG[lang]]
            if any(d in t for d in xlang_domains):
                skipped += 1; continue
            refs = XLANG[lang] + RUST_P0
            if not DRY:
                open(p, "w", encoding="utf-8", newline="\n").write(t.rstrip() + "\n" + section(refs))
            print(f"  {'DRY ' if DRY else ''}append {os.path.relpath(p, ROOT).replace(chr(92), '/')}  (lang={lang}, +{len(refs)})")
            done += 1
    print(f"[append-comparative-xlang] appended={done} skipped={skipped} dry={DRY}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
