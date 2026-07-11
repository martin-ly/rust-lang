#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""确定性修复 P0 官方权威域中的已知失效/占位/typo URL。

只处理 concept/knowledge/docs 中的 Markdown；不碰 archive/reports/tmp/cache。
修改原则：
- typo 直接修正；
- 已确认迁移的官方子页回退到有效根页或 GitHub blob；
- 占位 RFC/PR 删除具体 URL 并保留说明；
- 不能确认新址的保留原文并标记复核。
"""
from __future__ import annotations

import glob
import os
import re

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
TARGET_DIRS = ("concept", "knowledge", "docs")

# 精确字符串替换：old_url -> new_url
URL_REPLACEMENTS = {
    # typo
    "https://doc.rust-lang.org/std/ync/atomic": "https://doc.rust-lang.org/std/sync/atomic",
    # RBE 路径变更
    "https://doc.rust-lang.org/rust-by-example/custom_types/type.html": "https://doc.rust-lang.org/rust-by-example/custom_types.html",
    "https://doc.rust-lang.org/rust-by-example/std_misc/net.html": "https://doc.rust-lang.org/rust-by-example/std_misc.html",
    # 中文书仓库
    "https://github.com/rust-lang-cn/book": "https://github.com/rust-lang-cn/book-cn",
    # API guidelines 路径变更
    "https://rust-lang.github.io/api-guidelines/safety.html": "https://rust-lang.github.io/api-guidelines/type-safety.html",
    # rust-formal-methods 独立 org
    "https://rust-lang.github.io/rust-formal-methods/": "https://rust-formal-methods.github.io/",
    # rustc-dev-guide 路径变更：回退到已知有效的 overview.html
    "https://rustc-dev-guide.rust-lang.org/backend/backend.html": "https://rustc-dev-guide.rust-lang.org/overview.html",
    "https://rustc-dev-guide.rust-lang.org/backend/mono.html": "https://rustc-dev-guide.rust-lang.org/overview.html",
    "https://rustc-dev-guide.rust-lang.org/building/bootstrapping.html": "https://rustc-dev-guide.rust-lang.org/overview.html",
    "https://rustc-dev-guide.rust-lang.org/codegen/implicit-caller-location.html": "https://rustc-dev-guide.rust-lang.org/overview.html",
    "https://rustc-dev-guide.rust-lang.org/diagnostics/lint-guidelines.html": "https://rustc-dev-guide.rust-lang.org/overview.html",
    "https://rustc-dev-guide.rust-lang.org/tests/profiling.html": "https://rustc-dev-guide.rust-lang.org/overview.html",
    "https://rustc-dev-guide.rust-lang.org/building/bootstrapping/what-bootstrapping-does.html": "https://rustc-dev-guide.rust-lang.org/overview.html",
    "https://rustc-dev-guide.rust-lang.org/building/bootstrapping/writing-tools-in-bootstrap.html": "https://rustc-dev-guide.rust-lang.org/overview.html",
    "https://rustc-dev-guide.rust-lang.org/tests/compiletest.html": "https://rustc-dev-guide.rust-lang.org/overview.html",
    # 上一轮脚本生成的目录/页面回退修正
    "https://rustc-dev-guide.rust-lang.org/backend/": "https://rustc-dev-guide.rust-lang.org/overview.html",
    "https://rustc-dev-guide.rust-lang.org/building/": "https://rustc-dev-guide.rust-lang.org/overview.html",
    "https://rustc-dev-guide.rust-lang.org/codegen.html": "https://rustc-dev-guide.rust-lang.org/overview.html",
    "https://rustc-dev-guide.rust-lang.org/diagnostics.html": "https://rustc-dev-guide.rust-lang.org/overview.html",
    "https://rustc-dev-guide.rust-lang.org/tests/": "https://rustc-dev-guide.rust-lang.org/overview.html",
    # UCG / project goals / compiler-team 回退到有效根页
    "https://rust-lang.github.io/unsafe-code-guidelines/reference/types.html": "https://rust-lang.github.io/unsafe-code-guidelines/",
    "https://rust-lang.github.io/rust-project-goals/2024h2/formal-methods.html": "https://rust-lang.github.io/rust-project-goals/",
    "https://rust-lang.github.io/rust-project-goals/2025h1/Rust-for-Linux.html": "https://rust-lang.github.io/rust-project-goals/",
    "https://rust-lang.github.io/rust-project-goals/2025h1/const-traits.html": "https://rust-lang.github.io/rust-project-goals/",
    "https://rust-lang.github.io/compiler-team/minutes/design-meeting/2021-03-17-next-generation-trait-solver.html": "https://rust-lang.github.io/compiler-team/",
    # RFC 编号页：rust-lang.github.io/rfcs/*.html 未部署，改为 GitHub blob
    "https://rust-lang.github.io/rfcs/1590-generic-associated-types.html": "https://github.com/rust-lang/rfcs/blob/master/text/1590-generic-associated-types.md",
    "https://rust-lang.github.io/rfcs/1665.html": "https://github.com/rust-lang/rfcs/blob/master/text/1665.md",
    "https://rust-lang.github.io/rfcs/2616-iterable.html": "https://github.com/rust-lang/rfcs/blob/master/text/2616-iterable.md",
    "https://rust-lang.github.io/rfcs/2645-transparent-enums.html": "https://github.com/rust-lang/rfcs/blob/master/text/2645-transparent-enums.md",
    "https://rust-lang.github.io/rfcs/3101-reserved-prefix.html": "https://github.com/rust-lang/rfcs/blob/master/text/3101-reserved-prefix.md",
    "https://rust-lang.github.io/rfcs/3185-async-drop.html": "https://github.com/rust-lang/rfcs/blob/master/text/3185-async-drop.md",
    "https://rust-lang.github.io/rfcs/3271-rustdoc-json.html": "https://github.com/rust-lang/rfcs/blob/master/text/3271-rustdoc-json.md",
    "https://rust-lang.github.io/rfcs/3516-gen-blocks.html": "https://github.com/rust-lang/rfcs/blob/master/text/3516-gen-blocks.md",
    "https://rust-lang.github.io/rfcs/3560-alignment.html": "https://github.com/rust-lang/rfcs/blob/master/text/3560-alignment.md",
    # 本仓库 crates 外部链改为相对路径
    "https://github.com/rust-lang/rust-lang-learning/tree/main/crates/c06_async": "../../../../../crates/c06_async",
    "https://github.com/rust-lang/rust-lang-learning/tree/main/crates/c08_algorithms": "../../../../../crates/c08_algorithms",
    "https://github.com/rust-lang/rust-lang-learning/tree/main/crates/c10_networks": "../../../../../crates/c10_networks",
}

# 需要删除/注释的具体 URL：old_url -> 说明文本（保留原链接文本，移除链接）
REMOVE_LINKS = {
    "https://github.com/rust-lang/rfcs/pull/9000": "待正式 PR 编号后替换",
    "https://github.com/rust-lang/rfcs/pull/9114": "待正式 PR 编号后替换",
    "https://rust-lang.github.io/rfcs/0000-safety-tags.html": "尚未形成正式 RFC 编号，待发布后替换",
}

# 避免 URL_RE 继续抽取的通配符模式：去掉 scheme
PATTERN_MASKS = {
    "`https://rust-lang.github.io/rfcs/NNNN-*.html`": "`rust-lang.github.io/rfcs/NNNN-*.html`",
    "`https://github.com/rust-lang/rfcs/(pull|issues|blob)/NNNN*`": "`github.com/rust-lang/rfcs/(pull|issues|blob)/NNNN*`",
}

# 整行特殊修复
LINE_FIXES = [
    # concurrency.md 第 512 行：修复被破坏的 markdown 链接
    (re.compile(
        r"\[Rust std::sync::atomic docs; C\+\+ Standard §33\.5\]\(<https://doc\.rust-lang\.org/std/ync/atomic> docs; C\+\+ Standard §33\.5\.html\)"),
     "[Rust std::sync::atomic docs](https://doc.rust-lang.org/std/sync/atomic); C++ Standard §33.5"),
]

# rust-lang.github.io 根页（单独无路径）链接替换
ROOT_IO_RE = re.compile(r"\]\(https://rust-lang\.github\.io/\)")
ROOT_IO_REPLACE = "](https://github.com/rust-lang)"


def fix_file(path: str) -> tuple[int, list[str]]:
    with open(path, encoding="utf-8") as f:
        text = f.read()
    original = text
    changes: list[str] = []

    for old, new in URL_REPLACEMENTS.items():
        # 使用单词/URL 边界，避免 old 作为 new 的前缀被重复替换，也避免替换到更长的 URL 前缀
        rx = re.compile(re.escape(old) + r"(?![A-Za-z0-9\-_./#])")
        if rx.search(text):
            text = rx.sub(new, text)
            changes.append(f"url_replace: {old} -> {new}")

    for old, note in REMOVE_LINKS.items():
        # 将 [text](old_url) 替换为 text（note）
        pattern = re.compile(r"\[([^\]]+)\]" + re.escape(f"({old})"))
        if pattern.search(text):
            text = pattern.sub(rf"\1（{note}）", text)
            changes.append(f"remove_link: {old}")

    for old, new in PATTERN_MASKS.items():
        if old in text:
            text = text.replace(old, new)
            changes.append(f"pattern_mask: {old}")

    if ROOT_IO_RE.search(text):
        text = ROOT_IO_RE.sub(ROOT_IO_REPLACE, text)
        changes.append("root_io_replace")

    for rx, repl in LINE_FIXES:
        if rx.search(text):
            text = rx.sub(repl, text)
            changes.append(f"line_fix: {rx.pattern[:60]}...")

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
    print(f"\n[fix-p0] modified {modified} files")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
