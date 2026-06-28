#!/usr/bin/env python3
"""修复上一轮替换产生的重复 URL 及其他杂项失效链接."""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent / "concept"

REPLACEMENTS = [
    # 修复 rustc-dev-guide 后端重复替换
    ("https://rustc-dev-guide.rust-lang.org/backend/codegen.htmlcodegen.html#what-is-llvm", "https://rustc-dev-guide.rust-lang.org/backend/codegen.html#what-is-llvm"),
    ("https://rustc-dev-guide.rust-lang.org/backend/codegen.htmlcodegen.html", "https://rustc-dev-guide.rust-lang.org/backend/codegen.html"),
    ("https://rustc-dev-guide.rust-lang.org/backend/codegen.htmlbackend-agnostic.html", "https://rustc-dev-guide.rust-lang.org/backend/backend-agnostic.html"),
    ("https://rustc-dev-guide.rust-lang.org/backend/codegen.htmlmonomorph.html", "https://rustc-dev-guide.rust-lang.org/backend/monomorph.html"),
    ("https://rustc-dev-guide.rust-lang.org/backend/codegen.htmlmonomorph.html#lto-and-monomorphization", "https://rustc-dev-guide.rust-lang.org/backend/monomorph.html#lto-and-monomorphization"),
    ("https://rustc-dev-guide.rust-lang.org/backend/codegen.htmlindex.html", "https://rustc-dev-guide.rust-lang.org/backend/codegen.html"),
    ("https://rustc-dev-guide.rust-lang.org/optimizations.html", "https://rustc-dev-guide.rust-lang.org/"),
    # rust-lang.github.io 根 URL 实际不存在，指向 GitHub 组织
    ("https://rust-lang.github.io/", "https://github.com/rust-lang"),
    # 2026h1 目标页不存在
    ("https://rust-lang.github.io/rust-project-goals/2026h1/", "https://rust-lang.github.io/rust-project-goals/"),
    # rust-bindgen ffi patterns 不存在，指向 bindgen book 根
    ("https://rust-lang.github.io/rust-bindgen/some-ffi-patterns.html", "https://rust-lang.github.io/rust-bindgen/"),
    # 项目目标缺失页面
    ("https://rust-lang.github.io/rust-project-goals/2026/Rust-specification.html", "https://rust-lang.github.io/rust-project-goals/2026/"),
    ("https://rust-lang.github.io/rust-project-goals/2026/safety-tags.html", "https://rust-lang.github.io/rust-project-goals/2026/"),
    # Bevy ECS 也失效，统一指向 Bevy book 根
    ("https://bevyengine.org/learn/book/ecs/", "https://bevyengine.org/learn/book/"),
    # 无效的 docs.rs URL（含中文括号）指向 async-trait crate
    ("https://docs.rs/AFIT（async fn in trait，Rust 1.75.0+ 稳定）/", "https://docs.rs/async-trait/latest/async_trait/"),
]

BLOG_ROOT = "https://blog.rust-lang.org/"
INSIDE_ROOT = "https://blog.rust-lang.org/inside-rust/"


def main():
    changed = 0
    for p in sorted(ROOT.rglob('*.md')):
        text = p.read_text(encoding='utf-8')
        new_text = text
        for old, new in REPLACEMENTS:
            new_text = new_text.replace(old, new)
        # 批量替换已确认不存在的 2026 blog 文章
        new_text = re.sub(
            r'https://blog\.rust-lang\.org/inside-rust/2026/\d{2}/\d{2}/[^\s\)]+\.html',
            INSIDE_ROOT,
            new_text,
        )
        new_text = re.sub(
            r'https://blog\.rust-lang\.org/2026/\d{2}/\d{2}/[^\s\)]+\.html',
            BLOG_ROOT,
            new_text,
        )
        new_text = re.sub(
            r'https://blog\.rust-lang\.org/inside-rust/2025/',
            INSIDE_ROOT,
            new_text,
        )
        new_text = re.sub(
            r'https://blog\.rust-lang\.org/inside-rust/2021/09/06/Separating-contract-and-implementation\.html',
            INSIDE_ROOT,
            new_text,
        )
        new_text = re.sub(
            r'https://blog\.rust-lang\.org/inside-rust/2023/03/17/parallel-rustc\.html',
            INSIDE_ROOT,
            new_text,
        )
        if new_text != text:
            p.write_text(new_text, encoding='utf-8')
            changed += 1
    print(f'updated {changed} files')


if __name__ == '__main__':
    main()
