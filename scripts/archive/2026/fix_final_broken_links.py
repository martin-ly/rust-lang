#!/usr/bin/env python3
"""修复最后一批非 GitHub 失效链接."""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent / "concept"

REPLACEMENTS = [
    # 补齐 Inside Rust 博客缺失的年份（根据上下文判断为 2025）
    ("https://blog.rust-lang.org/inside-rust/08/20/electing-new-project-directors-2025/", "https://blog.rust-lang.org/inside-rust/2025/08/20/electing-new-project-directors-2025/"),
    ("https://blog.rust-lang.org/inside-rust/10/22/clippys-feature-warming-up/", "https://blog.rust-lang.org/inside-rust/2025/10/22/clippys-feature-warming-up/"),
    ("https://blog.rust-lang.org/inside-rust/07/15/call-for-testing-hint-mostly-unused/", "https://blog.rust-lang.org/inside-rust/2025/07/15/call-for-testing-hint-mostly-unused/"),
    ("https://blog.rust-lang.org/inside-rust/12/20/rustup-1.29.0-beta-cft/", "https://blog.rust-lang.org/inside-rust/2025/12/20/rustup-1.29.0-beta-cft/"),
    ("https://blog.rust-lang.org/inside-rust/10/16/infrastructure-team-q3-recap-and-q4-plan/", "https://blog.rust-lang.org/inside-rust/2025/10/16/infrastructure-team-q3-recap-and-q4-plan/"),
    ("https://blog.rust-lang.org/inside-rust/10/28/compiler-team-new-members/", "https://blog.rust-lang.org/inside-rust/2025/10/28/compiler-team-new-members/"),
    ("https://blog.rust-lang.org/inside-rust/09/30/all-hands-2026/", "https://blog.rust-lang.org/inside-rust/2025/09/30/all-hands-2026/"),
    # 修复误替换产生的畸形 rust-lang.github.io URL
    ("https://rust-lang.github.io/-cn", "https://github.com/rust-lang-cn"),
    ("https://rust-lang.github.io/rust-project-goals//2026/Rust-specification.html", "https://rust-lang.github.io/rust-project-goals/2026/"),
    ("https://rust-lang.github.io/rust-project-goals//2026/safety-tags.html", "https://rust-lang.github.io/rust-project-goals/2026/"),
    ("https://rust-lang.github.io/rust-bindgen//some-ffi-patterns.html", "https://rust-lang.github.io/rust-bindgen/"),
    ("https://rust-lang.github.io/rust-project-goals/2026h1/", "https://rust-lang.github.io/rust-project-goals/"),
]


def main():
    changed = 0
    for p in sorted(ROOT.rglob('*.md')):
        text = p.read_text(encoding='utf-8')
        new_text = text
        for old, new in REPLACEMENTS:
            new_text = new_text.replace(old, new)
        # 通用修复：blog.rust-lang.org/inside-rust/MM/DD/... -> 补齐 2025/
        new_text = re.sub(
            r'https://blog\.rust-lang\.org/inside-rust/(\d{2}/\d{2}/[^\s\)]+)',
            r'https://blog.rust-lang.org/inside-rust/2025/\1',
            new_text,
        )
        # 修复双斜杠
        new_text = new_text.replace('rust-lang.github.io/rust-project-goals//', 'rust-lang.github.io/rust-project-goals/')
        new_text = new_text.replace('rust-lang.github.io/rust-bindgen//', 'rust-lang.github.io/rust-bindgen/')
        if new_text != text:
            p.write_text(new_text, encoding='utf-8')
            changed += 1
    print(f'updated {changed} files')


if __name__ == '__main__':
    main()
