#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Append standardized metadata fields to behavioral pattern markdown files."""

import os
import re
from pathlib import Path

TARGET_DIR = Path("e:/_src/rust-lang/docs/research_notes/software_design_theory/01_design_patterns_formal/03_behavioral/")

SKIP_MARKERS = ["迁回待审", "权威国际化来源对齐升级中"]

METADATA_APPEND = """\n> **创建日期**: 2026-02-12
> **最后更新**: 2026-06-29
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: 🔄 迁回待审 / 权威国际化来源对齐升级中
> **对齐说明**: 本文档已于 2026-06-29 从 `archive/research_notes_2026_06_25/software_design_theory/01_design_patterns_formal/03_behavioral/` 迁回，正在按 [Rust Design Patterns – Behavioral](https://rust-unofficial.github.io/patterns/patterns/behavioural/index.html)、[Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)、GoF *Design Patterns* 等权威来源升级。
>
> **权威来源**: [Rust Design Patterns – Behavioral](https://rust-unofficial.github.io/patterns/patterns/behavioural/index.html) | [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) | [The Rust Programming Language](https://doc.rust-lang.org/book/) | [Rust Reference](https://doc.rust-lang.org/reference/)"""

# Pattern to locate the metadata block right after the H1 title.
BLOCK_PATTERN = re.compile(
    r"(> \*\*Bloom 层级\*\*: L5-L6 \(分析/评价/创造\))(?=\n)",
    re.MULTILINE,
)


def needs_skip(content: str) -> bool:
    return any(marker in content for marker in SKIP_MARKERS)


def main():
    modified = []
    skipped = []
    errors = []

    for md_path in sorted(TARGET_DIR.glob("*.md")):
        if md_path.name == "README.md":
            continue

        try:
            content = md_path.read_text(encoding="utf-8")

            if needs_skip(content):
                skipped.append(md_path.name)
                continue

            if not BLOCK_PATTERN.search(content):
                errors.append(f"{md_path.name}: metadata block pattern not found")
                continue

            new_content = BLOCK_PATTERN.sub(r"\1" + METADATA_APPEND, content, count=1)

            if new_content == content:
                errors.append(f"{md_path.name}: substitution did not change content")
                continue

            md_path.write_text(new_content, encoding="utf-8")
            modified.append(md_path.name)
        except Exception as exc:
            errors.append(f"{md_path.name}: {exc}")

    print("=== Modified ===")
    for name in modified:
        print(name)

    print("\n=== Skipped (already migrated) ===")
    for name in skipped:
        print(name)

    print("\n=== Errors ===")
    for err in errors:
        print(err)

    print(f"\nTotal modified: {len(modified)}")
    print(f"Total skipped: {len(skipped)}")
    print(f"Total errors: {len(errors)}")


if __name__ == "__main__":
    main()
