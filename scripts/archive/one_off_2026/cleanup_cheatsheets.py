#!/usr/bin/env python3
"""
Cleanup remaining Rust 1.94 TOC entries and stale status lines after the main
authoritative-links upgrade.
"""

from pathlib import Path

ROOT = Path("e:/_src/rust-lang/docs/research_notes")
TARGETS = [
    "10_quick_reference.md",
    "10_quick_find.md",
    "10_concurrency_cheatsheet.md",
    "10_lifetime_cheatsheet.md",
    "10_macros_cheatsheet.md",
    "10_error_handling_cheatsheet.md",
]

# Each replacement only injects the new "权威国际化资源链接" TOC entry;
# the existing 相关概念 / 权威来源索引 entries are kept as-is.
TOC_REPLACEMENTS = {
    "10_quick_reference.md": (
        "  - [🆕 Rust 1.94 深度整合更新](#-rust-194-深度整合更新)\n"
        "    - [本文档的Rust 1.94更新要点](#本文档的rust-194更新要点)\n"
        "      - [核心特性应用](#核心特性应用)\n"
        "      - [代码示例更新](#代码示例更新)\n"
        "      - [相关文档](#相关文档)\n"
        "  - [**最后更新**: 2026-06-29](#最后更新-2026-03-14-rust-194-深度整合)\n",
        "  - [🌍 权威国际化资源链接](#-权威国际化资源链接)\n",
    ),
    "10_quick_find.md": (
        "  - [🆕 Rust 1.94 深度整合更新](#-rust-194-深度整合更新)\n"
        "    - [本文档的Rust 1.94更新要点](#本文档的rust-194更新要点)\n"
        "      - [核心特性应用](#核心特性应用)\n"
        "      - [代码示例更新](#代码示例更新)\n"
        "      - [相关文档](#相关文档)\n",
        "  - [🌍 权威国际化资源链接](#-权威国际化资源链接)\n",
    ),
    "10_concurrency_cheatsheet.md": (
        "  - [🆕 Rust 1.94 研究更新](#-rust-194-研究更新)\n"
        "    - [核心研究点](#核心研究点)\n"
        "  - [🆕 Rust 1.94 深度整合更新](#-rust-194-深度整合更新)\n"
        "    - [本文档的Rust 1.94更新要点](#本文档的rust-194更新要点)\n"
        "      - [核心特性应用](#核心特性应用)\n"
        "      - [代码示例更新](#代码示例更新)\n"
        "      - [相关文档](#相关文档)\n"
        "  - [**最后更新**: 2026-06-29](#最后更新-2026-03-14-rust-194-深度整合)\n",
        "  - [🌍 权威国际化资源链接](#-权威国际化资源链接)\n",
    ),
    "10_lifetime_cheatsheet.md": (
        "  - [🆕 Rust 1.94 更新](#-rust-194-更新)\n"
        "  - [🆕 Rust 1.94 深度整合更新](#-rust-194-深度整合更新)\n"
        "    - [本文档的Rust 1.94更新要点](#本文档的rust-194更新要点)\n"
        "      - [核心特性应用](#核心特性应用)\n"
        "      - [代码示例更新](#代码示例更新)\n"
        "      - [相关文档](#相关文档)\n"
        "  - [**最后更新**: 2026-06-29](#最后更新-2026-03-14-rust-194-深度整合)\n",
        "  - [🌍 权威国际化资源链接](#-权威国际化资源链接)\n",
    ),
    "10_macros_cheatsheet.md": (
        "  - [🆕 Rust 1.94 深度整合更新](#-rust-194-深度整合更新)\n"
        "    - [本文档的Rust 1.94更新要点](#本文档的rust-194更新要点)\n"
        "      - [核心特性应用](#核心特性应用)\n"
        "      - [代码示例更新](#代码示例更新)\n"
        "      - [相关文档](#相关文档)\n"
        "  - [**最后更新**: 2026-06-29](#最后更新-2026-03-14-rust-194-深度整合)\n",
        "  - [🌍 权威国际化资源链接](#-权威国际化资源链接)\n",
    ),
    "10_error_handling_cheatsheet.md": (
        "  - [🆕 Rust 1.94 更新](#-rust-194-更新)\n"
        "  - [🆕 Rust 1.94 深度整合更新](#-rust-194-深度整合更新)\n"
        "    - [本文档的Rust 1.94更新要点](#本文档的rust-194更新要点)\n"
        "      - [核心特性应用](#核心特性应用)\n"
        "      - [代码示例更新](#代码示例更新)\n"
        "      - [相关文档](#相关文档)\n"
        "  - [**最后更新**: 2026-06-29](#最后更新-2026-03-14-rust-194-深度整合)\n",
        "  - [🌍 权威国际化资源链接](#-权威国际化资源链接)\n",
    ),
}

# Additional stale status lines to normalise.
STATUS_FIXES = {
    "10_quick_reference.md": (
        "**状态**: ✅ **研究笔记系统 100% 完成**（全面检查推进计划 Phase 1–8 完成）",
        "**状态**: ✅ 完成",
    ),
    "10_quick_find.md": (
        "**状态**: ✅ **Rust 1.93.1+ 更新完成**",
        "**状态**: ✅ 完成",
    ),
}


def main() -> None:
    for filename in TARGETS:
        path = ROOT / filename
        text = path.read_text(encoding="utf-8")

        if filename in TOC_REPLACEMENTS:
            old, new = TOC_REPLACEMENTS[filename]
            if old in text:
                text = text.replace(old, new, 1)
            else:
                print(f"  [warn] TOC pattern not found in {filename}")

        if filename in STATUS_FIXES:
            old, new = STATUS_FIXES[filename]
            text = text.replace(old, new, 1)

        path.write_text(text, encoding="utf-8")
        print(f"Cleaned {filename}")


if __name__ == "__main__":
    main()
