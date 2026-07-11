#!/usr/bin/env python3
"""为缺失来源链接的概念文件插入规范的 > **来源**: 行."""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent / "concept"

SOURCES = {
    "00_meta/terminology_glossary.md": "[TRPL](https://doc.rust-lang.org/book/) · [Rust Reference](https://doc.rust-lang.org/reference/) · [std API Docs](https://doc.rust-lang.org/std/) · [Rustnomicon](https://doc.rust-lang.org/nomicon/) · [Async Book](https://rust-lang.github.io/async-book/) · [Cargo Book](https://doc.rust-lang.org/cargo/) · [Edition Guide](https://doc.rust-lang.org/edition-guide/)",
    "03_advanced/04_macros.md": "[TRPL — Ch19.5 Macros](https://doc.rust-lang.org/book/ch19-06-macros.html) · [Rust Reference — Macros](https://doc.rust-lang.org/reference/macros.html) · [Rust By Example — Macros](https://doc.rust-lang.org/rust-by-example/macros.html)",
    "06_ecosystem/09_cargo_script.md": "[Cargo Book — Scripts](https://doc.rust-lang.org/cargo/reference/scripts.html) · [Rust 1.85 Release Notes](https://blog.rust-lang.org/2025/02/20/Rust-1.85.0.html)",
    "06_ecosystem/10_public_private_deps.md": "[Cargo Book — Dependencies](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html) · [Cargo Book — Features](https://doc.rust-lang.org/cargo/reference/features.html)",
    "06_ecosystem/30_system_composability.md": "[Rust Reference](https://doc.rust-lang.org/reference/) · [Cargo Book](https://doc.rust-lang.org/cargo/) · [Tokio Docs](https://docs.rs/tokio/) · [Tower Docs](https://docs.rs/tower/) · [rayon Docs](https://docs.rs/rayon/)",
    "06_ecosystem/README.md": "[TRPL](https://doc.rust-lang.org/book/) · [Cargo Book](https://doc.rust-lang.org/cargo/) · [Rust RFCs](https://rust-lang.github.io/rfcs/) · [crates.io](https://crates.io/)",
    "07_future/04_effects_system.md": "[Rust Project Goals 2025H1 — const traits](https://rust-lang.github.io/rust-project-goals/2025h1/const-trait.html) · [Keyword Generics Initiative](https://github.com/rust-lang/keyword-generics-initiative) · [a-mir-formality](https://github.com/rust-lang/a-mir-formality)",
    "07_future/17_arbitrary_self_types_preview.md": "[RFC 3519 — Arbitrary Self Types v2](https://rust-lang.github.io/rfcs/3519-arbitrary-self-types-v2.html) · [Rust Reference — Methods](https://doc.rust-lang.org/reference/items/associated-items.html)",
    "07_future/18_field_projections_preview.md": "[std::pin — Pinning](https://doc.rust-lang.org/std/pin/index.html) · [Rust Reference — Field Access](https://doc.rust-lang.org/reference/expressions.html#field-access-expressions)",
    "07_future/29_ebpf_rust.md": "[Aya Book](https://aya-rs.dev/book/) · [Linux Kernel BPF Docs](https://docs.kernel.org/bpf/)",
    "07_future/borrow_sanitizer.md": "[BorrowSanitizer MCP](https://github.com/rust-lang/compiler-team/issues/958) · [Rust Project Goals 2026 — BorrowSanitizer](https://rust-lang.github.io/rust-project-goals/2026/BorrowSanitizer.html) · [BorrowSanitizer 官方站点](https://borrowsanitizer.com/)",
    "07_future/README.md": "[Rust RFCs](https://rust-lang.github.io/rfcs/) · [Rust Blog](https://blog.rust-lang.org/) · [Rust Project Goals](https://rust-lang.github.io/rust-project-goals/)",
    "archive/03_advanced_03_unsafe_rust_archived.md": "[Rust Reference](https://doc.rust-lang.org/reference/) · [The Rust Programming Language](https://doc.rust-lang.org/book/) · [Rust Standard Library](https://doc.rust-lang.org/std/)",
    "archive/03_advanced_05_macros_archived.md": "[Rust Reference](https://doc.rust-lang.org/reference/) · [The Rust Programming Language](https://doc.rust-lang.org/book/) · [Rust Standard Library](https://doc.rust-lang.org/std/)",
    "archive/03_advanced_08_zero_cost_abstractions_archived.md": "[Rust Reference](https://doc.rust-lang.org/reference/) · [The Rust Programming Language](https://doc.rust-lang.org/book/) · [Rust Standard Library](https://doc.rust-lang.org/std/)",
    "archive/06_ecosystem_layer_index_legacy.md": "[TRPL](https://doc.rust-lang.org/book/) · [Cargo Book](https://doc.rust-lang.org/cargo/) · [crates.io](https://crates.io/) · [Rust RFCs](https://rust-lang.github.io/rfcs/)",
    "archive/07_future_layer_index_legacy.md": "[Rust RFCs](https://rust-lang.github.io/rfcs/) · [Rust Blog](https://blog.rust-lang.org/) · [Rust Project Goals](https://rust-lang.github.io/rust-project-goals/)",
    "archive/SUMMARY_mdbook_legacy.md": "[TRPL](https://doc.rust-lang.org/book/) · [Rust Reference](https://doc.rust-lang.org/reference/)",
    "sources/INDEX.md": "[Rust Reference](https://doc.rust-lang.org/reference/) · [TRPL](https://doc.rust-lang.org/book/) · [Rustonomicon](https://doc.rust-lang.org/nomicon/) · [Rust By Example](https://doc.rust-lang.org/rust-by-example/) · [RFCs](https://rust-lang.github.io/rfcs/)",
}


def main():
    for rel, links in SOURCES.items():
        path = ROOT / rel
        if not path.exists():
            print(f"skip (missing): {rel}")
            continue
        text = path.read_text(encoding="utf-8")
        if re.search(r'^>\s*\*\*来源\*\*:', text, re.MULTILINE):
            print(f"already has source: {rel}")
            continue
        new_text, n = re.subn(
            r'^(>\s*\*\*Summary\*\*:[^\n]+)$',
            rf'\1\n> **来源**: {links}',
            text,
            count=1,
            flags=re.MULTILINE,
        )
        if n == 0:
            print(f"no Summary line: {rel}")
            continue
        path.write_text(new_text, encoding="utf-8")
        print(f"added source: {rel}")


if __name__ == "__main__":
    main()
