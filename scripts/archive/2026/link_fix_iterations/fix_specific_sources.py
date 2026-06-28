#!/usr/bin/env python3
"""将部分概念文件的根 URL 来源替换为指向官方文档具体章节的权威链接."""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent / "concept"

SPECIFIC_SOURCES = {
    "01_foundation/00_pl_prerequisites.md": "[TRPL — Foreword](https://doc.rust-lang.org/book/foreword.html) · [Rust Reference](https://doc.rust-lang.org/reference/)",
    "01_foundation/00_start.md": "[TRPL — Getting Started](https://doc.rust-lang.org/book/ch01-00-getting-started.html) · [Rust Installation](https://www.rust-lang.org/tools/install)",
    "01_foundation/03_lifetimes_advanced.md": "[TRPL — Advanced Lifetimes](https://doc.rust-lang.org/book/ch19-02-advanced-lifetimes.html) · [Reference — Lifetime Elision](https://doc.rust-lang.org/reference/lifetime-elision.html) · [Reference — Subtyping and Variance](https://doc.rust-lang.org/reference/subtyping-and-variance.html)",
    "01_foundation/10_error_handling_basics.md": "[TRPL — Error Handling](https://doc.rust-lang.org/book/ch09-00-error-handling.html) · [std::result::Result](https://doc.rust-lang.org/std/result/enum.Result.html)",
    "01_foundation/11_numeric_types.md": "[TRPL — Data Types](https://doc.rust-lang.org/book/ch03-02-data-types.html) · [Reference — Types](https://doc.rust-lang.org/reference/types.html)",
    "01_foundation/20_variable_model.md": "[TRPL — Variables and Mutability](https://doc.rust-lang.org/book/ch03-01-variables-and-mutability.html) · [TRPL — Data Types](https://doc.rust-lang.org/book/ch03-02-data-types.html)",
    "01_foundation/21_effects_and_purity.md": "[Reference — Constant Evaluation](https://doc.rust-lang.org/reference/const_eval.html) · [Rust Project Goals — const traits](https://rust-lang.github.io/rust-project-goals/2025h1/const-trait.html)",
    "01_foundation/22_data_abstraction_spectrum.md": "[TRPL — Structs](https://doc.rust-lang.org/book/ch05-00-structs.html) · [TRPL — Enums and Pattern Matching](https://doc.rust-lang.org/book/ch06-00-enums.html) · [Reference — Items](https://doc.rust-lang.org/reference/items.html)",
    "01_foundation/28_ownership_inventories_brown_book.md": "[Brown University Interactive Rust Book](https://rust-book.cs.brown.edu/) · [TRPL — Understanding Ownership](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)",
    "03_advanced/00_before_formal.md": "[Rust Reference](https://doc.rust-lang.org/reference/) · [Rustonomicon](https://doc.rust-lang.org/nomicon/) · [Rust By Example](https://doc.rust-lang.org/rust-by-example/)",
    "03_advanced/02_async_advanced.md": "[Async Book](https://rust-lang.github.io/async-book/) · [TRPL — Async/Await](https://doc.rust-lang.org/book/ch17-00-async-await.html) · [std::future::Future](https://doc.rust-lang.org/std/future/trait.Future.html)",
    "03_advanced/08_nll_and_polonius.md": "[RFC 2094 — NLL](https://rust-lang.github.io/rfcs/2094-nll.html) · [Polonius](https://github.com/rust-lang/polonius) · [Reference — Lifetimes](https://doc.rust-lang.org/reference/items/lifetimes.html)",
    "03_advanced/12_unsafe_rust_patterns.md": "[Rustonomicon](https://doc.rust-lang.org/nomicon/) · [Reference — Unsafe Rust](https://doc.rust-lang.org/reference/unsafe.html)",
    "03_advanced/14_custom_allocators.md": "[std::alloc::GlobalAlloc](https://doc.rust-lang.org/std/alloc/trait.GlobalAlloc.html) · [Reference — Allocator API](https://doc.rust-lang.org/reference/allocator-api.html)",
    "03_advanced/15_zero_copy_parsing.md": "[std::io](https://doc.rust-lang.org/std/io/) · [Rust By Example — File I/O](https://doc.rust-lang.org/rust-by-example/std_misc/file.html)",
    "03_advanced/16_lock_free.md": "[Rustonomicon — Atomics](https://doc.rust-lang.org/nomicon/atomics.html) · [std::sync::atomic](https://doc.rust-lang.org/std/sync/atomic/index.html)",
    "03_advanced/17_type_erasure.md": "[TRPL — Trait Objects](https://doc.rust-lang.org/book/ch17-02-trait-objects.html) · [Reference — Dynamically Sized Types](https://doc.rust-lang.org/reference/dynamically-sized-types.html)",
    "03_advanced/18_network_programming.md": "[std::net](https://doc.rust-lang.org/std/net/) · [Tokio Docs](https://docs.rs/tokio/) · [Async Book](https://rust-lang.github.io/async-book/)",
    "03_advanced/19_parallel_distributed_pattern_spectrum.md": "[std::thread](https://doc.rust-lang.org/std/thread/) · [Rayon Docs](https://docs.rs/rayon/) · [TRPL — Fearless Concurrency](https://doc.rust-lang.org/book/ch16-00-concurrency.html)",
    "03_advanced/20_stream_processing_semantics.md": "[Async Book — Streams](https://rust-lang.github.io/async-book/05_streams/01_chapter.html) · [futures::stream](https://docs.rs/futures/)",
    "07_future/23_rust_edition_guide.md": "[Edition Guide](https://doc.rust-lang.org/edition-guide/) · [TRPL — Appendix: Rust Editions](https://doc.rust-lang.org/book/appendix-05-editions.html)",
    "07_future/24_roadmap.md": "[Rust Project Goals](https://rust-lang.github.io/rust-project-goals/) · [Rust Blog](https://blog.rust-lang.org/) · [Rust Roadmap](https://www.rust-lang.org/)",
    "07_future/27_compile_time_execution.md": "[Reference — Constant Evaluation](https://doc.rust-lang.org/reference/const_eval.html) · [TRPL — Macros](https://doc.rust-lang.org/book/ch19-06-macros.html)",
    "07_future/28_rust_for_webassembly.md": "[Rust and WebAssembly Book](https://rustwasm.github.io/book/) · [TRPL — Advanced Features](https://doc.rust-lang.org/book/ch19-00-advanced-features.html)",
}


def main():
    for rel, links in SPECIFIC_SOURCES.items():
        path = ROOT / rel
        if not path.exists():
            print(f"skip (missing): {rel}")
            continue
        text = path.read_text(encoding="utf-8")
        new_text, n = re.subn(
            r'^>\s*\*\*来源\*\*:\s*.*?$',
            f'> **来源**: {links}',
            text,
            count=1,
            flags=re.MULTILINE,
        )
        if n:
            path.write_text(new_text, encoding="utf-8")
            print(f"updated: {rel}")
        else:
            print(f"no source line: {rel}")


if __name__ == "__main__":
    main()
