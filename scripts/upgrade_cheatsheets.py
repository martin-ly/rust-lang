#!/usr/bin/env python3
"""
Upgrade docs/research_notes/ quick-reference / cheatsheet documents with
authoritative international Rust content links, remove Rust 1.94 templates,
and mark status as completed.
"""

from pathlib import Path
import re
from datetime import datetime

ROOT = Path("e:/_src/rust-lang/docs/research_notes")
TODAY = "2026-06-29"

# -----------------------------------------------------------------------------
# Common link blocks reused across files
# -----------------------------------------------------------------------------
COMMON_LINKS = """## 🌍 权威国际化资源链接
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)**
> **来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)**
> **来源: [cheats.rs](https://cheats.rs/)**

本节为速查内容提供官方权威来源与社区经典参考的直通链接，便于深入验证与扩展阅读。

### Rust Reference 核心章节

- [Reference 首页](https://doc.rust-lang.org/reference/)
- [Types](https://doc.rust-lang.org/reference/types.html)
- [Items / Traits](https://doc.rust-lang.org/reference/items/traits.html)
- [Expressions](https://doc.rust-lang.org/reference/expressions.html)
- [Statements](https://doc.rust-lang.org/reference/statements.html)
- [Crates and Source Files](https://doc.rust-lang.org/reference/crates-and-source-files.html)

### The Rust Programming Language 核心章节

- [TRPL 首页](https://doc.rust-lang.org/book/)
- [Ch. 4 - Understanding Ownership](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)
- [Ch. 9 - Error Handling](https://doc.rust-lang.org/book/ch09-00-error-handling.html)
- [Ch. 10 - Generic Types, Traits, Lifetimes](https://doc.rust-lang.org/book/ch10-00-generics.html)
- [Ch. 13 - Closures](https://doc.rust-lang.org/book/ch13-00-functional-features.html)
- [Ch. 15 - Smart Pointers](https://doc.rust-lang.org/book/ch15-00-smart-pointers.html)
- [Ch. 16 - Fearless Concurrency](https://doc.rust-lang.org/book/ch16-00-concurrency.html)
- [Ch. 19 - Advanced Features / Macros](https://doc.rust-lang.org/book/ch19-06-macros.html)

### Rust Standard Library 核心 API / 模块

- [std 首页](https://doc.rust-lang.org/std/)
- [std::result](https://doc.rust-lang.org/std/result/)
- [std::option](https://doc.rust-lang.org/std/option/)
- [std::error::Error](https://doc.rust-lang.org/std/error/trait.Error.html)
- [std::fmt](https://doc.rust-lang.org/std/fmt/)
- [std::panic](https://doc.rust-lang.org/std/panic/)
- [std::marker (Send / Sync / PhantomData)](https://doc.rust-lang.org/std/marker/)

### Rust By Example / Rust Cookbook / cheats.rs

- [Rust By Example 首页](https://doc.rust-lang.org/rust-by-example/)
- [Rust Cookbook 首页](https://rust-lang-nursery.github.io/rust-cookbook/)
- [cheats.rs 首页](https://cheats.rs/)

---

"""

CONCURRENCY_SPECIFIC = """### 并发专属权威链接

> **来源: [Rustonomicon - Concurrency](https://doc.rust-lang.org/nomicon/concurrency.html)**
> **来源: [Rust Reference - Memory Model](https://doc.rust-lang.org/reference/memory-model.html)**

#### std::sync / atomics

- [std::sync](https://doc.rust-lang.org/std/sync/)
- [std::sync::atomic](https://doc.rust-lang.org/std/sync/atomic/)
- [std::sync::Mutex](https://doc.rust-lang.org/std/sync/struct.Mutex.html)
- [std::sync::RwLock](https://doc.rust-lang.org/std/sync/struct.RwLock.html)
- [std::sync::Arc](https://doc.rust-lang.org/std/sync/struct.Arc.html)
- [std::sync::Barrier](https://doc.rust-lang.org/std/sync/struct.Barrier.html)
- [std::sync::Condvar](https://doc.rust-lang.org/std/sync/struct.Condvar.html)
- [std::thread](https://doc.rust-lang.org/std/thread/)
- [std::thread::LocalKey](https://doc.rust-lang.org/std/thread/struct.LocalKey.html)
- [AtomicUsize](https://doc.rust-lang.org/std/sync/atomic/struct.AtomicUsize.html)
- [Ordering](https://doc.rust-lang.org/std/sync/atomic/enum.Ordering.html)

#### Rust By Example / Cookbook / cheats.rs

- [RBE - Threads](https://doc.rust-lang.org/rust-by-example/std_misc/threads.html)
- [RBE - Channel](https://doc.rust-lang.org/rust-by-example/std_misc/channels.html)
- [RBE - Atomics](https://doc.rust-lang.org/rust-by-example/std_misc/atomics.html)
- [Rust Cookbook - Concurrency](https://rust-lang-nursery.github.io/rust-cookbook/concurrency.html)
- [cheats.rs - Concurrency](https://cheats.rs/#concurrency)

#### Nomicon / RFC / Miri

- [Rustonomicon - Concurrency](https://doc.rust-lang.org/nomicon/concurrency.html)
- [Rustonomicon - Atomics](https://doc.rust-lang.org/nomicon/atomics.html)
- [RFC 803 - Send / Sync](https://rust-lang.github.io/rfcs/0803-type-ascription.html)
- [RFC 1506 - Closures / Fn* traits](https://rust-lang.github.io/rfcs/1506-adt-kinds.html)
- [Miri - Undefined Behavior detection](https://github.com/rust-lang/miri)
- [Miri README](https://github.com/rust-lang/miri/blob/master/README.md)

"""

LIFETIME_SPECIFIC = """### 生命周期专属权威链接

> **来源: [Rust Reference - Lifetimes](https://doc.rust-lang.org/reference/lifetime-elision.html)**
> **来源: [TRPL Ch. 10 - Lifetimes](https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html)**

#### Reference Lifetime 章节

- [Lifetime Elision](https://doc.rust-lang.org/reference/lifetime-elision.html)
- [Trait and Lifetime Bounds](https://doc.rust-lang.org/reference/trait-bounds.html)
- [Higher-ranked Trait Bounds](https://doc.rust-lang.org/reference/higher-ranked-trait-bounds.html)
- [Subtyping and Variance](https://doc.rust-lang.org/reference/subtyping-and-variance.html)

#### Rust By Example / Cookbook / cheats.rs

- [RBE - Lifetimes](https://doc.rust-lang.org/rust-by-example/scope/lifetime.html)
- [RBE - Lifetime Elision](https://doc.rust-lang.org/rust-by-example/scope/lifetime/elision.html)
- [cheats.rs - Lifetimes](https://cheats.rs/#lifetimes)

#### NLL / RustBelt / Stacked Borrows

- [RFC 2094 - Non-Lexical Lifetimes (NLL)](https://rust-lang.github.io/rfcs/2094-nll.html)
- [RustBelt: Securing the Foundations of the Rust Programming Language](https://plv.mpi-sws.org/rustbelt/)
- [RustBelt paper (PDF)](https://plv.mpi-sws.org/rustbelt/rustbelt.pdf)
- [Stacked Borrows](https://github.com/rust-lang/unsafe-code-guidelines/blob/master/wip/stacked-borrows.md)
- [Rustonomicon - Ownership](https://doc.rust-lang.org/nomicon/ownership.html)
- [Rustonomicon - Lifetimes](https://doc.rust-lang.org/nomicon/lifetimes.html)

"""

MACROS_SPECIFIC = """### 宏系统专属权威链接

> **来源: [Rust Reference - Macros](https://doc.rust-lang.org/reference/macros.html)**
> **来源: [TRPL Ch. 19 - Macros](https://doc.rust-lang.org/book/ch19-06-macros.html)**

#### Reference Macros

- [Macros](https://doc.rust-lang.org/reference/macros.html)
- [Macro Rules](https://doc.rust-lang.org/reference/macros-by-example.html)
- [Procedural Macros](https://doc.rust-lang.org/reference/procedural-macros.html)
- [Derive Macros](https://doc.rust-lang.org/reference/attributes/derive.html)

#### Standard Library proc-macro

- [std::proc_macro](https://doc.rust-lang.org/proc_macro/)
- [proc_macro::TokenStream](https://doc.rust-lang.org/proc_macro/struct.TokenStream.html)

#### Rust By Example / Cookbook / cheats.rs

- [RBE - Macros](https://doc.rust-lang.org/rust-by-example/macros.html)
- [RBE - macro_rules!](https://doc.rust-lang.org/rust-by-example/macros.html)
- [cheats.rs - Macros](https://cheats.rs/#macros)

#### proc-macro RFC / rustc dev guide / Little Book

- [RFC 1566 - Procedural Macros](https://rust-lang.github.io/rfcs/1566-proc-macros.html)
- [rustc dev guide - Macro Expansion](https://rustc-dev-guide.rust-lang.org/macro-expansion.html)
- [rustc dev guide - Procedural Macros](https://rustc-dev-guide.rust-lang.org/proc-macros.html)
- [The Little Book of Rust Macros](https://veykril.github.io/tlborm/)
- [The Little Book of Rust Macros - Syntax Extensions](https://veykril.github.io/tlborm/decl-macros/minutiae/fragment-specifiers.html)

"""

ERROR_HANDLING_SPECIFIC = """### 错误处理专属权威链接

> **来源: [TRPL Ch. 9 - Error Handling](https://doc.rust-lang.org/book/ch09-00-error-handling.html)**
> **来源: [Rust Reference - Result](https://doc.rust-lang.org/std/result/)**

#### std::error::Error

- [std::error::Error trait](https://doc.rust-lang.org/std/error/trait.Error.html)
- [std::result::Result](https://doc.rust-lang.org/std/result/)
- [std::option::Option](https://doc.rust-lang.org/std/option/)
- [std::fmt::Display](https://doc.rust-lang.org/std/fmt/trait.Display.html)
- [std::fmt::Debug](https://doc.rust-lang.org/std/fmt/trait.Debug.html)

#### Rust By Example / Cookbook / cheats.rs

- [RBE - Error Handling](https://doc.rust-lang.org/rust-by-example/error.html)
- [RBE - Option & unwrap](https://doc.rust-lang.org/rust-by-example/error/option_unwrap.html)
- [RBE - Result](https://doc.rust-lang.org/rust-by-example/error/result.html)
- [RBE - ? operator](https://doc.rust-lang.org/rust-by-example/error/result/enter_question_mark.html)
- [Rust Cookbook - Errors](https://rust-lang-nursery.github.io/rust-cookbook/errors.html)
- [cheats.rs - Error Handling](https://cheats.rs/#error-handling)

#### RFC 2504 / anyhow / thiserror

- [RFC 2504 - Try Trait / `?`](https://rust-lang.github.io/rfcs/2504-try-trait.html)
- [anyhow docs](https://docs.rs/anyhow/latest/anyhow/)
- [anyhow GitHub](https://github.com/dtolnay/anyhow)
- [thiserror docs](https://docs.rs/thiserror/latest/thiserror/)
- [thiserror GitHub](https://github.com/dtolnay/thiserror)

"""

QUICK_SPECIFIC = """### 快速查找专属语言 / API 链接

> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

#### 所有权与借用

- [Reference - Ownership](https://doc.rust-lang.org/reference/ownership.html)
- [TRPL Ch. 4 - Ownership](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)
- [TRPL Ch. 4 - References and Borrowing](https://doc.rust-lang.org/book/ch04-02-references-and-borrowing.html)
- [std::cell (Cell / RefCell)](https://doc.rust-lang.org/std/cell/)
- [std::rc::Rc](https://doc.rust-lang.org/std/rc/struct.Rc.html)
- [std::sync::Arc](https://doc.rust-lang.org/std/sync/struct.Arc.html)

#### 类型系统

- [Reference - Types](https://doc.rust-lang.org/reference/types.html)
- [Reference - Traits](https://doc.rust-lang.org/reference/items/traits.html)
- [Reference - Generics](https://doc.rust-lang.org/reference/items/generics.html)
- [TRPL Ch. 10 - Generics](https://doc.rust-lang.org/book/ch10-00-generics.html)
- [std::marker (Send / Sync / Copy / Sized)](https://doc.rust-lang.org/std/marker/)

#### 异步与并发

- [TRPL Ch. 17 - Async / Await](https://doc.rust-lang.org/book/ch17-00-async-await.html)
- [std::future::Future](https://doc.rust-lang.org/std/future/trait.Future.html)
- [std::pin::Pin](https://doc.rust-lang.org/std/pin/struct.Pin.html)
- [std::sync](https://doc.rust-lang.org/std/sync/)
- [std::thread](https://doc.rust-lang.org/std/thread/)

#### 生命周期

- [Reference - Lifetime Elision](https://doc.rust-lang.org/reference/lifetime-elision.html)
- [TRPL Ch. 10 - Lifetimes](https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html)
- [cheats.rs - Lifetimes](https://cheats.rs/#lifetimes)

#### 宏与错误处理

- [Reference - Macros](https://doc.rust-lang.org/reference/macros.html)
- [TRPL Ch. 19 - Macros](https://doc.rust-lang.org/book/ch19-06-macros.html)
- [TRPL Ch. 9 - Error Handling](https://doc.rust-lang.org/book/ch09-00-error-handling.html)
- [std::result::Result](https://doc.rust-lang.org/std/result/)
- [std::option::Option](https://doc.rust-lang.org/std/option/)

"""

# -----------------------------------------------------------------------------
# File-specific replacement definitions
# -----------------------------------------------------------------------------
FILE_CONFIG = {
    "10_quick_reference.md": {
        "specific": QUICK_SPECIFIC,
        "status_old": '> **状态**: ✅ 已完成（全面检查推进计划 Phase 1–8 完成）',
        "status_new": '> **状态**: ✅ 完成',
        "footer_status_old": '**状态**: ✅ 权威来源对齐完成 (Batch 8)',
        "footer_status_new": '**状态**: ✅ 完成',
    },
    "10_quick_find.md": {
        "specific": QUICK_SPECIFIC,
        "status_old": '> **状态**: ✅ 已完成（全面检查推进计划 Phase 1–8 完成）',
        "status_new": '> **状态**: ✅ 完成',
        "footer_status_old": '**状态**: ✅ 权威来源对齐完成 (Batch 8)',
        "footer_status_new": '**状态**: ✅ 完成',
    },
    "10_concurrency_cheatsheet.md": {
        "specific": CONCURRENCY_SPECIFIC,
        "status_old": '**状态**: ✅ 已扩展 - 并发速查卡完整版',
        "status_new": '**状态**: ✅ 完成',
        "footer_status_old": '**状态**: ✅ 权威来源对齐完成 (Batch 8)',
        "footer_status_new": '**状态**: ✅ 完成',
    },
    "10_lifetime_cheatsheet.md": {
        "specific": LIFETIME_SPECIFIC,
        "status_old": '**状态**: ✅ 已扩展 - 生命周期速查卡完整版',
        "status_new": '**状态**: ✅ 完成',
        "footer_status_old": '**状态**: ✅ 权威来源对齐完成 (Batch 8)',
        "footer_status_new": '**状态**: ✅ 完成',
    },
    "10_macros_cheatsheet.md": {
        "specific": MACROS_SPECIFIC,
        "status_old": '> **状态**: ✅ 已扩展',
        "status_new": '> **状态**: ✅ 完成',
        "intermediate_status_old": '**状态**: ✅ 已扩展 - 宏速查卡完整版',
        "intermediate_status_new": '**状态**: ✅ 完成',
        "footer_status_old": '**状态**: ✅ 权威来源对齐完成 (Batch 8)',
        "footer_status_new": '**状态**: ✅ 完成',
    },
    "10_error_handling_cheatsheet.md": {
        "specific": ERROR_HANDLING_SPECIFIC,
        "status_old": '**状态**: ✅ 已完成 - 错误处理速查卡 (4/5)',
        "status_new": '**状态**: ✅ 完成',
        "footer_status_old": '**状态**: ✅ 权威来源对齐完成 (Batch 8)',
        "footer_status_new": '**状态**: ✅ 完成',
    },
}


def remove_194_sections(text: str) -> str:
    """Remove both variants of Rust 1.94 update / deep-integration sections."""
    # Variant 1: ## 🆕 Rust 1.94 深度整合更新 ... ---\n\n## 相关概念
    pattern1 = re.compile(
        r"## 🆕 Rust 1\.94 深度整合更新\n.*?\n---\n\n(?=## 相关概念)",
        re.DOTALL,
    )
    text = pattern1.sub("", text)

    # Variant 2: ## 🆕 Rust 1.94 更新 / 研究更新 ... ends before next major heading
    # These sections usually end with "**最后更新**: 2026-03-14" and a --- separator.
    pattern2 = re.compile(
        r"## 🆕 Rust 1\.94 (?:更新|研究更新)\n.*?\n---\n",
        re.DOTALL,
    )
    text = pattern2.sub("", text)

    # Clean up any leftover dangling lines that mention Rust 1.94 migration guide / 特性速查
    text = re.sub(r"- Rust 1\.94 迁移指南\n", "", text)
    text = re.sub(r"- \[Rust 1\.94 特性速查\n", "", text)
    text = re.sub(r"- Rust 1\.94 特性速查\n", "", text)

    return text


def update_metadata(text: str) -> str:
    """Update last-update date wherever it appears in the header/footer."""
    # Update header last-update line if present (preserve spacing)
    text = re.sub(
        r"^> \*\*最后更新\*\*: \d{4}-\d{2}-\d{2}$",
        f"> **最后更新**: {TODAY}",
        text,
        flags=re.MULTILINE,
    )
    # Update footer last-update lines
    text = re.sub(
        r"^\*\*最后更新\*\*: \d{4}-\d{2}-\d{2}$",
        f"**最后更新**: {TODAY}",
        text,
        flags=re.MULTILINE,
    )
    text = re.sub(
        r"\*\*最后更新\*\*: \d{4}-\d{2}-\d{2} \(Rust 1\.94 深度整合\)",
        f"**最后更新**: {TODAY}",
        text,
    )
    # Rust version stays 1.96.0+ (Edition 2024)
    return text


def insert_authoritative_links(text: str, specific: str) -> str:
    """Insert the authoritative links section right before ## 相关概念."""
    section = COMMON_LINKS + specific
    # Insert before the final "## 相关概念" heading
    marker = "## 相关概念\n"
    if marker in text:
        return text.replace(marker, section + marker, 1)
    # Fallback: append before the end if marker absent
    return text.rstrip() + "\n\n" + section


def process_file(filename: str, cfg: dict) -> None:
    path = ROOT / filename
    text = path.read_text(encoding="utf-8")

    # 1. Remove old 1.94 templates
    text = remove_194_sections(text)

    # 2. Update status lines
    text = text.replace(cfg["status_old"], cfg["status_new"], 1)
    if "intermediate_status_old" in cfg:
        text = text.replace(cfg["intermediate_status_old"], cfg["intermediate_status_new"], 1)
    text = text.replace(cfg["footer_status_old"], cfg["footer_status_new"], 1)

    # 3. Update dates
    text = update_metadata(text)

    # 4. Insert authoritative links
    text = insert_authoritative_links(text, cfg["specific"])

    path.write_text(text, encoding="utf-8")
    print(f"Updated {filename}")


def main() -> None:
    for filename, cfg in FILE_CONFIG.items():
        process_file(filename, cfg)


if __name__ == "__main__":
    main()
