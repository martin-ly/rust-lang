#!/usr/bin/env python3
"""Fix incorrect RFC references in concept/07_future/18_async_drop_preview.md.

Async Drop does not have a merged RFC. RFC 3308 is offset_of!, and RFC 3157
does not exist. The canonical tracking artifact is GitHub issue #126482 and the
async-fundamentals-initiative roadmap document.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
FILE = ROOT / "concept" / "07_future" / "18_async_drop_preview.md"

text = FILE.read_text(encoding="utf-8")

replacements = {
    # Wrong RFC link in the positioning paragraph
    "（[RFC 3308](https://rust-lang.github.io/rfcs//3308-offset_of.html)）": "（[Async Drop Initiative](https://github.com/rust-lang/rust/issues/126482)）",
    # Source block
    "[RFC 3308 — Async Drop](https://github.com/rust-lang/rfcs/pull/3308)": "[Async Drop Initiative](https://rust-lang.github.io/async-fundamentals-initiative/roadmap/async_drop.html)",
    "[RFC 3308 — Compatibility](https://github.com/rust-lang/rfcs/pull/3308)": "[Async Drop Initiative — Compatibility](https://rust-lang.github.io/async-fundamentals-initiative/roadmap/async_drop.html)",
    "[Async Drop RFC](https://rust-lang.github.io/rfcs//3184-thread-local-cell-methods.html)": "[Async Drop Initiative](https://rust-lang.github.io/async-fundamentals-initiative/roadmap/async_drop.html)",
    # Mentions of RFC 3157
    "`async drop`（[RFC 3157](https://github.com/rust-lang/rfcs/pull/3157)）允许析构函数执行异步操作": "`async drop`（[Async Drop Initiative](https://github.com/rust-lang/rust/issues/126482)）允许析构函数执行异步操作",
    "[来源: [Rust RFC 3157](https://github.com/rust-lang/rfcs/pull/3157)]": "[来源: [Async Drop Initiative](https://rust-lang.github.io/async-fundamentals-initiative/roadmap/async_drop.html)]",
    "[Rust RFC 3157](https://github.com/rust-lang/rfcs/pull/3157)": "[Async Drop Initiative](https://rust-lang.github.io/async-fundamentals-initiative/roadmap/async_drop.html)",
    "[来源: [Rust RFC 3157](https://github.com/rust-lang/rfcs/pull/3157)] · [来源: [Tokio Documentation](https://docs.rs/tokio/)]": "[来源: [Async Drop Initiative](https://rust-lang.github.io/async-fundamentals-initiative/roadmap/async_drop.html)] · [来源: [Tokio Documentation](https://docs.rs/tokio/)]",
}

for old, new in replacements.items():
    if old in text:
        text = text.replace(old, new)
    else:
        print(f"Warning: pattern not found: {old[:80]}...")

# Update the source block to point to canonical resources
old_source = """> **来源**:
> [RFC 3308 — Async Drop](https://github.com/rust-lang/rfcs/pull/3308) ·
> [Tracking Issue #126482](https://github.com/rust-lang/rust/issues/126482) ·
> [Rust Internals — Async Drop Discussion](https://internals.rust-lang.org/t/asynchronous-destructors/11127) ·
> [Without Boats Blog — Async Drop](https://without.boats/blog/let-futures-be-futures/) ·
> [TRPL Ch17 — Pin](https://doc.rust-lang.org/book/ch17-02-concurrency-with-async.html)"""

new_source = """> **来源**:
> [Tracking Issue #126482](https://github.com/rust-lang/rust/issues/126482) ·
> [Async Fundamentals Initiative — Async Drop](https://rust-lang.github.io/async-fundamentals-initiative/roadmap/async_drop.html) ·
> [Rust Internals — Async Drop Discussion](https://internals.rust-lang.org/t/asynchronous-destructors/11127) ·
> [Without Boats Blog — Async Drop](https://without.boats/blog/let-futures-be-futures/) ·
> [TRPL Ch17 — Pin](https://doc.rust-lang.org/book/ch17-02-concurrency-with-async.html)"""

if old_source in text:
    text = text.replace(old_source, new_source)
else:
    print("Warning: source block not found")

# Update the authority source table entry
old_table = """| [RFC 3308 — Async Drop](https://github.com/rust-lang/rfcs/pull/3308) | ✅ 一级 | 官方 RFC 提案 |"""
new_table = """| [Async Drop Initiative](https://rust-lang.github.io/async-fundamentals-initiative/roadmap/async_drop.html) | ✅ 一级 | 官方 Initiative 文档 |
| [Tracking Issue #126482](https://github.com/rust-lang/rust/issues/126482) | ✅ 一级 | 实现跟踪 |"""

if old_table in text:
    text = text.replace(old_table, new_table)
else:
    print("Warning: authority table entry not found")

FILE.write_text(text, encoding="utf-8")
print(f"Updated {FILE.relative_to(ROOT)}")
