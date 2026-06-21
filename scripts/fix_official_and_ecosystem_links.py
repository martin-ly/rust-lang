#!/usr/bin/env python3
"""修复 concept/ 中官方 doc.rust-lang.org 及部分生态站点的失效链接."""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent / "concept"

REPLACEMENTS = [
    # TRPL
    ("https://doc.rust-lang.org/book/ch14-05-configuration.html", "https://doc.rust-lang.org/cargo/reference/config.html"),
    ("https://doc.rust-lang.org/book/ch17-04-pin.html", "https://doc.rust-lang.org/book/ch17-03-ffo.html"),
    ("https://doc.rust-lang.org/book/ch19-02-advanced-traits.html", "https://doc.rust-lang.org/book/ch19-03-advanced-traits.html"),
    ("https://doc.rust-lang.org/book/ch19-05-advanced-lifetimes.html", "https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html"),
    # Cargo
    ("https://doc.rust-lang.org/cargo/reference/cargo-home.html", "https://doc.rust-lang.org/cargo/guide/cargo-home.html"),
    # Edition guide
    ("https://doc.rust-lang.org/edition-guide/faq.html", "https://doc.rust-lang.org/edition-guide/index.html"),
    ("https://doc.rust-lang.org/edition-guide/rust-2024/gen-blocks.html", "https://rust-lang.github.io/rfcs/3513-gen-blocks.html"),
    ("https://doc.rust-lang.org/edition-guide/rust-2018/module-system.html", "https://doc.rust-lang.org/edition-guide/rust-2018/path-changes.html"),
    # Unstable book
    ("https://doc.rust-lang.org/nightly/unstable-book/language-features/const-fn.html", "https://doc.rust-lang.org/reference/const_eval.html"),
    # Nomicon
    ("https://doc.rust-lang.org/nomicon/interior-mutability.html", "https://doc.rust-lang.org/nomicon/concurrency.html"),
    ("https://doc.rust-lang.org/nomicon/pinning.html", "https://doc.rust-lang.org/std/pin/index.html"),
    ("https://doc.rust-lang.org/nomicon/pins-and-fns.html", "https://doc.rust-lang.org/std/pin/index.html"),
    ("https://doc.rust-lang.org/nomicon/rc-mostly.html", "https://doc.rust-lang.org/std/rc/struct.Rc.html"),
    ("https://doc.rust-lang.org/nomicon/uninit.html", "https://doc.rust-lang.org/nomicon/uninitialized.html"),
    ("https://doc.rust-lang.org/nomicon/what-is-unsafe.html", "https://doc.rust-lang.org/nomicon/meet-safe-and-unsafe.html"),
    # Reference
    ("https://doc.rust-lang.org/reference/expressions/field-access-expr.html", "https://doc.rust-lang.org/reference/expressions.html#field-access-expressions"),
    ("https://doc.rust-lang.org/reference/expressions/generator-expr.html", "https://doc.rust-lang.org/reference/expressions.html#generator-expressions"),
    ("https://doc.rust-lang.org/reference/items/generators.html", "https://doc.rust-lang.org/reference/items/functions.html#generator-functions"),
    ("https://doc.rust-lang.org/reference/items/trait-aliases.html", "https://doc.rust-lang.org/reference/items/traits.html#trait-aliases"),
    ("https://doc.rust-lang.org/reference/memory-allocation.html", "https://doc.rust-lang.org/std/alloc/index.html"),
    ("https://doc.rust-lang.org/reference/panic-macro.html", "https://doc.rust-lang.org/reference/panic.html"),
    ("https://doc.rust-lang.org/reference/ownership.html", "https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html"),
    ("https://doc.rust-lang.org/reference/pointer-types.html", "https://doc.rust-lang.org/reference/types.html"),
    ("https://doc.rust-lang.org/reference/type-inference.html", "https://doc.rust-lang.org/reference/types.html"),
    ("https://doc.rust-lang.org/reference/unsafe-op.html", "https://doc.rust-lang.org/reference/unsafe-blocks.html"),
    # RBE
    ("https://doc.rust-lang.org/rust-by-example/concurrency.html", "https://doc.rust-lang.org/rust-by-example/std_misc/threads.html"),
    # Rustc overview
    ("https://doc.rust-lang.org/rustc/overview.html", "https://rustc-dev-guide.rust-lang.org/overview.html"),
    ("https://doc.rust-lang.org/rustc-guide/tests/intro.html", "https://rustc-dev-guide.rust-lang.org/tests/intro.html"),
    # std
    ("https://doc.rust-lang.org/std/assert_matches/", "https://doc.rust-lang.org/std/macro.assert_matches.html"),
    ("https://doc.rust-lang.org/std/assert_matches/macro.assert_matches.html", "https://doc.rust-lang.org/std/macro.assert_matches.html"),
    ("https://doc.rust-lang.org/std/num/struct.NonZeroU32.html", "https://doc.rust-lang.org/std/num/NonZeroU32.html"),
    ("https://doc.rust-lang.org/std/sync/atomic/struct.AtomicPtr.html", "https://doc.rust-lang.org/std/sync/atomic/AtomicPtr.html"),
    ("https://doc.rust-lang.org/std/sync/atomic/struct.AtomicUsize.html", "https://doc.rust-lang.org/std/sync/atomic/AtomicUsize.html"),
    # rust-lang.org double slash
    ("https://www.rust-lang.org//users", "https://www.rust-lang.org/"),
    # Chinese Rust book mirror no longer on GH pages
    ("https://rust-lang.github.io/rust-lang-cn/", "https://github.com/rust-lang-cn"),
    # wasm-pack docs moved under /docs
    ("https://rustwasm.github.io/wasm-pack/commands/build.html", "https://rustwasm.github.io/docs/wasm-pack/commands/build.html"),
    ("https://rustwasm.github.io/wasm-pack/book/", "https://rustwasm.github.io/docs/wasm-pack/"),
    ("https://rustwasm.github.io/wasm-pack/", "https://rustwasm.github.io/docs/wasm-pack/"),
    # serde limitations page removed, use root
    ("https://serde.rs/limitations.html", "https://serde.rs/"),
    # tikv docs restructured
    ("https://tikv.org/docs/5.1/benchmark/performance/", "https://tikv.org/docs/dev/benchmark/performance/"),
    ("https://tikv.org/docs/5.1/concepts/architecture/", "https://tikv.org/docs/dev/concepts/architecture/"),
    # TLBORM counting moved to print.html anchor
    ("https://veykril.github.io/tlborm/patterns/counting.html", "https://veykril.github.io/tlborm/print.html#counting"),
]


def main():
    changed = 0
    for p in sorted(ROOT.rglob('*.md')):
        text = p.read_text(encoding='utf-8')
        new_text = text
        for old, new in REPLACEMENTS:
            new_text = new_text.replace(old, new)
        if new_text != text:
            p.write_text(new_text, encoding='utf-8')
            changed += 1
            print(f"fixed: {p.relative_to(ROOT).as_posix()}")
    print(f"\nupdated {changed} files")


if __name__ == '__main__':
    main()
