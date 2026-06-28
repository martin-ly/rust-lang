#!/usr/bin/env python3
"""修复 concept/ 中剩余批量可映射的失效链接."""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent / "concept"

REPLACEMENTS = [
    # rust-lang.github.io
    ("https://rust-lang.github.io/api-guidelines/errors.html", "https://rust-lang.github.io/api-guidelines/dependability.html"),
    ("https://rust-lang.github.io/api-guidelines/testing.html", "https://rust-lang.github.io/api-guidelines/debuggability.html"),
    ("https://rust-lang.github.io/async-book/04_pinning/01_chapter.html", "https://rust-lang.github.io/async-book/"),
    ("https://rust-lang.github.io/async-book/08_workarounds/03_cancel_safe.html", "https://rust-lang.github.io/async-book/"),
    ("https://rust-lang.github.io/async-book/09_workarounds/00_intro.html", "https://rust-lang.github.io/async-book/"),
    ("https://rust-lang.github.io/async-book/09_workarounds/03_cancel_safe.html", "https://rust-lang.github.io/async-book/"),
    ("https://rust-lang.github.io/async-book/09_workarounds/03_cancellation.html", "https://rust-lang.github.io/async-book/"),
    ("https://rust-lang.github.io/compiler-team/working-groups/specialization/", "https://rust-lang.github.io/compiler-team/working-groups/"),
    ("https://rust-lang.github.io/formal-methods/", "https://rust-lang.github.io/"),
    ("https://rust-lang.github.io/rust-project-goals/2026/flagships.html", "https://rust-lang.github.io/rust-project-goals/2026/"),
    ("https://rust-lang.github.io/rust-project-goals/2026h1/cranelift.html", "https://rust-lang.github.io/rust-project-goals/2026h1/"),
    ("https://rust-lang.github.io/rustc-dev-guide/grammar.html", "https://rustc-dev-guide.rust-lang.org/"),
    # rustc-dev-guide.rust-lang.org
    ("https://rustc-dev-guide.rust-lang.org/backend/", "https://rustc-dev-guide.rust-lang.org/backend/codegen.html"),
    ("https://rustc-dev-guide.rust-lang.org/backend/index.html", "https://rustc-dev-guide.rust-lang.org/backend/codegen.html"),
    ("https://rustc-dev-guide.rust-lang.org/borrow_check/polonius.html", "https://rustc-dev-guide.rust-lang.org/borrow-check.html"),
    ("https://rustc-dev-guide.rust-lang.org/building/bootstrapping.html", "https://rustc-dev-guide.rust-lang.org/building/how-to-build-and-run.html"),
    ("https://rustc-dev-guide.rust-lang.org/const-eval/interpretation.html", "https://rustc-dev-guide.rust-lang.org/const-eval/interpret.html"),
    ("https://rustc-dev-guide.rust-lang.org/hir-lowering.html", "https://rustc-dev-guide.rust-lang.org/hir/lowering.html"),
    ("https://rustc-dev-guide.rust-lang.org/hir-type-checking.html", "https://rustc-dev-guide.rust-lang.org/hir-typeck/summary.html"),
    ("https://rustc-dev-guide.rust-lang.org/incremental-compilation.html", "https://rustc-dev-guide.rust-lang.org/queries/incremental-compilation.html"),
    ("https://rustc-dev-guide.rust-lang.org/rustc-driver.html", "https://rustc-dev-guide.rust-lang.org/rustc-driver/intro.html"),
    ("https://rustc-dev-guide.rust-lang.org/solver/coinduction.html", "https://rustc-dev-guide.rust-lang.org/solve/coinduction.html"),
    ("https://rustc-dev-guide.rust-lang.org/solver/engine.html", "https://rustc-dev-guide.rust-lang.org/solve/the-solver.html"),
    ("https://rustc-dev-guide.rust-lang.org/tests/index.html", "https://rustc-dev-guide.rust-lang.org/tests/intro.html"),
    ("https://rustc-dev-guide.rust-lang.org/type-checking.html", "https://rustc-dev-guide.rust-lang.org/hir-typeck/summary.html"),
    # rust-unofficial patterns
    ("https://rust-unofficial.github.io/patterns/anti_patterns/gold-plating.html", "https://rust-unofficial.github.io/patterns/"),
    ("https://rust-unofficial.github.io/patterns/creational/builder.html", "https://rust-unofficial.github.io/patterns/print.html#builder"),
    ("https://rust-unofficial.github.io/patterns/idioms/type-state.html", "https://rust-unofficial.github.io/patterns/"),
    ("https://rust-unofficial.github.io/patterns/patterns/behavioural/type-erasure.html", "https://rust-unofficial.github.io/patterns/"),
    ("https://rust-unofficial.github.io/patterns/patterns/behavioural/typestate.html", "https://rust-unofficial.github.io/patterns/"),
    ("https://rust-unofficial.github.io/patterns/patterns/creational/factory.html", "https://rust-unofficial.github.io/patterns/"),
    ("https://rust-unofficial.github.io/patterns/patterns/functional/closure.html", "https://rust-unofficial.github.io/patterns/"),
    # bevy
    ("https://bevyengine.org/learn/book/getting-started/assets/", "https://bevyengine.org/learn/book/"),
    ("https://bevyengine.org/learn/book/getting-started/bevy-app/", "https://bevyengine.org/learn/book/"),
    ("https://bevyengine.org/learn/book/getting-started/hot-reloading/", "https://bevyengine.org/learn/book/"),
    ("https://bevyengine.org/learn/book/getting-started/performance/", "https://bevyengine.org/learn/book/"),
    ("https://bevyengine.org/learn/book/getting-started/", "https://bevyengine.org/learn/book/"),
    # docs.rs
    ("https://docs.rs/embedded-hal/latest/embedded_hal/blocking/i2c/index.html", "https://docs.rs/embedded-hal/latest/embedded_hal/"),
    ("https://docs.rs/embedded-hal/latest/embedded_hal/spi/trait.Write.html", "https://docs.rs/embedded-hal/latest/embedded_hal/"),
    ("https://docs.rs/rustls/latest/rustls/manual/_00_impl_details/index.html", "https://docs.rs/rustls/latest/rustls/manual/index.html"),
    ("https://docs.rs/tonic/latest/tonic/codec/trait.Streaming.html", "https://docs.rs/tonic/latest/tonic/codec/"),
    # rust-embedded
    ("https://docs.rust-embedded.org/book/interrupts/index.html", "https://docs.rust-embedded.org/book/"),
    ("https://docs.rust-embedded.org/faq.html", "https://docs.rust-embedded.org/book/"),
    # tikv
    ("https://tikv.org/docs/5.1/benchmark/performance/", "https://tikv.org/docs/"),
    ("https://tikv.org/docs/5.1/concepts/architecture/", "https://tikv.org/docs/"),
    ("https://tikv.org/docs/dev/benchmark/performance/", "https://tikv.org/docs/"),
    ("https://tikv.org/docs/dev/concepts/architecture/", "https://tikv.org/docs/"),
    # rust-for-linux
    ("https://rust-for-linux.com/challenges", "https://rust-for-linux.com/"),
    ("https://rust-for-linux.com/getting-started", "https://rust-for-linux.com/"),
    ("https://rust-for-linux.com/safety", "https://rust-for-linux.com/"),
    ("https://rust-for-linux.com/status", "https://rust-for-linux.com/"),
    # plv (keep root or specific paper list)
    ("https://plv.mpi-sws.org/rust-belt/stacked-borrows/", "https://plv.mpi-sws.org/rustbelt/"),
    ("https://plv.mpi-sws.org/rustbelt/18/07/types-as-propositions.html", "https://plv.mpi-sws.org/rustbelt/"),
    ("https://plv.mpi-sws.org/rustbelt/tree-borrows/", "https://plv.mpi-sws.org/rustbelt/"),
    ("https://plv.mpi-sws.org/verusbelt/", "https://verus-lang.github.io/verus/"),
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
    print(f'updated {changed} files')


if __name__ == '__main__':
    main()
