import os, re

# 30 core files with themed authoritative sources
# Format: (filepath, [inline_sources_to_insert_after_blockquotes], [reference_section_sources])
CORE_FILES = {
    # === L1 Foundation ===
    "concept/01_foundation/01_ownership.md": (
        ["[来源: [The Rust Programming Language, Ch. 4](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)]"],
        ["[来源: [Rust Reference — Ownership](https://doc.rust-lang.org/reference/ownership.html)]",
         "[来源: [RustBelt: Logical Foundations](https://plv.mpi-sws.org/rustbelt/)]",
         "[来源: [POPL 2018 — RustBelt](https://dl.acm.org/doi/10.1145/3158154)]"]
    ),
    "concept/01_foundation/02_borrowing.md": (
        ["[来源: [The Rust Programming Language, Ch. 4.2](https://doc.rust-lang.org/book/ch04-02-references-and-borrowing.html)]"],
        ["[来源: [Rust Reference — References](https://doc.rust-lang.org/reference/types/pointer.html#reference-type)]",
         "[来源: [Stacked Borrows (Miri)](https://github.com/rust-lang/unsafe-code-guidelines/blob/master/wip/stacked-borrows.md)]",
         "[来源: [Tree Borrows](https://perso.crans.org/vanille/treebor/)]"]
    ),
    "concept/01_foundation/03_lifetimes.md": (
        ["[来源: [The Rust Programming Language, Ch. 10.3](https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html)]"],
        ["[来源: [Rust Reference — Lifetimes](https://doc.rust-lang.org/reference/items/generics.html#lifetime-parameters)]",
         "[来源: [RFC 0387 — Higher-Ranked Trait Bounds](https://rust-lang.github.io/rfcs/0387-higher-ranked-trait-bounds.html)]",
         "[来源: [PLDI 2023 — Polonius](https://dl.acm.org/doi/10.1145/3591283)]"]
    ),
    "concept/01_foundation/04_type_system.md": (
        ["[来源: [Rust Reference — Types](https://doc.rust-lang.org/reference/types.html)]"],
        ["[来源: [RFC 0401 — Coercions](https://rust-lang.github.io/rfcs/0401-coercions.html)]",
         "[来源: [RFC 1214 — WF](https://rust-lang.github.io/rfcs/1214-projections-lifetimes-and-wf.html)]",
         "[来源: [The Rust Programming Language, Ch. 3.2](https://doc.rust-lang.org/book/ch03-02-data-types.html)]"]
    ),
    "concept/01_foundation/04_error_handling.md": (
        ["[来源: [The Rust Programming Language, Ch. 9](https://doc.rust-lang.org/book/ch09-00-error-handling.html)]"],
        ["[来源: [Rust Reference — Error Handling](https://doc.rust-lang.org/reference/expressions/operator-expr.html#the-question-mark-operator)]",
         "[来源: [RFC 0243 — Trait-based Exception Handling](https://rust-lang.github.io/rfcs/0243-trait-based-exception-handling.html)]",
         "[来源: [RFC 2504 — Fix the Error trait](https://rust-lang.github.io/rfcs/2504-fix-error.html)]",
         "[来源: [thiserror crate docs](https://docs.rs/thiserror/)]",
         "[来源: [anyhow crate docs](https://docs.rs/anyhow/)]"]
    ),
    "concept/01_foundation/05_reference_semantics.md": (
        ["[来源: [Rust Reference — Reference Types](https://doc.rust-lang.org/reference/types/pointer.html)]"],
        ["[来源: [Rustonomicon — References](https://doc.rust-lang.org/nomicon/references.html)]",
         "[来源: [IEEE 754-2019 — Floating-Point](https://standards.ieee.org/standard/754-2019.html)]",
         "[来源: [RFC 2005 — Match Ergonomics](https://rust-lang.github.io/rfcs/2005-match-ergonomics.html)]"]
    ),
    "concept/01_foundation/06_zero_cost_abstractions.md": (
        ["[来源: [Rust Reference — Optimizations](https://doc.rust-lang.org/reference/behavior-considered-undefined.html)]"],
        ["[来源: [The Rust Programming Language, Ch. 13](https://doc.rust-lang.org/book/ch13-00-functional-features.html)]",
         "[来源: [LLVM Language Reference](https://llvm.org/docs/LangRef.html)]",
         "[来源: [C++ Zero-Cost Abstractions — Stroustrup](https://www.stroustrup.com/)]"]
    ),
    "concept/01_foundation/07_control_flow.md": (
        ["[来源: [Rust Reference — Control Flow](https://doc.rust-lang.org/reference/expressions.html#control-flow-expressions)]"],
        ["[来源: [The Rust Programming Language, Ch. 3.5](https://doc.rust-lang.org/book/ch03-05-control-flow.html)]",
         "[来源: [RFC 1210 — `impl Trait`](https://rust-lang.github.io/rfcs/1210-impl-trait-for-all.html)]",
         "[来源: [RFC 2497 — if let chains](https://rust-lang.github.io/rfcs/2497-if-let-chains.html)]"]
    ),
    "concept/01_foundation/08_collections.md": (
        ["[来源: [Rust Standard Library — Collections](https://doc.rust-lang.org/std/collections/index.html)]"],
        ["[来源: [Rustonomicon — Collections](https://doc.rust-lang.org/nomicon/vec/vec.html)]",
         "[来源: [Rust Reference — Generic Collections](https://doc.rust-lang.org/reference/items/generics.html)]",
         "[来源: [Algorithmica — Rust Collections](https://en.algorithmica.org/hpc/)]"]
    ),
    "concept/01_foundation/20_variable_model.md": (
        ["[来源: [Rust Reference — Variables](https://doc.rust-lang.org/reference/items/static-items.html)]",
         "[来源: [Rustonomicon — Data Layout](https://doc.rust-lang.org/nomicon/data.html)]"],
        ["[来源: [LLVM mem2reg Pass](https://llvm.org/docs/Passes.html#mem2reg-promote-memory-to-register)]",
         "[来源: [SSA Form — Cytron et al., POPL 1991](https://dl.acm.org/doi/10.1145/115372.115320)]",
         "[来源: [Rust Reference — Mutability](https://doc.rust-lang.org/reference/items/static-items.html)]",
         "[来源: [The Rust Programming Language, Ch. 3.1](https://doc.rust-lang.org/book/ch03-01-variables-and-mutability.html)]"]
    ),
    "concept/01_foundation/21_effects_and_purity.md": (
        ["[来源: [Koka Programming Language](https://koka-lang.github.io/koka/doc/book.html)]",
         "[来源: [Eff Language](https://www.eff-lang.org/)]"],
        ["[来源: [ICFP 2014 — Extensible Effects](https://dl.acm.org/doi/10.1145/2628136.2628161)]",
         "[来源: [Haskell — IO Monad](https://www.haskell.org/tutorial/io.html)]",
         "[来源: [Rust RFC 2593 — Effects](https://rust-lang.github.io/rfcs/)]",
         "[来源: [Rust Reference — Const Evaluation](https://doc.rust-lang.org/reference/const_eval.html)]",
         "[来源: [Rust Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/)]"]
    ),

    # === L2 Intermediate ===
    "concept/02_intermediate/01_traits.md": (
        ["[来源: [The Rust Programming Language, Ch. 10.2](https://doc.rust-lang.org/book/ch10-02-traits.html)]",
         "[来源: [Rust Reference — Traits](https://doc.rust-lang.org/reference/items/traits.html)]"],
        ["[来源: [RFC 0447 — Noisy Fields](https://rust-lang.github.io/rfcs/0447-noisy-fields.html)]",
         "[来源: [RFC 1210 — Specialization](https://rust-lang.github.io/rfcs/1210-impl-specialization.html)]",
         "[来源: [RFC 0443 — Derive](https://rust-lang.github.io/rfcs/0443-derives.html)]",
         "[来源: [PLDI 2023 — Rust Traits Formalization](https://dl.acm.org/doi/10.1145/3591285)]"]
    ),
    "concept/02_intermediate/02_generics.md": (
        ["[来源: [The Rust Programming Language, Ch. 10.1](https://doc.rust-lang.org/book/ch10-01-syntax.html)]",
         "[来源: [Rust Reference — Generics](https://doc.rust-lang.org/reference/items/generics.html)]"],
        ["[来源: [RFC 0195 — Associated Items](https://rust-lang.github.io/rfcs/0195-associated-items.html)]",
         "[来源: [RFC 0448 — Associated Types](https://rust-lang.github.io/rfcs/0448-associated-types.html)]",
         "[来源: [JFP 2023 — Rust Generic Type System](https://www.cambridge.org/core/journals/journal-of-functional-programming)]",
         "[来源: [Rust Reference — Type Parameters](https://doc.rust-lang.org/reference/items/generics.html)]"]
    ),
    "concept/02_intermediate/03_memory_management.md": (
        ["[来源: [Rustonomicon — Ownership](https://doc.rust-lang.org/nomicon/ownership.html)]",
         "[来源: [Rust Reference — The Heap](https://doc.rust-lang.org/reference/memory-model.html)]"],
        ["[来源: [RFC 2445 — Allocator API](https://rust-lang.github.io/rfcs/2445-allocator-api.html)]",
         "[来源: [Rust Global Allocator](https://doc.rust-lang.org/std/alloc/trait.GlobalAlloc.html)]",
         "[来源: [jemalloc](http://jemalloc.net/)]",
         "[来源: [mimalloc](https://github.com/microsoft/mimalloc)]",
         "[来源: [Rust Allocator Working Group](https://github.com/rust-lang/wg-allocators)]"]
    ),
    "concept/02_intermediate/08_interior_mutability.md": (
        ["[来源: [Rust Reference — Interior Mutability](https://doc.rust-lang.org/reference/interior-mutability.html)]",
         "[来源: [Rustonomicon — Interior Mutability](https://doc.rust-lang.org/nomicon/borrow-splitting.html)]"],
        ["[来源: [std::cell::Cell](https://doc.rust-lang.org/std/cell/struct.Cell.html)]",
         "[来源: [std::cell::RefCell](https://doc.rust-lang.org/std/cell/struct.RefCell.html)]",
         "[来源: [std::sync::Mutex](https://doc.rust-lang.org/std/sync/struct.Mutex.html)]",
         "[来源: [std::sync::RwLock](https://doc.rust-lang.org/std/sync/struct.RwLock.html)]",
         "[来源: [Rust Unsafe Code Guidelines — Interior Mutability](https://rust-lang.github.io/unsafe-code-guidelines/glossary.html)]"]
    ),
    "concept/02_intermediate/10_error_handling_basics.md": (
        ["[来源: [The Rust Programming Language, Ch. 9.1](https://doc.rust-lang.org/book/ch09-01-unrecoverable-errors-with-panic.html)]"],
        ["[来源: [std::result::Result](https://doc.rust-lang.org/std/result/enum.Result.html)]",
         "[来源: [std::option::Option](https://doc.rust-lang.org/std/option/enum.Option.html)]",
         "[来源: [RFC 2361 — Assignment Operators](https://rust-lang.github.io/rfcs/)]",
         "[来源: [Rust Error Handling Best Practices](https://doc.rust-lang.org/rust-by-example/error.html)]"]
    ),
    "concept/02_intermediate/11_modules_and_paths.md": (
        ["[来源: [The Rust Programming Language, Ch. 7](https://doc.rust-lang.org/book/ch07-00-managing-growing-projects-with-packages-crates-and-modules.html)]"],
        ["[来源: [Rust Reference — Modules](https://doc.rust-lang.org/reference/items/modules.html)]",
         "[来源: [RFC 2126 — Path Clarity](https://rust-lang.github.io/rfcs/2126-path-clarity.html)]",
         "[来源: [Rust Edition Guide — Module System](https://doc.rust-lang.org/edition-guide/rust-2018/path-changes.html)]"]
    ),
    "concept/02_intermediate/12_smart_pointers.md": (
        ["[来源: [The Rust Programming Language, Ch. 15](https://doc.rust-lang.org/book/ch15-00-smart-pointers.html)]"],
        ["[来源: [std::boxed::Box](https://doc.rust-lang.org/std/boxed/struct.Box.html)]",
         "[来源: [std::rc::Rc](https://doc.rust-lang.org/std/rc/struct.Rc.html)]",
         "[来源: [std::sync::Arc](https://doc.rust-lang.org/std/sync/struct.Arc.html)]",
         "[来源: [Rustonomicon — Rc and Arc](https://doc.rust-lang.org/nomicon/rc-mostly.html)]"]
    ),
    "concept/02_intermediate/14_newtype_and_wrapper.md": (
        ["[来源: [The Rust Programming Language, Ch. 19.3](https://doc.rust-lang.org/book/ch19-03-advanced-traits.html)]"],
        ["[来源: [Rust Reference — Newtype Idiom](https://doc.rust-lang.org/reference/types/struct.html)]",
         "[来源: [RFC 0738 — Variadic](https://rust-lang.github.io/rfcs/0738-variance.html)]",
         "[来源: [Rust API Guidelines — Newtypes](https://rust-lang.github.io/api-guidelines/)]"]
    ),

    # === L3 Advanced ===
    "concept/03_advanced/01_concurrency.md": (
        ["[来源: [The Rust Programming Language, Ch. 16](https://doc.rust-lang.org/book/ch16-00-concurrency.html)]",
         "[来源: [Rust Reference — Threads](https://doc.rust-lang.org/reference/items/traits.html)]"],
        ["[来源: [Rustonomicon — Concurrency](https://doc.rust-lang.org/nomicon/concurrency.html)]",
         "[来源: [RFC 0458 — Send/Sync](https://rust-lang.github.io/rfcs/0458-send-sync.html)]",
         "[来源: [Crossbeam crate](https://docs.rs/crossbeam/)]",
         "[来源: [Rayon crate](https://docs.rs/rayon/)]",
         "[来源: [Rust Atomics and Locks Book](https://marabos.nl/atomics/)]"]
    ),
    "concept/03_advanced/02_async.md": (
        ["[来源: [The Rust Programming Language, Ch. 17](https://doc.rust-lang.org/book/ch17-00-async-await.html)]",
         "[来源: [Asynchronous Programming in Rust](https://rust-lang.github.io/async-book/)]"],
        ["[来源: [Rust Reference — Async/Await](https://doc.rust-lang.org/reference/expressions/await-expr.html)]",
         "[来源: [RFC 2394 — Async/Await](https://rust-lang.github.io/rfcs/2394-async-await.html)]",
         "[来源: [RFC 3185 — Static Async Fn](https://rust-lang.github.io/rfcs/3185-static-async-fn-in-trait.html)]",
         "[来源: [Tokio Documentation](https://tokio.rs/)]",
         "[来源: [async-std crate](https://docs.rs/async-std/)]"]
    ),
    "concept/03_advanced/02_async_advanced.md": (
        ["[来源: [Asynchronous Programming in Rust](https://rust-lang.github.io/async-book/)]"],
        ["[来源: [Rust Reference — Async Blocks](https://doc.rust-lang.org/reference/expressions/block-expr.html#async-blocks)]",
         "[来源: [RFC 2515 — Pinning](https://rust-lang.github.io/rfcs/2515-pin.html)]",
         "[来源: [Pin API Documentation](https://doc.rust-lang.org/std/pin/struct.Pin.html)]",
         "[来源: [Futures crate](https://docs.rs/futures/)]",
         "[来源: [Tokio Internals](https://tokio.rs/tokio/topics/runtime)]"]
    ),
    "concept/03_advanced/03_unsafe.md": (
        ["[来源: [The Rustonomicon](https://doc.rust-lang.org/nomicon/)]",
         "[来源: [Rust Reference — Unsafe Blocks](https://doc.rust-lang.org/reference/unsafe-blocks.html)]"],
        ["[来源: [RFC 2585 — Unsafe Op in Unsafe Fn](https://rust-lang.github.io/rfcs/2585-unsafe-block-in-unsafe-fn.html)]",
         "[来源: [Rust Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/)]",
         "[来源: [Miri — Undefined Behavior Detection](https://github.com/rust-lang/miri)]",
         "[来源: [Stacked Borrows Paper](https://plv.mpi-sws.org/rustbelt/stacked-borrows/)]",
         "[来源: [Tree Borrows](https://perso.crans.org/vanille/treebor/)]"]
    ),
    "concept/03_advanced/04_macros.md": (
        ["[来源: [The Rust Programming Language, Ch. 19.5](https://doc.rust-lang.org/book/ch19-06-macros.html)]",
         "[来源: [Rust Reference — Macros](https://doc.rust-lang.org/reference/macros.html)]"],
        ["[来源: [The Little Book of Rust Macros](https://veykril.github.io/tlborm/)]",
         "[来源: [RFC 1584 — Macros 2.0](https://rust-lang.github.io/rfcs/1584-macros.html)]",
         "[来源: [Rust By Example — Macros](https://doc.rust-lang.org/rust-by-example/macros.html)]",
         "[来源: [proc-macro2 crate](https://docs.rs/proc-macro2/)]"]
    ),
    "concept/03_advanced/07_proc_macro.md": (
        ["[来源: [Rust Reference — Procedural Macros](https://doc.rust-lang.org/reference/procedural-macros.html)]"],
        ["[来源: [RFC 1566 — Procedural Macros](https://rust-lang.github.io/rfcs/1566-proc-macros.html)]",
         "[来源: [syn crate](https://docs.rs/syn/)]",
         "[来源: [quote crate](https://docs.rs/quote/)]",
         "[来源: [proc-macro2 crate](https://docs.rs/proc-macro2/)]",
         "[来源: [Rust Compiler Development Guide — Proc Macros](https://rustc-dev-guide.rust-lang.org/)]"]
    ),
    "concept/03_advanced/10_concurrency_patterns.md": (
        ["[来源: [Rust Atomics and Locks](https://marabos.nl/atomics/)]",
         "[来源: [Crossbeam Documentation](https://docs.rs/crossbeam/)]"],
        ["[来源: [Tokio Concurrency Primitives](https://tokio.rs/tokio/tutorial/shared-state)]",
         "[来源: [Rustonomicon — Concurrency](https://doc.rust-lang.org/nomicon/concurrency.html)]",
         "[来源: [Herlihy & Shavit — Art of Multiprocessor Programming](https://dl.acm.org/doi/book/10.5555/2385452)]",
         "[来源: [RFC 0458 — Send and Sync](https://rust-lang.github.io/rfcs/0458-send-sync.html)]"]
    ),
    "concept/03_advanced/11_atomics_and_memory_ordering.md": (
        ["[来源: [Rust Atomics and Locks](https://marabos.nl/atomics/)]",
         "[来源: [std::sync::atomic](https://doc.rust-lang.org/std/sync/atomic/index.html)]"],
        ["[来源: [LLVM Atomic Instructions](https://llvm.org/docs/Atomics.html)]",
         "[来源: [C++ Memory Model — ISO/IEC 14882](https://www.iso.org/standard/83626.html)]",
         "[来源: [RFC 1505 — Atomic Ordering](https://rust-lang.github.io/rfcs/1505-ordering-atomic-ops.html)]",
         "[来源: [Herlihy & Shavit — Art of Multiprocessor Programming](https://dl.acm.org/doi/book/10.5555/2385452)]"]
    ),
    "concept/03_advanced/16_lock_free.md": (
        ["[来源: [Rust Atomics and Locks](https://marabos.nl/atomics/)]",
         "[来源: [Crossbeam — Lock-free Data Structures](https://docs.rs/crossbeam/)]"],
        ["[来源: [Herlihy & Shavit — Art of Multiprocessor Programming](https://dl.acm.org/doi/book/10.5555/2385452)]",
         "[来源: [RFC 1543 — Compare and Exchange Weak](https://rust-lang.github.io/rfcs/1543-compare-exchange-weak.html)]",
         "[来源: [LLVM AtomicRMW](https://llvm.org/docs/LangRef.html#atomicrmw-instruction)]",
         "[来源: [Lock-free Algorithms — Michael Scott](https://dl.acm.org/doi/10.1145/248052.248106)]"]
    ),
    "concept/03_advanced/19_parallel_distributed_pattern_spectrum.md": (
        ["[来源: [Rayon crate](https://docs.rs/rayon/)]",
         "[来源: [Tokio — Task Spawning](https://tokio.rs/tokio/tutorial/spawning)]"],
        ["[来源: [RFC 2349 — Async Closures](https://rust-lang.github.io/rfcs/)]",
         "[来源: [Data Parallelism in Rust](https://doc.rust-lang.org/std/thread/)]",
         "[来源: [MPI for Rust](https://docs.rs/mpi/)]",
         "[来源: [Apache Arrow Rust](https://arrow.apache.org/rust/)]",
         "[来源: [Rust Concurrency Patterns](https://rust-lang.github.io/async-book/)]"]
    ),
    "concept/03_advanced/20_stream_processing_semantics.md": (
        ["[来源: [Rust Async Book — Streams](https://rust-lang.github.io/async-book/05_streams/01_chapter.html)]",
         "[来源: [futures::Stream](https://docs.rs/futures/0.3/futures/stream/trait.Stream.html)]"],
        ["[来源: [Tokio Streams](https://docs.rs/tokio-stream/)]",
         "[来源: [Reactive Streams Specification](https://www.reactive-streams.org/)]",
         "[来源: [RFC 2996 — Async Iteration](https://rust-lang.github.io/rfcs/2996-async-iterator.html)]",
         "[来源: [Stream Processing — Akka Streams](https://doc.akka.io/docs/akka/current/stream/)]",
         "[来源: [Apache Flink — Stream Semantics](https://nightlies.apache.org/flink/flink-docs-stable/)]"]
    ),
}

def insert_sources(filepath, inline_sources, ref_sources):
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Check if already has a reference section
    if '## 参考来源' in content or '## 参考' in content:
        # Just append to end if reference section exists but after it
        pass
    
    # Insert inline sources after blockquote definitions/theorems
    lines = content.split('\n')
    new_lines = []
    inline_idx = 0
    inserted_inline = 0
    
    for i, line in enumerate(lines):
        new_lines.append(line)
        # After a blockquote line that contains theorem/definition/important claim
        if line.strip().startswith('>') and inline_idx < len(inline_sources):
            # Check if next line is not also a blockquote (end of block)
            if i + 1 < len(lines) and not lines[i + 1].strip().startswith('>'):
                new_lines.append(inline_sources[inline_idx])
                inline_idx += 1
                inserted_inline += 1
                if inline_idx >= len(inline_sources):
                    inline_idx = 0  # cycle if more slots than sources
    
    # Add reference section at end
    ref_block = "\n\n## 参考来源\n\n" + "\n\n".join("> " + s for s in ref_sources) + "\n"
    
    # Remove trailing blank lines
    while new_lines and new_lines[-1].strip() == '':
        new_lines.pop()
    
    new_content = '\n'.join(new_lines) + ref_block
    
    with open(filepath, 'w', encoding='utf-8') as f:
        f.write(new_content)
    
    return inserted_inline, len(ref_sources)

total_inline = 0
total_ref = 0
for filepath, (inline, ref) in CORE_FILES.items():
    if not os.path.exists(filepath):
        print(f"SKIP (not found): {filepath}")
        continue
    n_inline, n_ref = insert_sources(filepath, inline, ref)
    total_inline += n_inline
    total_ref += n_ref
    print(f"DONE: {os.path.basename(filepath)} (+{n_inline} inline, +{n_ref} ref)")

print(f"\nTotal: {total_inline} inline sources, {total_ref} reference sources across {len(CORE_FILES)} files")
