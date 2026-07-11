#!/usr/bin/env python3
"""修正部分概念文件中不准确的 EN 标题与 Summary，使其与文件主题对齐."""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent / "concept"

# rel_path -> (EN, Summary)
CORRECTIONS = {
    "00_meta/boundary_extension_tree.md": (
        "Boundary Extension Tree",
        "A reasoning tree for extending Rust's safety boundaries across unsafe, FFI, and formal-verification layers.",
    ),
    "00_meta/semantic_bridge_algorithms_patterns.md": (
        "Algorithms–Patterns Semantic Bridge",
        "A semantic bridge linking algorithmic thinking to design patterns in Rust.",
    ),
    "01_foundation/18_strings_and_encoding.md": (
        "Strings and Encoding",
        "Rust's string types (`String`, `str`, `OsString`, `CString`) and Unicode/encoding handling.",
    ),
    "01_foundation/20_variable_model.md": (
        "Variable Model",
        "Rust's variable bindings, mutability, shadowing, and move/copy semantics.",
    ),
    "01_foundation/21_effects_and_purity.md": (
        "Effects and Purity",
        "Tracking side effects and purity in Rust functions, const contexts, and unsafe boundaries.",
    ),
    "02_intermediate/05_assert_matches.md": (
        "assert_matches! Macro",
        "The `assert_matches!` macro for pattern-based assertions on enums and trait objects.",
    ),
    "02_intermediate/07_closure_types.md": (
        "Closure Types",
        "Rust closure types, capture modes, `Fn`/`FnMut`/`FnOnce` traits, and lifetime interactions.",
    ),
    "02_intermediate/14_newtype_and_wrapper.md": (
        "Newtype and Wrapper Types",
        "Using newtype and wrapper patterns for type safety, zero-cost abstraction, and trait orphan rules.",
    ),
    "02_intermediate/22_api_naming_conventions.md": (
        "API Naming Conventions",
        "Rust API naming conventions aligned with the Rust API Guidelines and std library style.",
    ),
    "03_advanced/03_unsafe.md": (
        "Unsafe Rust",
        "Authoritative guide to `unsafe` Rust: raw pointers, extern blocks, and the safety-invariant contract.",
    ),
    "03_advanced/07_proc_macro.md": (
        "Procedural Macros",
        "Authoritative guide to procedural macros: derive, attribute, and function-like macros.",
    ),
    "03_advanced/18_network_programming.md": (
        "Network Programming",
        "Network programming patterns in Rust using std, Tokio, and async I/O.",
    ),
    "04_formal/04_rustbelt.md": (
        "RustBelt",
        "RustBelt: a formal model of Rust's ownership and borrowing in Iris separation logic.",
    ),
    "04_formal/05_verification_toolchain.md": (
        "Verification Toolchain",
        "The Rust formal verification toolchain: Miri, Kani, Creusot, Verus, Prusti, and RustBelt.",
    ),
    "04_formal/11_separation_logic.md": (
        "Separation Logic",
        "Separation-logic foundations and their application to verifying Rust ownership and aliasing.",
    ),
    "05_comparative/02_rust_vs_go.md": (
        "Rust vs Go",
        "Comparative analysis of Rust and Go across memory safety, concurrency, runtime, and error handling.",
    ),
    "05_comparative/11_rust_vs_kotlin.md": (
        "Rust vs Kotlin",
        "Comparative analysis of Rust and Kotlin across null safety, concurrency, and target domains.",
    ),
    "05_comparative/12_rust_vs_scala.md": (
        "Rust vs Scala",
        "Comparative analysis of Rust and Scala across type systems, functional programming, and runtime.",
    ),
    "05_comparative/15_rust_vs_typescript.md": (
        "Rust vs TypeScript",
        "Comparative analysis of Rust and TypeScript across type systems, compile-time guarantees, and domains.",
    ),
    "06_ecosystem/06_blockchain.md": (
        "Blockchain Development in Rust",
        "Blockchain ecosystem patterns, cryptography primitives, and smart-contract tooling in Rust.",
    ),
    "06_ecosystem/14_documentation.md": (
        "Documentation",
        "Writing and publishing Rust documentation with rustdoc, doc tests, and crate docs.",
    ),
    "06_ecosystem/58_platform_rust_integration.md": (
        "Platform Rust Integration",
        "Integrating Rust into large platforms: Android, Chromium, Linux, and bare-metal firmware.",
    ),
    "07_future/07_mcdc_coverage_preview.md": (
        "MC/DC Coverage Preview",
        "Preview of modified condition/decision coverage (MC/DC) support in Rust's coverage tooling.",
    ),
    "07_future/08_safety_tags_preview.md": (
        "Safety Tags Preview",
        "Preview of safety tags for annotating and propagating unsafe preconditions in Rust.",
    ),
    "07_future/10_derive_coerce_pointee_preview.md": (
        "Derive CoercePointee Preview",
        "Preview of the `CoercePointee` derive for custom smart-pointer types.",
    ),
    "07_future/11_const_trait_impl_preview.md": (
        "Const Trait Impl Preview",
        "Preview of const trait implementations (`const Trait`) for compile-time generic code.",
    ),
    "07_future/13_unsafe_fields_preview.md": (
        "Unsafe Fields Preview",
        "Preview of unsafe fields: marking individual fields as requiring unsafe access.",
    ),
    "07_future/14_ferrocene_preview.md": (
        "Ferrocene Preview",
        "Preview of Ferrocene: the safety-critical Rust toolchain qualification initiative.",
    ),
    "07_future/14_lifetime_capture_preview.md": (
        "Lifetime Capture Preview",
        "Preview of precise lifetime capture rules for `impl Trait` return types.",
    ),
    "07_future/15_gen_blocks_preview.md": (
        "Gen Blocks Preview",
        "Preview of generator blocks (`gen {}`) for ergonomic lazy iterators.",
    ),
    "07_future/15_pin_ergonomics_preview.md": (
        "Pin Ergonomics Preview",
        "Preview of ergonomic improvements to working with `Pin` in Rust.",
    ),
    "07_future/17_arbitrary_self_types_preview.md": (
        "Arbitrary Self Types Preview",
        "Preview of arbitrary self types: extending method receivers beyond `&self`, `&mut self`, and `Box<Self>`.",
    ),
    "07_future/17_const_trait_preview.md": (
        "Const Trait Preview",
        "Preview of const traits for generic compile-time computation.",
    ),
    "07_future/17_rust_specification_preview.md": (
        "Rust Specification Preview",
        "Preview of the official Rust specification effort and its relation to the Reference.",
    ),
    "07_future/18_async_drop_preview.md": (
        "Async Drop Preview",
        "Preview of asynchronous destructors (`AsyncDrop`) for async resource cleanup.",
    ),
    "07_future/18_field_projections_preview.md": (
        "Field Projections Preview",
        "Preview of safe field projections and pinned field access for self-referential types.",
    ),
    "07_future/20_borrowsanitizer_preview.md": (
        "BorrowSanitizer Preview",
        "Preview of BorrowSanitizer: dynamic aliasing-rule validation at runtime.",
    ),
    "07_future/22_gen_blocks_preview.md": (
        "Gen Blocks Preview",
        "Preview of generator blocks as a language-level lazy iteration construct.",
    ),
    "07_future/24_cargo_semver_checks_preview.md": (
        "Cargo SemVer Checks Preview",
        "Preview of `cargo-semver-checks` integration for automated semantic-versioning linting.",
    ),
    "07_future/26_specialization_preview.md": (
        "Specialization Preview",
        "Preview of trait specialization: allowing overlapping impls with a default/fallback.",
    ),
    "archive/01.md": (
        "Archive Entry",
        "Archived concept entry placeholder.",
    ),
    "archive/SUMMARY_mdbook_legacy.md": (
        "mdBook Summary (Legacy)",
        "Legacy mdBook summary for the Rust concept knowledge system.",
    ),
    "README.md": (
        "Rust Concept Knowledge System",
        "Top-level index and navigation for the Rust layered concept knowledge system.",
    ),
    "SUMMARY.md": (
        "Summary",
        "mdBook-style summary for the concept collection.",
    ),
    "sources/INDEX.md": (
        "Authority Source Index",
        "Index of authoritative sources used throughout the concept knowledge system.",
    ),
}


def main():
    for rel, (en, summary) in CORRECTIONS.items():
        path = ROOT / rel
        if not path.exists():
            print(f"skip (missing): {rel}")
            continue
        text = path.read_text(encoding="utf-8")
        new_text, n1 = re.subn(
            r'^>(\s*)\*\*EN\*\*:\s*.*?$',
            rf'>\1**EN**: {en}',
            text,
            count=1,
            flags=re.MULTILINE,
        )
        new_text, n2 = re.subn(
            r'^>(\s*)\*\*Summary\*\*:\s*.*?$',
            rf'>\1**Summary**: {summary}',
            new_text,
            count=1,
            flags=re.MULTILINE,
        )
        if n1 or n2:
            path.write_text(new_text, encoding="utf-8")
            print(f"updated: {rel}")
        else:
            print(f"no EN/Summary found: {rel}")


if __name__ == "__main__":
    main()
