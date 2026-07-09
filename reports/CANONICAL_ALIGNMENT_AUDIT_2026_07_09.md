# Canonical Alignment Audit Report

**Date**: 2026-07-09
**Scope**: `knowledge/**/*.md` and `docs/**/*.md` against `concept/` canonical pages
**Auditor**: automated metadata comparison + manual review
**Constraints**: no files modified; no `cargo build/test` executed.

---

## 1. Methodology

1. **Extracted metadata** from 509 `concept/` files, 139 `knowledge/` files, and 524 `docs/` files:
   - first H1 title,
   - `**EN**` and `**Summary**` fields,
   - H1–H3 headings,
   - presence and target of canonical/权威来源 links,
   - line count.
2. **Normalized topics** from EN fields, titles, headings, and path tokens (stop-word removal, lower-casing, ASCII folding).
3. **Scored matches** between each `knowledge/` or `docs/` file and every `concept/` file using weighted token overlap (EN > title > headings > path topics).
4. **Classified** candidates by size and structure:
   - `likely_summary_redirect` – has a `concept/` link and is short (<80 lines, ≤4 H2s);
   - `summary_redirect_but_substantial` – has a `concept/` link but still carries significant explanatory content;
   - `substantial_content` – no `concept/` link, long, and multi-section; likely a full concept tutorial.
5. **Manually reviewed** the highest-scoring and largest files to confirm whether they duplicate a `concept/` topic or represent a legitimately domain-specific guide.

---

## 2. `knowledge/` Files with Full Concept Explanations

Per `AGENTS.md`, `knowledge/` should contain only **summaries, redirect stubs, or learning-entry cards**. The files below read as full tutorials or deep dives.

### 2.1 Already link to `concept/` but still carry substantial content

These files mention a `concept/` authority source yet retain large explanatory bodies. They should be trimmed to a true redirect stub or a concise summary card.

| File | Closest `concept/` page | Lines | Recommendation |
|---|---|---:|---|
| `knowledge/03_advanced/unsafe/04_unsafe_rust.md` | `concept/03_advanced/02_unsafe/03_unsafe.md` | ~190 | `convert_to_redirect` |
| `knowledge/03_advanced/unsafe/README.md` | `concept/03_advanced/02_unsafe/35_unsafe_reference.md` | ~120 | `convert_to_summary` |
| `knowledge/03_advanced/03_inline_asm.md` | `concept/03_advanced/05_inline_assembly/13_inline_assembly.md` | ~250 | `convert_to_redirect` |
| `knowledge/99_archive/02_version_tracking.md` | `concept/07_future/00_version_tracking/05_rust_version_tracking.md` | ~260 | `convert_to_summary` |

### 2.2 No `concept/` canonical link and contain full tutorials

These files are the most serious canonical violations: they teach core Rust concepts in `knowledge/` instead of pointing to the authoritative `concept/` page. They should either be **migrated** into `concept/` (if the topic is missing there) or replaced with a **redirect stub**.

| File | Closest `concept/` page | Lines | Recommendation |
|---|---|---:|---|
| `knowledge/01_fundamentals/02_iterators.md` | `concept/02_intermediate/07_iterators_and_closures/15_iterator_patterns.md` | 444 | `migrate_to_concept` / `convert_to_redirect` |
| `knowledge/03_advanced/04_lazy_initialization.md` | `concept/02_intermediate/00_traits/28_construction_and_initialization.md` | 961 | `migrate_to_concept` |
| `knowledge/03_advanced/06_type_driven_correctness.md` | `concept/04_formal/00_type_theory/50_type_system_reference.md` | 1,248 | `migrate_to_concept` |
| `knowledge/04_expert/02_unsafe_audit.md` | `concept/03_advanced/02_unsafe/35_unsafe_reference.md` | 1,433 | `migrate_to_concept` |
| `knowledge/04_expert/academic/01_coq_formalization_guide.md` | `concept/04_formal/04_model_checking/13_formal_methods.md` | 661 | `migrate_to_concept` |
| `knowledge/02_intermediate/control_flow/01_if_let_guards.md` | `concept/07_future/00_version_tracking/rust_1_95_stabilized.md` | 442 | `convert_to_redirect` |
| `knowledge/02_intermediate/control_flow/02_let_chains.md` | `concept/07_future/01_edition_roadmap/44_edition_guide.md` | 405 | `convert_to_redirect` |
| `knowledge/02_intermediate/macros/01_cfg_select.md` | `concept/07_future/00_version_tracking/rust_1_95_stabilized.md` | 320 | `convert_to_redirect` |
| `knowledge/02_intermediate/type_system/01_core_range.md` | `concept/07_future/00_version_tracking/rust_1_96_stabilized.md` | 297 | `convert_to_redirect` |
| `knowledge/03_advanced/unsafe/03_maybe_uninit.md` | `concept/03_advanced/02_unsafe/35_unsafe_reference.md` | 472 | `migrate_to_concept` / `convert_to_redirect` |
| `knowledge/00_start/01_hello_world.md` | `concept/01_foundation/00_start/` | 330 | `convert_to_redirect` |
| `knowledge/00_start/02_installation.md` | `concept/06_ecosystem/01_cargo/` | 302 | `convert_to_redirect` |
| `knowledge/00_start/03_learning_roadmap.md` | `concept/00_meta/04_navigation/learning_mvp_path.md` | 405 | `convert_to_summary` |
| `knowledge/00_start/04_rust_philosophy.md` | `concept/01_foundation/00_start/` | 317 | `migrate_to_concept` |

### 2.3 Domain-specific reports currently in `knowledge/`

The `knowledge/04_expert/safety_critical/` tree (~50 files, many 400–900 lines) is a safety-critical systems report suite. It does not belong in `knowledge/` under the current rules; it should live in `docs/` or `content/`.

| File | Closest `concept/` page | Lines | Recommendation |
|---|---|---:|---|
| `knowledge/04_expert/safety_critical/09_reference/10_performance_optimization_guide.md` | `concept/06_ecosystem/10_performance/15_performance_optimization.md` | 534 | `convert_to_summary` + relocate to `docs/` |
| `knowledge/04_expert/safety_critical/04_axiomatic_reasoning/01_formal_verification_practical_guide.md` | `concept/06_ecosystem/08_formal_verification/74_formal_verification_tools.md` | 822 | `convert_to_summary` + relocate to `docs/` |
| `knowledge/04_expert/safety_critical/09_reference/07_ffi_integration_guide.md` | `concept/03_advanced/04_ffi/09_ffi_advanced.md` | 667 | `convert_to_summary` + relocate to `docs/` |
| `knowledge/04_expert/safety_critical/09_reference/01_api_design_guidelines.md` | `concept/06_ecosystem/03_design_patterns/42_api_design_patterns.md` | 702 | `convert_to_summary` + relocate to `docs/` |
| `knowledge/04_expert/safety_critical/10_standards/01_do_178c_rust_compliance_pathway.md` | `concept/06_ecosystem/11_domain_applications/20_licensing_and_compliance.md` | 727 | `keep` (domain report) but move to `docs/` |

Likewise, the `knowledge/06_ecosystem/` deep dives (Axum, Sea-ORM, SQLx, Tokio, Kubernetes) are ecosystem guides and should be moved to `docs/06_ecosystem/` or `content/` rather than remaining in `knowledge/`.

---

## 3. `docs/` Files with Sections Duplicating `concept/`

`docs/` may keep guides, reports, and cheatsheets, but concept-level explanations should either live in `concept/` or explicitly defer to it. The files below teach core concepts at length without a top-level `concept/` canonical link.

### 3.1 Substantial guides matching `concept/` topics (no `concept/` link)

| File | Closest `concept/` page | Lines | Recommendation |
|---|---|---:|---|
| `docs/05_guides/05_inline_assembly_guide.md` | `concept/03_advanced/05_inline_assembly/13_inline_assembly.md` | 845 | `migrate_to_concept` / add prominent `concept/` link |
| `docs/05_guides/05_async_programming_usage_guide.md` | `concept/03_advanced/01_async/02_async.md` | 1,936 | add `concept/` canonical link; keep as usage guide |
| `docs/05_guides/05_threads_concurrency_usage_guide.md` | `concept/03_advanced/00_concurrency/10_concurrency_patterns.md` | 1,663 | add `concept/` canonical link; keep as usage guide |
| `docs/05_guides/best_practices.md` | `concept/06_ecosystem/03_design_patterns/37_pattern_selection_best_practices.md` | 2,215 | add `concept/` canonical link; trim duplicated pattern theory |
| `docs/05_guides/05_design_patterns_usage_guide.md` | `concept/06_ecosystem/03_design_patterns/02_patterns.md` | 2,520 | add `concept/` canonical link; keep domain examples |
| `docs/05_guides/05_type_system_usage_guide.md` | `concept/01_foundation/02_type_system/04_type_system.md` | 314 | add `concept/` canonical link |
| `docs/05_guides/05_control_flow_functions_usage_guide.md` | `concept/01_foundation/04_control_flow/07_control_flow.md` | 337 | add `concept/` canonical link |
| `docs/05_guides/05_performance_tuning_guide.md` | `concept/06_ecosystem/10_performance/15_performance_optimization.md` | 1,073 | add `concept/` canonical link |
| `docs/06_toolchain/06_cargo_script_guide.md` | `concept/06_ecosystem/01_cargo/09_cargo_script.md` | 372 | add `concept/` canonical link |
| `docs/01_cargo_build_optimization.md` | `concept/06_ecosystem/01_cargo/87_build_std.md` | 339 | add `concept/` canonical link |
| `docs/01_core/01_ownership_borrowing_lifetimes.md` | `concept/01_foundation/01_ownership_borrow_lifetime/` | 409 | add `concept/` canonical link at top; trim redundant explanations |
| `docs/research_notes/formal_methods/10_async_state_machine.md` | `concept/03_advanced/01_async/02_async.md` | 1,792 | add `concept/` canonical link |
| `docs/research_notes/formal_methods/10_error_handling_decision_tree.md` | `concept/02_intermediate/03_error_handling/04_error_handling.md` | 3,888 | add `concept/` canonical link; migrate reusable decision logic |
| `docs/research_notes/formal_methods/10_ownership_model.md` | `concept/04_formal/01_ownership_logic/03_ownership_formal.md` | 3,618 | add `concept/` canonical link |
| `docs/research_notes/formal_methods/10_borrow_checker_proof.md` | `concept/04_formal/01_ownership_logic/28_borrow_checking_decidability.md` | 2,386 | add `concept/` canonical link |
| `docs/research_notes/10_tutorial_type_system.md` | `concept/01_foundation/02_type_system/04_type_system.md` | 1,151 | add `concept/` canonical link |
| `docs/research_notes/10_tutorial_ownership_safety.md` | `concept/04_formal/01_ownership_logic/03_ownership_formal.md` | 1,293 | add `concept/` canonical link |
| `docs/research_notes/10_tutorial_borrow_checker.md` | `concept/04_formal/01_ownership_logic/28_borrow_checking_decidability.md` | 1,176 | add `concept/` canonical link |
| `docs/research_notes/10_tutorial_lifetimes.md` | `concept/02_intermediate/00_traits/18_lifetimes_advanced.md` | 448 | add `concept/` canonical link |
| `docs/04_research/04_ng_trait_solver.md` | `concept/04_formal/05_rustc_internals/26_trait_solver_in_rustc.md` | 529 | add `concept/` canonical link |
| `docs/04_research/04_next_generation_trait_solver.md` | `concept/04_formal/05_rustc_internals/26_trait_solver_in_rustc.md` | 439 | add `concept/` canonical link |

### 3.2 Cheatsheets / reference cards that reproduce concept-level depth

These are labeled as quick references but run to 1,000+ lines and explain concepts from scratch. They should stay in `docs/` as **cheatsheets** but must begin with a clear `concept/` authority link and avoid re-deriving full semantics.

| File | Closest `concept/` page | Lines | Recommendation |
|---|---|---:|---|
| `docs/02_reference/quick_reference/02_type_system.md` | `concept/01_foundation/02_type_system/04_type_system.md` | 1,302 | `keep` but add top `concept/` link |
| `docs/02_reference/quick_reference/02_async_patterns.md` | `concept/03_advanced/01_async/25_async_advanced.md` | 1,309 | `keep` but add top `concept/` link |
| `docs/02_reference/quick_reference/02_error_handling_cheatsheet.md` | `concept/02_intermediate/03_error_handling/04_error_handling.md` | ~300 | `keep` but add top `concept/` link |
| `docs/02_reference/quick_reference/02_generics_cheatsheet.md` | `concept/02_intermediate/01_generics/02_generics.md` | ~250 | `keep` but add top `concept/` link |
| `docs/02_reference/quick_reference/02_smart_pointers_cheatsheet.md` | `concept/02_intermediate/02_memory_management/12_smart_pointers.md` | ~250 | `keep` but add top `concept/` link |
| `docs/02_reference/quick_reference/02_testing_cheatsheet.md` | `concept/01_foundation/10_testing_basics/16_testing_basics.md` | ~250 | `keep` but add top `concept/` link |
| `docs/02_reference/quick_reference/02_ownership_cheatsheet.md` | `concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md` | ~250 | `keep` but add top `concept/` link |
| `docs/02_reference/quick_reference/02_closures_cheatsheet.md` | `concept/01_foundation/11_quizzes/27_quiz_closures_iterators.md` | ~250 | `keep` but add top `concept/` link |
| `docs/02_reference/quick_reference/02_modules_cheatsheet.md` | `concept/02_intermediate/05_modules_and_visibility/10_module_system.md` | ~250 | `keep` but add top `concept/` link |
| `docs/02_reference/quick_reference/02_control_flow_functions_cheatsheet.md` | `concept/01_foundation/04_control_flow/07_control_flow.md` | ~250 | `keep` but add top `concept/` link |

### 3.3 Already converted to `concept/` redirects (good examples)

A few `docs/` files correctly point to `concept/` and should remain as-is:

- `docs/03_guides/03_async_closures_deep_dive.md` → `concept/03_advanced/01_async/24_async_closures.md`
- `docs/05_guides/05_unsafe_fields_preview.md` → `concept/07_future/03_preview_features/13_unsafe_fields_preview.md`
- `docs/05_guides/05_safety_tags_guide.md` → `concept/07_future/03_preview_features/08_safety_tags_preview.md`
- `docs/03_guides/03_semver_checks.md` → `concept/07_future/03_preview_features/46_cargo_semver_checks_preview.md`

---

## 4. Topics Covered in `knowledge/` or `docs/` but Missing a `concept/` Canonical Page

The following topics have substantial write-ups outside `concept/` and **do not appear to have a dedicated canonical page** inside `concept/`. For each, either create a new `concept/` page or explicitly designate an existing `concept/` page as the canonical home.

| Topic | Current location(s) | Suggested `concept/` home |
|---|---|---|
| **Lazy Initialization** (`LazyCell`/`LazyLock`) | `knowledge/03_advanced/04_lazy_initialization.md` | `concept/02_intermediate/02_memory_management/lazy_initialization.md` |
| **Type-Driven Correctness / Type-State** | `knowledge/03_advanced/06_type_driven_correctness.md` | `concept/02_intermediate/04_types_and_conversions/type_driven_correctness.md` |
| **Unsafe Code Auditing** | `knowledge/04_expert/02_unsafe_audit.md` | `concept/03_advanced/02_unsafe/unsafe_code_auditing.md` |
| **MaybeUninit** | `knowledge/03_advanced/unsafe/03_maybe_uninit.md` | `concept/03_advanced/02_unsafe/maybe_uninit.md` |
| **Rust Design Philosophy** | `knowledge/00_start/04_rust_philosophy.md` | `concept/01_foundation/00_start/rust_philosophy.md` |
| **Hello, World / First Program** | `knowledge/00_start/01_hello_world.md` | `concept/01_foundation/00_start/hello_world.md` or merge into getting-started index |
| **Installation & Toolchain Setup** | `knowledge/00_start/02_installation.md` | `concept/01_foundation/00_start/installation.md` |
| **Axum** | `knowledge/06_ecosystem/deep_dives/01_axum_deep_dive.md` | `concept/06_ecosystem/04_web_and_networking/axum.md` |
| **Sea-ORM** | `knowledge/06_ecosystem/databases/01_sea_orm_deep_dive.md` | `concept/06_ecosystem/06_data_and_distributed/sea_orm.md` |
| **SQLx** | `knowledge/06_ecosystem/databases/02_sqlx_deep_dive.md` | `concept/06_ecosystem/06_data_and_distributed/sqlx.md` |
| **Cargo Script** | `docs/06_toolchain/06_cargo_script_guide.md` | already exists: `concept/06_ecosystem/01_cargo/09_cargo_script.md` (link it explicitly) |

---

## 5. `docs/` Guides that Correctly Stay in `docs/` but Should Link More Explicitly to `concept/`

These files are legitimate guides, reports, or learning paths and do not need to be migrated. They should, however, open with a clear `concept/` authority link so readers know where the canonical explanation lives.

| File | Reason to stay in `docs/` | Missing `concept/` link for |
|---|---|---|
| `docs/01_learning/learning_mvp_path.md` | learning-path guide | `concept/00_meta/04_navigation/learning_mvp_path.md` |
| `docs/01_learning/01_cross_module_navigation.md` | navigation guide | `concept/00_meta/04_navigation/navigation.md` |
| `docs/02_reference/quick_reference/README.md` | quick-reference index | relevant `concept/` indexes |
| `docs/02_reference/02_cross_language_comparison.md` | comparative report | `concept/05_comparative/` pages |
| `docs/02_reference/02_edge_cases_and_special_cases.md` | reference companion | `concept/04_formal/05_rustc_internals/41_special_types_and_traits.md` |
| `docs/02_reference/02_standard_library_comprehensive_analysis_2025_12_25.md` | std-lib analysis report | `concept/02_intermediate/02_memory_management/`, `concept/01_foundation/05_collections/` |
| `docs/03_guides/03_miri_guide.md` | tool guide | `concept/04_formal/04_model_checking/31_miri.md` |
| `docs/03_guides/03_fuzzing_guide.md` | tool guide | `concept/06_ecosystem/09_testing_and_quality/` |
| `docs/05_guides/05_kani_practical_guide.md` | tool guide | `concept/04_formal/04_model_checking/32_kani.md` |
| `docs/05_guides/05_verus_practical_guide.md` | tool guide | `concept/07_future/03_preview_features/33_autoverus_preview.md` |
| `docs/05_guides/05_miri_practical_guide.md` | tool guide | `concept/04_formal/04_model_checking/31_miri.md` |
| `docs/05_guides/05_formal_verification_integration_guide.md` | integration guide | `concept/06_ecosystem/08_formal_verification/74_formal_verification_tools.md` |
| `docs/05_guides/05_embedded_rust_guide.md` | domain guide | `concept/06_ecosystem/05_systems_and_embedded/22_embedded_systems.md` |
| `docs/06_toolchain/01_compiler_features.md` | toolchain guide | `concept/06_ecosystem/00_toolchain/47_compiler_infrastructure.md` |
| `docs/06_toolchain/03_rustdoc_advanced.md` | toolchain guide | `concept/06_ecosystem/00_toolchain/77_rustdoc_196_changes.md` |
| `docs/06_toolchain/06_cranelift_backend_guide.md` | toolchain guide | `concept/07_future/03_preview_features/38_cranelift_backend_preview.md` |
| `docs/07_project/07_documentation_cross_reference_guide.md` | project guide | `concept/06_ecosystem/09_testing_and_quality/14_documentation.md` |

---

## 6. Summary Counts

| Category | Count | Note |
|---|---:|---|
| `concept/` files audited | 509 | canonical source base |
| `knowledge/` files audited | 139 | should be summaries/redirects only |
| `docs/` files audited | 524 | guides/reports/cheatsheets |
| `knowledge/` files already clean redirects/summaries | 35 | keep |
| `knowledge/` files with `concept/` link but still substantial | 14 | convert to cleaner redirect/summary |
| `knowledge/` files with substantial full content and no `concept/` link | 90 | primary remediation target |
| `docs/` meta/template/report files | 37 | correctly stay in `docs/` |
| `docs/` cheatsheets | 29 | keep, but add `concept/` links |
| `docs/` substantial guides matching `concept/` topics | ~250+ | review for migration or canonical linking |
| Topics missing a dedicated `concept/` page (candidates) | ~11 | see Section 4 |

**Top remediation priorities**:

1. Convert the 14 `knowledge/` redirect stubs that still contain full explanations into true stubs.
2. Migrate or redirect the 90 substantial `knowledge/` files, especially the core tutorials (`iterators`, `lazy_initialization`, `type_driven_correctness`, `unsafe_audit`).
3. Add a top-of-file `concept/` authority link to every `docs/` guide and cheatsheet that covers a `concept/` topic.
4. Relocate the `knowledge/04_expert/safety_critical/` suite to `docs/` or `content/`.
5. Create missing canonical pages for **Lazy Initialization**, **Type-Driven Correctness / Type-State**, **Unsafe Code Auditing**, **MaybeUninit**, and **Rust Design Philosophy**.

---

*Report generated by automated metadata comparison and manual review. No project files were modified.*
