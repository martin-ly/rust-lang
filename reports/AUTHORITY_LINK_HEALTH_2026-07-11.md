# 国际化权威来源 URL 健康（2026-07-11）

**EN**: International Authority URL Health
**Summary**: 仅检查 P0/P1/P2 权威域 URL 的有效性（4xx/5xx/超时/连接错），验证『对齐国际化权威』不仅是『有引用』且『引用有效』。带缓存，可增量。

> 扫描 concept/+knowledge/+docs/ 权威域唯一 URL: **2243** · 失效/异常: **247**

| 分级 | 失效/异常数 |
|:---|---:|
| P0 | 72 |
| P1 | 62 |
| P2 | 113 |

## 失效/异常清单（前 80）
| 分级 | 状态 | 错误 | URL | 引用文件（≤5） |
|:---|:---|:---|:---|:---|
| P0 | 404 | HTTPError | https://doc.rust-lang.org/book/ch10-00-generic-types-traits-and-lifetimes.html | docs/01_learning/learning_mvp_path.md; docs/research_notes/software_design_theory/07_crate_architectures/05_bevy_architecture.md |
| P0 | 404 | HTTPError | https://doc.rust-lang.org/book/ch13-00-functional-features-of-rust.html | docs/research_notes/software_design_theory/01_design_patterns_formal/03_behavioral/10_iterator.md |
| P0 | 404 | HTTPError | https://doc.rust-lang.org/book/ch17-02-async-fn-and-messages.html | concept/03_advanced/01_async/02_async.md |
| P0 | 404 | HTTPError | https://doc.rust-lang.org/book/ch17-04-pin.html | concept/03_advanced/01_async/02_async.md |
| P0 | 404 | HTTPError | https://doc.rust-lang.org/book/ch17-05-concurrency.html | concept/03_advanced/01_async/02_async.md |
| P0 | 404 | HTTPError | https://doc.rust-lang.org/book/ch21-00-final-project.html | docs/01_learning/learning_mvp_path.md |
| P0 | 404 | HTTPError | https://doc.rust-lang.org/nomicon/option-zipper.html | concept/03_advanced/06_low_level_patterns/36_ownership_performance_optimization.md |
| P0 | 404 | HTTPError | https://doc.rust-lang.org/nomicon/self-referential-structs.html | docs/research_notes/10_unsafe_code_guidelines_alignment.md |
| P0 | 404 | HTTPError | https://doc.rust-lang.org/nomicon/unions.html | docs/research_notes/10_unsafe_code_guidelines_alignment.md |
| P0 | 404 | HTTPError | https://doc.rust-lang.org/reference/editions.html | concept/03_advanced/03_proc_macros/31_production_grade_macro_development.md; docs/research_notes/software_design_theory/01_design_patterns_formal/01_creational/10_abstract_factory.md; docs/research_notes/software_design_theory/01_design_patterns_formal/01_creational/10_builder.md; docs/research_notes/software_design_theory/01_design_patterns_formal/01_creational/10_prototype.md; docs/research_notes/software_design_theory/01_design_patterns_formal/02_structural/10_adapter.md |
| P0 | 404 | HTTPError | https://doc.rust-lang.org/reference/higher-ranked-trait-bounds.html | docs/research_notes/10_lifetime_cheatsheet.md |
| P0 | 404 | HTTPError | https://doc.rust-lang.org/reference/lifetime-meaning.html | docs/research_notes/software_design_theory/01_design_patterns_formal/01_creational/10_abstract_factory.md; docs/research_notes/software_design_theory/01_design_patterns_formal/01_creational/10_builder.md; docs/research_notes/software_design_theory/01_design_patterns_formal/01_creational/10_prototype.md; docs/research_notes/software_design_theory/01_design_patterns_formal/02_structural/10_adapter.md; docs/research_notes/software_design_theory/01_design_patterns_formal/02_structural/10_bridge.md |
| P0 | 404 | HTTPError | https://doc.rust-lang.org/reference/lifetime-rules.html | concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md |
| P0 | 404 | HTTPError | https://doc.rust-lang.org/reference/ownership.html | concept/06_ecosystem/05_systems_and_embedded/08_wasi.md; docs/02_reference/quick_reference/02_ownership_cheatsheet.md |
| P0 | 404 | HTTPError | https://doc.rust-lang.org/reference/standard-library-mem.html | concept/03_advanced/02_unsafe/29_memory_model.md |
| P0 | 404 | HTTPError | https://doc.rust-lang.org/reference/subtyping-and-variance.html | docs/research_notes/10_lifetime_cheatsheet.md |
| P0 | 404 | HTTPError | https://doc.rust-lang.org/reference/type-inference.html | concept/04_formal/00_type_theory/27_type_checking_and_inference.md |
| P0 | 404 | HTTPError | https://doc.rust-lang.org/rust-by-example/custom_types/type.html | concept/01_foundation/07_modules_and_items/43_type_aliases.md |
| P0 | 404 | HTTPError | https://doc.rust-lang.org/rust-by-example/std_misc/net.html | concept/06_ecosystem/04_web_and_networking/38_network_protocols.md |
| P0 | 404 | HTTPError | https://doc.rust-lang.org/rustc/` | docs/05_guides/workflow/01_workflow_theory.md |
| P0 | 404 | HTTPError | https://doc.rust-lang.org/std/sync.html | docs/research_notes/software_design_theory/07_crate_architectures/19_crossbeam_architecture.md |
| P0 | 404 | HTTPError | https://doc.rust-lang.org/std/ync/atomic | concept/03_advanced/00_concurrency/01_concurrency.md |
| P0 | 404 | HTTPError | https://github.com/rust-lang-cn/book | docs/research_notes/10_i18n_translation_gap_analysis.md |
| P0 | 404 | HTTPError | https://github.com/rust-lang/rfcs/(pull|issues|blob | docs/research_notes/10_rfc_to_counterexample_mapping.md |
| P0 | 404 | HTTPError | https://github.com/rust-lang/rfcs/pull/9000 | docs/03_guides/03_quic_http3_guide.md |
| P0 | 404 | HTTPError | https://github.com/rust-lang/rfcs/pull/9114 | docs/03_guides/03_quic_http3_guide.md |
| P0 | 404 | HTTPError | https://github.com/rust-lang/rust-lang-learning/tree/main/crates/c06_async | docs/research_notes/software_design_theory/07_crate_architectures/22_redis_architecture.md; docs/research_notes/software_design_theory/07_crate_architectures/39_salvo_architecture.md; docs/research_notes/software_design_theory/07_crate_architectures/40_ntex_architecture.md; docs/research_notes/software_design_theory/07_crate_architectures/41_askama_architecture.md; docs/research_notes/software_design_theory/07_crate_architectures/42_maud_architecture.md |
| P0 | 404 | HTTPError | https://github.com/rust-lang/rust-lang-learning/tree/main/crates/c08_algorithms | docs/research_notes/software_design_theory/07_crate_architectures/35_ort_architecture.md; docs/research_notes/software_design_theory/07_crate_architectures/36_tract_architecture.md |
| P0 | 404 | HTTPError | https://github.com/rust-lang/rust-lang-learning/tree/main/crates/c10_networks | docs/research_notes/software_design_theory/07_crate_architectures/26_kafka_architecture.md; docs/research_notes/software_design_theory/07_crate_architectures/27_kube_rs_architecture.md; docs/research_notes/software_design_theory/07_crate_architectures/28_lapin_architecture.md; docs/research_notes/software_design_theory/07_crate_architectures/37_aws_sdk_architecture.md |
| P0 | 404 | HTTPError | https://rust-lang.github.io/ | concept/07_future/03_preview_features/45_std_autodiff_preview.md |
| P0 | 404 | HTTPError | https://rust-lang.github.io/api-guidelines/safety.html | docs/research_notes/software_design_theory/01_design_patterns_formal/01_creational/10_abstract_factory.md; docs/research_notes/software_design_theory/01_design_patterns_formal/01_creational/10_builder.md; docs/research_notes/software_design_theory/01_design_patterns_formal/01_creational/10_prototype.md; docs/research_notes/software_design_theory/01_design_patterns_formal/02_structural/10_adapter.md; docs/research_notes/software_design_theory/01_design_patterns_formal/02_structural/10_bridge.md |
| P0 | 404 | HTTPError | https://rust-lang.github.io/async-book/02_execution/03_async_lifetimes.html | docs/research_notes/10_async_book_alignment.md |
| P0 | 404 | HTTPError | https://rust-lang.github.io/async-book/04_pinning/01_chapter.html | docs/research_notes/10_async_book_alignment.md; docs/research_notes/10_knowledge_graph_index.md; docs/research_notes/10_learning_and_interview_alignment.md |
| P0 | 404 | HTTPError | https://rust-lang.github.io/async-book/04_pinning/index.html | concept/03_advanced/01_async/39_future_and_executor_mechanisms.md |
| P0 | 404 | HTTPError | https://rust-lang.github.io/async-book/` | docs/05_guides/workflow/01_workflow_theory.md |
| P0 | 404 | HTTPError | https://rust-lang.github.io/compiler-team/minutes/design-meeting/2021-03-17-next-generation-trait-solver.html | docs/04_research/04_next_generation_trait_solver.md |
| P0 | 404 | HTTPError | https://rust-lang.github.io/rfcs/0000-safety-tags.html | concept/00_meta/02_sources/international_authority_index.md |
| P0 | 404 | HTTPError | https://rust-lang.github.io/rfcs/1590-generic-associated-types.html | docs/research_notes/10_learning_and_interview_alignment.md |
| P0 | 404 | HTTPError | https://rust-lang.github.io/rfcs/1665.html | concept/00_meta/00_framework/theorem_inference_forest.md |
| P0 | 404 | HTTPError | https://rust-lang.github.io/rfcs/2000-2000-const-generics.html | concept/02_intermediate/00_traits/19_advanced_traits.md |
| P0 | 404 | HTTPError | https://rust-lang.github.io/rfcs/2616-iterable.html | docs/03_practice/03_project_11_web_server.md |
| P0 | 404 | HTTPError | https://rust-lang.github.io/rfcs/2645-transparent-enums.html | docs/research_notes/10_rfc_alignment_index.md |
| P0 | 404 | HTTPError | https://rust-lang.github.io/rfcs/3101-reserved-prefix.html | docs/research_notes/10_rfc_alignment_index.md |
| P0 | 404 | HTTPError | https://rust-lang.github.io/rfcs/3185-async-drop.html | docs/research_notes/10_rfc_alignment_index.md |
| P0 | 404 | HTTPError | https://rust-lang.github.io/rfcs/3271-rustdoc-json.html | concept/06_ecosystem/00_toolchain/77_rustdoc_196_changes.md |
| P0 | 404 | HTTPError | https://rust-lang.github.io/rfcs/3516-gen-blocks.html | docs/research_notes/10_async_ecosystem_alignment.md; docs/research_notes/10_version_evolution_alignment.md |
| P0 | 404 | HTTPError | https://rust-lang.github.io/rfcs/3560-alignment.html | docs/04_rust_language_feature_comprehensive_inventory_2026.md |
| P0 | 404 | HTTPError | https://rust-lang.github.io/rfcs/NNNN-*.html` | docs/research_notes/10_rfc_to_counterexample_mapping.md |
| P0 | 404 | HTTPError | https://rust-lang.github.io/rust-formal-methods/ | docs/research_notes/10_authoritative_source_alignment_network.md |
| P0 | 404 | HTTPError | https://rust-lang.github.io/rust-project-goals/2024h2/formal-methods.html | concept/04_formal/04_model_checking/05_verification_toolchain.md |
| P0 | 404 | HTTPError | https://rust-lang.github.io/rust-project-goals/2025h1/Rust-for-Linux.html | concept/06_ecosystem/06_data_and_distributed/04_application_domains.md |
| P0 | 404 | HTTPError | https://rust-lang.github.io/rust-project-goals/2025h1/const-traits.html | concept/07_future/03_preview_features/04_effects_system.md |
| P0 | 404 | HTTPError | https://rust-lang.github.io/unsafe-code-guidelines/reference/types.html | concept/02_intermediate/04_types_and_conversions/35_unions.md; concept/03_advanced/07_unsafe_internals/37_unsafe_collections_internals.md |
| P0 | 404 | HTTPError | https://rustc-dev-guide.rust-lang.org/backend/backend.html | concept/06_ecosystem/00_toolchain/67_llvm_backend_and_codegen.md |
| P0 | 404 | HTTPError | https://rustc-dev-guide.rust-lang.org/backend/mono.html | concept/06_ecosystem/00_toolchain/67_llvm_backend_and_codegen.md |
| P0 | 404 | HTTPError | https://rustc-dev-guide.rust-lang.org/building/bootstrapping.html | concept/06_ecosystem/00_toolchain/70_rustc_bootstrap.md |
| P0 | 404 | HTTPError | https://rustc-dev-guide.rust-lang.org/codegen/implicit-caller-location.html | concept/02_intermediate/03_error_handling/04_error_handling.md |
| P0 | 404 | HTTPError | https://rustc-dev-guide.rust-lang.org/diagnostics/lint-guidelines.html | concept/06_ecosystem/00_toolchain/69_compiler_diagnostics_and_ui_tests.md |
| P0 | 404 | HTTPError | https://rustc-dev-guide.rust-lang.org/rustc-driver.html | concept/03_advanced/03_proc_macros/30_macro_debugging_and_diagnostics.md; concept/06_ecosystem/00_toolchain/68_rustc_driver_and_stable_mir.md |
| P0 | 404 | HTTPError | https://rustc-dev-guide.rust-lang.org/tests/profiling.html | concept/06_ecosystem/00_toolchain/71_compiler_testing.md |
| P0 | 404 | HTTPError | https://rustc-dev-guide.rust-lang.org/type-checking.html | concept/04_formal/00_type_theory/27_type_checking_and_inference.md |
| P0 | 404 | HTTPError | https://spec.ferrocene.dev/borrowing.html | docs/research_notes/10_ferrocene_fls_alignment.md |
| P0 | 404 | HTTPError | https://spec.ferrocene.dev/lifetimes.html | docs/research_notes/10_ferrocene_fls_alignment.md |
| P0 | 404 | HTTPError | https://spec.ferrocene.dev/linkage.html | docs/research_notes/10_ferrocene_fls_alignment.md |
| P0 | 404 | HTTPError | https://spec.ferrocene.dev/modules-and-crates.html | docs/research_notes/10_ferrocene_fls_alignment.md |
| P0 | 404 | HTTPError | https://spec.ferrocene.dev/notation.html | docs/research_notes/10_ferrocene_fls_alignment.md |
| P0 | 404 | HTTPError | https://spec.ferrocene.dev/ownership.html | docs/research_notes/10_ferrocene_fls_alignment.md |
| P0 | 404 | HTTPError | https://spec.ferrocene.dev/subtyping.html | docs/research_notes/10_ferrocene_fls_alignment.md |
| P0 | 404 | HTTPError | https://spec.ferrocene.dev/syntax.html | docs/research_notes/10_ferrocene_fls_alignment.md |
| P0 | 404 | HTTPError | https://spec.ferrocene.dev/traits.html | docs/research_notes/10_ferrocene_fls_alignment.md |
| P0 | 404 | HTTPError | https://spec.ferrocene.dev/types.html | docs/research_notes/10_ferrocene_fls_alignment.md |
| P0 | 404 | HTTPError | https://spec.ferrocene.dev/unsafe-rust.html | docs/research_notes/10_ferrocene_fls_alignment.md |
| P1 | 403 | HTTPError | https://cacm.acm.org/ | concept/05_comparative/00_paradigms/03_paradigm_matrix.md |
| P1 | 403 | HTTPError | https://cacm.acm.org/magazines/2021/4/251364-safe-systems-programming-in-rust/ | docs/research_notes/formal_methods/10_ownership_model.md |
| P1 | 403 | HTTPError | https://dl.acm.org/ | concept/00_meta/03_audit/audit_checklist.md; concept/05_comparative/01_systems_languages/02_rust_vs_go.md; docs/00_meta/00_annual_review_template.md; docs/00_meta/00_content_reconstruction_plan_2026.md; docs/00_meta/00_docs_reorganization_complete.md |
| P1 | 403 | HTTPError | https://dl.acm.org/doi/10.1109/TSE.1982.235252 | concept/06_ecosystem/03_design_patterns/41_workflow_theory.md |
| P1 | 403 | HTTPError | https://dl.acm.org/doi/10.1145/1273496.1273513 | docs/research_notes/software_design_theory/07_crate_architectures/30_meilisearch_architecture.md |
| P1 | 403 | HTTPError | https://dl.acm.org/doi/10.1145/138403.138440 | docs/research_notes/10_advanced_data_structures_guide.md |
| P1 | 403 | HTTPError | https://dl.acm.org/doi/10.1145/143165.143169 | concept/01_foundation/00_start/21_effects_and_purity.md |
| P1 | 403 | HTTPError | https://dl.acm.org/doi/10.1145/1640089.1640095 | concept/06_ecosystem/03_design_patterns/02_patterns.md |
> … 另有 167 条，见 JSON。

## 诚信
- 仅查 P0/P1/P2 权威域（单一来源：maintenance/authority_coverage_dashboard.py）；不查其它外部域。
- 瞬时网络抖动可能导致个别误判；失效项需人工复核后替换/移除，勿据此脚本自动改文件。

*由 `scripts/check_authority_link_health.py` 生成*