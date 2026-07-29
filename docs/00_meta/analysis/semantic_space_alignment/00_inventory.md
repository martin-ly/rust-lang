# 语义空间相关概念页盘点

**EN**: Inventory of Semantic-Space Related Concept Pages
**Summary**: 自动盘点 `concept/` 中与语义空间、形式化方法、系统/架构语义、企业架构、AI 语义工程、Rust 1.97.1 相关的权威页，供国际来源对齐使用。

> **生成时间**: 2026-07-29
> **文件总数**: 501
> **范围规则**: 路径或正文中命中语义空间关键词的 `concept/**/*.md`

## 一、汇总统计

- 命中文件数：501
- 含 Mindmap：422 / 501
- 含反例节：48 / 501
- 总 `rust` 代码块：4404

## 二、按领域分组

### 00_concurrency（10 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/03_advanced/00_concurrency/01_concurrency.md`](../../concept/03_advanced/00_concurrency/01_concurrency.md) | Concurrency Models | L3 | yes | no | 27 | 5 |
| [`concept/03_advanced/00_concurrency/02_send_sync_auto_traits.md`](../../concept/03_advanced/00_concurrency/02_send_sync_auto_traits.md) | Send and Sync — Auto Traits as Compile-Time Concurrency Cont... | L3 | yes | no | 13 | 1 |
| [`concept/03_advanced/00_concurrency/03_concurrency_patterns.md`](../../concept/03_advanced/00_concurrency/03_concurrency_patterns.md) | Concurrency Patterns | L4 | yes | no | 34 | 4 |
| [`concept/03_advanced/00_concurrency/04_send_sync_boundaries.md`](../../concept/03_advanced/00_concurrency/04_send_sync_boundaries.md) | Send/Sync Boundary Judgment — Trait Objects, Closures, and A... | L3 | yes | no | 10 | 1 |
| [`concept/03_advanced/00_concurrency/05_cross_platform_concurrency.md`](../../concept/03_advanced/00_concurrency/05_cross_platform_concurrency.md) | Cross-Platform Concurrency | L4 | yes | yes | 5 | 2 |
| [`concept/03_advanced/00_concurrency/06_atomics_and_memory_ordering.md`](../../concept/03_advanced/00_concurrency/06_atomics_and_memory_ordering.md) | Atomics and Memory Ordering | L4 | yes | no | 24 | 3 |
| [`concept/03_advanced/00_concurrency/07_lock_free.md`](../../concept/03_advanced/00_concurrency/07_lock_free.md) | Locking Primitives | L4 | yes | no | 20 | 3 |
| [`concept/03_advanced/00_concurrency/08_parallel_distributed_pattern_spectrum.md`](../../concept/03_advanced/00_concurrency/08_parallel_distributed_pattern_spectrum.md) | Parallel Distributed Pattern Spectrum | L3 | yes | no | 18 | 3 |
| [`concept/03_advanced/00_concurrency/09_quiz_concurrency_async.md`](../../concept/03_advanced/00_concurrency/09_quiz_concurrency_async.md) | Concurrency and Async (Quiz) | L4 | no | no | 19 | 2 |
| [`concept/03_advanced/00_concurrency/10_quiz_semantic_models.md`](../../concept/03_advanced/00_concurrency/10_quiz_semantic_models.md) | Semantic Models and Cross-Language Comparisons Quiz | L4 | no | no | 4 | 1 |

### 00_framework（20 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/00_meta/00_framework/boundary_extension_tree.md`](../../concept/00_meta/00_framework/boundary_extension_tree.md) | Boundary Extension Tree | — | yes | no | 1 | 1 |
| [`concept/00_meta/00_framework/cognitive_dimension_matrix.md`](../../concept/00_meta/00_framework/cognitive_dimension_matrix.md) | Cognitive Dimension Matrix | — | yes | no | 0 | 1 |
| [`concept/00_meta/00_framework/competency_graph.md`](../../concept/00_meta/00_framework/competency_graph.md) | Competency Graph | — | yes | no | 0 | 1 |
| [`concept/00_meta/00_framework/comprehensive_rust_mapping.md`](../../concept/00_meta/00_framework/comprehensive_rust_mapping.md) | Comprehensive Rust Mapping | L1 | no | no | 0 | 2 |
| [`concept/00_meta/00_framework/concept_definition_decision_forest.md`](../../concept/00_meta/00_framework/concept_definition_decision_forest.md) | Concept Definition Decision Forest | — | yes | no | 0 | 1 |
| [`concept/00_meta/00_framework/cpp_rust_engineering_roadmap.md`](../../concept/00_meta/00_framework/cpp_rust_engineering_roadmap.md) | C/C++ to Rust Engineering Comparison Roadmap | L2 | no | no | 2 | 1 |
| [`concept/00_meta/00_framework/decidability_spectrum.md`](../../concept/00_meta/00_framework/decidability_spectrum.md) | Decidability Spectrum | L4 | no | no | 2 | 2 |
| [`concept/00_meta/00_framework/expressiveness_multiview.md`](../../concept/00_meta/00_framework/expressiveness_multiview.md) | Expressiveness Multiview | L4 | no | no | 7 | 2 |
| [`concept/00_meta/00_framework/fault_tree_analysis_collection.md`](../../concept/00_meta/00_framework/fault_tree_analysis_collection.md) | Fault Tree Analysis Collection | — | yes | no | 0 | 1 |
| [`concept/00_meta/00_framework/knowledge_mindmap.md`](../../concept/00_meta/00_framework/knowledge_mindmap.md) | Knowledge Mindmap | L1 | yes | no | 0 | 3 |
| [`concept/00_meta/00_framework/methodology.md`](../../concept/00_meta/00_framework/methodology.md) | Methodology | L2 | yes | no | 1 | 2 |
| [`concept/00_meta/00_framework/paradigm_transition_matrix.md`](../../concept/00_meta/00_framework/paradigm_transition_matrix.md) | Paradigm Transition Matrix | L4 | yes | no | 0 | 1 |
| [`concept/00_meta/00_framework/pattern_semantic_space_index.md`](../../concept/00_meta/00_framework/pattern_semantic_space_index.md) | Pattern Semantic Space Index | L2 | no | no | 0 | 1 |
| [`concept/00_meta/00_framework/pl_foundations_roadmap.md`](../../concept/00_meta/00_framework/pl_foundations_roadmap.md) | General PL Foundations Roadmap | L2 | no | no | 0 | 1 |
| [`concept/00_meta/00_framework/semantic_bridge_algorithms_patterns.md`](../../concept/00_meta/00_framework/semantic_bridge_algorithms_patterns.md) | Algorithms–Patterns Semantic Bridge | L4 | no | no | 7 | 2 |
| [`concept/00_meta/00_framework/semantic_expressiveness.md`](../../concept/00_meta/00_framework/semantic_expressiveness.md) | Semantic Expressiveness | L4 | yes | no | 1 | 2 |
| [`concept/00_meta/00_framework/semantic_space.md`](../../concept/00_meta/00_framework/semantic_space.md) | Semantic Space | L4 | yes | no | 9 | 3 |
| [`concept/00_meta/00_framework/theorem_inference_forest.md`](../../concept/00_meta/00_framework/theorem_inference_forest.md) | Theorem Inference Forest | — | yes | no | 0 | 1 |
| [`concept/00_meta/00_framework/theorem_registry.md`](../../concept/00_meta/00_framework/theorem_registry.md) | Global Theorem Chain Registry | — | no | no | 0 | 1 |
| [`concept/00_meta/00_framework/todos.md`](../../concept/00_meta/00_framework/todos.md) | Todos | L3 | no | no | 0 | 2 |

### 00_meta（2 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/README.md`](../../concept/README.md) | Rust Concept Knowledge System | — | no | no | 0 | 2 |
| [`concept/SUMMARY.md`](../../concept/SUMMARY.md) | Table of Contents | — | no | no | 0 | 1 |

### 00_paradigms（5 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/05_comparative/00_paradigms/01_paradigm_matrix.md`](../../concept/05_comparative/00_paradigms/01_paradigm_matrix.md) | Paradigm Matrix | L4 | yes | no | 12 | 4 |
| [`concept/05_comparative/00_paradigms/02_execution_model_isomorphism.md`](../../concept/05_comparative/00_paradigms/02_execution_model_isomorphism.md) | Execution Model Isomorphism | L4 | yes | no | 13 | 3 |
| [`concept/05_comparative/00_paradigms/03_cpp_rust_surface_features.md`](../../concept/05_comparative/00_paradigms/03_cpp_rust_surface_features.md) | C++ vs Rust: Construction, Operators, RTTI, and Friends | L3 | yes | no | 4 | 1 |
| [`concept/05_comparative/00_paradigms/04_five_models_definition_matrix.md`](../../concept/05_comparative/00_paradigms/04_five_models_definition_matrix.md) | Five Execution Models Definition Matrix | L2 | yes | no | 0 | 1 |
| [`concept/05_comparative/00_paradigms/05_language_semantic_model_matrix.md`](../../concept/05_comparative/00_paradigms/05_language_semantic_model_matrix.md) | Unified Language × Semantic Model Expressiveness Matrix | L5 | yes | no | 0 | 2 |

### 00_start（6 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/01_foundation/00_start/00_start.md`](../../concept/01_foundation/00_start/00_start.md) | Getting Started with Rust | L1 | yes | yes | 3 | 2 |
| [`concept/01_foundation/00_start/02_zero_cost_abstractions.md`](../../concept/01_foundation/00_start/02_zero_cost_abstractions.md) | Zero Cost Abstractions | L2 | yes | no | 14 | 2 |
| [`concept/01_foundation/00_start/03_closure_basics.md`](../../concept/01_foundation/00_start/03_closure_basics.md) | Closure Basics | L2 | yes | yes | 18 | 2 |
| [`concept/01_foundation/00_start/04_effects_and_purity.md`](../../concept/01_foundation/00_start/04_effects_and_purity.md) | Effects and Purity | L1 | yes | yes | 17 | 3 |
| [`concept/01_foundation/00_start/06_keywords.md`](../../concept/01_foundation/00_start/06_keywords.md) | Keywords | L1 | yes | yes | 4 | 2 |
| [`concept/01_foundation/00_start/07_operators_and_symbols.md`](../../concept/01_foundation/00_start/07_operators_and_symbols.md) | Operators and Symbols | L1 | yes | yes | 2 | 2 |

### 00_toolchain（16 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/06_ecosystem/00_toolchain/01_toolchain.md`](../../concept/06_ecosystem/00_toolchain/01_toolchain.md) | Toolchain and Cargo | L2 | yes | no | 16 | 6 |
| [`concept/06_ecosystem/00_toolchain/02_logging_observability.md`](../../concept/06_ecosystem/00_toolchain/02_logging_observability.md) | Logging Observability | L2 | yes | no | 9 | 2 |
| [`concept/06_ecosystem/00_toolchain/03_devops_and_ci_cd.md`](../../concept/06_ecosystem/00_toolchain/03_devops_and_ci_cd.md) | DevOps and CI/CD | L3 | yes | no | 7 | 2 |
| [`concept/06_ecosystem/00_toolchain/04_compiler_internals.md`](../../concept/06_ecosystem/00_toolchain/04_compiler_internals.md) | Rust Compiler Internals and Driver Architecture | L4 | yes | no | 7 | 2 |
| [`concept/06_ecosystem/00_toolchain/05_compiler_infrastructure.md`](../../concept/06_ecosystem/00_toolchain/05_compiler_infrastructure.md) | Compiler Infrastructure | L4 | yes | no | 1 | 2 |
| [`concept/06_ecosystem/00_toolchain/06_quiz_toolchain.md`](../../concept/06_ecosystem/00_toolchain/06_quiz_toolchain.md) | Toolchain (Quiz) | L3 | no | no | 9 | 2 |
| [`concept/06_ecosystem/00_toolchain/07_rustdoc_196_changes.md`](../../concept/06_ecosystem/00_toolchain/07_rustdoc_196_changes.md) | Rustdoc 1.96–1.97 Changes | L2 | yes | no | 4 | 1 |
| [`concept/06_ecosystem/00_toolchain/08_platform_rust_integration.md`](../../concept/06_ecosystem/00_toolchain/08_platform_rust_integration.md) | Integrating Rust into Existing Platforms and Codebases | L4 | yes | no | 6 | 1 |
| [`concept/06_ecosystem/00_toolchain/09_llvm_backend_and_codegen.md`](../../concept/06_ecosystem/00_toolchain/09_llvm_backend_and_codegen.md) | LLVM Backend and Code Generation in rustc | L2 | yes | no | 1 | 2 |
| [`concept/06_ecosystem/00_toolchain/10_rustc_driver_and_stable_mir.md`](../../concept/06_ecosystem/00_toolchain/10_rustc_driver_and_stable_mir.md) | rustc Driver, rustc_interface, and Stable MIR | L2 | yes | no | 4 | 2 |
| [`concept/06_ecosystem/00_toolchain/11_compiler_diagnostics_and_ui_tests.md`](../../concept/06_ecosystem/00_toolchain/11_compiler_diagnostics_and_ui_tests.md) | Compiler Diagnostics and UI Tests | L2 | yes | no | 5 | 2 |
| [`concept/06_ecosystem/00_toolchain/12_rustc_bootstrap.md`](../../concept/06_ecosystem/00_toolchain/12_rustc_bootstrap.md) | Bootstrapping the Rust Compiler | L2 | yes | no | 3 | 2 |
| [`concept/06_ecosystem/00_toolchain/13_compiler_testing.md`](../../concept/06_ecosystem/00_toolchain/13_compiler_testing.md) | Testing the Rust Compiler | L2 | yes | no | 0 | 2 |
| [`concept/06_ecosystem/00_toolchain/14_development_tools.md`](../../concept/06_ecosystem/00_toolchain/14_development_tools.md) | Development Tools Ecosystem | L1 | yes | no | 7 | 1 |
| [`concept/06_ecosystem/00_toolchain/15_z_flags_reference.md`](../../concept/06_ecosystem/00_toolchain/15_z_flags_reference.md) | rustc and Cargo `-Z` Unstable Flags Reference | L4 | yes | no | 0 | 1 |
| [`concept/06_ecosystem/00_toolchain/16_rustdoc_internals.md`](../../concept/06_ecosystem/00_toolchain/16_rustdoc_internals.md) | Rustdoc Internals | L4 | yes | no | 15 | 1 |

### 00_traits（4 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/02_intermediate/00_traits/01_traits.md`](../../concept/02_intermediate/00_traits/01_traits.md) | Traits | L2 | yes | no | 76 | 21 |
| [`concept/02_intermediate/00_traits/04_advanced_traits.md`](../../concept/02_intermediate/00_traits/04_advanced_traits.md) | Advanced Traits | L4 | yes | no | 24 | 5 |
| [`concept/02_intermediate/00_traits/05_construction_and_initialization.md`](../../concept/02_intermediate/00_traits/05_construction_and_initialization.md) | Construction and Initialization | L2 | yes | no | 7 | 2 |
| [`concept/02_intermediate/00_traits/06_derive_traits.md`](../../concept/02_intermediate/00_traits/06_derive_traits.md) | Derivable Traits | L2 | yes | no | 12 | 2 |

### 00_type_theory（17 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/04_formal/00_type_theory/01_type_theory.md`](../../concept/04_formal/00_type_theory/01_type_theory.md) | Type Theory | L4 | yes | no | 27 | 3 |
| [`concept/04_formal/00_type_theory/02_subtype_variance.md`](../../concept/04_formal/00_type_theory/02_subtype_variance.md) | Subtype and Variance | L4 | yes | no | 11 | 2 |
| [`concept/04_formal/00_type_theory/03_type_inference.md`](../../concept/04_formal/00_type_theory/03_type_inference.md) | Type Inference | L4 | yes | no | 9 | 2 |
| [`concept/04_formal/00_type_theory/04_category_theory.md`](../../concept/04_formal/00_type_theory/04_category_theory.md) | Category Theory | L4 | yes | no | 11 | 2 |
| [`concept/04_formal/00_type_theory/05_lambda_calculus.md`](../../concept/04_formal/00_type_theory/05_lambda_calculus.md) | Lambda Calculus | L4 | yes | no | 11 | 2 |
| [`concept/04_formal/00_type_theory/06_type_semantics.md`](../../concept/04_formal/00_type_theory/06_type_semantics.md) | Type Semantics | L4 | yes | no | 18 | 2 |
| [`concept/04_formal/00_type_theory/07_type_checking_and_inference.md`](../../concept/04_formal/00_type_theory/07_type_checking_and_inference.md) | Type Checking and Inference in rustc | L2 | yes | yes | 12 | 2 |
| [`concept/04_formal/00_type_theory/08_type_inference_complexity.md`](../../concept/04_formal/00_type_theory/08_type_inference_complexity.md) | Type Inference Complexity | L4 | yes | yes | 8 | 2 |
| [`concept/04_formal/00_type_theory/09_type_system_reference.md`](../../concept/04_formal/00_type_theory/09_type_system_reference.md) | Type System Reference | L2 | yes | yes | 3 | 2 |
| [`concept/04_formal/00_type_theory/10_dependent_refinement_types.md`](../../concept/04_formal/00_type_theory/10_dependent_refinement_types.md) | Dependent Types and Refinement Types | L4 | yes | no | 14 | 1 |
| [`concept/04_formal/00_type_theory/11_formal_design_pattern_theory.md`](../../concept/04_formal/00_type_theory/11_formal_design_pattern_theory.md) | Formal Design Pattern Theory | L4 | yes | no | 18 | 2 |
| [`concept/04_formal/00_type_theory/12_pattern_composition_algebra.md`](../../concept/04_formal/00_type_theory/12_pattern_composition_algebra.md) | Pattern Composition Algebra | L4 | yes | no | 15 | 2 |
| [`concept/04_formal/00_type_theory/13_formal_algorithm_theory.md`](../../concept/04_formal/00_type_theory/13_formal_algorithm_theory.md) | Formal Algorithm Theory | L4 | yes | no | 6 | 1 |
| [`concept/04_formal/00_type_theory/14_flux.md`](../../concept/04_formal/00_type_theory/14_flux.md) | Flux: Liquid Refinement Types for Rust | L4 | yes | no | 17 | 1 |
| [`concept/04_formal/00_type_theory/15_parametricity_and_theorems_for_free.md`](../../concept/04_formal/00_type_theory/15_parametricity_and_theorems_for_free.md) | Parametricity and Theorems for Free | L4 | yes | no | 8 | 1 |
| [`concept/04_formal/00_type_theory/16_expressive_power.md`](../../concept/04_formal/00_type_theory/16_expressive_power.md) | Felleisen Expressive Power | L4 | yes | no | 9 | 1 |
| [`concept/04_formal/00_type_theory/17_system_f.md`](../../concept/04_formal/00_type_theory/17_system_f.md) | System F and Rust Generic Polymorphism | L4 | yes | no | 6 | 1 |

### 00_version_tracking（10 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/07_future/00_version_tracking/01_rust_version_tracking.md`](../../concept/07_future/00_version_tracking/01_rust_version_tracking.md) | Rust Version Tracking | L3 | yes | no | 9 | 13 |
| [`concept/07_future/00_version_tracking/04_nightly_rust.md`](../../concept/07_future/00_version_tracking/04_nightly_rust.md) | How Rust is Made and “Nightly Rust” | L2 | yes | no | 2 | 1 |
| [`concept/07_future/00_version_tracking/feature_domain_matrix_197.md`](../../concept/07_future/00_version_tracking/feature_domain_matrix_197.md) | Rust 1.97.0 Feature × Domain Reverse-Lookup Matrix | L4 | yes | no | 0 | 1 |
| [`concept/07_future/00_version_tracking/rust_1_100_preview.md`](../../concept/07_future/00_version_tracking/rust_1_100_preview.md) | Rust 1.100+ Preview | L2 | yes | no | 0 | 3 |
| [`concept/07_future/00_version_tracking/rust_1_95_stabilized.md`](../../concept/07_future/00_version_tracking/rust_1_95_stabilized.md) | Rust 1.95.0 Stabilized Features | L2 | yes | no | 15 | 3 |
| [`concept/07_future/00_version_tracking/rust_1_96_stabilized.md`](../../concept/07_future/00_version_tracking/rust_1_96_stabilized.md) | Rust 1.96 Stabilized Features (current patch 1.96.1) | L2 | yes | no | 7 | 4 |
| [`concept/07_future/00_version_tracking/rust_1_97_1.md`](../../concept/07_future/00_version_tracking/rust_1_97_1.md) | Rust 1.97.1 Stable Patch | L2 | yes | no | 1 | 2 |
| [`concept/07_future/00_version_tracking/rust_1_97_preview.md`](../../concept/07_future/00_version_tracking/rust_1_97_preview.md) | Rust 1.97.0 Preview Archive | L2 | yes | no | 3 | 1 |
| [`concept/07_future/00_version_tracking/rust_1_97_stabilized.md`](../../concept/07_future/00_version_tracking/rust_1_97_stabilized.md) | Rust 1.97.0 Stabilized Features | L2 | yes | no | 15 | 2 |
| [`concept/07_future/00_version_tracking/rust_1_98_preview.md`](../../concept/07_future/00_version_tracking/rust_1_98_preview.md) | Rust 1.98+ Preview | L2 | yes | no | 8 | 2 |

### 01_async（12 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/03_advanced/01_async/01_async.md`](../../concept/03_advanced/01_async/01_async.md) | Async Programming | L3 | yes | no | 67 | 9 |
| [`concept/03_advanced/01_async/02_async_advanced.md`](../../concept/03_advanced/01_async/02_async_advanced.md) | Async Advanced | L3 | yes | no | 14 | 9 |
| [`concept/03_advanced/01_async/03_async_patterns.md`](../../concept/03_advanced/01_async/03_async_patterns.md) | Async Patterns | L4 | yes | no | 22 | 4 |
| [`concept/03_advanced/01_async/06_async_boundary_panorama.md`](../../concept/03_advanced/01_async/06_async_boundary_panorama.md) | Async Boundary Panorama | L3 | yes | no | 10 | 1 |
| [`concept/03_advanced/01_async/07_async_closures.md`](../../concept/03_advanced/01_async/07_async_closures.md) | Async Closures | L3 | yes | no | 20 | 3 |
| [`concept/03_advanced/01_async/08_pin_unpin.md`](../../concept/03_advanced/01_async/08_pin_unpin.md) | Pin and Unpin | L4 | yes | no | 25 | 3 |
| [`concept/03_advanced/01_async/11_pin_projection_counterexamples.md`](../../concept/03_advanced/01_async/11_pin_projection_counterexamples.md) | Pin Projection Counterexamples | L3 | yes | no | 8 | 1 |
| [`concept/03_advanced/01_async/12_waker_contract_deep_dive.md`](../../concept/03_advanced/01_async/12_waker_contract_deep_dive.md) | Waker Contract Deep Dive | L3 | yes | no | 4 | 1 |
| [`concept/03_advanced/01_async/13_async_trait_object_safety.md`](../../concept/03_advanced/01_async/13_async_trait_object_safety.md) | Async Trait Object Safety | L3 | yes | no | 7 | 1 |
| [`concept/03_advanced/01_async/14_gat_async_boundary.md`](../../concept/03_advanced/01_async/14_gat_async_boundary.md) | Generic Associated Types (GATs) at the Async Boundary | L4 | yes | no | 12 | 2 |
| [`concept/03_advanced/01_async/15_state_machine_semantics.md`](../../concept/03_advanced/01_async/15_state_machine_semantics.md) | State Machine Semantics and Workflow Models | L3 | yes | no | 5 | 2 |
| [`concept/03_advanced/01_async/16_structured_concurrency.md`](../../concept/03_advanced/01_async/16_structured_concurrency.md) | Structured Concurrency | L3 | yes | no | 3 | 1 |

### 01_cargo（23 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/06_ecosystem/01_cargo/01_cargo_script.md`](../../concept/06_ecosystem/01_cargo/01_cargo_script.md) | Cargo Script: Writing and Running Rust Scripts | L2 | yes | no | 12 | 2 |
| [`concept/06_ecosystem/01_cargo/02_public_private_deps.md`](../../concept/06_ecosystem/01_cargo/02_public_private_deps.md) | Cargo `public = true` Dependency Visibility and Resolver v3 | L4 | yes | no | 2 | 0 |
| [`concept/06_ecosystem/01_cargo/03_resolver_v3_public_feature_unification.md`](../../concept/06_ecosystem/01_cargo/03_resolver_v3_public_feature_unification.md) | Resolver v3 and `public = true` Feature-Unification Demo | L3 | yes | no | 0 | 1 |
| [`concept/06_ecosystem/01_cargo/04_cargo_196_features.md`](../../concept/06_ecosystem/01_cargo/04_cargo_196_features.md) | Cargo 1.96 Feature Highlights | L2 | yes | no | 3 | 1 |
| [`concept/06_ecosystem/01_cargo/05_cargo_build_scripts.md`](../../concept/06_ecosystem/01_cargo/05_cargo_build_scripts.md) | Cargo Build Scripts (`build.rs`) | L2 | yes | no | 16 | 2 |
| [`concept/06_ecosystem/01_cargo/06_cargo_dependency_resolution.md`](../../concept/06_ecosystem/01_cargo/06_cargo_dependency_resolution.md) | Cargo Dependency Resolution | L2 | yes | no | 2 | 2 |
| [`concept/06_ecosystem/01_cargo/07_cargo_source_replacement.md`](../../concept/06_ecosystem/01_cargo/07_cargo_source_replacement.md) | Cargo Source Replacement | L2 | yes | no | 0 | 2 |
| [`concept/06_ecosystem/01_cargo/08_cargo_registries_and_publishing.md`](../../concept/06_ecosystem/01_cargo/08_cargo_registries_and_publishing.md) | Cargo Registries and Publishing | L2 | yes | no | 2 | 2 |
| [`concept/06_ecosystem/01_cargo/09_cargo_authentication_and_cache.md`](../../concept/06_ecosystem/01_cargo/09_cargo_authentication_and_cache.md) | Cargo Authentication and Build Cache | L2 | yes | no | 2 | 2 |
| [`concept/06_ecosystem/01_cargo/10_cargo_manifest_reference.md`](../../concept/06_ecosystem/01_cargo/10_cargo_manifest_reference.md) | Cargo Manifest Reference | L2 | yes | no | 2 | 2 |
| [`concept/06_ecosystem/01_cargo/11_cargo_profiles_and_lints.md`](../../concept/06_ecosystem/01_cargo/11_cargo_profiles_and_lints.md) | Cargo Profiles and Lints | L2 | yes | no | 0 | 2 |
| [`concept/06_ecosystem/01_cargo/12_cargo_subcommands_and_plugins.md`](../../concept/06_ecosystem/01_cargo/12_cargo_subcommands_and_plugins.md) | Cargo Subcommands and Plugins | L2 | yes | no | 3 | 2 |
| [`concept/06_ecosystem/01_cargo/13_cargo_security_cves.md`](../../concept/06_ecosystem/01_cargo/13_cargo_security_cves.md) | Cargo Security Advisories: CVE-2026-5222 and CVE-2026-5223 | L2 | yes | no | 2 | 1 |
| [`concept/06_ecosystem/01_cargo/14_cargo_workspaces.md`](../../concept/06_ecosystem/01_cargo/14_cargo_workspaces.md) | Cargo Workspaces | L2 | yes | no | 0 | 1 |
| [`concept/06_ecosystem/01_cargo/15_cargo_getting_started.md`](../../concept/06_ecosystem/01_cargo/15_cargo_getting_started.md) | Cargo Getting Started | L1 | yes | no | 2 | 2 |
| [`concept/06_ecosystem/01_cargo/16_cargo_workflow.md`](../../concept/06_ecosystem/01_cargo/16_cargo_workflow.md) | Cargo Workflow | L2 | yes | no | 2 | 2 |
| [`concept/06_ecosystem/01_cargo/17_cargo_guide_practices.md`](../../concept/06_ecosystem/01_cargo/17_cargo_guide_practices.md) | Cargo Guide Practices | L2 | yes | no | 2 | 2 |
| [`concept/06_ecosystem/01_cargo/18_cargo_configuration.md`](../../concept/06_ecosystem/01_cargo/18_cargo_configuration.md) | Cargo Configuration | L2 | yes | no | 2 | 2 |
| [`concept/06_ecosystem/01_cargo/19_cargo_commands_reference.md`](../../concept/06_ecosystem/01_cargo/19_cargo_commands_reference.md) | Cargo Commands Reference | L2 | yes | no | 2 | 2 |
| [`concept/06_ecosystem/01_cargo/20_cargo_manifest_targets.md`](../../concept/06_ecosystem/01_cargo/20_cargo_manifest_targets.md) | Cargo Manifest Targets | L2 | yes | no | 2 | 2 |
| [`concept/06_ecosystem/01_cargo/21_cargo_registry_internals.md`](../../concept/06_ecosystem/01_cargo/21_cargo_registry_internals.md) | Cargo Registry Internals | L2 | yes | no | 2 | 2 |
| [`concept/06_ecosystem/01_cargo/22_build_std.md`](../../concept/06_ecosystem/01_cargo/22_build_std.md) | Cargo `build-std` | L2 | yes | no | 3 | 2 |
| [`concept/06_ecosystem/01_cargo/23_cargo_197_features.md`](../../concept/06_ecosystem/01_cargo/23_cargo_197_features.md) | Cargo 1.97 Feature Highlights | L2 | yes | no | 2 | 1 |

### 01_edition_roadmap（4 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/07_future/01_edition_roadmap/01_rust_edition_preview.md`](../../concept/07_future/01_edition_roadmap/01_rust_edition_preview.md) | Rust 2024 Edition Preview and Migration Notes | L2 | yes | no | 5 | 1 |
| [`concept/07_future/01_edition_roadmap/02_edition_guide.md`](../../concept/07_future/01_edition_roadmap/02_edition_guide.md) | Edition Guide | L3 | yes | no | 14 | 1 |
| [`concept/07_future/01_edition_roadmap/03_rust_edition_guide.md`](../../concept/07_future/01_edition_roadmap/03_rust_edition_guide.md) | Rust Edition Mechanism and Migration Guide | L2 | no | no | 0 | 1 |
| [`concept/07_future/01_edition_roadmap/04_roadmap.md`](../../concept/07_future/01_edition_roadmap/04_roadmap.md) | Roadmap | L4 | yes | no | 17 | 2 |

### 01_generics（3 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/02_intermediate/01_generics/01_generics.md`](../../concept/02_intermediate/01_generics/01_generics.md) | Generics | L2 | yes | no | 74 | 8 |
| [`concept/02_intermediate/01_generics/02_const_generics.md`](../../concept/02_intermediate/01_generics/02_const_generics.md) | Const Generics — Values as Type Parameters | L2 | yes | no | 15 | 1 |
| [`concept/02_intermediate/01_generics/04_quiz_traits_and_generics.md`](../../concept/02_intermediate/01_generics/04_quiz_traits_and_generics.md) | Traits and Generics (Quiz) | L2 | no | no | 20 | 2 |

### 01_ownership_borrow_lifetime（7 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/01_foundation/01_ownership_borrow_lifetime/00_ownership_borrow_lifetime_knowledge_map.md`](../../concept/01_foundation/01_ownership_borrow_lifetime/00_ownership_borrow_lifetime_knowledge_map.md) | Ownership, Borrowing & Lifetimes Knowledge Map | L2 | yes | no | 0 | 3 |
| [`concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md`](../../concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md) | Ownership | L1 | yes | no | 46 | 16 |
| [`concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md`](../../concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) | Borrowing | L1 | yes | no | 53 | 21 |
| [`concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md`](../../concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) | Lifetimes | L1 | yes | no | 41 | 7 |
| [`concept/01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md`](../../concept/01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md) | Lifetimes Advanced | L1 | yes | yes | 49 | 24 |
| [`concept/01_foundation/01_ownership_borrow_lifetime/05_move_semantics.md`](../../concept/01_foundation/01_ownership_borrow_lifetime/05_move_semantics.md) | Move Semantics | L1 | yes | no | 6 | 2 |
| [`concept/01_foundation/01_ownership_borrow_lifetime/06_ownership_inventories_brown_book.md`](../../concept/01_foundation/01_ownership_borrow_lifetime/06_ownership_inventories_brown_book.md) | Brown University Ownership Inventory | L2 | yes | yes | 3 | 2 |

### 01_ownership_logic（6 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/04_formal/01_ownership_logic/01_linear_logic.md`](../../concept/04_formal/01_ownership_logic/01_linear_logic.md) | Linear and Affine Logic | L4 | yes | no | 13 | 8 |
| [`concept/04_formal/01_ownership_logic/02_ownership_formal.md`](../../concept/04_formal/01_ownership_logic/02_ownership_formal.md) | Ownership Formalization | L4 | yes | no | 17 | 7 |
| [`concept/04_formal/01_ownership_logic/03_linear_logic_applications.md`](../../concept/04_formal/01_ownership_logic/03_linear_logic_applications.md) | Linear Logic Applications | L4 | yes | no | 10 | 2 |
| [`concept/04_formal/01_ownership_logic/04_borrow_checking_decidability.md`](../../concept/04_formal/01_ownership_logic/04_borrow_checking_decidability.md) | Borrow Checking Decidability | L4 | yes | no | 10 | 2 |
| [`concept/04_formal/01_ownership_logic/05_tree_borrows_deep_dive.md`](../../concept/04_formal/01_ownership_logic/05_tree_borrows_deep_dive.md) | Tree Borrows Deep Dive | L4 | yes | no | 3 | 2 |
| [`concept/04_formal/01_ownership_logic/06_behavior_considered_undefined.md`](../../concept/04_formal/01_ownership_logic/06_behavior_considered_undefined.md) | Behavior Considered Undefined | L2 | yes | no | 2 | 2 |

### 01_systems_languages（9 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/05_comparative/01_systems_languages/01_rust_vs_cpp.md`](../../concept/05_comparative/01_systems_languages/01_rust_vs_cpp.md) | Rust vs C++ | L4 | yes | yes | 14 | 2 |
| [`concept/05_comparative/01_systems_languages/02_cpp_abi_object_model.md`](../../concept/05_comparative/01_systems_languages/02_cpp_abi_object_model.md) | C++ Abi Object Model | L4 | yes | no | 18 | 3 |
| [`concept/05_comparative/01_systems_languages/03_rust_vs_go.md`](../../concept/05_comparative/01_systems_languages/03_rust_vs_go.md) | Rust vs Go | L4 | yes | no | 11 | 3 |
| [`concept/05_comparative/01_systems_languages/04_rust_vs_ruby.md`](../../concept/05_comparative/01_systems_languages/04_rust_vs_ruby.md) | Rust vs Ruby | L4 | yes | no | 8 | 2 |
| [`concept/05_comparative/01_systems_languages/05_rust_vs_swift.md`](../../concept/05_comparative/01_systems_languages/05_rust_vs_swift.md) | Rust vs Swift | L4 | yes | no | 6 | 2 |
| [`concept/05_comparative/01_systems_languages/06_rust_vs_zig.md`](../../concept/05_comparative/01_systems_languages/06_rust_vs_zig.md) | Rust vs Zig | L4 | yes | no | 8 | 2 |
| [`concept/05_comparative/01_systems_languages/07_rust_vs_ada_spark.md`](../../concept/05_comparative/01_systems_languages/07_rust_vs_ada_spark.md) | Rust vs Ada/SPARK | L5 | yes | no | 3 | 1 |
| [`concept/05_comparative/01_systems_languages/08_rust_vs_d.md`](../../concept/05_comparative/01_systems_languages/08_rust_vs_d.md) | Rust vs D | L5 | yes | no | 7 | 2 |
| [`concept/05_comparative/01_systems_languages/09_rust_vs_nim.md`](../../concept/05_comparative/01_systems_languages/09_rust_vs_nim.md) | Rust vs Nim | L5 | yes | no | 4 | 1 |

### 01_terminology（2 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/00_meta/01_terminology/01_terminology_glossary.md`](../../concept/00_meta/01_terminology/01_terminology_glossary.md) | Terminology Glossary | L0 | no | no | 0 | 1 |
| [`concept/00_meta/01_terminology/02_bilingual_template_v2.md`](../../concept/00_meta/01_terminology/02_bilingual_template_v2.md) | Bilingual Concept Template v2 | L1 | no | no | 5 | 2 |

### 02_core_crates（1 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/06_ecosystem/02_core_crates/01_core_crates.md`](../../concept/06_ecosystem/02_core_crates/01_core_crates.md) | Core Crates | L2 | yes | yes | 17 | 4 |

### 02_managed_languages（11 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/05_comparative/02_managed_languages/01_rust_vs_java.md`](../../concept/05_comparative/02_managed_languages/01_rust_vs_java.md) | Rust vs Java | L4 | yes | no | 7 | 2 |
| [`concept/05_comparative/02_managed_languages/02_rust_vs_python.md`](../../concept/05_comparative/02_managed_languages/02_rust_vs_python.md) | Rust vs Python | L4 | yes | no | 6 | 2 |
| [`concept/05_comparative/02_managed_languages/03_rust_vs_javascript.md`](../../concept/05_comparative/02_managed_languages/03_rust_vs_javascript.md) | Rust vs JavaScript | L4 | yes | no | 5 | 2 |
| [`concept/05_comparative/02_managed_languages/04_rust_vs_kotlin.md`](../../concept/05_comparative/02_managed_languages/04_rust_vs_kotlin.md) | Rust vs Kotlin | L4 | yes | no | 6 | 2 |
| [`concept/05_comparative/02_managed_languages/05_rust_vs_scala.md`](../../concept/05_comparative/02_managed_languages/05_rust_vs_scala.md) | Rust vs Scala | L4 | yes | no | 6 | 2 |
| [`concept/05_comparative/02_managed_languages/06_rust_vs_csharp.md`](../../concept/05_comparative/02_managed_languages/06_rust_vs_csharp.md) | Rust vs C# | L4 | yes | no | 6 | 2 |
| [`concept/05_comparative/02_managed_languages/07_rust_vs_elixir.md`](../../concept/05_comparative/02_managed_languages/07_rust_vs_elixir.md) | Rust vs Elixir: Concurrency and Fault Tolerance Comparison | L5 | yes | no | 8 | 2 |
| [`concept/05_comparative/02_managed_languages/08_rust_vs_typescript.md`](../../concept/05_comparative/02_managed_languages/08_rust_vs_typescript.md) | Rust vs TypeScript | L4 | yes | no | 6 | 2 |
| [`concept/05_comparative/02_managed_languages/09_rust_vs_haskell.md`](../../concept/05_comparative/02_managed_languages/09_rust_vs_haskell.md) | Rust vs Haskell | L5 | yes | yes | 9 | 1 |
| [`concept/05_comparative/02_managed_languages/10_rust_vs_ocaml.md`](../../concept/05_comparative/02_managed_languages/10_rust_vs_ocaml.md) | Rust vs OCaml: Ownership and Algebraic Effects in Systems an... | L5 | yes | no | 10 | 2 |
| [`concept/05_comparative/02_managed_languages/11_rust_vs_fsharp.md`](../../concept/05_comparative/02_managed_languages/11_rust_vs_fsharp.md) | Rust vs F#: Ownership-Centric Systems Programming vs Functio... | L5 | yes | yes | 7 | 2 |

### 02_memory_management（5 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/02_intermediate/02_memory_management/01_memory_management.md`](../../concept/02_intermediate/02_memory_management/01_memory_management.md) | Memory Management | L2 | yes | no | 57 | 5 |
| [`concept/02_intermediate/02_memory_management/02_interior_mutability.md`](../../concept/02_intermediate/02_memory_management/02_interior_mutability.md) | Interior Mutability | L3 | yes | no | 11 | 3 |
| [`concept/02_intermediate/02_memory_management/03_cow_and_borrowed.md`](../../concept/02_intermediate/02_memory_management/03_cow_and_borrowed.md) | Cow and Borrowed | L3 | yes | no | 8 | 2 |
| [`concept/02_intermediate/02_memory_management/04_smart_pointers.md`](../../concept/02_intermediate/02_memory_management/04_smart_pointers.md) | Smart Pointers | L3 | yes | no | 12 | 3 |
| [`concept/02_intermediate/02_memory_management/05_quiz_memory_management.md`](../../concept/02_intermediate/02_memory_management/05_quiz_memory_management.md) | Memory Management (Quiz) | L2 | no | no | 27 | 2 |

### 02_preview_features（33 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/07_future/02_preview_features/01_effects_system.md`](../../concept/07_future/02_preview_features/01_effects_system.md) | Effect System | L4 | yes | no | 26 | 3 |
| [`concept/07_future/02_preview_features/02_mcdc_coverage_preview.md`](../../concept/07_future/02_preview_features/02_mcdc_coverage_preview.md) | MC/DC Coverage Preview | L4 | yes | no | 6 | 2 |
| [`concept/07_future/02_preview_features/03_safety_tags_preview.md`](../../concept/07_future/02_preview_features/03_safety_tags_preview.md) | Safety Tags Preview | L4 | yes | no | 6 | 2 |
| [`concept/07_future/02_preview_features/04_parallel_frontend_preview.md`](../../concept/07_future/02_preview_features/04_parallel_frontend_preview.md) | Parallel Frontend Preview | L3 | yes | no | 6 | 2 |
| [`concept/07_future/02_preview_features/05_derive_coerce_pointee_preview.md`](../../concept/07_future/02_preview_features/05_derive_coerce_pointee_preview.md) | Derive CoercePointee Preview | L3 | yes | no | 8 | 2 |
| [`concept/07_future/02_preview_features/06_const_trait_impl_preview.md`](../../concept/07_future/02_preview_features/06_const_trait_impl_preview.md) | Const Trait Impl Preview | L3 | yes | no | 7 | 2 |
| [`concept/07_future/02_preview_features/07_stable_abi_preview.md`](../../concept/07_future/02_preview_features/07_stable_abi_preview.md) | Stable Application Binary Interface (ABI) Preview | L2 | yes | no | 4 | 1 |
| [`concept/07_future/02_preview_features/08_inline_const_pattern_preview.md`](../../concept/07_future/02_preview_features/08_inline_const_pattern_preview.md) | Inline Const Pattern Preview | L2 | yes | no | 9 | 1 |
| [`concept/07_future/02_preview_features/09_return_type_notation_preview.md`](../../concept/07_future/02_preview_features/09_return_type_notation_preview.md) | Return Type Notation Preview | L4 | yes | no | 10 | 1 |
| [`concept/07_future/02_preview_features/10_must_not_suspend_preview.md`](../../concept/07_future/02_preview_features/10_must_not_suspend_preview.md) | `must_not_suspend` Lint Preview | L4 | yes | no | 4 | 1 |
| [`concept/07_future/02_preview_features/11_unsafe_fields_preview.md`](../../concept/07_future/02_preview_features/11_unsafe_fields_preview.md) | Unsafe Fields Preview | L4 | yes | no | 8 | 2 |
| [`concept/07_future/02_preview_features/12_ferrocene_preview.md`](../../concept/07_future/02_preview_features/12_ferrocene_preview.md) | Ferrocene: The Delivered Qualified Rust Toolchain for Safety... | L4 | yes | no | 0 | 1 |
| [`concept/07_future/02_preview_features/13_lifetime_capture_preview.md`](../../concept/07_future/02_preview_features/13_lifetime_capture_preview.md) | Precise Lifetime Capture in `impl Trait` Preview | L4 | yes | no | 4 | 1 |
| [`concept/07_future/02_preview_features/14_pin_ergonomics_preview.md`](../../concept/07_future/02_preview_features/14_pin_ergonomics_preview.md) | Pin Ergonomics Preview | L4 | yes | no | 10 | 1 |
| [`concept/07_future/02_preview_features/15_rpitit_preview.md`](../../concept/07_future/02_preview_features/15_rpitit_preview.md) | Return Position Impl Trait In Traits (RPITIT) Preview | L3 | yes | no | 8 | 1 |
| [`concept/07_future/02_preview_features/16_cranelift_backend_preview.md`](../../concept/07_future/02_preview_features/16_cranelift_backend_preview.md) | Cranelift Backend Preview | L3 | yes | no | 9 | 2 |
| [`concept/07_future/02_preview_features/17_type_alias_impl_trait_preview.md`](../../concept/07_future/02_preview_features/17_type_alias_impl_trait_preview.md) | Type Alias Impl Trait (TAIT) Preview | L3 | yes | no | 4 | 1 |
| [`concept/07_future/02_preview_features/18_arbitrary_self_types_preview.md`](../../concept/07_future/02_preview_features/18_arbitrary_self_types_preview.md) | Arbitrary Self Types Preview | L4 | yes | no | 11 | 2 |
| [`concept/07_future/02_preview_features/20_ergonomic_ref_counting_preview.md`](../../concept/07_future/02_preview_features/20_ergonomic_ref_counting_preview.md) | Ergonomic Ref Counting Preview | L4 | yes | no | 7 | 2 |
| [`concept/07_future/02_preview_features/21_rust_specification_preview.md`](../../concept/07_future/02_preview_features/21_rust_specification_preview.md) | Rust Specification Preview | L4 | yes | no | 6 | 2 |
| [`concept/07_future/02_preview_features/22_async_drop_preview.md`](../../concept/07_future/02_preview_features/22_async_drop_preview.md) | Async Drop Preview | L4 | yes | no | 7 | 2 |
| [`concept/07_future/02_preview_features/23_field_projections_preview.md`](../../concept/07_future/02_preview_features/23_field_projections_preview.md) | Field Projections Preview | L4 | yes | no | 10 | 2 |
| [`concept/07_future/02_preview_features/24_borrow_sanitizer.md`](../../concept/07_future/02_preview_features/24_borrow_sanitizer.md) | BorrowSanitizer (BSan) — Dynamic aliasing rule verification ... | L4 | yes | no | 4 | 2 |
| [`concept/07_future/02_preview_features/26_std_autodiff_preview.md`](../../concept/07_future/02_preview_features/26_std_autodiff_preview.md) | Std Autodiff Preview | L5 | yes | no | 7 | 2 |
| [`concept/07_future/02_preview_features/27_cargo_semver_checks_preview.md`](../../concept/07_future/02_preview_features/27_cargo_semver_checks_preview.md) | Cargo SemVer Checks Preview | L4 | yes | no | 2 | 1 |
| [`concept/07_future/02_preview_features/28_wasm_target_evolution.md`](../../concept/07_future/02_preview_features/28_wasm_target_evolution.md) | WebAssembly Target Evolution Preview | L2 | yes | no | 1 | 1 |
| [`concept/07_future/02_preview_features/29_aarch64_sve_sme_preview.md`](../../concept/07_future/02_preview_features/29_aarch64_sve_sme_preview.md) | Aarch64 Sve Sme Preview | L4 | yes | no | 5 | 1 |
| [`concept/07_future/02_preview_features/30_rust_in_space.md`](../../concept/07_future/02_preview_features/30_rust_in_space.md) | Rust in Space Preview | L4 | yes | no | 4 | 1 |
| [`concept/07_future/02_preview_features/31_specialization_preview.md`](../../concept/07_future/02_preview_features/31_specialization_preview.md) | Specialization Preview | L4 | yes | no | 8 | 2 |
| [`concept/07_future/02_preview_features/32_compile_time_execution.md`](../../concept/07_future/02_preview_features/32_compile_time_execution.md) | Compile Time Execution | L4 | yes | no | 6 | 2 |
| [`concept/07_future/02_preview_features/33_autoverus_preview.md`](../../concept/07_future/02_preview_features/33_autoverus_preview.md) | AutoVerus / Verus Preview Tracking | L7 | yes | no | 2 | 1 |
| [`concept/07_future/02_preview_features/34_open_enums_preview.md`](../../concept/07_future/02_preview_features/34_open_enums_preview.md) | Open Enums Preview | L4 | yes | no | 13 | 2 |
| [`concept/07_future/02_preview_features/36_unsafe_pinned_preview.md`](../../concept/07_future/02_preview_features/36_unsafe_pinned_preview.md) | UnsafePinned Preview | L4 | yes | no | 3 | 2 |

### 02_separation_logic（4 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/04_formal/02_separation_logic/01_rustbelt.md`](../../concept/04_formal/02_separation_logic/01_rustbelt.md) | RustBelt and Verification Toolchain | L4 | yes | no | 16 | 10 |
| [`concept/04_formal/02_separation_logic/02_separation_logic.md`](../../concept/04_formal/02_separation_logic/02_separation_logic.md) | Separation Logic | L5 | yes | no | 10 | 2 |
| [`concept/04_formal/02_separation_logic/03_safety_tags_in_formal.md`](../../concept/04_formal/02_separation_logic/03_safety_tags_in_formal.md) | Safety Tags in Formal Verification — Redirect Stub | L4 | no | no | 0 | 1 |
| [`concept/04_formal/02_separation_logic/04_borrow_sanitizer_in_formal.md`](../../concept/04_formal/02_separation_logic/04_borrow_sanitizer_in_formal.md) | BorrowSanitizer: Runtime Tree Borrows Violation Detection | L4 | yes | no | 0 | 2 |

### 02_sources（5 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/00_meta/02_sources/01_authority_source_map.md`](../../concept/00_meta/02_sources/01_authority_source_map.md) | Authority Source Map | L4 | no | no | 0 | 2 |
| [`concept/00_meta/02_sources/02_rustbelt_predicate_map.md`](../../concept/00_meta/02_sources/02_rustbelt_predicate_map.md) | RustBelt Predicate Map | L4 | yes | no | 0 | 1 |
| [`concept/00_meta/02_sources/03_sources.md`](../../concept/00_meta/02_sources/03_sources.md) | Sources | L3 | yes | no | 0 | 2 |
| [`concept/00_meta/02_sources/04_topic_authority_alignment_map.md`](../../concept/00_meta/02_sources/04_topic_authority_alignment_map.md) | Topic-Authority Alignment Map | L0 | no | no | 0 | 2 |
| [`concept/00_meta/02_sources/05_international_authority_index.md`](../../concept/00_meta/02_sources/05_international_authority_index.md) | International Authority Index | L2 | no | no | 0 | 1 |

### 02_type_system（5 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/01_foundation/02_type_system/01_type_system.md`](../../concept/01_foundation/02_type_system/01_type_system.md) | Type System Basics | L1 | yes | no | 63 | 29 |
| [`concept/01_foundation/02_type_system/02_never_type.md`](../../concept/01_foundation/02_type_system/02_never_type.md) | Never Type | L3 | yes | yes | 16 | 2 |
| [`concept/01_foundation/02_type_system/03_numerics.md`](../../concept/01_foundation/02_type_system/03_numerics.md) | Numerics | L1 | yes | no | 19 | 2 |
| [`concept/01_foundation/02_type_system/04_coercion_and_casting.md`](../../concept/01_foundation/02_type_system/04_coercion_and_casting.md) | Coercion and Casting | L2 | yes | no | 18 | 4 |
| [`concept/01_foundation/02_type_system/05_data_abstraction_spectrum.md`](../../concept/01_foundation/02_type_system/05_data_abstraction_spectrum.md) | Data Abstraction Spectrum | L1 | yes | yes | 14 | 2 |

### 02_unsafe（8 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/03_advanced/02_unsafe/00_before_formal.md`](../../concept/03_advanced/02_unsafe/00_before_formal.md) | Formal Methods: Before Entering L4 | L3 | yes | no | 0 | 2 |
| [`concept/03_advanced/02_unsafe/01_unsafe.md`](../../concept/03_advanced/02_unsafe/01_unsafe.md) | Safe and Effective Unsafe Rust | L3 | yes | no | 61 | 37 |
| [`concept/03_advanced/02_unsafe/02_unsafe_boundary_panorama.md`](../../concept/03_advanced/02_unsafe/02_unsafe_boundary_panorama.md) | Unsafe Boundary Panorama | L3 | yes | no | 12 | 1 |
| [`concept/03_advanced/02_unsafe/03_nll_and_polonius.md`](../../concept/03_advanced/02_unsafe/03_nll_and_polonius.md) | NLL and Polonius | L4 | yes | no | 13 | 3 |
| [`concept/03_advanced/02_unsafe/04_unsafe_rust_patterns.md`](../../concept/03_advanced/02_unsafe/04_unsafe_rust_patterns.md) | Unsafe Rust Patterns | L3 | yes | yes | 2 | 2 |
| [`concept/03_advanced/02_unsafe/05_quiz_unsafe.md`](../../concept/03_advanced/02_unsafe/05_quiz_unsafe.md) | Unsafe Rust (Quiz) | L4 | no | no | 21 | 2 |
| [`concept/03_advanced/02_unsafe/06_memory_model.md`](../../concept/03_advanced/02_unsafe/06_memory_model.md) | Memory Model | L2 | yes | yes | 9 | 2 |
| [`concept/03_advanced/02_unsafe/07_unsafe_reference.md`](../../concept/03_advanced/02_unsafe/07_unsafe_reference.md) | Unsafe Reference | L2 | yes | yes | 6 | 2 |

### 03_audit（4 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/00_meta/03_audit/02_asp_marking_guide.md`](../../concept/00_meta/03_audit/02_asp_marking_guide.md) | Asp Marking Guide | L2 | yes | no | 0 | 1 |
| [`concept/00_meta/03_audit/03_audit_checklist.md`](../../concept/00_meta/03_audit/03_audit_checklist.md) | Audit Checklist | L3 | no | no | 0 | 2 |
| [`concept/00_meta/03_audit/06_grading_system.md`](../../concept/00_meta/03_audit/06_grading_system.md) | Grading System | — | no | no | 0 | 1 |
| [`concept/00_meta/03_audit/07_quality_dashboard_v2.md`](../../concept/00_meta/03_audit/07_quality_dashboard_v2.md) | Quality Dashboard V2 | — | no | no | 0 | 1 |

### 03_design_patterns（19 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/06_ecosystem/03_design_patterns/01_patterns.md`](../../concept/06_ecosystem/03_design_patterns/01_patterns.md) | Design Patterns Overview | L3 | yes | no | 47 | 12 |
| [`concept/06_ecosystem/03_design_patterns/02_idioms_spectrum.md`](../../concept/06_ecosystem/03_design_patterns/02_idioms_spectrum.md) | Idioms Spectrum | L3 | yes | no | 37 | 3 |
| [`concept/06_ecosystem/03_design_patterns/03_system_design_principles.md`](../../concept/06_ecosystem/03_design_patterns/03_system_design_principles.md) | System Design Principles | L5 | yes | no | 10 | 3 |
| [`concept/06_ecosystem/03_design_patterns/04_system_composability.md`](../../concept/06_ecosystem/03_design_patterns/04_system_composability.md) | System Composability | L5 | yes | no | 23 | 3 |
| [`concept/06_ecosystem/03_design_patterns/05_microservice_patterns.md`](../../concept/06_ecosystem/03_design_patterns/05_microservice_patterns.md) | Microservice Patterns | L3 | yes | no | 15 | 2 |
| [`concept/06_ecosystem/03_design_patterns/06_event_driven_architecture.md`](../../concept/06_ecosystem/03_design_patterns/06_event_driven_architecture.md) | Event Driven Architecture | L3 | yes | no | 15 | 2 |
| [`concept/06_ecosystem/03_design_patterns/07_cqrs_event_sourcing.md`](../../concept/06_ecosystem/03_design_patterns/07_cqrs_event_sourcing.md) | Cqrs Event Sourcing | L4 | yes | no | 20 | 1 |
| [`concept/06_ecosystem/03_design_patterns/08_architecture_patterns.md`](../../concept/06_ecosystem/03_design_patterns/08_architecture_patterns.md) | Architecture Patterns | L4 | yes | no | 13 | 2 |
| [`concept/06_ecosystem/03_design_patterns/09_pattern_implementation_comparison.md`](../../concept/06_ecosystem/03_design_patterns/09_pattern_implementation_comparison.md) | Pattern Implementation Comparison | L4 | yes | no | 19 | 3 |
| [`concept/06_ecosystem/03_design_patterns/10_pattern_selection_best_practices.md`](../../concept/06_ecosystem/03_design_patterns/10_pattern_selection_best_practices.md) | Pattern Selection Best Practices | L4 | yes | no | 13 | 2 |
| [`concept/06_ecosystem/03_design_patterns/11_formal_design_pattern_theory.md`](../../concept/06_ecosystem/03_design_patterns/11_formal_design_pattern_theory.md) | Formal Design Pattern Theory (Redirect Stub) | L0 | no | no | 0 | 1 |
| [`concept/06_ecosystem/03_design_patterns/12_frontier_research_and_innovative_patterns.md`](../../concept/06_ecosystem/03_design_patterns/12_frontier_research_and_innovative_patterns.md) | Frontier Research and Innovative Patterns | L4 | yes | no | 19 | 2 |
| [`concept/06_ecosystem/03_design_patterns/13_engineering_and_production_patterns.md`](../../concept/06_ecosystem/03_design_patterns/13_engineering_and_production_patterns.md) | Engineering Practice and Production-Grade Patterns | L5 | yes | no | 9 | 1 |
| [`concept/06_ecosystem/03_design_patterns/14_design_patterns_glossary.md`](../../concept/06_ecosystem/03_design_patterns/14_design_patterns_glossary.md) | Design Patterns Glossary | L1 | yes | no | 6 | 2 |
| [`concept/06_ecosystem/03_design_patterns/15_design_patterns_faq.md`](../../concept/06_ecosystem/03_design_patterns/15_design_patterns_faq.md) | Design Patterns FAQ | L2 | yes | no | 5 | 3 |
| [`concept/06_ecosystem/03_design_patterns/16_pattern_composition_algebra.md`](../../concept/06_ecosystem/03_design_patterns/16_pattern_composition_algebra.md) | Pattern Composition Algebra (Redirect Stub) | L0 | no | no | 0 | 1 |
| [`concept/06_ecosystem/03_design_patterns/17_workflow_theory.md`](../../concept/06_ecosystem/03_design_patterns/17_workflow_theory.md) | Workflow Theory & Formalization | L4 | yes | no | 17 | 1 |
| [`concept/06_ecosystem/03_design_patterns/18_api_design_patterns.md`](../../concept/06_ecosystem/03_design_patterns/18_api_design_patterns.md) | API Design Patterns | L3 | yes | no | 21 | 2 |
| [`concept/06_ecosystem/03_design_patterns/19_model_driven_engineering.md`](../../concept/06_ecosystem/03_design_patterns/19_model_driven_engineering.md) | Model-Driven Engineering | L5 | yes | no | 5 | 1 |

### 03_domain_comparisons（2 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/05_comparative/03_domain_comparisons/01_safety_boundaries.md`](../../concept/05_comparative/03_domain_comparisons/01_safety_boundaries.md) | Safety Boundaries | L4 | yes | yes | 9 | 4 |
| [`concept/05_comparative/03_domain_comparisons/02_quiz_rust_vs_systems.md`](../../concept/05_comparative/03_domain_comparisons/02_quiz_rust_vs_systems.md) | Quiz Rust Vs Systems | L4 | no | no | 14 | 2 |

### 03_error_handling（4 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/02_intermediate/03_error_handling/01_error_handling.md`](../../concept/02_intermediate/03_error_handling/01_error_handling.md) | Error Handling Intermediate | L2 | yes | no | 63 | 10 |
| [`concept/02_intermediate/03_error_handling/02_error_handling_deep_dive.md`](../../concept/02_intermediate/03_error_handling/02_error_handling_deep_dive.md) | Error Handling Deep Dive | L3 | yes | no | 9 | 2 |
| [`concept/02_intermediate/03_error_handling/03_panic.md`](../../concept/02_intermediate/03_error_handling/03_panic.md) | Panic | L2 | yes | no | 4 | 2 |
| [`concept/02_intermediate/03_error_handling/04_exception_safety_rust_cpp.md`](../../concept/02_intermediate/03_error_handling/04_exception_safety_rust_cpp.md) | Exception Safety: C++ vs Rust | L2 | yes | no | 6 | 2 |

### 03_operational_semantics（9 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/04_formal/03_operational_semantics/01_denotational_semantics.md`](../../concept/04_formal/03_operational_semantics/01_denotational_semantics.md) | Denotational Semantics | L4 | yes | no | 9 | 2 |
| [`concept/04_formal/03_operational_semantics/02_hoare_logic.md`](../../concept/04_formal/03_operational_semantics/02_hoare_logic.md) | Hoare Logic | L4 | yes | no | 8 | 2 |
| [`concept/04_formal/03_operational_semantics/03_operational_semantics.md`](../../concept/04_formal/03_operational_semantics/03_operational_semantics.md) | Operational Semantics | L4 | yes | no | 13 | 2 |
| [`concept/04_formal/03_operational_semantics/04_evaluation_strategies.md`](../../concept/04_formal/03_operational_semantics/04_evaluation_strategies.md) | Evaluation Strategies | L4 | yes | no | 14 | 2 |
| [`concept/04_formal/03_operational_semantics/05_axiomatic_semantics.md`](../../concept/04_formal/03_operational_semantics/05_axiomatic_semantics.md) | Axiomatic Semantics | L4 | yes | no | 15 | 2 |
| [`concept/04_formal/03_operational_semantics/06_observational_equivalence.md`](../../concept/04_formal/03_operational_semantics/06_observational_equivalence.md) | Observational Equivalence | L4 | yes | no | 8 | 1 |
| [`concept/04_formal/03_operational_semantics/07_aeneas_symbolic_semantics.md`](../../concept/04_formal/03_operational_semantics/07_aeneas_symbolic_semantics.md) | Aeneas Symbolic Semantics | L4 | yes | no | 4 | 2 |
| [`concept/04_formal/03_operational_semantics/08_constant_evaluation.md`](../../concept/04_formal/03_operational_semantics/08_constant_evaluation.md) | Constant Evaluation | L2 | yes | no | 6 | 2 |
| [`concept/04_formal/03_operational_semantics/09_llvm_ir_poison_ub.md`](../../concept/04_formal/03_operational_semantics/09_llvm_ir_poison_ub.md) | Poison, Undefined Behavior, and Freeze in LLVM IR | L4 | yes | no | 0 | 1 |

### 03_values_and_references（3 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/01_foundation/03_values_and_references/01_reference_semantics.md`](../../concept/01_foundation/03_values_and_references/01_reference_semantics.md) | Reference Semantics | L2 | yes | no | 35 | 3 |
| [`concept/01_foundation/03_values_and_references/02_value_vs_reference_semantics.md`](../../concept/01_foundation/03_values_and_references/02_value_vs_reference_semantics.md) | Value Semantics vs Reference Semantics | L1 | yes | yes | 5 | 2 |
| [`concept/01_foundation/03_values_and_references/03_variable_model.md`](../../concept/01_foundation/03_values_and_references/03_variable_model.md) | Variable Model | L1 | yes | yes | 12 | 2 |

### 04_control_flow（2 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/01_foundation/04_control_flow/02_patterns.md`](../../concept/01_foundation/04_control_flow/02_patterns.md) | Patterns | L2 | yes | yes | 14 | 2 |
| [`concept/01_foundation/04_control_flow/04_statements_and_expressions.md`](../../concept/01_foundation/04_control_flow/04_statements_and_expressions.md) | Statements and Expressions | L2 | yes | yes | 7 | 2 |

### 04_ffi（2 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/03_advanced/04_ffi/01_rust_ffi.md`](../../concept/03_advanced/04_ffi/01_rust_ffi.md) | Rust FFI | L4 | yes | no | 18 | 4 |
| [`concept/03_advanced/04_ffi/02_ffi_advanced.md`](../../concept/03_advanced/04_ffi/02_ffi_advanced.md) | FFI Advanced Topics | L4 | yes | no | 12 | 2 |

### 04_model_checking（11 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/04_formal/04_model_checking/01_verification_toolchain.md`](../../concept/04_formal/04_model_checking/01_verification_toolchain.md) | Verification Toolchain | L3 | yes | no | 17 | 5 |
| [`concept/04_formal/04_model_checking/02_formal_methods.md`](../../concept/04_formal/04_model_checking/02_formal_methods.md) | Formal Methods (Merged Redirect) | L4 | no | no | 0 | 1 |
| [`concept/04_formal/04_model_checking/03_aerospace_certification_formal_methods.md`](../../concept/04_formal/04_model_checking/03_aerospace_certification_formal_methods.md) | Aerospace Certification & Formal Methods | L4 | yes | no | 7 | 2 |
| [`concept/04_formal/04_model_checking/04_modern_verification_tools.md`](../../concept/04_formal/04_model_checking/04_modern_verification_tools.md) | Modern Verification Tools | L4 | yes | no | 10 | 2 |
| [`concept/04_formal/04_model_checking/05_programming_language_foundations.md`](../../concept/04_formal/04_model_checking/05_programming_language_foundations.md) | Programming Language Foundations | L5 | yes | no | 12 | 2 |
| [`concept/04_formal/04_model_checking/06_quiz_formal_methods.md`](../../concept/04_formal/04_model_checking/06_quiz_formal_methods.md) | Formal Methods (Quiz) | L4 | yes | no | 10 | 2 |
| [`concept/04_formal/04_model_checking/07_autoverus.md`](../../concept/04_formal/04_model_checking/07_autoverus.md) | AutoVerus and Verus Automated Verification Ecosystem | L4 | yes | no | 2 | 2 |
| [`concept/04_formal/04_model_checking/08_miri.md`](../../concept/04_formal/04_model_checking/08_miri.md) | Miri: Rust Undefined Behavior Detector | L2 | yes | no | 4 | 2 |
| [`concept/04_formal/04_model_checking/09_kani.md`](../../concept/04_formal/04_model_checking/09_kani.md) | Kani: Rust Bounded Model Checker | L2 | yes | no | 11 | 2 |
| [`concept/04_formal/04_model_checking/10_certified_toolchains_and_packages.md`](../../concept/04_formal/04_model_checking/10_certified_toolchains_and_packages.md) | Certified Toolchains and Certified Package Inventory | L4 | yes | no | 2 | 1 |
| [`concept/04_formal/04_model_checking/11_creusot.md`](../../concept/04_formal/04_model_checking/11_creusot.md) | Creusot: Rust Deductive Verifier on Why3 | L4 | yes | no | 11 | 2 |

### 04_navigation（9 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/00_meta/04_navigation/03_concept_index.md`](../../concept/00_meta/04_navigation/03_concept_index.md) | Concept Index | L3 | no | no | 0 | 2 |
| [`concept/00_meta/04_navigation/04_inter_layer_map.md`](../../concept/00_meta/04_navigation/04_inter_layer_map.md) | Inter Layer Map | L4 | no | no | 0 | 2 |
| [`concept/00_meta/04_navigation/06_intra_layer_model_map.md`](../../concept/00_meta/04_navigation/06_intra_layer_model_map.md) | Intra Layer Model Map | — | no | no | 0 | 1 |
| [`concept/00_meta/04_navigation/07_learning_guide.md`](../../concept/00_meta/04_navigation/07_learning_guide.md) | Learning Guide | L3 | no | no | 0 | 3 |
| [`concept/00_meta/04_navigation/09_navigation.md`](../../concept/00_meta/04_navigation/09_navigation.md) | Navigation | L3 | no | no | 0 | 3 |
| [`concept/00_meta/04_navigation/10_problem_graph.md`](../../concept/00_meta/04_navigation/10_problem_graph.md) | Problem Graph | L4 | yes | no | 0 | 1 |
| [`concept/00_meta/04_navigation/12_self_assessment.md`](../../concept/00_meta/04_navigation/12_self_assessment.md) | Self Assessment | L3 | no | no | 57 | 5 |
| [`concept/00_meta/04_navigation/13_foundations_gap_closure_index.md`](../../concept/00_meta/04_navigation/13_foundations_gap_closure_index.md) | Foundations Gap Closure Index | L0 | no | no | 0 | 1 |
| [`concept/00_meta/04_navigation/15_quiz_registry.md`](../../concept/00_meta/04_navigation/15_quiz_registry.md) | Quiz Registry — Human-readable index of all assessment asset... | L0 | no | no | 0 | 1 |

### 04_research_and_experimental（10 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/07_future/04_research_and_experimental/01_ai_integration.md`](../../concept/07_future/04_research_and_experimental/01_ai_integration.md) | AI Integration | L4 | yes | no | 9 | 2 |
| [`concept/07_future/04_research_and_experimental/02_formal_methods.md`](../../concept/07_future/04_research_and_experimental/02_formal_methods.md) | Formal Methods Industrialization | L5 | yes | yes | 9 | 4 |
| [`concept/07_future/04_research_and_experimental/03_evolution.md`](../../concept/07_future/04_research_and_experimental/03_evolution.md) | Evolution | L4 | yes | yes | 19 | 6 |
| [`concept/07_future/04_research_and_experimental/04_rust_for_linux.md`](../../concept/07_future/04_research_and_experimental/04_rust_for_linux.md) | Operating Systems | L4 | yes | no | 11 | 11 |
| [`concept/07_future/04_research_and_experimental/05_rust_in_ai.md`](../../concept/07_future/04_research_and_experimental/05_rust_in_ai.md) | Rust In AI | L4 | yes | no | 7 | 2 |
| [`concept/07_future/04_research_and_experimental/06_rust_for_webassembly.md`](../../concept/07_future/04_research_and_experimental/06_rust_for_webassembly.md) | Rust for WebAssembly Research | L3 | yes | no | 11 | 2 |
| [`concept/07_future/04_research_and_experimental/07_ebpf_rust.md`](../../concept/07_future/04_research_and_experimental/07_ebpf_rust.md) | eBPF Rust | L5 | yes | no | 15 | 2 |
| [`concept/07_future/04_research_and_experimental/08_llm_system_architecture.md`](../../concept/07_future/04_research_and_experimental/08_llm_system_architecture.md) | LLM System Architecture | L5 | yes | no | 5 | 2 |
| [`concept/07_future/04_research_and_experimental/11_rust_for_ai_model_serving.md`](../../concept/07_future/04_research_and_experimental/11_rust_for_ai_model_serving.md) | Rust for AI Model Serving and Inference Systems | L5 | yes | no | 3 | 1 |
| [`concept/07_future/04_research_and_experimental/README.md`](../../concept/07_future/04_research_and_experimental/README.md) | L7 Research and Experimental | L5 | no | no | 0 | 2 |

### 04_types_and_conversions（5 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/02_intermediate/04_types_and_conversions/01_range_types.md`](../../concept/02_intermediate/04_types_and_conversions/01_range_types.md) | Range Types | L2 | yes | no | 12 | 2 |
| [`concept/02_intermediate/04_types_and_conversions/02_closure_types.md`](../../concept/02_intermediate/04_types_and_conversions/02_closure_types.md) | Closure Types | L2 | yes | no | 17 | 2 |
| [`concept/02_intermediate/04_types_and_conversions/03_newtype_and_wrapper.md`](../../concept/02_intermediate/04_types_and_conversions/03_newtype_and_wrapper.md) | Newtype and Wrapper Types | L3 | yes | no | 12 | 2 |
| [`concept/02_intermediate/04_types_and_conversions/04_type_system_advanced.md`](../../concept/02_intermediate/04_types_and_conversions/04_type_system_advanced.md) | Type System Advanced | L4 | yes | no | 18 | 2 |
| [`concept/02_intermediate/04_types_and_conversions/05_rtti_and_dynamic_typing.md`](../../concept/02_intermediate/04_types_and_conversions/05_rtti_and_dynamic_typing.md) | RTTI and Dynamic Type Identification | L2 | yes | no | 7 | 2 |

### 04_web_and_networking（10 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/06_ecosystem/04_web_and_networking/01_distributed_systems.md`](../../concept/06_ecosystem/04_web_and_networking/01_distributed_systems.md) | Distributed Systems | L3 | yes | no | 9 | 2 |
| [`concept/06_ecosystem/04_web_and_networking/02_cloud_native.md`](../../concept/06_ecosystem/04_web_and_networking/02_cloud_native.md) | Cloud Native | L3 | yes | no | 8 | 2 |
| [`concept/06_ecosystem/04_web_and_networking/03_web_frameworks.md`](../../concept/06_ecosystem/04_web_and_networking/03_web_frameworks.md) | Web Frameworks | L3 | yes | no | 11 | 3 |
| [`concept/06_ecosystem/04_web_and_networking/04_http_client_development.md`](../../concept/06_ecosystem/04_web_and_networking/04_http_client_development.md) | HTTP Client Development in Rust | L5 | yes | no | 10 | 1 |
| [`concept/06_ecosystem/04_web_and_networking/05_glommio_and_thread_per_core.md`](../../concept/06_ecosystem/04_web_and_networking/05_glommio_and_thread_per_core.md) | Glommio and Thread-per-Core Async Runtimes | L4 | yes | no | 7 | 1 |
| [`concept/06_ecosystem/04_web_and_networking/06_websocket_realtime_communication.md`](../../concept/06_ecosystem/04_web_and_networking/06_websocket_realtime_communication.md) | WebSocket Real-Time Communication | L2 | yes | no | 12 | 3 |
| [`concept/06_ecosystem/04_web_and_networking/07_network_protocols.md`](../../concept/06_ecosystem/04_web_and_networking/07_network_protocols.md) | Network Protocols | L3 | yes | no | 9 | 2 |
| [`concept/06_ecosystem/04_web_and_networking/08_high_performance_network_service_architecture.md`](../../concept/06_ecosystem/04_web_and_networking/08_high_performance_network_service_architecture.md) | High-Performance Network Service Architecture | L4 | yes | no | 21 | 3 |
| [`concept/06_ecosystem/04_web_and_networking/09_reactive_programming.md`](../../concept/06_ecosystem/04_web_and_networking/09_reactive_programming.md) | Reactive Programming | L2 | yes | no | 14 | 2 |
| [`concept/06_ecosystem/04_web_and_networking/10_tokio_runtime_internals.md`](../../concept/06_ecosystem/04_web_and_networking/10_tokio_runtime_internals.md) | Tokio Runtime Internals | L3 | yes | no | 8 | 1 |

### 05_collections（2 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/01_foundation/05_collections/01_collections.md`](../../concept/01_foundation/05_collections/01_collections.md) | Collections | L2 | yes | no | 16 | 2 |
| [`concept/01_foundation/05_collections/02_collections_advanced.md`](../../concept/01_foundation/05_collections/02_collections_advanced.md) | Collections Advanced | L4 | yes | no | 11 | 2 |

### 05_modules_and_visibility（3 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/02_intermediate/05_modules_and_visibility/01_module_system.md`](../../concept/02_intermediate/05_modules_and_visibility/01_module_system.md) | Module System Advanced | L3 | yes | no | 15 | 2 |
| [`concept/02_intermediate/05_modules_and_visibility/02_friend_vs_module_privacy.md`](../../concept/02_intermediate/05_modules_and_visibility/02_friend_vs_module_privacy.md) | Friend vs Module Privacy | L2 | yes | no | 5 | 2 |
| [`concept/02_intermediate/05_modules_and_visibility/03_api_naming_conventions.md`](../../concept/02_intermediate/05_modules_and_visibility/03_api_naming_conventions.md) | Idiomatic Rust API Naming Conventions | L2 | yes | no | 17 | 2 |

### 05_rustc_internals（17 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/04_formal/05_rustc_internals/01_rustc_query_system.md`](../../concept/04_formal/05_rustc_internals/01_rustc_query_system.md) | The Rustc Query System and Incremental Compilation | L2 | yes | no | 5 | 2 |
| [`concept/04_formal/05_rustc_internals/02_mir_codegen_llvm_primer.md`](../../concept/04_formal/05_rustc_internals/02_mir_codegen_llvm_primer.md) | MIR, Codegen, and LLVM IR Primer | L2 | yes | yes | 3 | 2 |
| [`concept/04_formal/05_rustc_internals/03_trait_solver_in_rustc.md`](../../concept/04_formal/05_rustc_internals/03_trait_solver_in_rustc.md) | The Trait Solver in rustc | L2 | yes | no | 10 | 2 |
| [`concept/04_formal/05_rustc_internals/04_name_resolution_and_hir.md`](../../concept/04_formal/05_rustc_internals/04_name_resolution_and_hir.md) | Name Resolution and HIR in rustc | L2 | yes | no | 7 | 2 |
| [`concept/04_formal/05_rustc_internals/05_application_binary_interface.md`](../../concept/04_formal/05_rustc_internals/05_application_binary_interface.md) | Application Binary Interface | L2 | yes | no | 8 | 2 |
| [`concept/04_formal/05_rustc_internals/06_names_and_resolution.md`](../../concept/04_formal/05_rustc_internals/06_names_and_resolution.md) | Names, Scopes and Resolution | L2 | yes | yes | 4 | 2 |
| [`concept/04_formal/05_rustc_internals/07_special_types_and_traits.md`](../../concept/04_formal/05_rustc_internals/07_special_types_and_traits.md) | Special Types and Traits | L2 | yes | no | 2 | 2 |
| [`concept/04_formal/05_rustc_internals/08_type_layout.md`](../../concept/04_formal/05_rustc_internals/08_type_layout.md) | Type Layout | L2 | yes | no | 6 | 2 |
| [`concept/04_formal/05_rustc_internals/09_destructors.md`](../../concept/04_formal/05_rustc_internals/09_destructors.md) | Destructors | L2 | yes | no | 5 | 2 |
| [`concept/04_formal/05_rustc_internals/10_lexical_structure.md`](../../concept/04_formal/05_rustc_internals/10_lexical_structure.md) | Lexical Structure | L2 | yes | yes | 8 | 2 |
| [`concept/04_formal/05_rustc_internals/11_items_reference.md`](../../concept/04_formal/05_rustc_internals/11_items_reference.md) | Items Reference | L2 | yes | yes | 11 | 2 |
| [`concept/04_formal/05_rustc_internals/12_attributes.md`](../../concept/04_formal/05_rustc_internals/12_attributes.md) | Attributes | L2 | yes | yes | 7 | 2 |
| [`concept/04_formal/05_rustc_internals/13_statements_and_expressions_reference.md`](../../concept/04_formal/05_rustc_internals/13_statements_and_expressions_reference.md) | Statements and Expressions Reference | L2 | yes | yes | 7 | 2 |
| [`concept/04_formal/05_rustc_internals/14_patterns_reference.md`](../../concept/04_formal/05_rustc_internals/14_patterns_reference.md) | Patterns Reference | L2 | yes | yes | 6 | 2 |
| [`concept/04_formal/05_rustc_internals/15_generics_compiler_behavior.md`](../../concept/04_formal/05_rustc_internals/15_generics_compiler_behavior.md) | Generics Compiler Behavior | L4 | yes | yes | 7 | 2 |
| [`concept/04_formal/05_rustc_internals/16_names_reference.md`](../../concept/04_formal/05_rustc_internals/16_names_reference.md) | Names Reference | L2 | yes | yes | 4 | 2 |
| [`concept/04_formal/05_rustc_internals/17_reference_appendices.md`](../../concept/04_formal/05_rustc_internals/17_reference_appendices.md) | Reference Appendices | L2 | yes | yes | 3 | 2 |

### 05_systems_and_embedded（13 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/06_ecosystem/05_systems_and_embedded/01_wasi.md`](../../concept/06_ecosystem/05_systems_and_embedded/01_wasi.md) | WASI and WebAssembly Component Model | L3 | yes | no | 11 | 3 |
| [`concept/06_ecosystem/05_systems_and_embedded/02_cross_compilation.md`](../../concept/06_ecosystem/05_systems_and_embedded/02_cross_compilation.md) | Cross Compilation | L2 | yes | no | 5 | 2 |
| [`concept/06_ecosystem/05_systems_and_embedded/03_embedded_systems.md`](../../concept/06_ecosystem/05_systems_and_embedded/03_embedded_systems.md) | Embedded Systems | L3 | yes | no | 10 | 2 |
| [`concept/06_ecosystem/05_systems_and_embedded/04_cli_development.md`](../../concept/06_ecosystem/05_systems_and_embedded/04_cli_development.md) | CLI Development | L3 | yes | no | 9 | 2 |
| [`concept/06_ecosystem/05_systems_and_embedded/05_os_kernel.md`](../../concept/06_ecosystem/05_systems_and_embedded/05_os_kernel.md) | Rust for Operating System Kernel Development | L5 | yes | no | 12 | 2 |
| [`concept/06_ecosystem/05_systems_and_embedded/06_robotics.md`](../../concept/06_ecosystem/05_systems_and_embedded/06_robotics.md) | Robotics | L4 | yes | no | 15 | 1 |
| [`concept/06_ecosystem/05_systems_and_embedded/07_embedded_graphics.md`](../../concept/06_ecosystem/05_systems_and_embedded/07_embedded_graphics.md) | Embedded Graphics Development with Rust | L5 | yes | no | 8 | 2 |
| [`concept/06_ecosystem/05_systems_and_embedded/08_c_to_rust_translation.md`](../../concept/06_ecosystem/05_systems_and_embedded/08_c_to_rust_translation.md) | C To Rust Translation | L4 | yes | no | 4 | 3 |
| [`concept/06_ecosystem/05_systems_and_embedded/09_embedded_hal_1_0_migration.md`](../../concept/06_ecosystem/05_systems_and_embedded/09_embedded_hal_1_0_migration.md) | Embedded-HAL 1.0 Migration and Embassy Production Status | L2 | yes | no | 6 | 2 |
| [`concept/06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md`](../../concept/06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md) | Target Tier Platform Support: Guarantees and Changes in Rust... | L3 | yes | no | 2 | 1 |
| [`concept/06_ecosystem/05_systems_and_embedded/11_async_no_std_embedded.md`](../../concept/06_ecosystem/05_systems_and_embedded/11_async_no_std_embedded.md) | Async in no_std and Embedded Systems | L4 | yes | no | 3 | 2 |
| [`concept/06_ecosystem/05_systems_and_embedded/12_gpu_programming_and_hpc.md`](../../concept/06_ecosystem/05_systems_and_embedded/12_gpu_programming_and_hpc.md) | GPU Programming and High-Performance Computing with Rust | L6 | yes | no | 10 | 1 |
| [`concept/06_ecosystem/05_systems_and_embedded/README.md`](../../concept/06_ecosystem/05_systems_and_embedded/README.md) | Systems and Embedded Topic Index | L0 | no | no | 0 | 1 |

### 06_data_and_distributed（9 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/06_ecosystem/06_data_and_distributed/01_application_domains.md`](../../concept/06_ecosystem/06_data_and_distributed/01_application_domains.md) | Application Domains | L4 | yes | yes | 12 | 3 |
| [`concept/06_ecosystem/06_data_and_distributed/02_database_access.md`](../../concept/06_ecosystem/06_data_and_distributed/02_database_access.md) | Database Access Ecosystem | L3 | yes | no | 8 | 2 |
| [`concept/06_ecosystem/06_data_and_distributed/03_stream_processing_ecosystem.md`](../../concept/06_ecosystem/06_data_and_distributed/03_stream_processing_ecosystem.md) | Stream Processing Ecosystem | L3 | yes | no | 12 | 2 |
| [`concept/06_ecosystem/06_data_and_distributed/04_database_systems.md`](../../concept/06_ecosystem/06_data_and_distributed/04_database_systems.md) | Database Systems in Rust | L3 | yes | no | 11 | 2 |
| [`concept/06_ecosystem/06_data_and_distributed/05_data_engineering.md`](../../concept/06_ecosystem/06_data_and_distributed/05_data_engineering.md) | Data Engineering | L3 | yes | no | 13 | 2 |
| [`concept/06_ecosystem/06_data_and_distributed/06_distributed_consensus.md`](../../concept/06_ecosystem/06_data_and_distributed/06_distributed_consensus.md) | Distributed Consensus | L4 | yes | no | 8 | 2 |
| [`concept/06_ecosystem/06_data_and_distributed/07_rust_for_data_science.md`](../../concept/06_ecosystem/06_data_and_distributed/07_rust_for_data_science.md) | Rust for Data Science and Scientific Computing | L4 | yes | no | 10 | 2 |
| [`concept/06_ecosystem/06_data_and_distributed/08_crdt_type_zoo.md`](../../concept/06_ecosystem/06_data_and_distributed/08_crdt_type_zoo.md) | CRDT Type Zoo: State-based, Op-based, and the Merge Lattice | L4 | yes | no | 6 | 1 |
| [`concept/06_ecosystem/06_data_and_distributed/09_causal_ordering_vector_clocks.md`](../../concept/06_ecosystem/06_data_and_distributed/09_causal_ordering_vector_clocks.md) | Causal Ordering and Vector Clocks | L4 | yes | no | 1 | 1 |

### 06_low_level_patterns（8 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/03_advanced/06_low_level_patterns/01_custom_allocators.md`](../../concept/03_advanced/06_low_level_patterns/01_custom_allocators.md) | Custom Allocators | L3 | yes | no | 12 | 3 |
| [`concept/03_advanced/06_low_level_patterns/02_zero_copy_parsing.md`](../../concept/03_advanced/06_low_level_patterns/02_zero_copy_parsing.md) | Zero Copy Parsing | L3 | yes | no | 13 | 3 |
| [`concept/03_advanced/06_low_level_patterns/03_type_erasure.md`](../../concept/03_advanced/06_low_level_patterns/03_type_erasure.md) | Type Erasure | L3 | yes | no | 11 | 5 |
| [`concept/03_advanced/06_low_level_patterns/05_stream_processing_semantics.md`](../../concept/03_advanced/06_low_level_patterns/05_stream_processing_semantics.md) | Stream Processing Semantics | L4 | yes | no | 8 | 3 |
| [`concept/03_advanced/06_low_level_patterns/06_ownership_performance_optimization.md`](../../concept/03_advanced/06_low_level_patterns/06_ownership_performance_optimization.md) | Ownership Performance Optimization | L3 | yes | yes | 10 | 2 |
| [`concept/03_advanced/06_low_level_patterns/07_rust_runtime.md`](../../concept/03_advanced/06_low_level_patterns/07_rust_runtime.md) | The Rust Runtime | L2 | yes | yes | 8 | 2 |
| [`concept/03_advanced/06_low_level_patterns/08_memory_allocation_and_lifetime.md`](../../concept/03_advanced/06_low_level_patterns/08_memory_allocation_and_lifetime.md) | Memory Allocation and Lifetime | L2 | yes | no | 8 | 2 |
| [`concept/03_advanced/06_low_level_patterns/09_variables.md`](../../concept/03_advanced/06_low_level_patterns/09_variables.md) | Variables | L2 | yes | no | 8 | 2 |

### 06_macros_and_metaprogramming（3 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/02_intermediate/06_macros_and_metaprogramming/01_assert_matches.md`](../../concept/02_intermediate/06_macros_and_metaprogramming/01_assert_matches.md) | assert_matches! Macro | L2 | yes | no | 18 | 2 |
| [`concept/02_intermediate/06_macros_and_metaprogramming/04_metaprogramming.md`](../../concept/02_intermediate/06_macros_and_metaprogramming/04_metaprogramming.md) | Metaprogramming | L4 | yes | no | 8 | 2 |
| [`concept/02_intermediate/06_macros_and_metaprogramming/05_c_preprocessor_vs_rust_macros.md`](../../concept/02_intermediate/06_macros_and_metaprogramming/05_c_preprocessor_vs_rust_macros.md) | C Preprocessor vs Rust Macros | L2 | yes | no | 6 | 2 |

### 06_notation（1 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/04_formal/06_notation/01_notation.md`](../../concept/04_formal/06_notation/01_notation.md) | Notation | L1 | yes | no | 2 | 3 |

### 06_strings_and_text（2 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/01_foundation/06_strings_and_text/01_strings_and_text.md`](../../concept/01_foundation/06_strings_and_text/01_strings_and_text.md) | Strings and Text | L2 | yes | no | 19 | 2 |
| [`concept/01_foundation/06_strings_and_text/02_strings_and_encoding.md`](../../concept/01_foundation/06_strings_and_text/02_strings_and_encoding.md) | Strings and Encoding | L3 | yes | no | 9 | 2 |

### 07_concurrency_semantics（8 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/04_formal/07_concurrency_semantics/01_process_calculi_for_rust.md`](../../concept/04_formal/07_concurrency_semantics/01_process_calculi_for_rust.md) | Process Calculi for Rust: CSP, CCS, and the Pi-Calculus | L4 | yes | no | 6 | 1 |
| [`concept/04_formal/07_concurrency_semantics/02_linearizability_and_consistency.md`](../../concept/04_formal/07_concurrency_semantics/02_linearizability_and_consistency.md) | Linearizability and the Consistency Spectrum | L4 | yes | no | 2 | 1 |
| [`concept/04_formal/07_concurrency_semantics/03_actor_semantics.md`](../../concept/04_formal/07_concurrency_semantics/03_actor_semantics.md) | Actor Semantics: From Hewitt's Axioms to the Rust Ecosystem | L4 | yes | no | 4 | 1 |
| [`concept/04_formal/07_concurrency_semantics/04_algebraic_effects.md`](../../concept/04_formal/07_concurrency_semantics/04_algebraic_effects.md) | Algebraic Effects and Effect Handlers: From Free Monads to R... | L4 | yes | no | 4 | 1 |
| [`concept/04_formal/07_concurrency_semantics/05_stm_semantics.md`](../../concept/04_formal/07_concurrency_semantics/05_stm_semantics.md) | Software Transactional Memory Semantics: From Herlihy-Moss t... | L4 | yes | no | 5 | 1 |
| [`concept/04_formal/07_concurrency_semantics/06_distributed_consensus_theory.md`](../../concept/04_formal/07_concurrency_semantics/06_distributed_consensus_theory.md) | Distributed Consensus and Impossibility Theory: FLP, CAP, Pa... | L4 | yes | no | 3 | 1 |
| [`concept/04_formal/07_concurrency_semantics/07_session_types.md`](../../concept/04_formal/07_concurrency_semantics/07_session_types.md) | Session Types and Rust Communication Protocols | L4 | yes | no | 4 | 1 |
| [`concept/04_formal/07_concurrency_semantics/README.md`](../../concept/04_formal/07_concurrency_semantics/README.md) | Concurrency Semantics (Formal Models of Concurrent Computati... | L4 | no | no | 0 | 1 |

### 07_modules_and_items（3 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/01_foundation/07_modules_and_items/01_modules_and_paths.md`](../../concept/01_foundation/07_modules_and_items/01_modules_and_paths.md) | Modules and Paths | L1 | yes | no | 11 | 3 |
| [`concept/01_foundation/07_modules_and_items/05_enumerations.md`](../../concept/01_foundation/07_modules_and_items/05_enumerations.md) | Enumerations | L1 | yes | no | 10 | 2 |
| [`concept/01_foundation/07_modules_and_items/10_preludes.md`](../../concept/01_foundation/07_modules_and_items/10_preludes.md) | Preludes | L2 | yes | yes | 6 | 2 |

### 07_security_and_cryptography（3 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/06_ecosystem/07_security_and_cryptography/01_security_practices.md`](../../concept/06_ecosystem/07_security_and_cryptography/01_security_practices.md) | Security Practices | L3 | yes | no | 8 | 2 |
| [`concept/06_ecosystem/07_security_and_cryptography/02_security_cryptography.md`](../../concept/06_ecosystem/07_security_and_cryptography/02_security_cryptography.md) | Security and Cryptography | L3 | yes | no | 18 | 2 |
| [`concept/06_ecosystem/07_security_and_cryptography/03_cargo_vet_supply_chain.md`](../../concept/06_ecosystem/07_security_and_cryptography/03_cargo_vet_supply_chain.md) | cargo vet and Supply-Chain Auditing | L3 | yes | no | 0 | 1 |

### 07_unsafe_internals（1 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/03_advanced/07_unsafe_internals/01_unsafe_collections_internals.md`](../../concept/03_advanced/07_unsafe_internals/01_unsafe_collections_internals.md) | Unsafe Collections Internals | L3 | yes | no | 8 | 2 |

### 08_algorithm_semantics（6 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/04_formal/08_algorithm_semantics/01_hoare_logic_for_rust.md`](../../concept/04_formal/08_algorithm_semantics/01_hoare_logic_for_rust.md) | Hoare Logic for Rust Algorithms | L4 | no | no | 0 | 2 |
| [`concept/04_formal/08_algorithm_semantics/02_refinement_calculus.md`](../../concept/04_formal/08_algorithm_semantics/02_refinement_calculus.md) | Refinement Calculus for Rust Algorithms | L4 | yes | no | 6 | 2 |
| [`concept/04_formal/08_algorithm_semantics/03_iterator_correctness.md`](../../concept/04_formal/08_algorithm_semantics/03_iterator_correctness.md) | Iterator Correctness Semantics | L4 | yes | no | 12 | 2 |
| [`concept/04_formal/08_algorithm_semantics/04_unsafe_algorithm_invariants.md`](../../concept/04_formal/08_algorithm_semantics/04_unsafe_algorithm_invariants.md) | Semantic Invariants of Unsafe Algorithms | L4 | yes | no | 8 | 2 |
| [`concept/04_formal/08_algorithm_semantics/05_algorithm_equivalence.md`](../../concept/04_formal/08_algorithm_semantics/05_algorithm_equivalence.md) | Observational Equivalence of Algorithm Implementations | L4 | yes | no | 5 | 2 |
| [`concept/04_formal/08_algorithm_semantics/README.md`](../../concept/04_formal/08_algorithm_semantics/README.md) | Algorithm Semantics | L4 | no | no | 0 | 1 |

### 08_error_handling（2 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/01_foundation/08_error_handling/01_error_handling_basics.md`](../../concept/01_foundation/08_error_handling/01_error_handling_basics.md) | Error Handling Basics | L2 | yes | no | 15 | 4 |
| [`concept/01_foundation/08_error_handling/03_panic_and_abort.md`](../../concept/01_foundation/08_error_handling/03_panic_and_abort.md) | Panic and Abort | L2 | yes | no | 12 | 2 |

### 08_formal_verification（2 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/06_ecosystem/08_formal_verification/01_formal_ecosystem_tower.md`](../../concept/06_ecosystem/08_formal_verification/01_formal_ecosystem_tower.md) | Formal Verification Ecosystem Tower | L5 | yes | no | 8 | 4 |
| [`concept/06_ecosystem/08_formal_verification/02_formal_verification_tools.md`](../../concept/06_ecosystem/08_formal_verification/02_formal_verification_tools.md) | Formal Verification Tools | L4 | yes | no | 13 | 3 |

### 08_quizzes（1 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/02_intermediate/08_quizzes/30_quiz_cpp_rust_foundations.md`](../../concept/02_intermediate/08_quizzes/30_quiz_cpp_rust_foundations.md) | Quiz: C/C++ to Rust Foundations | L2 | no | no | 0 | 1 |

### 08_usability_testing_framework.md（1 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/00_meta/08_usability_testing_framework.md`](../../concept/00_meta/08_usability_testing_framework.md) | Rust Knowledge Base Usability Testing Framework | L0 | no | no | 0 | 1 |

### 09_system_semantics（7 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/04_formal/09_system_semantics/01_actor_model_semantics.md`](../../concept/04_formal/09_system_semantics/01_actor_model_semantics.md) | Actor Model System Semantics | L4 | no | no | 0 | 1 |
| [`concept/04_formal/09_system_semantics/02_pi_calculus_for_rust.md`](../../concept/04_formal/09_system_semantics/02_pi_calculus_for_rust.md) | Pi-Calculus for Rust System Semantics | L4 | no | no | 0 | 1 |
| [`concept/04_formal/09_system_semantics/03_component_based_semantics.md`](../../concept/04_formal/09_system_semantics/03_component_based_semantics.md) | Component-Based System Semantics | L4 | yes | no | 6 | 1 |
| [`concept/04_formal/09_system_semantics/04_distributed_systems_semantics.md`](../../concept/04_formal/09_system_semantics/04_distributed_systems_semantics.md) | Distributed Systems Semantics | L4 | yes | no | 5 | 1 |
| [`concept/04_formal/09_system_semantics/05_reactive_systems_semantics.md`](../../concept/04_formal/09_system_semantics/05_reactive_systems_semantics.md) | Reactive Systems Semantics | L4 | yes | no | 5 | 1 |
| [`concept/04_formal/09_system_semantics/06_systems_engineering_standards.md`](../../concept/04_formal/09_system_semantics/06_systems_engineering_standards.md) | Systems Engineering Standards and Rust Mapping | L4 | yes | no | 3 | 1 |
| [`concept/04_formal/09_system_semantics/README.md`](../../concept/04_formal/09_system_semantics/README.md) | System Semantics | L4 | no | no | 0 | 1 |

### 09_testing_and_quality（4 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/06_ecosystem/09_testing_and_quality/01_testing_strategies.md`](../../concept/06_ecosystem/09_testing_and_quality/01_testing_strategies.md) | Testing Strategies | L3 | yes | no | 9 | 2 |
| [`concept/06_ecosystem/09_testing_and_quality/02_documentation.md`](../../concept/06_ecosystem/09_testing_and_quality/02_documentation.md) | Documentation | L2 | yes | no | 9 | 2 |
| [`concept/06_ecosystem/09_testing_and_quality/03_testing.md`](../../concept/06_ecosystem/09_testing_and_quality/03_testing.md) | Testing Ecosystem | L2 | yes | no | 10 | 2 |
| [`concept/06_ecosystem/09_testing_and_quality/04_benchmarking.md`](../../concept/06_ecosystem/09_testing_and_quality/04_benchmarking.md) | Benchmarking with Criterion in Rust | L2 | yes | no | 7 | 2 |

### 10_architecture_semantics（5 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/04_formal/10_architecture_semantics/01_software_architecture_formalization.md`](../../concept/04_formal/10_architecture_semantics/01_software_architecture_formalization.md) | Software Architecture Formalization | L4 | yes | no | 1 | 1 |
| [`concept/04_formal/10_architecture_semantics/02_architecture_pattern_semantics.md`](../../concept/04_formal/10_architecture_semantics/02_architecture_pattern_semantics.md) | Architecture Pattern Semantics | L4 | yes | no | 5 | 7 |
| [`concept/04_formal/10_architecture_semantics/03_architecture_refinement.md`](../../concept/04_formal/10_architecture_semantics/03_architecture_refinement.md) | Architecture Refinement | L4 | yes | no | 3 | 2 |
| [`concept/04_formal/10_architecture_semantics/04_rust_architecture_constraints.md`](../../concept/04_formal/10_architecture_semantics/04_rust_architecture_constraints.md) | Rust Architecture Semantics Constraints | L4 | yes | no | 4 | 1 |
| [`concept/04_formal/10_architecture_semantics/README.md`](../../concept/04_formal/10_architecture_semantics/README.md) | Architecture Semantics | L4 | no | no | 0 | 1 |

### 10_performance（1 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/06_ecosystem/10_performance/01_performance_optimization.md`](../../concept/06_ecosystem/10_performance/01_performance_optimization.md) | Performance Optimization | L3 | yes | no | 18 | 4 |

### 10_testing_basics（1 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/01_foundation/10_testing_basics/01_testing_basics.md`](../../concept/01_foundation/10_testing_basics/01_testing_basics.md) | Testing Basics | L2 | yes | no | 9 | 2 |

### 11_computational_models（6 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/04_formal/11_computational_models/01_computational_semantics_framework.md`](../../concept/04_formal/11_computational_models/01_computational_semantics_framework.md) | A Unified Framework of Computational Semantics | L4 | yes | no | 2 | 1 |
| [`concept/04_formal/11_computational_models/02_computability_theory.md`](../../concept/04_formal/11_computational_models/02_computability_theory.md) | Computability Theory | L4 | yes | no | 3 | 1 |
| [`concept/04_formal/11_computational_models/03_formal_languages_and_automata.md`](../../concept/04_formal/11_computational_models/03_formal_languages_and_automata.md) | Formal Languages and Automata | L4 | yes | no | 7 | 1 |
| [`concept/04_formal/11_computational_models/04_mathematical_functions_of_computation.md`](../../concept/04_formal/11_computational_models/04_mathematical_functions_of_computation.md) | Mathematical Functions of Computation | L4 | yes | no | 4 | 1 |
| [`concept/04_formal/11_computational_models/05_equivalence_of_computational_models.md`](../../concept/04_formal/11_computational_models/05_equivalence_of_computational_models.md) | Equivalence of Computational Models | L4 | yes | no | 2 | 1 |
| [`concept/04_formal/11_computational_models/README.md`](../../concept/04_formal/11_computational_models/README.md) | Computational Models and Computability | L4 | no | no | 0 | 1 |

### 11_domain_applications（23 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/06_ecosystem/11_domain_applications/01_blockchain.md`](../../concept/06_ecosystem/11_domain_applications/01_blockchain.md) | Blockchain Development in Rust | L4 | yes | no | 15 | 3 |
| [`concept/06_ecosystem/11_domain_applications/02_game_ecs.md`](../../concept/06_ecosystem/11_domain_applications/02_game_ecs.md) | Game ECS Architecture | L3 | yes | no | 25 | 3 |
| [`concept/06_ecosystem/11_domain_applications/03_webassembly.md`](../../concept/06_ecosystem/11_domain_applications/03_webassembly.md) | WebAssembly Ecosystem | L3 | yes | no | 8 | 2 |
| [`concept/06_ecosystem/11_domain_applications/04_licensing_and_compliance.md`](../../concept/06_ecosystem/11_domain_applications/04_licensing_and_compliance.md) | Licensing and Compliance | L3 | yes | no | 6 | 2 |
| [`concept/06_ecosystem/11_domain_applications/05_game_development.md`](../../concept/06_ecosystem/11_domain_applications/05_game_development.md) | Game Development Ecosystem | L3 | yes | no | 8 | 2 |
| [`concept/06_ecosystem/11_domain_applications/06_game_development.md`](../../concept/06_ecosystem/11_domain_applications/06_game_development.md) | Game Development (Merged Redirect) | L5 | no | no | 0 | 1 |
| [`concept/06_ecosystem/11_domain_applications/07_algorithms_competitive_programming.md`](../../concept/06_ecosystem/11_domain_applications/07_algorithms_competitive_programming.md) | Algorithms Competitive Programming | L3 | yes | no | 31 | 3 |
| [`concept/06_ecosystem/11_domain_applications/08_algorithm_engineering_practice.md`](../../concept/06_ecosystem/11_domain_applications/08_algorithm_engineering_practice.md) | Algorithm Engineering Practice | L4 | yes | no | 25 | 4 |
| [`concept/06_ecosystem/11_domain_applications/09_data_structures_in_rust.md`](../../concept/06_ecosystem/11_domain_applications/09_data_structures_in_rust.md) | Data Structures in Rust | L5 | yes | no | 10 | 2 |
| [`concept/06_ecosystem/11_domain_applications/10_algorithm_complexity_analysis.md`](../../concept/06_ecosystem/11_domain_applications/10_algorithm_complexity_analysis.md) | Algorithm Complexity Analysis in Rust | L5 | yes | no | 6 | 1 |
| [`concept/06_ecosystem/11_domain_applications/11_cutting_edge_algorithms.md`](../../concept/06_ecosystem/11_domain_applications/11_cutting_edge_algorithms.md) | Cutting-Edge Algorithm Technologies | L5 | yes | no | 4 | 1 |
| [`concept/06_ecosystem/11_domain_applications/12_formal_algorithm_theory.md`](../../concept/06_ecosystem/11_domain_applications/12_formal_algorithm_theory.md) | Formal Algorithm Theory (Redirect Stub) | L0 | no | no | 0 | 1 |
| [`concept/06_ecosystem/11_domain_applications/13_machine_learning_ecosystem.md`](../../concept/06_ecosystem/11_domain_applications/13_machine_learning_ecosystem.md) | Machine Learning Ecosystem | L3 | yes | no | 17 | 2 |
| [`concept/06_ecosystem/11_domain_applications/14_industrial_case_studies.md`](../../concept/06_ecosystem/11_domain_applications/14_industrial_case_studies.md) | Industrial Rust Adoption Case Studies | L5 | yes | no | 7 | 2 |
| [`concept/06_ecosystem/11_domain_applications/15_game_engine_internals.md`](../../concept/06_ecosystem/11_domain_applications/15_game_engine_internals.md) | Game Engine Internals | L4 | yes | no | 13 | 2 |
| [`concept/06_ecosystem/11_domain_applications/16_quantum_computing_rust.md`](../../concept/06_ecosystem/11_domain_applications/16_quantum_computing_rust.md) | Rust in Quantum Computing Ecosystems | L4 | yes | no | 12 | 2 |
| [`concept/06_ecosystem/11_domain_applications/17_webassembly_advanced.md`](../../concept/06_ecosystem/11_domain_applications/17_webassembly_advanced.md) | Advanced WebAssembly Development with Rust | L4 | yes | no | 16 | 2 |
| [`concept/06_ecosystem/11_domain_applications/18_wasm_glossary.md`](../../concept/06_ecosystem/11_domain_applications/18_wasm_glossary.md) | WebAssembly Glossary | L1 | yes | no | 0 | 3 |
| [`concept/06_ecosystem/11_domain_applications/19_wasm_faq.md`](../../concept/06_ecosystem/11_domain_applications/19_wasm_faq.md) | WebAssembly FAQ | L2 | yes | no | 7 | 3 |
| [`concept/06_ecosystem/11_domain_applications/20_wasm_javascript_interop.md`](../../concept/06_ecosystem/11_domain_applications/20_wasm_javascript_interop.md) | WebAssembly JavaScript Interop | L2 | yes | no | 7 | 3 |
| [`concept/06_ecosystem/11_domain_applications/21_safety_critical_topic_index.md`](../../concept/06_ecosystem/11_domain_applications/21_safety_critical_topic_index.md) | Safety-Critical Rust Topic Index | L4 | no | no | 0 | 0 |
| [`concept/06_ecosystem/11_domain_applications/22_autosar_and_rust.md`](../../concept/06_ecosystem/11_domain_applications/22_autosar_and_rust.md) | AUTOSAR and Rust | L3 | yes | no | 1 | 1 |
| [`concept/06_ecosystem/11_domain_applications/23_safety_critical_systems_engineering.md`](../../concept/06_ecosystem/11_domain_applications/23_safety_critical_systems_engineering.md) | Safety-Critical Systems Engineering | L5 | yes | no | 4 | 1 |

### 11_quizzes（6 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/01_foundation/11_quizzes/01_quiz_type_system.md`](../../concept/01_foundation/11_quizzes/01_quiz_type_system.md) | Type System (Quiz) | L2 | no | yes | 14 | 2 |
| [`concept/01_foundation/11_quizzes/02_quiz_error_handling.md`](../../concept/01_foundation/11_quizzes/02_quiz_error_handling.md) | Error Handling (Quiz) | L2 | no | yes | 20 | 2 |
| [`concept/01_foundation/11_quizzes/03_quiz_modules_testing.md`](../../concept/01_foundation/11_quizzes/03_quiz_modules_testing.md) | Modules and Testing (Quiz) | L2 | no | yes | 22 | 2 |
| [`concept/01_foundation/11_quizzes/04_quiz_closures_iterators.md`](../../concept/01_foundation/11_quizzes/04_quiz_closures_iterators.md) | Closures and Iterators (Quiz) | L2 | no | yes | 33 | 2 |
| [`concept/01_foundation/11_quizzes/05_quiz_pl_foundations.md`](../../concept/01_foundation/11_quizzes/05_quiz_pl_foundations.md) | Quiz: General PL Foundations | L1 | no | yes | 0 | 2 |
| [`concept/01_foundation/11_quizzes/06_quiz_ownership_borrowing.md`](../../concept/01_foundation/11_quizzes/06_quiz_ownership_borrowing.md) | Ownership, Borrowing and Lifetimes (Quiz) | L2 | no | yes | 18 | 2 |

### 12_concurrency_models（4 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/04_formal/12_concurrency_models/01_models_of_concurrency.md`](../../concept/04_formal/12_concurrency_models/01_models_of_concurrency.md) | Models of Concurrency | L4 | yes | no | 6 | 1 |
| [`concept/04_formal/12_concurrency_models/02_expressiveness_of_concurrent_models.md`](../../concept/04_formal/12_concurrency_models/02_expressiveness_of_concurrent_models.md) | Expressiveness of Concurrent Models | L4 | yes | no | 4 | 1 |
| [`concept/04_formal/12_concurrency_models/03_parallel_concurrent_async_distributed_semantics.md`](../../concept/04_formal/12_concurrency_models/03_parallel_concurrent_async_distributed_semantics.md) | Semantics Boundaries of Parallel, Concurrent, Async, and Dis... | L4 | yes | no | 4 | 1 |
| [`concept/04_formal/12_concurrency_models/README.md`](../../concept/04_formal/12_concurrency_models/README.md) | Concurrency Model Comparison | L4 | no | no | 0 | 1 |

### 12_networking（7 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/06_ecosystem/12_networking/01_advanced_network_protocols.md`](../../concept/06_ecosystem/12_networking/01_advanced_network_protocols.md) | Advanced Network Protocols in Rust | L2 | yes | no | 8 | 2 |
| [`concept/06_ecosystem/12_networking/02_network_security.md`](../../concept/06_ecosystem/12_networking/02_network_security.md) | Network Security in Rust | L5 | yes | no | 8 | 1 |
| [`concept/06_ecosystem/12_networking/03_custom_protocol_implementation.md`](../../concept/06_ecosystem/12_networking/03_custom_protocol_implementation.md) | Custom Network Protocol Implementation in Rust | L5 | yes | no | 4 | 1 |
| [`concept/06_ecosystem/12_networking/04_network_programming_quick_start.md`](../../concept/06_ecosystem/12_networking/04_network_programming_quick_start.md) | Rust Network Programming Quick Start | L2 | yes | no | 7 | 2 |
| [`concept/06_ecosystem/12_networking/05_networking_basics.md`](../../concept/06_ecosystem/12_networking/05_networking_basics.md) | Networking Basics | L2 | yes | no | 18 | 4 |
| [`concept/06_ecosystem/12_networking/06_formal_network_protocol_theory.md`](../../concept/06_ecosystem/12_networking/06_formal_network_protocol_theory.md) | Formal Network Protocol Theory | L4 | yes | no | 16 | 3 |
| [`concept/06_ecosystem/12_networking/README.md`](../../concept/06_ecosystem/12_networking/README.md) | Networking Topic Index | L0 | no | no | 0 | 1 |

### 13_quizzes（4 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/06_ecosystem/13_quizzes/01_quiz_networking_async_ecosystem.md`](../../concept/06_ecosystem/13_quizzes/01_quiz_networking_async_ecosystem.md) | Networking and Async Ecosystem Quiz | L2 | no | no | 2 | 1 |
| [`concept/06_ecosystem/13_quizzes/02_quiz_database_storage.md`](../../concept/06_ecosystem/13_quizzes/02_quiz_database_storage.md) | Database and Storage Ecosystem Quiz | L2 | no | no | 1 | 1 |
| [`concept/06_ecosystem/13_quizzes/03_quiz_security_testing.md`](../../concept/06_ecosystem/13_quizzes/03_quiz_security_testing.md) | Security and Testing Ecosystem Quiz | L2 | no | no | 1 | 1 |
| [`concept/06_ecosystem/13_quizzes/04_quiz_domain_applications.md`](../../concept/06_ecosystem/13_quizzes/04_quiz_domain_applications.md) | Domain Applications Ecosystem Quiz | L2 | no | no | 2 | 1 |

### 13_semantic_engineering（6 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/04_formal/13_semantic_engineering/01_ontology_engineering.md`](../../concept/04_formal/13_semantic_engineering/01_ontology_engineering.md) | Ontology Engineering Methodologies | L4 | yes | no | 1 | 1 |
| [`concept/04_formal/13_semantic_engineering/02_description_logic_and_owl.md`](../../concept/04_formal/13_semantic_engineering/02_description_logic_and_owl.md) | Description Logic and OWL | L4 | yes | no | 2 | 1 |
| [`concept/04_formal/13_semantic_engineering/03_knowledge_graph_construction.md`](../../concept/04_formal/13_semantic_engineering/03_knowledge_graph_construction.md) | Knowledge Graph Construction | L4 | yes | no | 3 | 1 |
| [`concept/04_formal/13_semantic_engineering/04_semantic_interoperability.md`](../../concept/04_formal/13_semantic_engineering/04_semantic_interoperability.md) | Semantic Interoperability | L4 | yes | no | 1 | 1 |
| [`concept/04_formal/13_semantic_engineering/05_knowledge_graph_reasoning.md`](../../concept/04_formal/13_semantic_engineering/05_knowledge_graph_reasoning.md) | Knowledge Graph Reasoning | L4 | yes | no | 1 | 1 |
| [`concept/04_formal/13_semantic_engineering/README.md`](../../concept/04_formal/13_semantic_engineering/README.md) | Semantic Engineering and Ontology | L4 | yes | no | 0 | 1 |

### 14_enterprise_architecture（5 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/06_ecosystem/14_enterprise_architecture/01_enterprise_architecture_frameworks.md`](../../concept/06_ecosystem/14_enterprise_architecture/01_enterprise_architecture_frameworks.md) | Enterprise Architecture Frameworks | L5 | yes | no | 1 | 1 |
| [`concept/06_ecosystem/14_enterprise_architecture/02_architecture_governance_and_adrs.md`](../../concept/06_ecosystem/14_enterprise_architecture/02_architecture_governance_and_adrs.md) | Architecture Governance and Architecture Decision Records | L5 | yes | no | 0 | 1 |
| [`concept/06_ecosystem/14_enterprise_architecture/03_architecture_standards_alignment.md`](../../concept/06_ecosystem/14_enterprise_architecture/03_architecture_standards_alignment.md) | Architecture Standards Alignment | L5 | yes | no | 0 | 1 |
| [`concept/06_ecosystem/14_enterprise_architecture/04_domain_driven_design_in_rust.md`](../../concept/06_ecosystem/14_enterprise_architecture/04_domain_driven_design_in_rust.md) | Domain-Driven Design Tactical Patterns in Rust | L5 | yes | no | 9 | 1 |
| [`concept/06_ecosystem/14_enterprise_architecture/README.md`](../../concept/06_ecosystem/14_enterprise_architecture/README.md) | Enterprise Architecture | L5 | no | no | 0 | 1 |

### INDEX.md（1 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/sources/INDEX.md`](../../concept/sources/INDEX.md) | Authority Source Index | — | no | no | 0 | 1 |

### README.md（5 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/03_advanced/README.md`](../../concept/03_advanced/README.md) | Readme | L3 | yes | no | 0 | 6 |
| [`concept/04_formal/README.md`](../../concept/04_formal/README.md) | Formal Methods Layer Overview | L4 | yes | no | 0 | 6 |
| [`concept/05_comparative/README.md`](../../concept/05_comparative/README.md) | Readme | L5 | yes | no | 0 | 4 |
| [`concept/06_ecosystem/README.md`](../../concept/06_ecosystem/README.md) | Readme | L3 | yes | no | 0 | 3 |
| [`concept/07_future/README.md`](../../concept/07_future/README.md) | Futures | L5 | yes | no | 0 | 4 |

### archive（1 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/07_future/archive/01_ai_integration_original.md`](../../concept/07_future/archive/01_ai_integration_original.md) | Ai Integration Original | — | yes | yes | 3 | 2 |

### knowledge_topology（11 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/00_meta/knowledge_topology/01_concept_definition_atlas.md`](../../concept/00_meta/knowledge_topology/01_concept_definition_atlas.md) | Concept Definition Atlas | L0 | no | no | 0 | 0 |
| [`concept/00_meta/knowledge_topology/02_attribute_relationship_atlas.md`](../../concept/00_meta/knowledge_topology/02_attribute_relationship_atlas.md) | Attribute Relationship Atlas | L0 | no | no | 0 | 0 |
| [`concept/00_meta/knowledge_topology/03_scenario_decision_tree_atlas.md`](../../concept/00_meta/knowledge_topology/03_scenario_decision_tree_atlas.md) | Scenario Decision Tree Atlas | L0 | no | no | 0 | 1 |
| [`concept/00_meta/knowledge_topology/04_example_counterexample_atlas.md`](../../concept/00_meta/knowledge_topology/04_example_counterexample_atlas.md) | Example and Counterexample Atlas | L0 | no | no | 0 | 1 |
| [`concept/00_meta/knowledge_topology/05_logical_reasoning_atlas.md`](../../concept/00_meta/knowledge_topology/05_logical_reasoning_atlas.md) | Logical Reasoning Atlas | L0 | no | no | 0 | 1 |
| [`concept/00_meta/knowledge_topology/06_inter_layer_mapping_atlas.md`](../../concept/00_meta/knowledge_topology/06_inter_layer_mapping_atlas.md) | Inter-Layer Mapping Atlas | L0 | no | no | 0 | 0 |
| [`concept/00_meta/knowledge_topology/07_intra_layer_mapping_atlas.md`](../../concept/00_meta/knowledge_topology/07_intra_layer_mapping_atlas.md) | Intra-Layer Mapping Atlas | L0 | no | no | 0 | 0 |
| [`concept/00_meta/knowledge_topology/09_reasoning_judgment_tree_atlas.md`](../../concept/00_meta/knowledge_topology/09_reasoning_judgment_tree_atlas.md) | Reasoning Judgment Tree Atlas | L0 | no | no | 0 | 1 |
| [`concept/00_meta/knowledge_topology/11_semantic_model_atlas.md`](../../concept/00_meta/knowledge_topology/11_semantic_model_atlas.md) | Semantic Model Atlas | L0 | yes | no | 0 | 1 |
| [`concept/00_meta/knowledge_topology/kg_ontology_v2.md`](../../concept/00_meta/knowledge_topology/kg_ontology_v2.md) | Knowledge Graph Ontology v2.0 | — | no | no | 0 | 1 |
| [`concept/00_meta/knowledge_topology/kg_tlo_alignment.md`](../../concept/00_meta/knowledge_topology/kg_tlo_alignment.md) | Top-level Ontology Alignment for Rust Knowledge Graph | L0 | no | no | 0 | 1 |

### theorem_tier_spec.md（1 页）

| 文件 | EN 标题 | Bloom | Mindmap | 反例 | rust 块 | 权威来源行 |
|------|---------|-------|---------|------|---------|------------|
| [`concept/sources/theorem_tier_spec.md`](../../concept/sources/theorem_tier_spec.md) | Theorem Tier Spec | — | no | no | 0 | 2 |

## 三、P0/P1 缺口速查

| 缺口 | 证据 | 建议动作 |
|------|------|----------|
| 缺少顶层 `concept/00_meta/15_semantic_space.md` | 盘点未命中该文件 | Wave 1 创建 |
| 部分页无反例节 | 反例列 “no” | Wave 2 补充 |
| 部分页无 Mindmap | Mindmap 列 “no” | Wave 2 补充 |
| 权威来源行数低 | 权威来源行 <= 1 | Wave 2 增加国际引用 |

## 四、后续使用方式

- 本文件由 `tmp/inventory_semantic_space.py` 生成，后续波次更新后重新生成。
- 与 `01_formal_sources_baseline.md` 结合，可得到“页→权威来源”的覆盖矩阵。