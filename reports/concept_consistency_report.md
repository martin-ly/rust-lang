# 概念一致性审计报告 (Concept Consistency Report)

> 生成时间: 2026-05-24T17:14:56.160247
> 扫描文件数: 208
> 提取概念定义数: 655
> 跨文件引用数: 170

## 目录

- [概念一致性审计报告 (Concept Consistency Report)](.#概念一致性审计报告-concept-consistency-report)
  - [目录](.#目录)
  - [一、执行摘要](.#一执行摘要)
  - [二、Send / Sync 一致性检查](.#二send--sync-一致性检查)
  - [三、所有权三规则一致性检查](.#三所有权三规则一致性检查)
  - [四、生命周期省略规则一致性检查](.#四生命周期省略规则一致性检查)
  - [五、unsafe 语义一致性检查](.#五unsafe-语义一致性检查)
  - [六、跨文件段落引用有效性检查](.#六跨文件段落引用有效性检查)
  - [七、附录：概念定义统计](.#七附录概念定义统计)
    - [7.1 按概念分类统计](.#71-按概念分类统计)
    - [7.2 按文件统计](.#72-按文件统计)

---

## 一、执行摘要

| 检查项 | 状态 | 详情 |
|:---|:---|:---|
| Send / Sync 一致性 | ✅ 通过 | 检测到 0 项 |
| 所有权三规则一致性 | ✅ 通过 | 检测到 0 项 |
| 生命周期省略规则一致性 | ✅ 通过 | 检测到 0 项 |
| unsafe 语义一致性 | ✅ 通过 | 检测到 0 项 |
| 跨文件段落引用有效性 | ✅ 全部有效 | 共 170 个引用 |
| **总计** | **0 错误 / 0 警告 / 0 提示** | — |

## 二、Send / Sync 一致性检查

> ✅ 未检测到一致性问题。

## 三、所有权三规则一致性检查

> ✅ 未检测到一致性问题。

## 四、生命周期省略规则一致性检查

> ✅ 未检测到一致性问题。

## 五、unsafe 语义一致性检查

> ✅ 未检测到一致性问题。

## 六、跨文件段落引用有效性检查

> ✅ 所有跨文件段落引用均有效。

## 七、附录：概念定义统计

### 7.1 按概念分类统计

| 概念 | 提取次数 | 涉及文件数 |
|:---|:---|:---|
| unsafe-UB | 233 | 74 |
| 所有权-Move语义 | 110 | 45 |
| Send+Sync | 72 | 44 |
| 所有权-作用域绑定 | 48 | 24 |
| unsafe-契约 | 44 | 21 |
| 所有权-唯一所有权 | 36 | 18 |
| unsafe-不变式 | 29 | 4 |
| unsafe-语义 | 21 | 15 |
| 生命周期-定义 | 16 | 9 |
| Send | 11 | 5 |
| Sync | 10 | 7 |
| 所有权-Copy例外 | 9 | 5 |
| 生命周期-Rule3 | 7 | 2 |
| 生命周期-Rule2 | 5 | 2 |
| 生命周期-Rule1 | 4 | 2 |

### 7.2 按文件统计

| 文件 | 概念定义数 | 跨文件引用数 | 章节数 |
|:---|:---|:---|:---|
| concept\00_meta\asp_marking_guide.md | 1 | 0 | 15 |
| concept\00_meta\audit_checklist.md | 1 | 0 | 9 |
| concept\00_meta\authority_source_map.md | 1 | 0 | 0 |
| concept\00_meta\boundary_extension_tree.md | 1 | 0 | 5 |
| concept\00_meta\cognitive_dimension_matrix.md | 5 | 0 | 8 |
| concept\00_meta\competency_graph.md | 2 | 0 | 2 |
| concept\00_meta\concept_definition_decision_forest.md | 10 | 0 | 24 |
| concept\00_meta\concept_index.md | 8 | 4 | 23 |
| concept\00_meta\decidability_spectrum.md | 5 | 0 | 19 |
| concept\00_meta\expressiveness_multiview.md | 4 | 0 | 20 |
| concept\00_meta\fault_tree_analysis_collection.md | 11 | 0 | 17 |
| concept\00_meta\inter_layer_map.md | 11 | 2 | 14 |
| concept\00_meta\inter_layer_topology.md | 4 | 0 | 3 |
| concept\00_meta\intra_layer_model_map.md | 0 | 0 | 9 |
| concept\00_meta\kg_ontology.md | 0 | 0 | 0 |
| concept\00_meta\knowledge_mindmap.md | 2 | 0 | 0 |
| concept\00_meta\learning_guide.md | 8 | 0 | 13 |
| concept\00_meta\methodology.md | 0 | 0 | 20 |
| concept\00_meta\navigation.md | 2 | 0 | 0 |
| concept\00_meta\paradigm_transition_matrix.md | 6 | 0 | 4 |
| concept\00_meta\problem_graph.md | 1 | 0 | 0 |
| concept\00_meta\quality_dashboard_v2.md | 0 | 0 | 4 |
| concept\00_meta\quick_reference.md | 5 | 1 | 0 |
| concept\00_meta\rustbelt_predicate_map.md | 3 | 0 | 11 |
| concept\00_meta\self_assessment.md | 13 | 1 | 0 |
| concept\00_meta\semantic_bridge_algorithms_patterns.md | 0 | 0 | 13 |
| concept\00_meta\semantic_expressiveness.md | 6 | 42 | 56 |
| concept\00_meta\semantic_space.md | 14 | 19 | 30 |
| concept\00_meta\sources.md | 1 | 0 | 14 |
| concept\00_meta\theorem_inference_forest.md | 8 | 0 | 14 |
| concept\00_meta\todos.md | 0 | 0 | 3 |
| concept\01_foundation\01_ownership.md | 44 | 2 | 33 |
| concept\01_foundation\02_borrowing.md | 4 | 2 | 36 |
| concept\01_foundation\03_lifetimes.md | 11 | 1 | 34 |
| concept\01_foundation\03_lifetimes_advanced.md | 15 | 4 | 28 |
| concept\01_foundation\04_type_system.md | 3 | 3 | 59 |
| concept\01_foundation\05_reference_semantics.md | 1 | 0 | 40 |
| concept\01_foundation\06_zero_cost_abstractions.md | 0 | 0 | 16 |
| concept\01_foundation\07_control_flow.md | 0 | 0 | 12 |
| concept\01_foundation\08_collections.md | 1 | 0 | 12 |
| concept\01_foundation\09_strings_and_text.md | 0 | 0 | 12 |
| concept\01_foundation\10_error_handling_basics.md | 1 | 0 | 15 |
| concept\01_foundation\10_numerics.md | 0 | 0 | 16 |
| concept\01_foundation\11_modules_and_paths.md | 0 | 0 | 12 |
| concept\01_foundation\11_numeric_types.md | 0 | 0 | 12 |
| concept\01_foundation\12_attributes_and_macros.md | 0 | 0 | 12 |
| concept\01_foundation\13_panic_and_abort.md | 1 | 0 | 15 |
| concept\01_foundation\14_coercion_and_casting.md | 0 | 0 | 13 |
| concept\01_foundation\15_closure_basics.md | 3 | 0 | 12 |
| concept\01_foundation\16_testing_basics.md | 0 | 0 | 10 |
| concept\01_foundation\17_collections_advanced.md | 0 | 0 | 17 |
| concept\01_foundation\18_strings_and_encoding.md | 1 | 0 | 15 |
| concept\01_foundation\19_numerics.md | 0 | 0 | 12 |
| concept\01_foundation\20_variable_model.md | 4 | 0 | 18 |
| concept\01_foundation\21_effects_and_purity.md | 1 | 0 | 18 |
| concept\01_foundation\22_data_abstraction_spectrum.md | 1 | 0 | 17 |
| concept\02_intermediate\01_traits.md | 7 | 1 | 31 |
| concept\02_intermediate\02_generics.md | 3 | 5 | 48 |
| concept\02_intermediate\03_memory_management.md | 18 | 1 | 43 |
| concept\02_intermediate\04_error_handling.md | 1 | 3 | 60 |
| concept\02_intermediate\05_assert_matches.md | 0 | 0 | 14 |
| concept\02_intermediate\06_range_types.md | 0 | 0 | 15 |
| concept\02_intermediate\07_closure_types.md | 3 | 0 | 13 |
| concept\02_intermediate\08_interior_mutability.md | 1 | 0 | 8 |
| concept\02_intermediate\09_serde_patterns.md | 0 | 0 | 13 |
| concept\02_intermediate\10_module_system.md | 0 | 0 | 12 |
| concept\02_intermediate\11_cow_and_borrowed.md | 0 | 0 | 12 |
| concept\02_intermediate\12_smart_pointers.md | 2 | 0 | 10 |
| concept\02_intermediate\13_dsl_and_embedding.md | 0 | 0 | 12 |
| concept\02_intermediate\14_newtype_and_wrapper.md | 0 | 0 | 13 |
| concept\02_intermediate\15_error_handling_deep_dive.md | 0 | 0 | 12 |
| concept\02_intermediate\15_iterator_patterns.md | 0 | 0 | 13 |
| concept\02_intermediate\16_iterator_patterns.md | 1 | 0 | 14 |
| concept\02_intermediate\17_macro_patterns.md | 0 | 0 | 12 |
| concept\02_intermediate\18_lifetimes_advanced.md | 0 | 0 | 12 |
| concept\02_intermediate\19_advanced_traits.md | 0 | 0 | 12 |
| concept\02_intermediate\20_type_system_advanced.md | 0 | 0 | 13 |
| concept\02_intermediate\21_metaprogramming.md | 0 | 0 | 14 |
| concept\02_intermediate\22_iterator_patterns.md | 0 | 0 | 11 |
| concept\03_advanced\01_concurrency.md | 31 | 9 | 24 |
| concept\03_advanced\02_async.md | 11 | 9 | 44 |
| concept\03_advanced\02_async_advanced.md | 8 | 5 | 9 |
| concept\03_advanced\02_async_patterns.md | 2 | 2 | 12 |
| concept\03_advanced\03_unsafe.md | 101 | 2 | 39 |
| concept\03_advanced\04_macros.md | 0 | 1 | 30 |
| concept\03_advanced\05_rust_ffi.md | 1 | 0 | 10 |
| concept\03_advanced\06_pin_unpin.md | 1 | 0 | 10 |
| concept\03_advanced\07_proc_macro.md | 0 | 0 | 9 |
| concept\03_advanced\08_nll_and_polonius.md | 0 | 0 | 9 |
| concept\03_advanced\09_ffi_advanced.md | 0 | 0 | 13 |
| concept\03_advanced\10_concurrency_patterns.md | 3 | 0 | 10 |
| concept\03_advanced\11_atomics_and_memory_ordering.md | 0 | 0 | 11 |
| concept\03_advanced\12_unsafe_rust_patterns.md | 13 | 0 | 13 |
| concept\03_advanced\13_async_patterns.md | 1 | 0 | 13 |
| concept\03_advanced\14_custom_allocators.md | 0 | 0 | 14 |
| concept\03_advanced\15_zero_copy_parsing.md | 0 | 0 | 14 |
| concept\03_advanced\16_lock_free.md | 0 | 0 | 11 |
| concept\03_advanced\17_type_erasure.md | 1 | 0 | 12 |
| concept\03_advanced\18_network_programming.md | 0 | 0 | 16 |
| concept\03_advanced\19_parallel_distributed_pattern_spectrum.md | 0 | 0 | 19 |
| concept\03_advanced\20_stream_processing_semantics.md | 0 | 0 | 27 |
| concept\04_formal\01_linear_logic.md | 10 | 2 | 29 |
| concept\04_formal\02_type_theory.md | 3 | 17 | 24 |
| concept\04_formal\03_ownership_formal.md | 5 | 10 | 29 |
| concept\04_formal\04_rustbelt.md | 6 | 4 | 34 |
| concept\04_formal\05_verification_toolchain.md | 1 | 1 | 20 |
| concept\04_formal\06_subtype_variance.md | 3 | 0 | 12 |
| concept\04_formal\07_separation_logic.md | 0 | 0 | 12 |
| concept\04_formal\08_type_inference.md | 0 | 0 | 12 |
| concept\04_formal\09_linear_logic_applications.md | 1 | 0 | 13 |
| concept\04_formal\09_operational_semantics.md | 7 | 0 | 23 |
| concept\04_formal\10_category_theory.md | 0 | 0 | 12 |
| concept\04_formal\11_separation_logic.md | 1 | 0 | 13 |
| concept\04_formal\12_denotational_semantics.md | 3 | 0 | 12 |
| concept\04_formal\13_formal_methods.md | 1 | 0 | 14 |
| concept\04_formal\14_lambda_calculus.md | 0 | 0 | 11 |
| concept\04_formal\15_hoare_logic.md | 0 | 0 | 15 |
| concept\04_formal\16_aerospace_certification_formal_methods.md | 1 | 0 | 18 |
| concept\04_formal\17_operational_semantics.md | 6 | 0 | 22 |
| concept\04_formal\18_evaluation_strategies.md | 2 | 0 | 15 |
| concept\05_comparative\01_rust_vs_cpp.md | 14 | 0 | 47 |
| concept\05_comparative\02_cpp_abi_object_model.md | 2 | 0 | 29 |
| concept\05_comparative\02_rust_vs_go.md | 2 | 0 | 31 |
| concept\05_comparative\03_paradigm_matrix.md | 0 | 0 | 19 |
| concept\05_comparative\04_safety_boundaries.md | 23 | 13 | 23 |
| concept\05_comparative\05_execution_model_isomorphism.md | 4 | 0 | 22 |
| concept\05_comparative\06_rust_vs_java.md | 2 | 0 | 12 |
| concept\05_comparative\07_rust_vs_python.md | 2 | 0 | 12 |
| concept\05_comparative\08_rust_vs_javascript.md | 0 | 0 | 12 |
| concept\05_comparative\08_rust_vs_ruby.md | 1 | 0 | 12 |
| concept\05_comparative\09_rust_vs_swift.md | 1 | 0 | 12 |
| concept\05_comparative\10_rust_vs_zig.md | 0 | 0 | 12 |
| concept\05_comparative\11_rust_vs_kotlin.md | 0 | 0 | 15 |
| concept\05_comparative\12_rust_vs_scala.md | 0 | 0 | 14 |
| concept\05_comparative\13_rust_vs_csharp.md | 0 | 0 | 14 |
| concept\05_comparative\14_rust_vs_elixir.md | 0 | 0 | 12 |
| concept\05_comparative\15_rust_vs_typescript.md | 2 | 0 | 16 |
| concept\05_comparative\16_rust_vs_ruby.md | 0 | 0 | 12 |
| concept\06_ecosystem\01_toolchain.md | 2 | 0 | 40 |
| concept\06_ecosystem\02_patterns.md | 4 | 0 | 22 |
| concept\06_ecosystem\03_core_crates.md | 1 | 0 | 33 |
| concept\06_ecosystem\03_idioms_spectrum.md | 7 | 0 | 39 |
| concept\06_ecosystem\04_application_domains.md | 0 | 0 | 39 |
| concept\06_ecosystem\05_formal_ecosystem_tower.md | 2 | 0 | 8 |
| concept\06_ecosystem\05_system_design_principles.md | 5 | 0 | 15 |
| concept\06_ecosystem\06_blockchain.md | 5 | 0 | 23 |
| concept\06_ecosystem\07_game_ecs.md | 2 | 0 | 33 |
| concept\06_ecosystem\08_wasi.md | 5 | 0 | 16 |
| concept\06_ecosystem\09_cargo_script.md | 0 | 0 | 13 |
| concept\06_ecosystem\10_public_private_deps.md | 1 | 0 | 15 |
| concept\06_ecosystem\11_webassembly.md | 0 | 0 | 12 |
| concept\06_ecosystem\12_testing_strategies.md | 1 | 0 | 13 |
| concept\06_ecosystem\13_logging_observability.md | 0 | 0 | 13 |
| concept\06_ecosystem\14_documentation.md | 0 | 0 | 10 |
| concept\06_ecosystem\15_performance_optimization.md | 4 | 0 | 14 |
| concept\06_ecosystem\16_testing.md | 1 | 0 | 12 |
| concept\06_ecosystem\17_cross_compilation.md | 0 | 0 | 12 |
| concept\06_ecosystem\18_distributed_systems.md | 0 | 0 | 13 |
| concept\06_ecosystem\19_security_practices.md | 2 | 0 | 13 |
| concept\06_ecosystem\20_licensing_and_compliance.md | 1 | 0 | 12 |
| concept\06_ecosystem\21_game_development.md | 0 | 0 | 12 |
| concept\06_ecosystem\22_embedded_systems.md | 0 | 0 | 14 |
| concept\06_ecosystem\23_database_access.md | 0 | 0 | 14 |
| concept\06_ecosystem\24_cloud_native.md | 1 | 0 | 13 |
| concept\06_ecosystem\25_cli_development.md | 0 | 0 | 12 |
| concept\06_ecosystem\26_game_development.md | 3 | 0 | 10 |
| concept\06_ecosystem\27_web_frameworks.md | 0 | 0 | 21 |
| concept\06_ecosystem\28_devops_and_ci_cd.md | 3 | 0 | 15 |
| concept\06_ecosystem\29_algorithms_competitive_programming.md | 1 | 0 | 30 |
| concept\06_ecosystem\30_system_composability.md | 1 | 0 | 12 |
| concept\06_ecosystem\31_microservice_patterns.md | 1 | 0 | 7 |
| concept\06_ecosystem\32_event_driven_architecture.md | 1 | 0 | 14 |
| concept\06_ecosystem\33_idioms_spectrum.md | 7 | 0 | 37 |
| concept\06_ecosystem\34_formal_ecosystem_tower.md | 2 | 0 | 8 |
| concept\06_ecosystem\35_pattern_composition_algebra.md | 1 | 0 | 20 |
| concept\06_ecosystem\36_stream_processing_ecosystem.md | 3 | 0 | 16 |
| concept\06_ecosystem\37_database_systems.md | 2 | 0 | 9 |
| concept\06_ecosystem\38_network_protocols.md | 0 | 0 | 8 |
| concept\06_ecosystem\39_os_kernel.md | 0 | 0 | 6 |
| concept\07_future\01_ai_integration.md | 3 | 0 | 34 |
| concept\07_future\02_formal_methods.md | 2 | 0 | 47 |
| concept\07_future\03_evolution.md | 1 | 0 | 35 |
| concept\07_future\04_effects_system.md | 4 | 3 | 18 |
| concept\07_future\05_rust_version_tracking.md | 1 | 1 | 25 |
| concept\07_future\07_mcdc_coverage_preview.md | 0 | 0 | 11 |
| concept\07_future\08_safety_tags_preview.md | 5 | 0 | 14 |
| concept\07_future\09_parallel_frontend_preview.md | 0 | 0 | 12 |
| concept\07_future\10_derive_coerce_pointee_preview.md | 0 | 0 | 12 |
| concept\07_future\11_const_trait_impl_preview.md | 0 | 0 | 12 |
| concept\07_future\12_return_type_notation_preview.md | 0 | 0 | 12 |
| concept\07_future\13_unsafe_fields_preview.md | 13 | 0 | 12 |
| concept\07_future\14_ferrocene_preview.md | 0 | 0 | 12 |
| concept\07_future\15_gen_blocks_preview.md | 0 | 0 | 12 |
| concept\07_future\16_cranelift_backend_preview.md | 2 | 0 | 14 |
| concept\07_future\17_rust_specification_preview.md | 3 | 0 | 12 |
| concept\07_future\18_async_drop_preview.md | 2 | 0 | 12 |
| concept\07_future\19_rust_for_linux.md | 1 | 0 | 12 |
| concept\07_future\20_borrowsanitizer_preview.md | 3 | 0 | 13 |
| concept\07_future\21_rust_in_ai.md | 0 | 0 | 12 |
| concept\07_future\22_edition_guide.md | 0 | 0 | 12 |
| concept\07_future\23_rust_edition_guide.md | 0 | 0 | 11 |
| concept\07_future\24_roadmap.md | 0 | 0 | 21 |
| concept\07_future\25_open_enums_preview.md | 0 | 0 | 19 |
| concept\07_future\26_specialization_preview.md | 0 | 0 | 12 |
| concept\07_future\27_compile_time_execution.md | 0 | 0 | 13 |
| concept\07_future\28_rust_for_webassembly.md | 1 | 0 | 18 |
| concept\07_future\29_ebpf_rust.md | 4 | 0 | 24 |
| concept\07_future\archive\01_ai_integration_original.md | 5 | 0 | 32 |

---

> 本报告由 `scripts/concept_consistency_auditor.py` 自动生成。
