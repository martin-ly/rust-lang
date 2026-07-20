# 知识体系质量仪表盘 (KB Quality Dashboard)

> 生成时间: 2026-07-20T14:44:21.236855+00:00
> 扫描文件数: 527

## 全局指标

| 指标 | 数值 | 目标 | 状态 |
|:---|:---|:---|:---|
| 总文件数 | 527 | 27 | ✅ |
| 总定理链 (⟹) | 2120 | ≥270 | ✅ |
| 总反命题 | 732 | ≥40 | ✅ |
| 总 Mermaid 图 | 1077 | ≥50 | ✅ |
| 编译验证代码块 | 5293 | ≥150 | ✅ |
| 定理矩阵总行 | 24675 | — | — |
| 死链数量 | 23 | 0 | ❌ |
| docs/content/knowledge 死链数量 | 210 | 0 | ❌ |
| 反向推理 (⟸) | 317 | ≥50 | ✅ |
| 模板化 ⟹ | 0 | 0 | ✅ |
| 前置概念覆盖率 | 457/457 | 100% | ✅ |
| 后置概念覆盖率 | 457/457 | 100% | ✅ |
| 双标签覆盖率 | 457/457 | >=95% | ✅ |
| 非法标签组合 | 0 | 0 | ✅ |

## 按层级分布

| 层级 | 文件数 | 平均 ⟹/文件 | 平均过渡段/文件 | 认知路径 | ⟸/文件 | 模板化 | 前置覆盖 | 后置覆盖 | 双标签 |
|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|
| L0 | 70 | 7.0 | 2.8 | 35/70 (50%) | 0.6 | 0 | 16/70 | 14/70 | 69/70 |
| L1 | 57 | 4.2 | 2.3 | 40/57 (70%) | 1.5 | 0 | 57/57 | 57/57 | 57/57 |
| L2 | 41 | 5.1 | 1.2 | 25/41 (60%) | 1.8 | 0 | 41/41 | 41/41 | 41/41 |
| L3 | 72 | 5.7 | 2.2 | 55/72 (76%) | 1.6 | 0 | 72/72 | 72/72 | 72/72 |
| L4 | 61 | 3.5 | 1.1 | 35/61 (57%) | 0.1 | 0 | 61/61 | 61/61 | 61/61 |
| L5 | 27 | 3.1 | 1.4 | 19/27 (70%) | 0.0 | 0 | 27/27 | 27/27 | 27/27 |
| L6 | 130 | 2.6 | 1.4 | 61/130 (46%) | 0.0 | 0 | 130/130 | 130/130 | 130/130 |
| L7 | 69 | 2.0 | 0.6 | 38/69 (55%) | 0.0 | 0 | 69/69 | 69/69 | 69/69 |

## 风险文件

| 文件 | 层级 | 未通过项 |
|:---|:---|:---|
| E:\_src\rust-lang\concept\01_foundation\00_start\01_pl_prerequisites.md | L1 | 过渡段落不足 (0 < 3); 缺失反命题 |
| E:\_src\rust-lang\concept\01_foundation\00_start\02_zero_cost_abstractions.md | L1 | 过渡段落不足 (2 < 3) |
| E:\_src\rust-lang\concept\01_foundation\00_start\03_closure_basics.md | L1 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\01_foundation\00_start\04_effects_and_purity.md | L1 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\00_start\05_std_io_and_process.md | L1 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\01_foundation\00_start\06_keywords.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\00_start\07_operators_and_symbols.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\05_move_semantics.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\06_ownership_inventories_brown_book.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\02_never_type.md | L1 | 过渡段落不足 (0 < 3); 缺失反命题 |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\03_numerics.md | L1 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\04_coercion_and_casting.md | L1 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\05_data_abstraction_spectrum.md | L1 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\03_values_and_references\01_reference_semantics.md | L1 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\01_foundation\03_values_and_references\02_value_vs_reference_semantics.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\03_values_and_references\03_variable_model.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\04_control_flow\01_control_flow.md | L1 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\01_foundation\04_control_flow\02_patterns.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\04_control_flow\03_let_chains.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\04_control_flow\04_statements_and_expressions.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\04_control_flow\05_let_else.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\05_collections\01_collections.md | L1 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\01_foundation\05_collections\02_collections_advanced.md | L1 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\01_foundation\06_strings_and_text\01_strings_and_text.md | L1 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\01_foundation\06_strings_and_text\02_strings_and_encoding.md | L1 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\01_foundation\06_strings_and_text\03_formatting_and_display.md | L1 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\01_modules_and_paths.md | L1 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\03_use_declarations.md | L1 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\07_type_aliases.md | L1 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\08_static_items.md | L1 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\09_const_items_and_const_fn.md | L1 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\10_preludes.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\08_error_handling\01_error_handling_basics.md | L1 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\01_foundation\08_error_handling\03_panic_and_abort.md | L1 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\01_foundation\09_macros_basics\01_attributes_and_macros.md | L1 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\01_foundation\10_testing_basics\01_testing_basics.md | L1 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\01_quiz_type_system.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\02_quiz_error_handling.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\03_quiz_modules_testing.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\04_quiz_closures_iterators.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\05_quiz_pl_foundations.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\06_quiz_ownership_borrowing.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\03_serde_patterns.md | L2 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\04_advanced_traits.md | L2 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\05_construction_and_initialization.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (1 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\06_derive_traits.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (2 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\07_generic_associated_types.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\08_negative_impls.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\09_associated_type_defaults.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\02_const_generics.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (2 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\04_quiz_traits_and_generics.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\05_const_generics_and_trait_objects.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\02_interior_mutability.md | L2 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\03_cow_and_borrowed.md | L2 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\04_smart_pointers.md | L2 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\05_quiz_memory_management.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\03_error_handling\02_error_handling_deep_dive.md | L2 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\02_intermediate\03_error_handling\03_panic.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\03_error_handling\04_exception_safety_rust_cpp.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (2 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\01_range_types.md | L2 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\02_closure_types.md | L2 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\03_newtype_and_wrapper.md | L2 | 过渡段落不足 (2 < 3) |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\04_type_system_advanced.md | L2 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\05_rtti_and_dynamic_typing.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\06_unions.md | L2 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\07_type_conversions.md | L2 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\02_intermediate\05_modules_and_visibility\01_module_system.md | L2 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\02_intermediate\05_modules_and_visibility\02_friend_vs_module_privacy.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\05_modules_and_visibility\03_api_naming_conventions.md | L2 | 缺失认知路径; 过渡段落不足 (2 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\01_assert_matches.md | L2 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\02_dsl_and_embedding.md | L2 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\03_macro_patterns.md | L2 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\04_metaprogramming.md | L2 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\05_c_preprocessor_vs_rust_macros.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\06_attributes_by_category.md | L2 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\02_intermediate\07_iterators_and_closures\01_iterator_patterns.md | L2 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\02_intermediate\08_quizzes\30_quiz_cpp_rust_foundations.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\01_concurrency.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\02_send_sync_auto_traits.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\03_concurrency_patterns.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\04_send_sync_boundaries.md | L3 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\06_atomics_and_memory_ordering.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\07_lock_free.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\08_parallel_distributed_pattern_spectrum.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\09_quiz_concurrency_async.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\10_quiz_semantic_models.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (1 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\01_async\02_async_advanced.md | L3 | 过渡段落不足 (0 < 3); 缺失反命题 |
| E:\_src\rust-lang\concept\03_advanced\01_async\03_async_patterns.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\03_advanced\01_async\05_async_cancellation_safety.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\01_async\06_async_boundary_panorama.md | L3 | 过渡段落不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\01_async\07_async_closures.md | L3 | 过渡段落不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\01_async\08_pin_unpin.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\03_advanced\01_async\10_executor_fairness_and_scheduling.md | L3 | 过渡段落不足 (2 < 3) |
| E:\_src\rust-lang\concept\03_advanced\01_async\11_pin_projection_counterexamples.md | L3 | 过渡段落不足 (2 < 3) |
| E:\_src\rust-lang\concept\03_advanced\01_async\12_waker_contract_deep_dive.md | L3 | 过渡段落不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\01_async\13_async_trait_object_safety.md | L3 | 过渡段落不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\01_async\14_gat_async_boundary.md | L3 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\01_async\15_state_machine_semantics.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\00_before_formal.md | L3 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\02_unsafe_boundary_panorama.md | L3 | 过渡段落不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\03_nll_and_polonius.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\05_quiz_unsafe.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\08_async_in_unsafe_contexts.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\02_proc_macro.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\10_quiz_macros.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\11_conditional_compilation.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\01_rust_ffi.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\02_ffi_advanced.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\03_linkage.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (1 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\04_async_ffi_boundary.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\05_unsafe_extern_blocks.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\05_inline_assembly\01_inline_assembly.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\01_custom_allocators.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\02_zero_copy_parsing.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\03_type_erasure.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\04_network_programming.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\05_stream_processing_semantics.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\06_ownership_performance_optimization.md | L3 | 过渡段落不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\08_memory_allocation_and_lifetime.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\09_variables.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\10_visibility_and_privacy.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\07_unsafe_internals\01_unsafe_collections_internals.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\02_subtype_variance.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\03_type_inference.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\04_category_theory.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\05_lambda_calculus.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\06_type_semantics.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\07_type_checking_and_inference.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (1 < 3) |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\08_type_inference_complexity.md | L4 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\09_type_system_reference.md | L4 | 缺失认知路径; 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\10_dependent_refinement_types.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\03_linear_logic_applications.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\04_borrow_checking_decidability.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\05_tree_borrows_deep_dive.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\06_behavior_considered_undefined.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\02_separation_logic.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\03_safety_tags_in_formal.md | L4 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\04_borrow_sanitizer_in_formal.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\01_denotational_semantics.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\02_hoare_logic.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\03_operational_semantics.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\04_evaluation_strategies.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\05_axiomatic_semantics.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\06_aeneas_symbolic_semantics.md | L4 | 过渡段落不足 (0 < 3); 定理链不足 (1 < 3); 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\07_constant_evaluation.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\01_verification_toolchain.md | L4 | 过渡段落不足 (0 < 3); 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\02_formal_methods.md | L4 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\03_aerospace_certification_formal_methods.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\04_modern_verification_tools.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\05_programming_language_foundations.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\06_quiz_formal_methods.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\07_autoverus.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (1 < 3) |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\08_miri.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\09_kani.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\10_certified_toolchains_and_packages.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\01_rustc_query_system.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (1 < 3) |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\02_mir_codegen_llvm_primer.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\03_trait_solver_in_rustc.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\04_name_resolution_and_hir.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\05_application_binary_interface.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\06_names_and_resolution.md | L4 | 定理链不足 (2 < 3) |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\07_special_types_and_traits.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (2 < 3); 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\08_type_layout.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\09_destructors.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\12_attributes.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\13_statements_and_expressions_reference.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\14_patterns_reference.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\15_generics_compiler_behavior.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\16_names_reference.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\17_reference_appendices.md | L4 | 过渡段落不足 (0 < 3); 定理链不足 (2 < 3) |
| E:\_src\rust-lang\concept\04_formal\06_notation\01_notation.md | L4 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\07_concurrency_semantics\04_algebraic_effects.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\07_concurrency_semantics\05_stm_semantics.md | L4 | 缺失认知路径; 过渡段落不足 (2 < 3); 定理链不足 (1 < 3) |
| E:\_src\rust-lang\concept\04_formal\07_concurrency_semantics\06_distributed_consensus_theory.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\00_paradigms\02_execution_model_isomorphism.md | L5 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\00_paradigms\03_cpp_rust_surface_features.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\00_paradigms\05_language_semantic_model_matrix.md | L5 | 过渡段落不足 (2 < 3) |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\01_rust_vs_cpp.md | L5 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\02_cpp_abi_object_model.md | L5 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\04_rust_vs_ruby.md | L5 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\05_rust_vs_swift.md | L5 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\06_rust_vs_zig.md | L5 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\07_rust_vs_ada_spark.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\08_rust_vs_d.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\09_rust_vs_nim.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\01_rust_vs_java.md | L5 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\02_rust_vs_python.md | L5 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\03_rust_vs_javascript.md | L5 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\04_rust_vs_kotlin.md | L5 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\05_rust_vs_scala.md | L5 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\06_rust_vs_csharp.md | L5 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\07_rust_vs_elixir.md | L5 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\08_rust_vs_typescript.md | L5 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\09_rust_vs_haskell.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\10_rust_vs_ocaml.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\11_rust_vs_fsharp.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\03_domain_comparisons\02_quiz_rust_vs_systems.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\02_logging_observability.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\03_devops_and_ci_cd.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\04_compiler_internals.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\05_compiler_infrastructure.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\06_quiz_toolchain.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\07_rustdoc_196_changes.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\08_platform_rust_integration.md | L6 | 过渡段落不足 (2 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\09_llvm_backend_and_codegen.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\10_rustc_driver_and_stable_mir.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\11_compiler_diagnostics_and_ui_tests.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\12_rustc_bootstrap.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\13_compiler_testing.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\14_development_tools.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\01_cargo_script.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\03_resolver_v3_public_feature_unification.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\04_cargo_196_features.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\05_cargo_build_scripts.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\06_cargo_dependency_resolution.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\07_cargo_source_replacement.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\08_cargo_registries_and_publishing.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\09_cargo_authentication_and_cache.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\10_cargo_manifest_reference.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\11_cargo_profiles_and_lints.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\12_cargo_subcommands_and_plugins.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\13_cargo_security_cves.md | L6 | 过渡段落不足 (2 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\14_cargo_workspaces.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\15_cargo_getting_started.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\16_cargo_workflow.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\17_cargo_guide_practices.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\18_cargo_configuration.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\19_cargo_commands_reference.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\20_cargo_manifest_targets.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\21_cargo_registry_internals.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\23_cargo_197_features.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\02_idioms_spectrum.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\03_system_design_principles.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\04_system_composability.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\05_microservice_patterns.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\06_event_driven_architecture.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\07_cqrs_event_sourcing.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\08_architecture_patterns.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\16_pattern_composition_algebra.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\17_workflow_theory.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\18_api_design_patterns.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\01_distributed_systems.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\02_cloud_native.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\03_web_frameworks.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\04_http_client_development.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\07_network_protocols.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\09_reactive_programming.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\10_tokio_runtime_internals.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\01_wasi.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\02_cross_compilation.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\03_embedded_systems.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\04_cli_development.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\05_os_kernel.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\06_robotics.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\07_embedded_graphics.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\08_c_to_rust_translation.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\11_async_no_std_embedded.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\12_gpu_programming_and_hpc.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\02_database_access.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\03_stream_processing_ecosystem.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\04_database_systems.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\05_data_engineering.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\06_distributed_consensus.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\07_rust_for_data_science.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\07_security_and_cryptography\01_security_practices.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\07_security_and_cryptography\02_security_cryptography.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\07_security_and_cryptography\03_cargo_vet_supply_chain.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\08_formal_verification\01_formal_ecosystem_tower.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (1 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\08_formal_verification\02_formal_verification_tools.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\09_testing_and_quality\01_testing_strategies.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\09_testing_and_quality\02_documentation.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\09_testing_and_quality\03_testing.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\09_testing_and_quality\04_benchmarking.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\10_performance\01_performance_optimization.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\01_blockchain.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\02_game_ecs.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (1 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\03_webassembly.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\04_licensing_and_compliance.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\05_game_development.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\07_algorithms_competitive_programming.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\10_algorithm_complexity_analysis.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\13_machine_learning_ecosystem.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\14_industrial_case_studies.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\15_game_engine_internals.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\16_quantum_computing_rust.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\17_webassembly_advanced.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\22_autosar_and_rust.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\12_networking\03_custom_protocol_implementation.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\13_quizzes\01_quiz_networking_async_ecosystem.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\13_quizzes\02_quiz_database_storage.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\13_quizzes\03_quiz_security_testing.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (1 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\13_quizzes\04_quiz_domain_applications.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (1 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\01_rust_version_tracking.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\02_editions.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\feature_domain_matrix_197.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\migration_197_decision_tree.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_95_stabilized.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_96_stabilized.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_97_stabilized.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_98_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_98_stabilized.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\01_edition_roadmap\02_edition_guide.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\01_edition_roadmap\04_roadmap.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\02_preview_features\01_effects_system.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\02_preview_features\02_mcdc_coverage_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\02_preview_features\03_safety_tags_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\02_preview_features\04_parallel_frontend_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\02_preview_features\05_derive_coerce_pointee_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\02_preview_features\06_const_trait_impl_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\02_preview_features\07_stable_abi_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\02_preview_features\08_inline_const_pattern_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\02_preview_features\09_return_type_notation_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\02_preview_features\10_must_not_suspend_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\02_preview_features\11_unsafe_fields_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\02_preview_features\12_ferrocene_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\02_preview_features\13_lifetime_capture_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\02_preview_features\14_pin_ergonomics_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\02_preview_features\15_rpitit_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\02_preview_features\16_cranelift_backend_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\02_preview_features\17_type_alias_impl_trait_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\02_preview_features\18_arbitrary_self_types_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\02_preview_features\20_ergonomic_ref_counting_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\02_preview_features\21_rust_specification_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\02_preview_features\22_async_drop_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\02_preview_features\23_field_projections_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\02_preview_features\24_borrow_sanitizer.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\02_preview_features\25_gen_blocks_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\02_preview_features\26_std_autodiff_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\02_preview_features\27_cargo_semver_checks_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\02_preview_features\28_wasm_target_evolution.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\02_preview_features\29_aarch64_sve_sme_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\02_preview_features\30_rust_in_space.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\02_preview_features\31_specialization_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\02_preview_features\32_compile_time_execution.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\02_preview_features\34_open_enums_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\01_ai_integration.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (1 < 3) |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\04_rust_for_linux.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\05_rust_in_ai.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\06_rust_for_webassembly.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\07_ebpf_rust.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\05_quizzes\01_quiz_version_and_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |

## 死链检测

| 来源文件 | 引用路径 | 解析后的绝对路径 |
|:---|:---|:---|
| E:\_src\rust-lang\concept\00_meta\00_framework\cpp_rust_engineering_roadmap.md | ../../../archive/reports/2026_07/SEMANTIC_SPACE_CRITICAL_AUDIT_2026_05_24.md | E:\_src\rust-lang\archive\reports\2026_07\SEMANTIC_SPACE_CRITICAL_AUDIT_2026_05_24.md |
| E:\_src\rust-lang\concept\00_meta\00_framework\fault_tree_analysis_collection.md | ../../../archive/reports/2026_07/MIRI_VALIDATION_2026_05_27.md | E:\_src\rust-lang\archive\reports\2026_07\MIRI_VALIDATION_2026_05_27.md |
| E:\_src\rust-lang\concept\00_meta\00_framework\pl_foundations_roadmap.md | ../../../archive/reports/2026_07/SEMANTIC_SPACE_CRITICAL_AUDIT_2026_05_24.md | E:\_src\rust-lang\archive\reports\2026_07\SEMANTIC_SPACE_CRITICAL_AUDIT_2026_05_24.md |
| E:\_src\rust-lang\concept\00_meta\03_audit\07_quality_dashboard_v2.md | ../../../archive/reports/2026_07/QUALITY_BASELINE_v2_0.md | E:\_src\rust-lang\archive\reports\2026_07\QUALITY_BASELINE_v2_0.md |
| E:\_src\rust-lang\concept\00_meta\04_navigation\08_learning_mvp_path.md | ../../../archive/reports/2026_07/GOOGLE_COMPREHENSIVE_RUST_MAPPING_2026_06_19.md | E:\_src\rust-lang\archive\reports\2026_07\GOOGLE_COMPREHENSIVE_RUST_MAPPING_2026_06_19.md |
| E:\_src\rust-lang\concept\00_meta\04_navigation\09_navigation.md | ../../../archive/reports/2026_07/QUALITY_BASELINE_v1_9.md | E:\_src\rust-lang\archive\reports\2026_07\QUALITY_BASELINE_v1_9.md |
| E:\_src\rust-lang\concept\00_meta\04_navigation\09_navigation.md | ../../../archive/reports/2026_07/code_block_compile_report.md | E:\_src\rust-lang\archive\reports\2026_07\code_block_compile_report.md |
| E:\_src\rust-lang\concept\00_meta\04_navigation\09_navigation.md | ../../../archive/reports/2026_07/concept_audit_report.md | E:\_src\rust-lang\archive\reports\2026_07\concept_audit_report.md |
| E:\_src\rust-lang\concept\00_meta\04_navigation\09_navigation.md | ../../../archive/reports/2026_07/concept_consistency_report.md | E:\_src\rust-lang\archive\reports\2026_07\concept_consistency_report.md |
| E:\_src\rust-lang\concept\00_meta\04_navigation\13_foundations_gap_closure_index.md | ../../../archive/reports/2026_07/SEMANTIC_SPACE_CRITICAL_AUDIT_2026_05_24.md | E:\_src\rust-lang\archive\reports\2026_07\SEMANTIC_SPACE_CRITICAL_AUDIT_2026_05_24.md |
| E:\_src\rust-lang\concept\01_foundation\05_collections\01_collections.md | ../../../knowledge/02_intermediate/01_collections.md | E:\_src\rust-lang\knowledge\02_intermediate\01_collections.md |
| E:\_src\rust-lang\concept\01_foundation\06_strings_and_text\01_strings_and_text.md | ../../../knowledge/02_intermediate/05_strings.md | E:\_src\rust-lang\knowledge\02_intermediate\05_strings.md |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\01_traits.md | ../../../knowledge/02_intermediate/06_traits.md | E:\_src\rust-lang\knowledge\02_intermediate\06_traits.md |
| E:\_src\rust-lang\concept\03_advanced\01_async\07_async_closures.md | ../../../knowledge/06_ecosystem/02_edition_2024.md | E:\_src\rust-lang\knowledge\06_ecosystem\02_edition_2024.md |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\01_unsafe.md | ../../../knowledge/03_advanced/unsafe/03_unsafe_rust.md | E:\_src\rust-lang\knowledge\03_advanced\unsafe\03_unsafe_rust.md |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\01_rust_ffi.md | ../../../knowledge/03_advanced/02_ffi.md | E:\_src\rust-lang\knowledge\03_advanced\02_ffi.md |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\05_tree_borrows_deep_dive.md | ../../../archive/docs/content/academic/10_tree_borrows_guide.md | E:\_src\rust-lang\archive\docs\content\academic\10_tree_borrows_guide.md |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\05_tree_borrows_deep_dive.md | ../../../knowledge/04_expert/miri/01_tree_borrows.md | E:\_src\rust-lang\knowledge\04_expert\miri\01_tree_borrows.md |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\04_compiler_internals.md | ../../../knowledge/04_expert/01_compiler_internals.md | E:\_src\rust-lang\knowledge\04_expert\01_compiler_internals.md |
| E:\_src\rust-lang\concept\06_ecosystem\10_performance\01_performance_optimization.md | ../../../knowledge/03_advanced/05_performance_optimization.md | E:\_src\rust-lang\knowledge\03_advanced\05_performance_optimization.md |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_98_preview.md | ../../../archive/reports/2026_07/RUST_198_NIGHTLY_PROBE_2026_06_28.md | E:\_src\rust-lang\archive\reports\2026_07\RUST_198_NIGHTLY_PROBE_2026_06_28.md |
| E:\_src\rust-lang\concept\07_future\01_edition_roadmap\01_rust_edition_preview.md | ../../../knowledge/06_ecosystem/02_edition_2024.md | E:\_src\rust-lang\knowledge\06_ecosystem\02_edition_2024.md |
| E:\_src\rust-lang\concept\07_future\01_edition_roadmap\02_edition_guide.md | ../../../knowledge/06_ecosystem/02_edition_2024.md | E:\_src\rust-lang\knowledge\06_ecosystem\02_edition_2024.md |

## docs/content/knowledge 死链检查

> 扫描范围：`docs/`、`content/`、`knowledge/` 下所有 `.md` 文件中的本地 markdown 链接。
> 排除：`http/https`、`mailto:`、纯锚点 `#`、跨仓库绝对路径 `/`。

| 来源文件 | 行号 | 引用路径 | 解析后的绝对路径 |
|:---|---:|:---|:---|
| content\ecosystem\deep_dives\README.md | 24 | ../../../knowledge/03_advanced/async | content\ecosystem\deep_dives\..\..\..\knowledge\03_advanced\async |
| content\ecosystem\deep_dives\README.md | 32 | ../../../knowledge/03_advanced/concurrency | content\ecosystem\deep_dives\..\..\..\knowledge\03_advanced\concurrency |
| content\ecosystem\deep_dives\README.md | 33 | ../../../knowledge/06_ecosystem/databases | content\ecosystem\deep_dives\..\..\..\knowledge\06_ecosystem\databases |
| content\ecosystem\deep_dives\README.md | 49 | ../../../knowledge/05_reference/03_std_library_cheatsheet.md | content\ecosystem\deep_dives\..\..\..\knowledge\05_reference\03_std_library_cheatsheet.md |
| content\safety_critical\README.md | 22 | ../../knowledge | content\safety_critical\..\..\knowledge |
| docs\00_meta\00_master_index.md | 17 | ../../knowledge | docs\00_meta\..\..\knowledge |
| docs\00_meta\11_reorganization_complete.md | 232 | ../../archive/cargo_package_management_from_c02/00_INDEX.md | docs\00_meta\..\..\archive\cargo_package_management_from_c02\00_INDEX.md |
| docs\00_meta\analysis\00_rust_2026_project_goals_monthly_tracking.md | 392 | ../../../archive/docs/c_class_audit_2026_06_08/00_meta/analysis/00_rust_global_alignment_symmetric_difference_analysis_2026_05.md | docs\00_meta\analysis\..\..\..\archive\docs\c_class_audit_2026_06_08\00_meta\analysis\00_rust_global_alignment_symmetric_difference_analysis_2026_05.md |
| docs\00_meta\analysis\00_rust_2026_project_goals_monthly_tracking.md | 393 | ../../../archive/docs/c_class_audit_2026_06_08/00_meta/analysis/00_rust_global_alignment_symmetric_difference_analysis_2026.md | docs\00_meta\analysis\..\..\..\archive\docs\c_class_audit_2026_06_08\00_meta\analysis\00_rust_global_alignment_symmetric_difference_analysis_2026.md |
| docs\00_meta\analysis\00_rust_2026_project_goals_monthly_tracking.md | 394 | ../../../archive/reports/2026_07/COMPILATION_OPTIMIZATION_REPORT.md | docs\00_meta\analysis\..\..\..\archive\reports\2026_07\COMPILATION_OPTIMIZATION_REPORT.md |
| docs\00_meta\analysis\00_rust_2026_project_goals_monthly_tracking.md | 395 | ../../../archive/reports/2026_07/sccache-benchmark.md | docs\00_meta\analysis\..\..\..\archive\reports\2026_07\sccache-benchmark.md |
| docs\00_meta\history\00_reorganization.md | 215 | ../../../archive/docs/2026_03_reorganization/PROJECT_100_PERCENT_COMPLETION_FINAL.md | docs\00_meta\history\..\..\..\archive\docs\2026_03_reorganization\PROJECT_100_PERCENT_COMPLETION_FINAL.md |
| docs\03_reference\quick_reference\01_ai_ml_cheatsheet.md | 11 | ../../../archive/guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2026.md | docs\03_reference\quick_reference\..\..\..\archive\guides\AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2026.md |
| docs\03_reference\quick_reference\01_ai_ml_cheatsheet.md | 639 | ../../../archive/guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2026.md | docs\03_reference\quick_reference\..\..\..\archive\guides\AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2026.md |
| docs\03_reference\quick_reference\06_cargo_cheatsheet.md | 884 | ../../../archive/cargo_package_management_from_c02/00_INDEX.md | docs\03_reference\quick_reference\..\..\..\archive\cargo_package_management_from_c02\00_INDEX.md |
| docs\03_reference\quick_reference\06_cargo_cheatsheet.md | 893 | ../../../archive/cargo_package_management_from_c02/examples/01_simple_cli.md | docs\03_reference\quick_reference\..\..\..\archive\cargo_package_management_from_c02\examples\01_simple_cli.md |
| docs\03_reference\quick_reference\06_cargo_cheatsheet.md | 894 | ../../../archive/cargo_package_management_from_c02/examples/02_library_with_features.md | docs\03_reference\quick_reference\..\..\..\archive\cargo_package_management_from_c02\examples\02_library_with_features.md |
| docs\03_reference\quick_reference\06_cargo_cheatsheet.md | 895 | ../../../archive/cargo_package_management_from_c02/examples/03_workspace_project.md | docs\03_reference\quick_reference\..\..\..\archive\cargo_package_management_from_c02\examples\03_workspace_project.md |
| docs\03_reference\quick_reference\06_cargo_cheatsheet.md | 919 | ../../../archive/cargo_package_management_from_c02/README.md | docs\03_reference\quick_reference\..\..\..\archive\cargo_package_management_from_c02\README.md |
| docs\03_reference\quick_reference\12_modules_cheatsheet.md | 12 | ../../../archive/cargo_package_management_from_c02/00_INDEX.md | docs\03_reference\quick_reference\..\..\..\archive\cargo_package_management_from_c02\00_INDEX.md |
| docs\03_reference\quick_reference\12_modules_cheatsheet.md | 791 | ../../../archive/cargo_package_management_from_c02/00_INDEX.md | docs\03_reference\quick_reference\..\..\..\archive\cargo_package_management_from_c02\00_INDEX.md |
| docs\03_reference\quick_reference\12_modules_cheatsheet.md | 823 | ../../../archive/cargo_package_management_from_c02/00_INDEX.md | docs\03_reference\quick_reference\..\..\..\archive\cargo_package_management_from_c02\00_INDEX.md |
| docs\03_reference\quick_reference\22_rust_198_nightly_preview_cheatsheet.md | 316 | ../../../knowledge/06_ecosystem/02_edition_2024.md | docs\03_reference\quick_reference\..\..\..\knowledge\06_ecosystem\02_edition_2024.md |
| docs\04_guides\04_embedded_rust_guide.md | 11 | ../../knowledge/03_advanced/unsafe/README.md | docs\04_guides\..\..\knowledge\03_advanced\unsafe\README.md |
| docs\07_thinking\04_multi_dimensional_concept_matrix.md | 16 | ../../knowledge | docs\07_thinking\..\..\knowledge |
| docs\07_thinking\README.md | 22 | ../../knowledge | docs\07_thinking\..\..\knowledge |
| docs\08_usage_guides\02_ai_rust_ecosystem_guide.md | 76 | ../../archive/guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2026.md | docs\08_usage_guides\..\..\archive\guides\AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2026.md |
| docs\08_usage_guides\02_ai_rust_ecosystem_guide.md | 137 | ../../archive/guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2026.md | docs\08_usage_guides\..\..\archive\guides\AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2026.md |
| docs\08_usage_guides\02_ai_rust_ecosystem_guide.md | 496 | ../../archive/guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2026.md | docs\08_usage_guides\..\..\archive\guides\AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2026.md |
| docs\08_usage_guides\02_ai_rust_ecosystem_guide.md | 507 | ../../archive/guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2026.md | docs\08_usage_guides\..\..\archive\guides\AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2026.md |
| docs\08_usage_guides\03_algorithms_usage_guide.md | 50 | ../../knowledge/02_intermediate | docs\08_usage_guides\..\..\knowledge\02_intermediate |
| docs\08_usage_guides\05_cfg_select_macro_guide.md | 344 | ../../knowledge/06_ecosystem/02_edition_2024.md | docs\08_usage_guides\..\..\knowledge\06_ecosystem\02_edition_2024.md |
| docs\09_toolchain\03_rust_1_93_vs_1_92_comparison.md | 10 | ../../archive/docs/06_toolchain/06_05_rust_1_93_vs_1_92_comparison.md | docs\09_toolchain\..\..\archive\docs\06_toolchain\06_05_rust_1_93_vs_1_92_comparison.md |
| docs\09_toolchain\04_rust_1_93_full_changelog.md | 10 | ../../archive/docs/06_toolchain/06_07_rust_1_93_full_changelog.md | docs\09_toolchain\..\..\archive\docs\06_toolchain\06_07_rust_1_93_full_changelog.md |
| docs\09_toolchain\05_rust_1_93_compatibility_deep_dive.md | 10 | ../../archive/docs/06_toolchain/06_09_rust_1_93_compatibility_deep_dive.md | docs\09_toolchain\..\..\archive\docs\06_toolchain\06_09_rust_1_93_compatibility_deep_dive.md |
| docs\09_toolchain\06_rust_1_93_cargo_rustdoc_changes.md | 10 | ../../archive/docs/06_toolchain/06_11_rust_1_93_cargo_rustdoc_changes.md | docs\09_toolchain\..\..\archive\docs\06_toolchain\06_11_rust_1_93_cargo_rustdoc_changes.md |
| docs\09_toolchain\README.md | 506 | ../../archive/docs/2026_05_historical_docs/08_rust_version_evolution_1.89_to_1.93.md | docs\09_toolchain\..\..\archive\docs\2026_05_historical_docs\08_rust_version_evolution_1.89_to_1.93.md |
| docs\09_toolchain\README.md | 508 | ../../archive/docs/2026_05_historical_docs/10_rust_1.89_to_1.93_cumulative_features_overview.md | docs\09_toolchain\..\..\archive\docs\2026_05_historical_docs\10_rust_1.89_to_1.93_cumulative_features_overview.md |
| docs\11_project\04_hierarchy_mapping_master.md | 234 | ../../archive/rust-ownership-decidability/formal-foundations/RUST_FORMAL_SEMANTICS_DEEP.md | docs\11_project\..\..\archive\rust-ownership-decidability\formal-foundations\RUST_FORMAL_SEMANTICS_DEEP.md |
| docs\11_project\README.md | 20 | ../../knowledge | docs\11_project\..\..\knowledge |
| docs\12_research_notes\00_organization_and_navigation.md | 62 | ../../archive/research_notes_2026_06_25/10_contributing.md | docs\12_research_notes\..\..\archive\research_notes_2026_06_25\10_contributing.md |
| docs\12_research_notes\01_alignment_matrices\32_rust_book_alignment.md | 66 | ../../../archive/research_notes/10_cargo_194_features.md | docs\12_research_notes\01_alignment_matrices\..\..\..\archive\research_notes\10_cargo_194_features.md |
| docs\12_research_notes\01_alignment_matrices\32_rust_book_alignment.md | 74 | ../../../archive/research_notes_2026_06_25/10_rust_194_comprehensive_analysis.md | docs\12_research_notes\01_alignment_matrices\..\..\..\archive\research_notes_2026_06_25\10_rust_194_comprehensive_analysis.md |
| docs\12_research_notes\01_alignment_matrices\36_rustbelt_alignment.md | 61 | ../../../archive/deprecated/coq_skeleton/README.md | docs\12_research_notes\01_alignment_matrices\..\..\..\archive\deprecated\coq_skeleton\README.md |
| docs\12_research_notes\01_alignment_matrices\36_rustbelt_alignment.md | 80 | ../../../archive/deprecated/coq_skeleton/README.md | docs\12_research_notes\01_alignment_matrices\..\..\..\archive\deprecated\coq_skeleton\README.md |
| docs\12_research_notes\01_alignment_matrices\36_rustbelt_alignment.md | 82 | ../../../archive/research_notes_2026_06_25/10_coq_isabelle_proof_scaffolding.md | docs\12_research_notes\01_alignment_matrices\..\..\..\archive\research_notes_2026_06_25\10_coq_isabelle_proof_scaffolding.md |
| docs\12_research_notes\01_alignment_matrices\36_rustbelt_alignment.md | 132 | ../../../archive/deprecated/coq_skeleton/README.md | docs\12_research_notes\01_alignment_matrices\..\..\..\archive\deprecated\coq_skeleton\README.md |
| docs\12_research_notes\01_alignment_matrices\36_rustbelt_alignment.md | 132 | ../../../archive/research_notes_2026_06_25/10_coq_isabelle_proof_scaffolding.md | docs\12_research_notes\01_alignment_matrices\..\..\..\archive\research_notes_2026_06_25\10_coq_isabelle_proof_scaffolding.md |
| docs\12_research_notes\01_alignment_matrices\42_toolchain_ecosystem_alignment.md | 57 | ../../../archive/research_notes/10_cargo_194_features.md | docs\12_research_notes\01_alignment_matrices\..\..\..\archive\research_notes\10_cargo_194_features.md |
| docs\12_research_notes\02_formal_methods\05_formal_methods_completeness_checklist.md | 101 | ../../../archive/research_notes_2026_06_25/10_maintenance_guide.md | docs\12_research_notes\02_formal_methods\..\..\..\archive\research_notes_2026_06_25\10_maintenance_guide.md |
| docs\12_research_notes\02_formal_methods\README.md | 232 | ../../../archive/rust-ownership-decidability/actor-specialty/ACTOR_MODEL_DEEP_DIVE.md | docs\12_research_notes\02_formal_methods\..\..\..\archive\rust-ownership-decidability\actor-specialty\ACTOR_MODEL_DEEP_DIVE.md |
| docs\12_research_notes\02_formal_methods\README.md | 260 | ../../../archive/rust-ownership-decidability/actor-specialty/ACTOR_MODEL_DEEP_DIVE.md | docs\12_research_notes\02_formal_methods\..\..\..\archive\rust-ownership-decidability\actor-specialty\ACTOR_MODEL_DEEP_DIVE.md |
| docs\12_research_notes\02_formal_methods\README.md | 297 | ../../../archive/rust-ownership-decidability/actor-specialty/ACTOR_MODEL_DEEP_DIVE.md | docs\12_research_notes\02_formal_methods\..\..\..\archive\rust-ownership-decidability\actor-specialty\ACTOR_MODEL_DEEP_DIVE.md |
| docs\12_research_notes\03_formal_proofs\13_formal_language_and_proofs.md | 409 | ../../../archive/deprecated/coq_skeleton/README.md | docs\12_research_notes\03_formal_proofs\..\..\..\archive\deprecated\coq_skeleton\README.md |
| docs\12_research_notes\03_formal_proofs\14_formal_methods_master_index.md | 77 | ../../../archive/deprecated/coq_skeleton/OWNERSHIP_UNIQUENESS.v | docs\12_research_notes\03_formal_proofs\..\..\..\archive\deprecated\coq_skeleton\OWNERSHIP_UNIQUENESS.v |
| docs\12_research_notes\03_formal_proofs\14_formal_methods_master_index.md | 78 | ../../../archive/deprecated/coq_skeleton/BORROW_DATARACE_FREE.v | docs\12_research_notes\03_formal_proofs\..\..\..\archive\deprecated\coq_skeleton\BORROW_DATARACE_FREE.v |
| docs\12_research_notes\03_formal_proofs\14_formal_methods_master_index.md | 79 | ../../../archive/deprecated/coq_skeleton/TYPE_SAFETY.v | docs\12_research_notes\03_formal_proofs\..\..\..\archive\deprecated\coq_skeleton\TYPE_SAFETY.v |
| docs\12_research_notes\03_formal_proofs\14_formal_methods_master_index.md | 80 | ../../../archive/deprecated/coq_skeleton/DISTRIBUTED_PATTERNS.v | docs\12_research_notes\03_formal_proofs\..\..\..\archive\deprecated\coq_skeleton\DISTRIBUTED_PATTERNS.v |
| docs\12_research_notes\03_formal_proofs\14_formal_methods_master_index.md | 81 | ../../../archive/deprecated/coq_skeleton/WORKFLOW_FORMALIZATION.v | docs\12_research_notes\03_formal_proofs\..\..\..\archive\deprecated\coq_skeleton\WORKFLOW_FORMALIZATION.v |
| docs\12_research_notes\03_formal_proofs\17_formal_verification_guide.md | 74 | ../../../archive/deprecated/coq_skeleton/OWNERSHIP_UNIQUENESS.v | docs\12_research_notes\03_formal_proofs\..\..\..\archive\deprecated\coq_skeleton\OWNERSHIP_UNIQUENESS.v |
| docs\12_research_notes\03_formal_proofs\17_formal_verification_guide.md | 74 | ../../../archive/research_notes_2026_06_25/10_coq_isabelle_proof_scaffolding.md | docs\12_research_notes\03_formal_proofs\..\..\..\archive\research_notes_2026_06_25\10_coq_isabelle_proof_scaffolding.md |
| docs\12_research_notes\03_formal_proofs\18_international_formal_verification_index.md | 61 | ../../../archive/deprecated/coq_skeleton/README.md | docs\12_research_notes\03_formal_proofs\..\..\..\archive\deprecated\coq_skeleton\README.md |
| docs\12_research_notes\03_formal_proofs\18_international_formal_verification_index.md | 91 | ../../../archive/deprecated/coq_skeleton/OWNERSHIP_UNIQUENESS.v | docs\12_research_notes\03_formal_proofs\..\..\..\archive\deprecated\coq_skeleton\OWNERSHIP_UNIQUENESS.v |
| docs\12_research_notes\03_formal_proofs\21_proof_index.md | 111 | ../../../archive/research_notes_2026_06_25/10_coq_isabelle_proof_scaffolding.md | docs\12_research_notes\03_formal_proofs\..\..\..\archive\research_notes_2026_06_25\10_coq_isabelle_proof_scaffolding.md |
| docs\12_research_notes\03_formal_proofs\21_proof_index.md | 664 | ../../../archive/deprecated/coq_skeleton/OWNERSHIP_UNIQUENESS.v | docs\12_research_notes\03_formal_proofs\..\..\..\archive\deprecated\coq_skeleton\OWNERSHIP_UNIQUENESS.v |
| docs\12_research_notes\03_formal_proofs\21_proof_index.md | 664 | ../../../archive/research_notes_2026_06_25/10_coq_isabelle_proof_scaffolding.md | docs\12_research_notes\03_formal_proofs\..\..\..\archive\research_notes_2026_06_25\10_coq_isabelle_proof_scaffolding.md |
| docs\12_research_notes\03_formal_proofs\21_proof_index.md | 860 | ../../../archive/research_notes_2026_06_25/10_progress_tracking.md | docs\12_research_notes\03_formal_proofs\..\..\..\archive\research_notes_2026_06_25\10_progress_tracking.md |
| docs\12_research_notes\03_formal_proofs\21_proof_index.md | 861 | ../../../archive/research_notes_2026_06_25/10_task_checklist.md | docs\12_research_notes\03_formal_proofs\..\..\..\archive\research_notes_2026_06_25\10_task_checklist.md |
| docs\12_research_notes\03_formal_proofs\31_verification_tools_decision_tree.md | 475 | ../../../archive/research_notes_2026_06_25/10_coq_isabelle_proof_scaffolding.md | docs\12_research_notes\03_formal_proofs\..\..\..\archive\research_notes_2026_06_25\10_coq_isabelle_proof_scaffolding.md |
| docs\12_research_notes\03_formal_proofs\33_version_evolution_counterexamples.md | 224 | ../../../archive/research_notes_2026_06_25/10_rust_194_195_feature_matrix.md | docs\12_research_notes\03_formal_proofs\..\..\..\archive\research_notes_2026_06_25\10_rust_194_195_feature_matrix.md |
| docs\12_research_notes\03_formal_proofs\33_version_evolution_counterexamples.md | 225 | ../../../archive/research_notes/10_rust_193_counterexamples_index.md | docs\12_research_notes\03_formal_proofs\..\..\..\archive\research_notes\10_rust_193_counterexamples_index.md |
| docs\12_research_notes\05_type_theory\05_type_system_foundations.md | 20 | ../../../archive/rust-ownership-decidability/formal-foundations/README.md | docs\12_research_notes\05_type_theory\..\..\..\archive\rust-ownership-decidability\formal-foundations\README.md |
| docs\12_research_notes\05_type_theory\06_variance_theory.md | 768 | ../../../archive/docs/c_class_audit_2026_06_08/rust-formal-engineering-system/01_theoretical_foundations/01_type_system/06_variance.md | docs\12_research_notes\05_type_theory\..\..\..\archive\docs\c_class_audit_2026_06_08\rust-formal-engineering-system\01_theoretical_foundations\01_type_system\06_variance.md |
| docs\12_research_notes\05_type_theory\README.md | 309 | ../../../archive/deprecated/coq_skeleton/README.md | docs\12_research_notes\05_type_theory\..\..\..\archive\deprecated\coq_skeleton\README.md |
| docs\12_research_notes\06_concept_models\03_argumentation_gap_index.md | 152 | ../../../archive/deprecated/coq_skeleton/README.md | docs\12_research_notes\06_concept_models\..\..\..\archive\deprecated\coq_skeleton\README.md |
| docs\12_research_notes\06_concept_models\03_argumentation_gap_index.md | 223 | ../../../archive/research_notes_2026_06_25/10_feature_template.md | docs\12_research_notes\06_concept_models\..\..\..\archive\research_notes_2026_06_25\10_feature_template.md |
| docs\12_research_notes\06_concept_models\13_knowledge_graph_index.md | 411 | ../../../archive/research_notes_2026_06_25/10_rust_194_195_feature_matrix.md | docs\12_research_notes\06_concept_models\..\..\..\archive\research_notes_2026_06_25\10_rust_194_195_feature_matrix.md |
| docs\12_research_notes\06_concept_models\13_knowledge_graph_index.md | 515 | ../../../archive/research_notes_2026_06_25/10_rust_194_195_feature_matrix.md | docs\12_research_notes\06_concept_models\..\..\..\archive\research_notes_2026_06_25\10_rust_194_195_feature_matrix.md |
| docs\12_research_notes\06_concept_models\17_unified_systematic_framework.md | 596 | ../../../archive/research_notes/10_rust_193_feature_matrix.md | docs\12_research_notes\06_concept_models\..\..\..\archive\research_notes\10_rust_193_feature_matrix.md |
| docs\12_research_notes\06_concept_models\17_unified_systematic_framework.md | 660 | ../../../archive/research_notes_2026_06_25/10_feature_template.md | docs\12_research_notes\06_concept_models\..\..\..\archive\research_notes_2026_06_25\10_feature_template.md |
| docs\12_research_notes\06_concept_models\18_visualization_index.md | 264 | ../../../archive/research_notes_2026_06_25/10_task_checklist.md | docs\12_research_notes\06_concept_models\..\..\..\archive\research_notes_2026_06_25\10_task_checklist.md |
| docs\12_research_notes\06_concept_models\18_visualization_index.md | 265 | ../../../archive/research_notes_2026_06_25/10_progress_tracking.md | docs\12_research_notes\06_concept_models\..\..\..\archive\research_notes_2026_06_25\10_progress_tracking.md |
| docs\12_research_notes\06_concept_models\18_visualization_index.md | 474 | ../../../archive/research_notes_2026_06_25/10_coq_isabelle_proof_scaffolding.md | docs\12_research_notes\06_concept_models\..\..\..\archive\research_notes_2026_06_25\10_coq_isabelle_proof_scaffolding.md |
| docs\12_research_notes\06_concept_models\18_visualization_index.md | 475 | ../../../archive/research_notes_2026_06_25/10_coq_isabelle_proof_scaffolding.md | docs\12_research_notes\06_concept_models\..\..\..\archive\research_notes_2026_06_25\10_coq_isabelle_proof_scaffolding.md |
| docs\12_research_notes\06_concept_models\18_visualization_index.md | 476 | ../../../archive/research_notes_2026_06_25/10_coq_isabelle_proof_scaffolding.md | docs\12_research_notes\06_concept_models\..\..\..\archive\research_notes_2026_06_25\10_coq_isabelle_proof_scaffolding.md |
| docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\01_creational\01_abstract_factory.md | 663 | ../../../../../archive/research_notes/10_rust_193_counterexamples_index.md | docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\01_creational\..\..\..\..\..\archive\research_notes\10_rust_193_counterexamples_index.md |
| docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\01_creational\02_builder.md | 852 | ../../../../../archive/research_notes/10_rust_193_counterexamples_index.md | docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\01_creational\..\..\..\..\..\archive\research_notes\10_rust_193_counterexamples_index.md |
| docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\01_creational\03_factory_method.md | 652 | ../../../../../archive/research_notes/10_rust_193_counterexamples_index.md | docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\01_creational\..\..\..\..\..\archive\research_notes\10_rust_193_counterexamples_index.md |
| docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\01_creational\04_prototype.md | 633 | ../../../../../archive/research_notes/10_rust_193_counterexamples_index.md | docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\01_creational\..\..\..\..\..\archive\research_notes\10_rust_193_counterexamples_index.md |
| docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\01_creational\05_singleton.md | 630 | ../../../../../archive/research_notes/10_rust_193_counterexamples_index.md | docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\01_creational\..\..\..\..\..\archive\research_notes\10_rust_193_counterexamples_index.md |
| docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\02_structural\01_adapter.md | 714 | ../../../../../archive/research_notes/10_rust_193_counterexamples_index.md | docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\02_structural\..\..\..\..\..\archive\research_notes\10_rust_193_counterexamples_index.md |
| docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\02_structural\02_bridge.md | 647 | ../../../../../archive/research_notes/10_rust_193_counterexamples_index.md | docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\02_structural\..\..\..\..\..\archive\research_notes\10_rust_193_counterexamples_index.md |
| docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\02_structural\03_composite.md | 749 | ../../../../../archive/research_notes/10_rust_193_counterexamples_index.md | docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\02_structural\..\..\..\..\..\archive\research_notes\10_rust_193_counterexamples_index.md |
| docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\02_structural\04_decorator.md | 712 | ../../../../../archive/research_notes/10_rust_193_counterexamples_index.md | docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\02_structural\..\..\..\..\..\archive\research_notes\10_rust_193_counterexamples_index.md |
| docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\02_structural\05_facade.md | 717 | ../../../../../archive/research_notes/10_rust_193_counterexamples_index.md | docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\02_structural\..\..\..\..\..\archive\research_notes\10_rust_193_counterexamples_index.md |
| docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\02_structural\06_flyweight.md | 719 | ../../../../../archive/research_notes/10_rust_193_counterexamples_index.md | docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\02_structural\..\..\..\..\..\archive\research_notes\10_rust_193_counterexamples_index.md |
| docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\02_structural\07_proxy.md | 675 | ../../../../../archive/research_notes/10_rust_193_counterexamples_index.md | docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\02_structural\..\..\..\..\..\archive\research_notes\10_rust_193_counterexamples_index.md |
| docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\03_behavioral\01_chain_of_responsibility.md | 705 | ../../../../../archive/research_notes/10_rust_193_counterexamples_index.md | docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\03_behavioral\..\..\..\..\..\archive\research_notes\10_rust_193_counterexamples_index.md |
| docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\03_behavioral\02_command.md | 731 | ../../../../../archive/research_notes/10_rust_193_counterexamples_index.md | docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\03_behavioral\..\..\..\..\..\archive\research_notes\10_rust_193_counterexamples_index.md |
| docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\03_behavioral\03_interpreter.md | 699 | ../../../../../archive/research_notes/10_rust_193_counterexamples_index.md | docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\03_behavioral\..\..\..\..\..\archive\research_notes\10_rust_193_counterexamples_index.md |
| docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\03_behavioral\04_iterator.md | 604 | ../../../../../archive/research_notes/10_rust_193_counterexamples_index.md | docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\03_behavioral\..\..\..\..\..\archive\research_notes\10_rust_193_counterexamples_index.md |
| docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\03_behavioral\05_mediator.md | 629 | ../../../../../archive/research_notes/10_rust_193_counterexamples_index.md | docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\03_behavioral\..\..\..\..\..\archive\research_notes\10_rust_193_counterexamples_index.md |
| docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\03_behavioral\06_memento.md | 587 | ../../../../../archive/research_notes/10_rust_193_counterexamples_index.md | docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\03_behavioral\..\..\..\..\..\archive\research_notes\10_rust_193_counterexamples_index.md |
| docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\03_behavioral\07_observer.md | 598 | ../../../../../archive/research_notes/10_rust_193_counterexamples_index.md | docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\03_behavioral\..\..\..\..\..\archive\research_notes\10_rust_193_counterexamples_index.md |
| docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\03_behavioral\08_state.md | 666 | ../../../../../archive/research_notes/10_rust_193_counterexamples_index.md | docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\03_behavioral\..\..\..\..\..\archive\research_notes\10_rust_193_counterexamples_index.md |
| docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\03_behavioral\09_strategy.md | 639 | ../../../../../archive/research_notes/10_rust_193_counterexamples_index.md | docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\03_behavioral\..\..\..\..\..\archive\research_notes\10_rust_193_counterexamples_index.md |
| docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\03_behavioral\10_template_method.md | 657 | ../../../../../archive/research_notes/10_rust_193_counterexamples_index.md | docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\03_behavioral\..\..\..\..\..\archive\research_notes\10_rust_193_counterexamples_index.md |
| docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\03_behavioral\11_visitor.md | 643 | ../../../../../archive/research_notes/10_rust_193_counterexamples_index.md | docs\12_research_notes\08_software_design_theory\01_design_patterns_formal\03_behavioral\..\..\..\..\..\archive\research_notes\10_rust_193_counterexamples_index.md |
| docs\12_research_notes\08_software_design_theory\08_crate_architectures\00_crate_architecture_master_index.md | 95 | ../../../../knowledge/06_ecosystem/databases/02_sqlx_deep_dive.md | docs\12_research_notes\08_software_design_theory\08_crate_architectures\..\..\..\..\knowledge\06_ecosystem\databases\02_sqlx_deep_dive.md |
| docs\12_research_notes\08_software_design_theory\08_crate_architectures\00_crate_architecture_master_index.md | 101 | ../../../../knowledge/06_ecosystem/databases/02_sqlx_deep_dive.md | docs\12_research_notes\08_software_design_theory\08_crate_architectures\..\..\..\..\knowledge\06_ecosystem\databases\02_sqlx_deep_dive.md |
| docs\12_research_notes\08_software_design_theory\08_crate_architectures\00_crate_architecture_master_index.md | 589 | ../../../../knowledge/06_ecosystem/databases/02_sqlx_deep_dive.md | docs\12_research_notes\08_software_design_theory\08_crate_architectures\..\..\..\..\knowledge\06_ecosystem\databases\02_sqlx_deep_dive.md |
| docs\12_research_notes\08_software_design_theory\08_crate_architectures\00_crate_architecture_master_index.md | 590 | ../../../../knowledge/06_ecosystem/databases/02_sqlx_deep_dive.md | docs\12_research_notes\08_software_design_theory\08_crate_architectures\..\..\..\..\knowledge\06_ecosystem\databases\02_sqlx_deep_dive.md |
| docs\12_research_notes\08_software_design_theory\08_crate_architectures\00_crate_architecture_master_index.md | 623 | ../../../../archive/rust-ownership-decidability/16-program-semantics/09-workflow-ownership-analysis.md | docs\12_research_notes\08_software_design_theory\08_crate_architectures\..\..\..\..\archive\rust-ownership-decidability\16-program-semantics\09-workflow-ownership-analysis.md |
| docs\12_research_notes\08_software_design_theory\08_crate_architectures\01_serde_architecture.md | 6 | ../../../../archive/content/ecosystem/serialization/serde_best_practices.md | docs\12_research_notes\08_software_design_theory\08_crate_architectures\..\..\..\..\archive\content\ecosystem\serialization\serde_best_practices.md |
| docs\12_research_notes\08_software_design_theory\08_crate_architectures\09_sqlx_architecture.md | 3 | ../../../../knowledge/06_ecosystem/databases/02_sqlx_deep_dive.md | docs\12_research_notes\08_software_design_theory\08_crate_architectures\..\..\..\..\knowledge\06_ecosystem\databases\02_sqlx_deep_dive.md |
| docs\12_research_notes\08_software_design_theory\08_crate_architectures\09_sqlx_architecture.md | 10 | ../../../../knowledge/06_ecosystem/databases/02_sqlx_deep_dive.md | docs\12_research_notes\08_software_design_theory\08_crate_architectures\..\..\..\..\knowledge\06_ecosystem\databases\02_sqlx_deep_dive.md |
| docs\12_research_notes\08_software_design_theory\08_crate_architectures\10_tonic_architecture.md | 5 | ../../../../archive/content/ecosystem/web_frameworks/grpc_microservices_guide.md | docs\12_research_notes\08_software_design_theory\08_crate_architectures\..\..\..\..\archive\content\ecosystem\web_frameworks\grpc_microservices_guide.md |
| docs\12_research_notes\08_software_design_theory\08_crate_architectures\14_actix_web_architecture.md | 6 | ../../../../archive/content/ecosystem/web_frameworks/actix_web_vs_axum.md | docs\12_research_notes\08_software_design_theory\08_crate_architectures\..\..\..\..\archive\content\ecosystem\web_frameworks\actix_web_vs_axum.md |
| docs\12_research_notes\08_software_design_theory\08_crate_architectures\18_sqlx_advanced_architecture.md | 3 | ../../../../knowledge/06_ecosystem/databases/02_sqlx_deep_dive.md | docs\12_research_notes\08_software_design_theory\08_crate_architectures\..\..\..\..\knowledge\06_ecosystem\databases\02_sqlx_deep_dive.md |
| docs\12_research_notes\08_software_design_theory\08_crate_architectures\18_sqlx_advanced_architecture.md | 10 | ../../../../knowledge/06_ecosystem/databases/02_sqlx_deep_dive.md | docs\12_research_notes\08_software_design_theory\08_crate_architectures\..\..\..\..\knowledge\06_ecosystem\databases\02_sqlx_deep_dive.md |
| docs\12_research_notes\10_tutorials_and_guides\03_best_practices.md | 112 | ../../../archive/deprecated/coq_skeleton/README.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\deprecated\coq_skeleton\README.md |
| docs\12_research_notes\10_tutorials_and_guides\03_best_practices.md | 262 | ../../../archive/research_notes_2026_06_25/10_template.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\research_notes_2026_06_25\10_template.md |
| docs\12_research_notes\10_tutorials_and_guides\03_best_practices.md | 680 | ../../../archive/research_notes_2026_06_25/10_contributing.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\research_notes_2026_06_25\10_contributing.md |
| docs\12_research_notes\10_tutorials_and_guides\03_best_practices.md | 819 | ../../../archive/research_notes_2026_06_25/10_template.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\research_notes_2026_06_25\10_template.md |
| docs\12_research_notes\10_tutorials_and_guides\03_best_practices.md | 820 | ../../../archive/research_notes_2026_06_25/10_contributing.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\research_notes_2026_06_25\10_contributing.md |
| docs\12_research_notes\10_tutorials_and_guides\03_best_practices.md | 822 | ../../../archive/research_notes_2026_06_25/10_maintenance_guide.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\research_notes_2026_06_25\10_maintenance_guide.md |
| docs\12_research_notes\10_tutorials_and_guides\05_faq.md | 101 | ../../../archive/research_notes_2026_06_25/10_getting_started.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\research_notes_2026_06_25\10_getting_started.md |
| docs\12_research_notes\10_tutorials_and_guides\05_faq.md | 111 | ../../../archive/research_notes_2026_06_25/10_getting_started.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\research_notes_2026_06_25\10_getting_started.md |
| docs\12_research_notes\10_tutorials_and_guides\05_faq.md | 222 | ../../../archive/research_notes_2026_06_25/10_template.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\research_notes_2026_06_25\10_template.md |
| docs\12_research_notes\10_tutorials_and_guides\05_faq.md | 267 | ../../../archive/research_notes_2026_06_25/10_contributing.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\research_notes_2026_06_25\10_contributing.md |
| docs\12_research_notes\10_tutorials_and_guides\05_faq.md | 268 | ../../../archive/research_notes_2026_06_25/10_template.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\research_notes_2026_06_25\10_template.md |
| docs\12_research_notes\10_tutorials_and_guides\05_faq.md | 280 | ../../../archive/research_notes_2026_06_25/10_template.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\research_notes_2026_06_25\10_template.md |
| docs\12_research_notes\10_tutorials_and_guides\05_faq.md | 288 | ../../../archive/research_notes_2026_06_25/10_contributing.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\research_notes_2026_06_25\10_contributing.md |
| docs\12_research_notes\10_tutorials_and_guides\05_faq.md | 307 | ../../../archive/research_notes_2026_06_25/10_contributing.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\research_notes_2026_06_25\10_contributing.md |
| docs\12_research_notes\10_tutorials_and_guides\05_faq.md | 402 | ../../../archive/research_notes_2026_06_25/10_template.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\research_notes_2026_06_25\10_template.md |
| docs\12_research_notes\10_tutorials_and_guides\05_faq.md | 441 | ../../../archive/research_notes_2026_06_25/10_contributing.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\research_notes_2026_06_25\10_contributing.md |
| docs\12_research_notes\10_tutorials_and_guides\05_faq.md | 454 | ../../../archive/research_notes_2026_06_25/10_getting_started.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\research_notes_2026_06_25\10_getting_started.md |
| docs\12_research_notes\10_tutorials_and_guides\05_faq.md | 457 | ../../../archive/research_notes_2026_06_25/10_contributing.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\research_notes_2026_06_25\10_contributing.md |
| docs\12_research_notes\10_tutorials_and_guides\12_quick_find.md | 316 | ../../../archive/deprecated/coq_skeleton/README.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\deprecated\coq_skeleton\README.md |
| docs\12_research_notes\10_tutorials_and_guides\12_quick_find.md | 316 | ../../../archive/deprecated/README.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\deprecated\README.md |
| docs\12_research_notes\10_tutorials_and_guides\12_quick_find.md | 377 | ../../../archive/research_notes_2026_06_25/10_writing_guide.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\research_notes_2026_06_25\10_writing_guide.md |
| docs\12_research_notes\10_tutorials_and_guides\12_quick_find.md | 449 | ../../../archive/research_notes_2026_06_25/10_progress_tracking.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\research_notes_2026_06_25\10_progress_tracking.md |
| docs\12_research_notes\10_tutorials_and_guides\12_quick_find.md | 450 | ../../../archive/research_notes_2026_06_25/10_task_checklist.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\research_notes_2026_06_25\10_task_checklist.md |
| docs\12_research_notes\10_tutorials_and_guides\12_quick_find.md | 451 | ../../../archive/research_notes_2026_06_25/10_statistics.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\research_notes_2026_06_25\10_statistics.md |
| docs\12_research_notes\10_tutorials_and_guides\12_quick_find.md | 459 | ../../../archive/research_notes_2026_06_25/10_writing_guide.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\research_notes_2026_06_25\10_writing_guide.md |
| docs\12_research_notes\10_tutorials_and_guides\13_quick_reference.md | 169 | ../../../archive/deprecated/coq_skeleton/README.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\deprecated\coq_skeleton\README.md |
| docs\12_research_notes\10_tutorials_and_guides\13_quick_reference.md | 169 | ../../../archive/deprecated/README.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\deprecated\README.md |
| docs\12_research_notes\10_tutorials_and_guides\13_quick_reference.md | 355 | ../../../archive/research_notes_2026_06_25/10_getting_started.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\research_notes_2026_06_25\10_getting_started.md |
| docs\12_research_notes\10_tutorials_and_guides\13_quick_reference.md | 357 | ../../../archive/research_notes_2026_06_25/10_maintenance_guide.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\research_notes_2026_06_25\10_maintenance_guide.md |
| docs\12_research_notes\10_tutorials_and_guides\13_quick_reference.md | 362 | ../../../archive/research_notes_2026_06_25/10_example.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\research_notes_2026_06_25\10_example.md |
| docs\12_research_notes\10_tutorials_and_guides\13_quick_reference.md | 366 | ../../../archive/research_notes_2026_06_25/10_feature_template.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\research_notes_2026_06_25\10_feature_template.md |
| docs\12_research_notes\10_tutorials_and_guides\15_resources.md | 360 | ../../../archive/deprecated/coq_skeleton/README.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\deprecated\coq_skeleton\README.md |
| docs\12_research_notes\10_tutorials_and_guides\15_resources.md | 406 | ../../../archive/deprecated/coq_skeleton/README.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\deprecated\coq_skeleton\README.md |
| docs\12_research_notes\10_tutorials_and_guides\16_tools_guide.md | 79 | ../../../archive/deprecated/README.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\deprecated\README.md |
| docs\12_research_notes\10_tutorials_and_guides\16_tools_guide.md | 308 | ../../../archive/deprecated/README.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\deprecated\README.md |
| docs\12_research_notes\10_tutorials_and_guides\22_user_guide.md | 302 | ../../../archive/research_notes_2026_06_25/10_project_maintenance_guide.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\research_notes_2026_06_25\10_project_maintenance_guide.md |
| docs\12_research_notes\10_tutorials_and_guides\22_user_guide.md | 309 | ../../../archive/research_notes_2026_06_25/10_project_maintenance_guide.md | docs\12_research_notes\10_tutorials_and_guides\..\..\..\archive\research_notes_2026_06_25\10_project_maintenance_guide.md |
| docs\12_research_notes\13_meta_reports\02_changelog.md | 132 | ../../../archive/research_notes/10_rust_193_counterexamples_index.md | docs\12_research_notes\13_meta_reports\..\..\..\archive\research_notes\10_rust_193_counterexamples_index.md |
| docs\12_research_notes\13_meta_reports\02_changelog.md | 219 | ../../../archive/research_notes_2026_06_25/10_feature_template.md | docs\12_research_notes\13_meta_reports\..\..\..\archive\research_notes_2026_06_25\10_feature_template.md |
| docs\12_research_notes\13_meta_reports\03_classification.md | 66 | ../../../archive/research_notes_2026_06_25/10_writing_guide.md | docs\12_research_notes\13_meta_reports\..\..\..\archive\research_notes_2026_06_25\10_writing_guide.md |
| docs\12_research_notes\13_meta_reports\03_classification.md | 67 | ../../../archive/research_notes_2026_06_25/10_contributing.md | docs\12_research_notes\13_meta_reports\..\..\..\archive\research_notes_2026_06_25\10_contributing.md |
| docs\12_research_notes\13_meta_reports\03_classification.md | 67 | ../../../archive/research_notes_2026_06_25/10_maintenance_guide.md | docs\12_research_notes\13_meta_reports\..\..\..\archive\research_notes_2026_06_25\10_maintenance_guide.md |
| docs\12_research_notes\13_meta_reports\03_classification.md | 67 | ../../../archive/research_notes_2026_06_25/10_statistics.md | docs\12_research_notes\13_meta_reports\..\..\..\archive\research_notes_2026_06_25\10_statistics.md |
| docs\12_research_notes\13_meta_reports\03_classification.md | 68 | ../../../archive/research_notes_2026_06_25/10_example.md | docs\12_research_notes\13_meta_reports\..\..\..\archive\research_notes_2026_06_25\10_example.md |
| docs\12_research_notes\13_meta_reports\03_classification.md | 68 | ../../../archive/research_notes_2026_06_25/10_getting_started.md | docs\12_research_notes\13_meta_reports\..\..\..\archive\research_notes_2026_06_25\10_getting_started.md |
| docs\12_research_notes\13_meta_reports\03_classification.md | 69 | ../../../archive/research_notes_2026_06_25/10_task_checklist.md | docs\12_research_notes\13_meta_reports\..\..\..\archive\research_notes_2026_06_25\10_task_checklist.md |
| docs\12_research_notes\13_meta_reports\03_classification.md | 69 | ../../../archive/research_notes_2026_06_25/10_progress_tracking.md | docs\12_research_notes\13_meta_reports\..\..\..\archive\research_notes_2026_06_25\10_progress_tracking.md |
| docs\12_research_notes\13_meta_reports\05_comprehensive_summary.md | 194 | ../../../archive/research_notes/10_rust_193_counterexamples_index.md | docs\12_research_notes\13_meta_reports\..\..\..\archive\research_notes\10_rust_193_counterexamples_index.md |
| docs\12_research_notes\13_meta_reports\05_comprehensive_summary.md | 197 | ../../../archive/deprecated/README.md | docs\12_research_notes\13_meta_reports\..\..\..\archive\deprecated\README.md |
| docs\12_research_notes\13_meta_reports\08_content_enhancement.md | 275 | ../../../archive/research_notes_2026_06_25/10_maintenance_guide.md | docs\12_research_notes\13_meta_reports\..\..\..\archive\research_notes_2026_06_25\10_maintenance_guide.md |
| docs\12_research_notes\13_meta_reports\08_content_enhancement.md | 714 | ../../../archive/research_notes_2026_06_25/10_writing_guide.md | docs\12_research_notes\13_meta_reports\..\..\..\archive\research_notes_2026_06_25\10_writing_guide.md |
| docs\12_research_notes\13_meta_reports\08_content_enhancement.md | 715 | ../../../archive/research_notes_2026_06_25/10_template.md | docs\12_research_notes\13_meta_reports\..\..\..\archive\research_notes_2026_06_25\10_template.md |
| docs\12_research_notes\13_meta_reports\08_content_enhancement.md | 732 | ../../../archive/research_notes_2026_06_25/10_example.md | docs\12_research_notes\13_meta_reports\..\..\..\archive\research_notes_2026_06_25\10_example.md |
| docs\12_research_notes\13_meta_reports\10_incremental_update_flow.md | 286 | ../../../archive/research_notes_2026_06_25/10_maintenance_guide.md | docs\12_research_notes\13_meta_reports\..\..\..\archive\research_notes_2026_06_25\10_maintenance_guide.md |
| docs\12_research_notes\13_meta_reports\10_incremental_update_flow.md | 288 | ../../../archive/research_notes_2026_06_25/10_feature_template.md | docs\12_research_notes\13_meta_reports\..\..\..\archive\research_notes_2026_06_25\10_feature_template.md |
| docs\12_research_notes\13_meta_reports\10_incremental_update_flow.md | 307 | ../../../archive/research_notes/10_rust_191_research_update_2025_11_15.md | docs\12_research_notes\13_meta_reports\..\..\..\archive\research_notes\10_rust_191_research_update_2025_11_15.md |
| docs\12_research_notes\13_meta_reports\10_incremental_update_flow.md | 308 | ../../../archive/research_notes/10_rust_192_research_update_2025_12_11.md | docs\12_research_notes\13_meta_reports\..\..\..\archive\research_notes\10_rust_192_research_update_2025_12_11.md |
| docs\12_research_notes\13_meta_reports\10_incremental_update_flow.md | 319 | ../../../archive/research_notes_2026_06_25/10_coq_isabelle_proof_scaffolding.md | docs\12_research_notes\13_meta_reports\..\..\..\archive\research_notes_2026_06_25\10_coq_isabelle_proof_scaffolding.md |
| docs\12_research_notes\13_meta_reports\11_quality_checklist.md | 471 | ../../../archive/research_notes_2026_06_25/10_template.md | docs\12_research_notes\13_meta_reports\..\..\..\archive\research_notes_2026_06_25\10_template.md |
| docs\12_research_notes\13_meta_reports\11_quality_checklist.md | 501 | ../../../archive/research_notes_2026_06_25/10_template.md | docs\12_research_notes\13_meta_reports\..\..\..\archive\research_notes_2026_06_25\10_template.md |
| docs\12_research_notes\13_meta_reports\11_quality_checklist.md | 502 | ../../../archive/research_notes_2026_06_25/10_contributing.md | docs\12_research_notes\13_meta_reports\..\..\..\archive\research_notes_2026_06_25\10_contributing.md |
| docs\12_research_notes\13_meta_reports\13_research_notes_organization.md | 120 | ../../../archive/docs/deprecated/README.md | docs\12_research_notes\13_meta_reports\..\..\..\archive\docs\deprecated\README.md |
| docs\12_research_notes\13_meta_reports\13_research_notes_organization.md | 121 | ../../../archive/docs/deprecated/coq_skeleton/README.md | docs\12_research_notes\13_meta_reports\..\..\..\archive\docs\deprecated\coq_skeleton\README.md |
| docs\12_research_notes\13_meta_reports\13_research_notes_organization.md | 121 | ../../../archive/deprecated/coq_skeleton/README.md | docs\12_research_notes\13_meta_reports\..\..\..\archive\deprecated\coq_skeleton\README.md |
| docs\12_research_notes\13_meta_reports\16_system_summary.md | 316 | ../../../archive/research_notes_2026_06_25/10_template.md | docs\12_research_notes\13_meta_reports\..\..\..\archive\research_notes_2026_06_25\10_template.md |
| docs\12_research_notes\13_meta_reports\16_system_summary.md | 324 | ../../../archive/research_notes_2026_06_25/10_contributing.md | docs\12_research_notes\13_meta_reports\..\..\..\archive\research_notes_2026_06_25\10_contributing.md |
| docs\12_research_notes\13_meta_reports\16_system_summary.md | 381 | ../../../archive/research_notes_2026_06_25/10_getting_started.md | docs\12_research_notes\13_meta_reports\..\..\..\archive\research_notes_2026_06_25\10_getting_started.md |
| docs\12_research_notes\13_meta_reports\16_system_summary.md | 390 | ../../../archive/research_notes_2026_06_25/10_contributing.md | docs\12_research_notes\13_meta_reports\..\..\..\archive\research_notes_2026_06_25\10_contributing.md |
| docs\12_research_notes\13_meta_reports\16_system_summary.md | 392 | ../../../archive/research_notes_2026_06_25/10_template.md | docs\12_research_notes\13_meta_reports\..\..\..\archive\research_notes_2026_06_25\10_template.md |
| docs\12_research_notes\13_meta_reports\16_system_summary.md | 538 | ../../../archive/deprecated/coq_skeleton/OWNERSHIP_UNIQUENESS.v | docs\12_research_notes\13_meta_reports\..\..\..\archive\deprecated\coq_skeleton\OWNERSHIP_UNIQUENESS.v |
| docs\12_research_notes\13_meta_reports\16_system_summary.md | 539 | ../../../archive/deprecated/coq_skeleton/BORROW_DATARACE_FREE.v | docs\12_research_notes\13_meta_reports\..\..\..\archive\deprecated\coq_skeleton\BORROW_DATARACE_FREE.v |
| docs\12_research_notes\13_meta_reports\16_system_summary.md | 540 | ../../../archive/deprecated/coq_skeleton/TYPE_SAFETY.v | docs\12_research_notes\13_meta_reports\..\..\..\archive\deprecated\coq_skeleton\TYPE_SAFETY.v |
| docs\12_research_notes\README.md | 275 | ../../archive/docs/temp/README.md | docs\12_research_notes\..\..\archive\docs\temp\README.md |
| docs\12_research_notes\README.md | 337 | ../../archive/research_notes_2026_06_25/10_getting_started.md | docs\12_research_notes\..\..\archive\research_notes_2026_06_25\10_getting_started.md |
| docs\12_research_notes\README.md | 345 | ../../archive/research_notes_2026_06_25/10_template.md | docs\12_research_notes\..\..\archive\research_notes_2026_06_25\10_template.md |
| docs\12_research_notes\README.md | 357 | ../../archive/research_notes_2026_06_25/10_contributing.md | docs\12_research_notes\..\..\archive\research_notes_2026_06_25\10_contributing.md |
| docs\12_research_notes\README.md | 359 | ../../archive/research_notes_2026_06_25/10_template.md | docs\12_research_notes\..\..\archive\research_notes_2026_06_25\10_template.md |
| docs\12_research_notes\README.md | 360 | ../../archive/research_notes_2026_06_25/10_progress_tracking.md | docs\12_research_notes\..\..\archive\research_notes_2026_06_25\10_progress_tracking.md |
| docs\12_research_notes\README.md | 361 | ../../archive/research_notes_2026_06_25/10_task_checklist.md | docs\12_research_notes\..\..\archive\research_notes_2026_06_25\10_task_checklist.md |
| docs\12_research_notes\README.md | 362 | ../../archive/research_notes_2026_06_25/10_writing_guide.md | docs\12_research_notes\..\..\archive\research_notes_2026_06_25\10_writing_guide.md |
| docs\12_research_notes\README.md | 470 | ../../archive/research_notes/10_rust_191_research_update_2025_11_15.md | docs\12_research_notes\..\..\archive\research_notes\10_rust_191_research_update_2025_11_15.md |
| docs\12_research_notes\README.md | 470 | ../../archive/research_notes/10_rust_192_research_update_2025_12_11.md | docs\12_research_notes\..\..\archive\research_notes\10_rust_192_research_update_2025_12_11.md |
| docs\12_research_notes\README.md | 520 | ../../archive/research_notes_2026_06_25/10_getting_started.md | docs\12_research_notes\..\..\archive\research_notes_2026_06_25\10_getting_started.md |
| docs\12_research_notes\README.md | 522 | ../../archive/research_notes_2026_06_25/10_maintenance_guide.md | docs\12_research_notes\..\..\archive\research_notes_2026_06_25\10_maintenance_guide.md |
| docs\12_research_notes\README.md | 527 | ../../archive/research_notes_2026_06_25/10_example.md | docs\12_research_notes\..\..\archive\research_notes_2026_06_25\10_example.md |
| docs\12_research_notes\README.md | 552 | ../../archive/research_notes_2026_06_25/10_getting_started.md | docs\12_research_notes\..\..\archive\research_notes_2026_06_25\10_getting_started.md |
| docs\13_templates\01_versioned_doc_template.md | 20 | ../../archive/docs/2026_03_reorganization/VERSION_INDEX.md | docs\13_templates\..\..\archive\docs\2026_03_reorganization\VERSION_INDEX.md |
| docs\13_templates\01_versioned_doc_template.md | 220 | ../../archive/docs/2026_03_reorganization/VERSION_INDEX.md | docs\13_templates\..\..\archive\docs\2026_03_reorganization\VERSION_INDEX.md |
| docs\13_templates\01_versioned_doc_template.md | 326 | ../../archive/docs/2026_03_reorganization/VERSION_INDEX.md | docs\13_templates\..\..\archive\docs\2026_03_reorganization\VERSION_INDEX.md |
| docs\README.md | 28 | ../archive/docs/c_class_audit_2026_06_08/02_reference/quick_reference | docs\..\archive\docs\c_class_audit_2026_06_08\02_reference\quick_reference |

## 文件详细统计

| 文件 | 层级 | 行数 | ⟹ | ⟸ | 模板 | 反命题 | Mermaid | 代码块 | 过渡段 | 认知路径 | 前置 | 后置 | 受众 | 分级 |
|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|
| E:\_src\rust-lang\concept\00_meta\00_framework\bloom_taxonomy.md | L0 | 201 | 1 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\boundary_extension_tree.md | L0 | 362 | 1 | 0 | 0 | 1 | 3 | 1 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\cognitive_dimension_matrix.md | L0 | 403 | 1 | 0 | 0 | 1 | 2 | 0 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\competency_graph.md | L0 | 429 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\comprehensive_rust_mapping.md | L0 | 240 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\concept_definition_decision_forest.md | L0 | 1175 | 3 | 0 | 0 | 1 | 10 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\cpp_rust_engineering_roadmap.md | L0 | 263 | 0 | 0 | 0 | 0 | 2 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\decidability_spectrum.md | L0 | 963 | 2 | 0 | 0 | 1 | 6 | 2 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\expressiveness_multiview.md | L0 | 829 | 0 | 0 | 0 | 1 | 7 | 7 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\fault_tree_analysis_collection.md | L0 | 806 | 1 | 0 | 0 | 1 | 7 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\knowledge_mindmap.md | L0 | 308 | 1 | 0 | 0 | 1 | 2 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\methodology.md | L0 | 586 | 1 | 0 | 0 | 2 | 5 | 1 | 6 | ✅ | ✅ | ✅ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\paradigm_transition_matrix.md | L0 | 330 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\pattern_semantic_space_index.md | L0 | 206 | 0 | 0 | 0 | 0 | 2 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\pl_foundations_roadmap.md | L0 | 182 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\semantic_bridge_algorithms_patterns.md | L0 | 735 | 1 | 0 | 0 | 1 | 0 | 7 | 6 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\semantic_expressiveness.md | L0 | 1133 | 1 | 0 | 0 | 1 | 2 | 1 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\semantic_space.md | L0 | 1360 | 10 | 0 | 0 | 2 | 5 | 9 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\theorem_inference_forest.md | L0 | 557 | 15 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\theorem_registry.md | L0 | 219 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\todos.md | L0 | 349 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\01_terminology\01_terminology_glossary.md | L0 | 466 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\01_terminology\02_bilingual_template_v2.md | L0 | 327 | 0 | 2 | 0 | 5 | 1 | 5 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\01_terminology\03_bilingual_template.md | L0 | 166 | 0 | 0 | 0 | 1 | 1 | 1 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\02_sources\01_authority_source_map.md | L0 | 217 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\02_sources\02_rustbelt_predicate_map.md | L0 | 435 | 9 | 0 | 0 | 1 | 6 | 0 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\02_sources\03_sources.md | L0 | 495 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 研究者级 |
| E:\_src\rust-lang\concept\00_meta\02_sources\04_topic_authority_alignment_map.md | L0 | 393 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\00_meta\02_sources\05_international_authority_index.md | L0 | 251 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 研究者 / 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\01_concept_audit_guide.md | L0 | 109 | 1 | 0 | 0 | 1 | 1 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\02_asp_marking_guide.md | L0 | 552 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\03_audit_checklist.md | L0 | 484 | 2 | 1 | 0 | 2 | 1 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\04_concept_consistency_audit_checklist.md | L0 | 15 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\05_template_deduplication_guide.md | L0 | 95 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\06_grading_system.md | L0 | 163 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\07_quality_dashboard_v2.md | L0 | 330 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\08_feature_inventory_methodology.md | L0 | 50 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\01_cross_reference_matrix.md | L0 | 17 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\02_career_landscape.md | L0 | 236 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\03_concept_index.md | L0 | 795 | 4 | 0 | 0 | 2 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\04_inter_layer_map.md | L0 | 634 | 12 | 0 | 0 | 1 | 2 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\05_inter_layer_topology.md | L0 | 17 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ✅ | ❌ | ❌ | 初学者 | 专家级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\06_intra_layer_model_map.md | L0 | 367 | 11 | 0 | 0 | 1 | 5 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\07_learning_guide.md | L0 | 692 | 3 | 0 | 0 | 1 | 1 | 0 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\08_learning_mvp_path.md | L0 | 372 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ✅ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\09_navigation.md | L0 | 295 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\10_problem_graph.md | L0 | 552 | 1 | 0 | 0 | 1 | 7 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\11_quick_reference.md | L0 | 859 | 1 | 0 | 0 | 1 | 0 | 25 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\12_self_assessment.md | L0 | 2298 | 0 | 0 | 0 | 1 | 0 | 57 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\13_foundations_gap_closure_index.md | L0 | 147 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\14_learning_mvp_path_en.md | L0 | 292 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\15_quiz_registry.md | L0 | 150 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\05_quizzes\01_quiz_meta_framework.md | L0 | 373 | 0 | 0 | 0 | 0 | 0 | 2 | 0 | ❌ | ✅ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\06_trpl_3rd_ed_mapping.md | L0 | 13 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\07_placeholders\01_placeholder_generic.md | L0 | 25 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\07_trpl_3rd_edition_alignment.md | L0 | 82 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\08_usability_testing_framework.md | L0 | 129 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\01_concept_definition_atlas.md | L0 | 566 | 1 | 1 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\02_attribute_relationship_atlas.md | L0 | 561 | 27 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\03_scenario_decision_tree_atlas.md | L0 | 620 | 0 | 0 | 0 | 0 | 9 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\04_example_counterexample_atlas.md | L0 | 541 | 1 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\05_logical_reasoning_atlas.md | L0 | 191 | 17 | 2 | 0 | 0 | 4 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\06_inter_layer_mapping_atlas.md | L0 | 203 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\07_intra_layer_mapping_atlas.md | L0 | 594 | 347 | 33 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\08_concept_source_alignment_atlas.md | L0 | 52 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\09_reasoning_judgment_tree_atlas.md | L0 | 742 | 4 | 0 | 0 | 0 | 8 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\10_gap_and_action_plan.md | L0 | 78 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\11_semantic_model_atlas.md | L0 | 521 | 0 | 0 | 0 | 1 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\kg_ontology_v2.md | L0 | 331 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\kg_tlo_alignment.md | L0 | 264 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\00_start.md | L1 | 343 | 4 | 2 | 0 | 1 | 2 | 3 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\01_pl_prerequisites.md | L1 | 598 | 3 | 2 | 0 | 0 | 1 | 14 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\02_zero_cost_abstractions.md | L1 | 919 | 3 | 2 | 0 | 2 | 3 | 14 | 2 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\03_closure_basics.md | L1 | 951 | 4 | 2 | 0 | 2 | 2 | 18 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\04_effects_and_purity.md | L1 | 849 | 0 | 0 | 0 | 2 | 1 | 17 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\05_std_io_and_process.md | L1 | 503 | 4 | 4 | 0 | 4 | 2 | 10 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\06_keywords.md | L1 | 292 | 0 | 0 | 0 | 0 | 1 | 4 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\07_operators_and_symbols.md | L1 | 279 | 0 | 0 | 0 | 0 | 1 | 2 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\00_ownership_borrow_lifetime_knowledge_map.md | L1 | 447 | 5 | 2 | 0 | 1 | 6 | 0 | 5 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\01_ownership.md | L1 | 2020 | 27 | 2 | 0 | 3 | 8 | 46 | 16 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\02_borrowing.md | L1 | 2159 | 13 | 3 | 0 | 3 | 7 | 53 | 20 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\03_lifetimes.md | L1 | 1557 | 23 | 2 | 0 | 3 | 6 | 40 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\04_lifetimes_advanced.md | L1 | 1894 | 3 | 2 | 0 | 1 | 1 | 49 | 10 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\05_move_semantics.md | L1 | 363 | 3 | 0 | 0 | 0 | 1 | 6 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\06_ownership_inventories_brown_book.md | L1 | 226 | 0 | 0 | 0 | 0 | 1 | 3 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\01_type_system.md | L1 | 3376 | 23 | 2 | 0 | 3 | 13 | 63 | 16 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\02_never_type.md | L1 | 678 | 3 | 2 | 0 | 0 | 1 | 16 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\03_numerics.md | L1 | 1146 | 3 | 2 | 0 | 2 | 2 | 19 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\04_coercion_and_casting.md | L1 | 1072 | 3 | 2 | 0 | 2 | 2 | 18 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\05_data_abstraction_spectrum.md | L1 | 877 | 0 | 0 | 0 | 2 | 1 | 14 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\03_values_and_references\01_reference_semantics.md | L1 | 1522 | 4 | 2 | 0 | 3 | 8 | 35 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\03_values_and_references\02_value_vs_reference_semantics.md | L1 | 281 | 0 | 0 | 0 | 0 | 1 | 5 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\03_values_and_references\03_variable_model.md | L1 | 757 | 0 | 0 | 0 | 2 | 1 | 12 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\04_control_flow\01_control_flow.md | L1 | 1749 | 3 | 2 | 0 | 2 | 6 | 25 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\04_control_flow\02_patterns.md | L1 | 400 | 0 | 0 | 0 | 0 | 1 | 14 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\04_control_flow\03_let_chains.md | L1 | 495 | 0 | 0 | 0 | 4 | 1 | 24 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\04_control_flow\04_statements_and_expressions.md | L1 | 306 | 0 | 0 | 0 | 0 | 1 | 7 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\04_control_flow\05_let_else.md | L1 | 362 | 0 | 0 | 0 | 2 | 1 | 11 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\05_collections\01_collections.md | L1 | 938 | 3 | 2 | 0 | 2 | 3 | 16 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\05_collections\02_collections_advanced.md | L1 | 1067 | 6 | 2 | 0 | 2 | 3 | 11 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\06_strings_and_text\01_strings_and_text.md | L1 | 947 | 3 | 2 | 0 | 2 | 2 | 19 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\06_strings_and_text\02_strings_and_encoding.md | L1 | 908 | 4 | 2 | 0 | 2 | 3 | 9 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\06_strings_and_text\03_formatting_and_display.md | L1 | 481 | 4 | 3 | 0 | 4 | 2 | 9 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\01_modules_and_paths.md | L1 | 993 | 10 | 2 | 0 | 2 | 2 | 11 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\02_functions.md | L1 | 447 | 4 | 2 | 0 | 1 | 1 | 10 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\03_use_declarations.md | L1 | 318 | 4 | 2 | 0 | 1 | 1 | 10 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\04_structs.md | L1 | 395 | 9 | 2 | 0 | 1 | 1 | 8 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\05_enumerations.md | L1 | 392 | 9 | 2 | 0 | 1 | 1 | 10 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\06_implementations.md | L1 | 377 | 5 | 2 | 0 | 1 | 1 | 8 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\07_type_aliases.md | L1 | 460 | 4 | 3 | 0 | 4 | 2 | 10 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\08_static_items.md | L1 | 449 | 4 | 3 | 0 | 4 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\09_const_items_and_const_fn.md | L1 | 473 | 5 | 3 | 0 | 4 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\10_preludes.md | L1 | 267 | 0 | 0 | 0 | 0 | 1 | 6 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\11_crates_and_source_files.md | L1 | 378 | 4 | 2 | 0 | 2 | 3 | 7 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\12_items.md | L1 | 434 | 4 | 2 | 0 | 1 | 2 | 14 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\08_error_handling\01_error_handling_basics.md | L1 | 1078 | 3 | 2 | 0 | 2 | 2 | 15 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\08_error_handling\02_error_handling_control_flow.md | L1 | 382 | 3 | 3 | 0 | 1 | 2 | 11 | 7 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\08_error_handling\03_panic_and_abort.md | L1 | 1020 | 8 | 2 | 0 | 2 | 2 | 12 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\09_macros_basics\01_attributes_and_macros.md | L1 | 993 | 3 | 2 | 0 | 2 | 2 | 14 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\10_testing_basics\01_testing_basics.md | L1 | 815 | 3 | 2 | 0 | 2 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\10_testing_basics\02_useful_development_tools.md | L1 | 341 | 4 | 2 | 0 | 1 | 3 | 2 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\01_quiz_type_system.md | L1 | 610 | 0 | 0 | 0 | 0 | 0 | 14 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\02_quiz_error_handling.md | L1 | 744 | 0 | 0 | 0 | 1 | 0 | 20 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\03_quiz_modules_testing.md | L1 | 800 | 0 | 0 | 0 | 0 | 0 | 22 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\04_quiz_closures_iterators.md | L1 | 788 | 0 | 0 | 0 | 0 | 0 | 33 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\05_quiz_pl_foundations.md | L1 | 269 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\06_quiz_ownership_borrowing.md | L1 | 597 | 0 | 0 | 0 | 0 | 0 | 18 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\01_traits.md | L2 | 3202 | 15 | 2 | 0 | 7 | 6 | 76 | 10 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\02_dispatch_mechanisms.md | L2 | 2338 | 14 | 2 | 0 | 1 | 1 | 42 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\03_serde_patterns.md | L2 | 941 | 3 | 3 | 0 | 2 | 3 | 9 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\04_advanced_traits.md | L2 | 1046 | 3 | 3 | 0 | 2 | 2 | 21 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\05_construction_and_initialization.md | L2 | 346 | 1 | 0 | 0 | 0 | 1 | 7 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\06_derive_traits.md | L2 | 410 | 2 | 0 | 0 | 0 | 1 | 12 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\07_generic_associated_types.md | L2 | 676 | 0 | 0 | 0 | 0 | 3 | 14 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\08_negative_impls.md | L2 | 358 | 0 | 0 | 0 | 2 | 1 | 13 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\09_associated_type_defaults.md | L2 | 387 | 0 | 0 | 0 | 2 | 1 | 12 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\01_generics.md | L2 | 3350 | 23 | 2 | 0 | 7 | 7 | 74 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\02_const_generics.md | L2 | 616 | 2 | 0 | 0 | 4 | 1 | 15 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\03_type_level_programming.md | L2 | 885 | 8 | 2 | 0 | 1 | 1 | 13 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\04_quiz_traits_and_generics.md | L2 | 762 | 0 | 0 | 0 | 0 | 0 | 20 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\05_const_generics_and_trait_objects.md | L2 | 235 | 0 | 0 | 0 | 1 | 2 | 4 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\01_memory_management.md | L2 | 2279 | 23 | 3 | 0 | 7 | 6 | 57 | 7 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\02_interior_mutability.md | L2 | 973 | 9 | 3 | 0 | 2 | 3 | 11 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\03_cow_and_borrowed.md | L2 | 819 | 4 | 3 | 0 | 2 | 3 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\04_smart_pointers.md | L2 | 977 | 9 | 3 | 0 | 2 | 3 | 12 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\05_quiz_memory_management.md | L2 | 810 | 0 | 0 | 0 | 0 | 0 | 27 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\03_error_handling\01_error_handling.md | L2 | 2932 | 22 | 4 | 0 | 7 | 9 | 63 | 7 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\03_error_handling\02_error_handling_deep_dive.md | L2 | 861 | 3 | 3 | 0 | 2 | 2 | 9 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\03_error_handling\03_panic.md | L2 | 272 | 0 | 0 | 0 | 0 | 1 | 4 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\02_intermediate\03_error_handling\04_exception_safety_rust_cpp.md | L2 | 371 | 2 | 0 | 0 | 0 | 1 | 6 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\01_range_types.md | L2 | 709 | 3 | 3 | 0 | 2 | 3 | 12 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\02_closure_types.md | L2 | 878 | 11 | 3 | 0 | 2 | 4 | 17 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\03_newtype_and_wrapper.md | L2 | 852 | 3 | 3 | 0 | 2 | 2 | 12 | 2 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\04_type_system_advanced.md | L2 | 1307 | 3 | 3 | 0 | 2 | 2 | 18 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\05_rtti_and_dynamic_typing.md | L2 | 352 | 0 | 0 | 0 | 0 | 1 | 7 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\06_unions.md | L2 | 468 | 4 | 3 | 0 | 4 | 2 | 7 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\07_type_conversions.md | L2 | 499 | 4 | 4 | 0 | 4 | 2 | 10 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\02_intermediate\05_modules_and_visibility\01_module_system.md | L2 | 912 | 8 | 3 | 0 | 2 | 4 | 15 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\05_modules_and_visibility\02_friend_vs_module_privacy.md | L2 | 323 | 0 | 0 | 0 | 0 | 1 | 5 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\05_modules_and_visibility\03_api_naming_conventions.md | L2 | 570 | 0 | 0 | 0 | 0 | 1 | 17 | 2 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\01_assert_matches.md | L2 | 786 | 3 | 3 | 0 | 2 | 4 | 18 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\02_dsl_and_embedding.md | L2 | 893 | 5 | 3 | 0 | 2 | 2 | 11 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\03_macro_patterns.md | L2 | 881 | 4 | 3 | 0 | 2 | 2 | 9 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\04_metaprogramming.md | L2 | 923 | 3 | 3 | 0 | 2 | 3 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\05_c_preprocessor_vs_rust_macros.md | L2 | 308 | 0 | 0 | 0 | 0 | 1 | 6 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\06_attributes_by_category.md | L2 | 514 | 4 | 4 | 0 | 4 | 2 | 10 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\02_intermediate\07_iterators_and_closures\01_iterator_patterns.md | L2 | 1466 | 13 | 2 | 0 | 1 | 2 | 23 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\08_quizzes\30_quiz_cpp_rust_foundations.md | L2 | 307 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\01_concurrency.md | L3 | 2194 | 21 | 2 | 0 | 3 | 13 | 27 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\02_send_sync_auto_traits.md | L3 | 623 | 10 | 1 | 0 | 4 | 2 | 13 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\03_concurrency_patterns.md | L3 | 2376 | 3 | 3 | 0 | 2 | 4 | 34 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\04_send_sync_boundaries.md | L3 | 484 | 0 | 0 | 0 | 4 | 1 | 10 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\05_cross_platform_concurrency.md | L3 | 269 | 6 | 2 | 0 | 1 | 1 | 5 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\06_atomics_and_memory_ordering.md | L3 | 1563 | 8 | 3 | 0 | 2 | 3 | 24 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\07_lock_free.md | L3 | 1272 | 3 | 3 | 0 | 2 | 2 | 20 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\08_parallel_distributed_pattern_spectrum.md | L3 | 1152 | 3 | 3 | 0 | 2 | 1 | 18 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\09_quiz_concurrency_async.md | L3 | 799 | 0 | 0 | 0 | 0 | 0 | 19 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\10_quiz_semantic_models.md | L3 | 437 | 1 | 0 | 0 | 0 | 0 | 4 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\01_async.md | L3 | 3522 | 21 | 3 | 0 | 6 | 10 | 63 | 3 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\02_async_advanced.md | L3 | 703 | 5 | 3 | 0 | 0 | 1 | 14 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\03_async_patterns.md | L3 | 1327 | 3 | 3 | 0 | 2 | 2 | 22 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\04_future_and_executor_mechanisms.md | L3 | 1284 | 8 | 2 | 0 | 2 | 1 | 20 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\05_async_cancellation_safety.md | L3 | 570 | 0 | 0 | 0 | 5 | 2 | 11 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\06_async_boundary_panorama.md | L3 | 545 | 26 | 0 | 0 | 6 | 3 | 10 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\07_async_closures.md | L3 | 673 | 3 | 0 | 0 | 1 | 1 | 20 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\08_pin_unpin.md | L3 | 1037 | 6 | 3 | 0 | 2 | 3 | 22 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\09_stream_algebra_and_backpressure.md | L3 | 504 | 5 | 2 | 0 | 1 | 3 | 7 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\10_executor_fairness_and_scheduling.md | L3 | 377 | 11 | 3 | 0 | 1 | 2 | 5 | 2 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\11_pin_projection_counterexamples.md | L3 | 456 | 5 | 2 | 0 | 5 | 3 | 8 | 2 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\12_waker_contract_deep_dive.md | L3 | 397 | 11 | 0 | 0 | 3 | 4 | 4 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\13_async_trait_object_safety.md | L3 | 353 | 4 | 0 | 0 | 0 | 3 | 7 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\14_gat_async_boundary.md | L3 | 524 | 0 | 0 | 0 | 0 | 2 | 12 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\15_state_machine_semantics.md | L3 | 210 | 0 | 0 | 0 | 1 | 1 | 5 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\00_before_formal.md | L3 | 187 | 0 | 0 | 0 | 0 | 2 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\01_unsafe.md | L3 | 3555 | 18 | 2 | 0 | 4 | 11 | 63 | 3 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\02_unsafe_boundary_panorama.md | L3 | 506 | 19 | 0 | 0 | 5 | 3 | 12 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\03_nll_and_polonius.md | L3 | 911 | 3 | 3 | 0 | 3 | 2 | 13 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\04_unsafe_rust_patterns.md | L3 | 86 | 3 | 0 | 0 | 1 | 1 | 2 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\05_quiz_unsafe.md | L3 | 704 | 0 | 0 | 0 | 0 | 0 | 21 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\06_memory_model.md | L3 | 500 | 5 | 2 | 0 | 1 | 1 | 9 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\07_unsafe_reference.md | L3 | 331 | 3 | 2 | 0 | 1 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\08_async_in_unsafe_contexts.md | L3 | 274 | 0 | 0 | 0 | 4 | 2 | 5 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\01_macros.md | L3 | 2573 | 26 | 3 | 0 | 8 | 9 | 59 | 8 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\02_proc_macro.md | L3 | 1180 | 3 | 3 | 0 | 2 | 3 | 14 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\03_proc_macro_code_generation_optimization.md | L3 | 447 | 7 | 2 | 0 | 1 | 1 | 13 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\04_macro_debugging_and_diagnostics.md | L3 | 439 | 7 | 2 | 0 | 1 | 1 | 9 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\05_production_grade_macro_development.md | L3 | 459 | 7 | 2 | 0 | 1 | 1 | 10 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\06_macro_glossary.md | L3 | 746 | 8 | 2 | 0 | 1 | 1 | 27 | 6 | ✅ | ✅ | ✅ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\07_macro_faq.md | L3 | 871 | 8 | 2 | 0 | 1 | 1 | 37 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\08_syn_quote_reference.md | L3 | 1263 | 8 | 3 | 0 | 2 | 1 | 36 | 6 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\09_macro_hygiene.md | L3 | 1008 | 8 | 2 | 0 | 2 | 1 | 32 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\10_quiz_macros.md | L3 | 771 | 0 | 0 | 0 | 0 | 0 | 24 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\11_conditional_compilation.md | L3 | 345 | 0 | 0 | 0 | 0 | 1 | 11 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\01_rust_ffi.md | L3 | 1045 | 3 | 3 | 0 | 2 | 4 | 18 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\02_ffi_advanced.md | L3 | 983 | 3 | 3 | 0 | 2 | 2 | 12 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\03_linkage.md | L3 | 488 | 1 | 0 | 0 | 1 | 1 | 16 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\04_async_ffi_boundary.md | L3 | 225 | 0 | 0 | 0 | 2 | 2 | 2 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\05_unsafe_extern_blocks.md | L3 | 554 | 0 | 0 | 0 | 3 | 2 | 14 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\05_inline_assembly\01_inline_assembly.md | L3 | 883 | 0 | 0 | 0 | 1 | 1 | 27 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\01_custom_allocators.md | L3 | 906 | 3 | 3 | 0 | 2 | 2 | 12 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\02_zero_copy_parsing.md | L3 | 952 | 3 | 3 | 0 | 2 | 2 | 13 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\03_type_erasure.md | L3 | 923 | 4 | 3 | 0 | 2 | 2 | 11 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\04_network_programming.md | L3 | 1111 | 3 | 3 | 0 | 2 | 3 | 16 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\05_stream_processing_semantics.md | L3 | 952 | 3 | 3 | 0 | 1 | 1 | 8 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\06_ownership_performance_optimization.md | L3 | 231 | 4 | 0 | 0 | 1 | 1 | 10 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\07_rust_runtime.md | L3 | 315 | 3 | 2 | 0 | 1 | 1 | 8 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\08_memory_allocation_and_lifetime.md | L3 | 208 | 0 | 0 | 0 | 0 | 1 | 8 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\09_variables.md | L3 | 209 | 0 | 0 | 0 | 0 | 1 | 8 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\10_visibility_and_privacy.md | L3 | 239 | 0 | 0 | 0 | 0 | 2 | 8 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\07_unsafe_internals\01_unsafe_collections_internals.md | L3 | 546 | 4 | 4 | 0 | 4 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\01_process_model_and_lifecycle.md | L3 | 520 | 8 | 2 | 0 | 2 | 2 | 5 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\02_advanced_process_management.md | L3 | 366 | 8 | 2 | 0 | 1 | 2 | 5 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\03_async_process_management.md | L3 | 441 | 8 | 2 | 0 | 2 | 2 | 11 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\04_cross_platform_process_management.md | L3 | 365 | 8 | 2 | 0 | 2 | 2 | 7 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\05_ipc_mechanisms.md | L3 | 327 | 8 | 2 | 0 | 1 | 2 | 8 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\06_process_monitoring_and_diagnostics.md | L3 | 349 | 8 | 2 | 0 | 1 | 2 | 7 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\07_process_security_and_sandboxing.md | L3 | 310 | 8 | 2 | 0 | 1 | 2 | 9 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\08_process_performance_engineering.md | L3 | 284 | 8 | 2 | 0 | 1 | 2 | 5 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\09_process_testing_and_benchmarking.md | L3 | 299 | 8 | 2 | 0 | 1 | 2 | 7 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\10_modern_process_libraries.md | L3 | 281 | 8 | 2 | 0 | 1 | 2 | 8 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\01_type_theory.md | L4 | 1830 | 29 | 0 | 0 | 4 | 6 | 27 | 3 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\02_subtype_variance.md | L4 | 669 | 5 | 0 | 0 | 2 | 3 | 10 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\03_type_inference.md | L4 | 789 | 3 | 0 | 0 | 2 | 3 | 9 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\04_category_theory.md | L4 | 855 | 3 | 0 | 0 | 2 | 2 | 11 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\05_lambda_calculus.md | L4 | 786 | 3 | 0 | 0 | 2 | 2 | 11 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\06_type_semantics.md | L4 | 978 | 5 | 0 | 0 | 3 | 1 | 18 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\07_type_checking_and_inference.md | L4 | 476 | 1 | 0 | 0 | 2 | 1 | 12 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\08_type_inference_complexity.md | L4 | 452 | 0 | 0 | 0 | 2 | 1 | 8 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\09_type_system_reference.md | L4 | 456 | 0 | 0 | 0 | 1 | 1 | 3 | 6 | ❌ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\10_dependent_refinement_types.md | L4 | 929 | 0 | 0 | 0 | 5 | 1 | 14 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\01_linear_logic.md | L4 | 1291 | 14 | 0 | 0 | 4 | 6 | 13 | 3 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\02_ownership_formal.md | L4 | 1696 | 11 | 0 | 0 | 1 | 6 | 17 | 3 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\03_linear_logic_applications.md | L4 | 778 | 3 | 0 | 0 | 2 | 2 | 10 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\04_borrow_checking_decidability.md | L4 | 467 | 3 | 0 | 0 | 1 | 3 | 10 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\05_tree_borrows_deep_dive.md | L4 | 220 | 0 | 0 | 0 | 1 | 1 | 3 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\06_behavior_considered_undefined.md | L4 | 211 | 0 | 0 | 0 | 0 | 1 | 2 | 0 | ❌ | ✅ | ✅ | 专家 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\01_rustbelt.md | L4 | 1471 | 5 | 0 | 0 | 1 | 6 | 16 | 10 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\02_separation_logic.md | L4 | 871 | 4 | 0 | 0 | 2 | 2 | 10 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\03_safety_tags_in_formal.md | L4 | 20 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\04_borrow_sanitizer_in_formal.md | L4 | 213 | 0 | 0 | 0 | 1 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\01_denotational_semantics.md | L4 | 710 | 3 | 0 | 0 | 4 | 2 | 9 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\02_hoare_logic.md | L4 | 924 | 3 | 0 | 0 | 2 | 3 | 8 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\03_operational_semantics.md | L4 | 1124 | 3 | 0 | 0 | 2 | 2 | 13 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\04_evaluation_strategies.md | L4 | 721 | 0 | 0 | 0 | 2 | 1 | 14 | 0 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\05_axiomatic_semantics.md | L4 | 1063 | 5 | 0 | 0 | 4 | 1 | 15 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\06_aeneas_symbolic_semantics.md | L4 | 491 | 1 | 0 | 0 | 0 | 2 | 4 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\07_constant_evaluation.md | L4 | 222 | 0 | 0 | 0 | 0 | 1 | 6 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\01_verification_toolchain.md | L4 | 1586 | 3 | 0 | 0 | 0 | 5 | 17 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\02_formal_methods.md | L4 | 28 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\03_aerospace_certification_formal_methods.md | L4 | 1148 | 3 | 0 | 0 | 1 | 2 | 7 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\04_modern_verification_tools.md | L4 | 581 | 3 | 0 | 0 | 1 | 1 | 10 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\05_programming_language_foundations.md | L4 | 510 | 3 | 0 | 0 | 1 | 1 | 12 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\06_quiz_formal_methods.md | L4 | 708 | 0 | 0 | 0 | 0 | 1 | 10 | 0 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\07_autoverus.md | L4 | 242 | 1 | 0 | 0 | 1 | 1 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\08_miri.md | L4 | 367 | 0 | 0 | 0 | 3 | 2 | 4 | 0 | ❌ | ✅ | ✅ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\09_kani.md | L4 | 427 | 0 | 0 | 0 | 1 | 1 | 11 | 0 | ❌ | ✅ | ✅ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\10_certified_toolchains_and_packages.md | L4 | 267 | 0 | 0 | 0 | 1 | 2 | 2 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\01_rustc_query_system.md | L4 | 640 | 1 | 0 | 0 | 1 | 4 | 5 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\02_mir_codegen_llvm_primer.md | L4 | 420 | 8 | 3 | 0 | 2 | 2 | 3 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\03_trait_solver_in_rustc.md | L4 | 476 | 3 | 3 | 0 | 1 | 2 | 10 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\04_name_resolution_and_hir.md | L4 | 375 | 0 | 0 | 0 | 3 | 2 | 7 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\05_application_binary_interface.md | L4 | 283 | 0 | 0 | 0 | 1 | 1 | 8 | 0 | ❌ | ✅ | ✅ | 专家 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\06_names_and_resolution.md | L4 | 264 | 2 | 0 | 0 | 1 | 1 | 4 | 6 | ✅ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\07_special_types_and_traits.md | L4 | 242 | 2 | 0 | 0 | 0 | 1 | 2 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\08_type_layout.md | L4 | 206 | 0 | 0 | 0 | 0 | 1 | 6 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\09_destructors.md | L4 | 235 | 0 | 0 | 0 | 0 | 1 | 5 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\10_lexical_structure.md | L4 | 301 | 3 | 0 | 0 | 1 | 1 | 8 | 6 | ✅ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\11_items_reference.md | L4 | 302 | 3 | 0 | 0 | 1 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\12_attributes.md | L4 | 230 | 3 | 0 | 0 | 1 | 1 | 7 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\13_statements_and_expressions_reference.md | L4 | 213 | 3 | 0 | 0 | 1 | 1 | 7 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\14_patterns_reference.md | L4 | 209 | 3 | 0 | 0 | 1 | 1 | 6 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\15_generics_compiler_behavior.md | L4 | 227 | 4 | 0 | 0 | 1 | 1 | 7 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\16_names_reference.md | L4 | 207 | 3 | 0 | 0 | 1 | 1 | 4 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\17_reference_appendices.md | L4 | 208 | 2 | 0 | 0 | 1 | 1 | 3 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\06_notation\01_notation.md | L4 | 175 | 0 | 0 | 0 | 0 | 2 | 2 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\07_concurrency_semantics\01_process_calculi_for_rust.md | L4 | 366 | 6 | 0 | 0 | 4 | 2 | 6 | 8 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\07_concurrency_semantics\02_linearizability_and_consistency.md | L4 | 369 | 10 | 0 | 0 | 3 | 2 | 2 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\07_concurrency_semantics\03_actor_semantics.md | L4 | 348 | 18 | 0 | 0 | 3 | 2 | 4 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\07_concurrency_semantics\04_algebraic_effects.md | L4 | 799 | 0 | 0 | 0 | 4 | 1 | 4 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\07_concurrency_semantics\05_stm_semantics.md | L4 | 827 | 1 | 0 | 0 | 5 | 1 | 5 | 2 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\07_concurrency_semantics\06_distributed_consensus_theory.md | L4 | 858 | 23 | 0 | 0 | 7 | 1 | 3 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\00_paradigms\01_paradigm_matrix.md | L5 | 1300 | 8 | 0 | 0 | 5 | 9 | 12 | 16 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\00_paradigms\02_execution_model_isomorphism.md | L5 | 1049 | 3 | 0 | 0 | 1 | 6 | 13 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\05_comparative\00_paradigms\03_cpp_rust_surface_features.md | L5 | 296 | 0 | 0 | 0 | 0 | 1 | 4 | 0 | ❌ | ✅ | ✅ | 进阶 | 研究者级 |
| E:\_src\rust-lang\concept\05_comparative\00_paradigms\04_five_models_definition_matrix.md | L5 | 156 | 10 | 0 | 0 | 0 | 2 | 0 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\00_paradigms\05_language_semantic_model_matrix.md | L5 | 560 | 4 | 0 | 0 | 6 | 2 | 0 | 2 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\01_rust_vs_cpp.md | L5 | 2223 | 9 | 0 | 0 | 3 | 11 | 14 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\02_cpp_abi_object_model.md | L5 | 975 | 4 | 0 | 0 | 2 | 1 | 18 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\03_rust_vs_go.md | L5 | 1038 | 3 | 0 | 0 | 3 | 7 | 11 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\04_rust_vs_ruby.md | L5 | 786 | 3 | 0 | 0 | 2 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\05_rust_vs_swift.md | L5 | 766 | 3 | 0 | 0 | 2 | 2 | 6 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\06_rust_vs_zig.md | L5 | 800 | 3 | 0 | 0 | 2 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\07_rust_vs_ada_spark.md | L5 | 569 | 0 | 0 | 0 | 1 | 1 | 3 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\08_rust_vs_d.md | L5 | 702 | 0 | 0 | 0 | 1 | 1 | 7 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\09_rust_vs_nim.md | L5 | 656 | 0 | 0 | 0 | 1 | 1 | 4 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\01_rust_vs_java.md | L5 | 658 | 3 | 0 | 0 | 2 | 4 | 7 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\02_rust_vs_python.md | L5 | 747 | 3 | 0 | 0 | 2 | 3 | 6 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\03_rust_vs_javascript.md | L5 | 758 | 3 | 0 | 0 | 2 | 3 | 5 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\04_rust_vs_kotlin.md | L5 | 850 | 3 | 0 | 0 | 2 | 2 | 6 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\05_rust_vs_scala.md | L5 | 810 | 3 | 0 | 0 | 2 | 2 | 6 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\06_rust_vs_csharp.md | L5 | 895 | 4 | 0 | 0 | 2 | 2 | 6 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\07_rust_vs_elixir.md | L5 | 943 | 3 | 0 | 0 | 3 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\08_rust_vs_typescript.md | L5 | 974 | 3 | 0 | 0 | 2 | 3 | 6 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\09_rust_vs_haskell.md | L5 | 799 | 0 | 0 | 0 | 1 | 1 | 8 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\10_rust_vs_ocaml.md | L5 | 821 | 0 | 0 | 0 | 2 | 2 | 10 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\11_rust_vs_fsharp.md | L5 | 800 | 0 | 0 | 0 | 2 | 2 | 7 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\03_domain_comparisons\01_safety_boundaries.md | L5 | 1074 | 8 | 0 | 0 | 1 | 8 | 9 | 9 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\05_comparative\03_domain_comparisons\02_quiz_rust_vs_systems.md | L5 | 798 | 0 | 0 | 0 | 0 | 0 | 14 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\01_toolchain.md | L6 | 1973 | 13 | 0 | 0 | 2 | 10 | 16 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\02_logging_observability.md | L6 | 724 | 3 | 0 | 0 | 2 | 4 | 9 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\03_devops_and_ci_cd.md | L6 | 905 | 3 | 0 | 0 | 2 | 3 | 7 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\04_compiler_internals.md | L6 | 918 | 3 | 0 | 0 | 2 | 1 | 7 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\05_compiler_infrastructure.md | L6 | 334 | 3 | 0 | 0 | 1 | 1 | 1 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\06_quiz_toolchain.md | L6 | 668 | 0 | 0 | 0 | 1 | 0 | 9 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\07_rustdoc_196_changes.md | L6 | 368 | 0 | 0 | 0 | 0 | 1 | 4 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\08_platform_rust_integration.md | L6 | 361 | 0 | 0 | 0 | 1 | 1 | 6 | 2 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\09_llvm_backend_and_codegen.md | L6 | 338 | 0 | 0 | 0 | 0 | 1 | 1 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\10_rustc_driver_and_stable_mir.md | L6 | 295 | 0 | 0 | 0 | 0 | 1 | 4 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\11_compiler_diagnostics_and_ui_tests.md | L6 | 308 | 0 | 0 | 0 | 0 | 1 | 5 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\12_rustc_bootstrap.md | L6 | 293 | 0 | 0 | 0 | 1 | 1 | 3 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\13_compiler_testing.md | L6 | 309 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\14_development_tools.md | L6 | 273 | 0 | 0 | 0 | 1 | 1 | 7 | 0 | ❌ | ✅ | ✅ | 初学者 | 入门级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\15_z_flags_reference.md | L6 | 198 | 0 | 0 | 0 | 1 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\01_cargo_script.md | L6 | 776 | 3 | 0 | 0 | 1 | 3 | 12 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\02_public_private_deps.md | L6 | 307 | 4 | 0 | 0 | 1 | 2 | 2 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\03_resolver_v3_public_feature_unification.md | L6 | 227 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\04_cargo_196_features.md | L6 | 339 | 0 | 0 | 0 | 1 | 1 | 3 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\05_cargo_build_scripts.md | L6 | 571 | 0 | 0 | 0 | 3 | 3 | 16 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\06_cargo_dependency_resolution.md | L6 | 593 | 0 | 0 | 0 | 1 | 1 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\07_cargo_source_replacement.md | L6 | 325 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\08_cargo_registries_and_publishing.md | L6 | 373 | 0 | 0 | 0 | 1 | 1 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\09_cargo_authentication_and_cache.md | L6 | 345 | 0 | 0 | 0 | 1 | 1 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\10_cargo_manifest_reference.md | L6 | 356 | 0 | 0 | 0 | 1 | 1 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\11_cargo_profiles_and_lints.md | L6 | 363 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\12_cargo_subcommands_and_plugins.md | L6 | 287 | 0 | 0 | 0 | 1 | 1 | 3 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\13_cargo_security_cves.md | L6 | 557 | 4 | 0 | 0 | 4 | 2 | 2 | 2 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\14_cargo_workspaces.md | L6 | 306 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\15_cargo_getting_started.md | L6 | 215 | 0 | 0 | 0 | 1 | 2 | 2 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\16_cargo_workflow.md | L6 | 223 | 0 | 0 | 0 | 1 | 1 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\17_cargo_guide_practices.md | L6 | 218 | 0 | 0 | 0 | 1 | 2 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\18_cargo_configuration.md | L6 | 243 | 0 | 0 | 0 | 1 | 1 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\19_cargo_commands_reference.md | L6 | 226 | 0 | 0 | 0 | 1 | 1 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\20_cargo_manifest_targets.md | L6 | 221 | 0 | 0 | 0 | 0 | 1 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\21_cargo_registry_internals.md | L6 | 203 | 0 | 0 | 0 | 1 | 1 | 2 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\22_build_std.md | L6 | 380 | 3 | 0 | 0 | 0 | 3 | 3 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\23_cargo_197_features.md | L6 | 291 | 0 | 0 | 0 | 1 | 1 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\02_core_crates\01_core_crates.md | L6 | 1406 | 8 | 0 | 0 | 2 | 7 | 17 | 3 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\01_patterns.md | L6 | 3217 | 17 | 0 | 0 | 2 | 6 | 47 | 8 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\02_idioms_spectrum.md | L6 | 1525 | 4 | 0 | 0 | 1 | 5 | 37 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\03_system_design_principles.md | L6 | 833 | 3 | 0 | 0 | 1 | 7 | 10 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\04_system_composability.md | L6 | 823 | 0 | 0 | 0 | 0 | 5 | 23 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\05_microservice_patterns.md | L6 | 1035 | 3 | 0 | 0 | 1 | 7 | 15 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\06_event_driven_architecture.md | L6 | 1054 | 3 | 0 | 0 | 1 | 5 | 15 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\07_cqrs_event_sourcing.md | L6 | 1563 | 3 | 0 | 0 | 3 | 2 | 20 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\08_architecture_patterns.md | L6 | 1364 | 3 | 0 | 0 | 2 | 1 | 13 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\09_pattern_implementation_comparison.md | L6 | 1011 | 4 | 0 | 0 | 1 | 1 | 19 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\10_pattern_selection_best_practices.md | L6 | 849 | 4 | 0 | 0 | 1 | 1 | 13 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\11_formal_design_pattern_theory.md | L6 | 1142 | 4 | 0 | 0 | 1 | 1 | 18 | 6 | ❌ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\12_frontier_research_and_innovative_patterns.md | L6 | 1086 | 4 | 0 | 0 | 1 | 1 | 19 | 6 | ❌ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\13_engineering_and_production_patterns.md | L6 | 379 | 3 | 0 | 0 | 1 | 1 | 9 | 6 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\14_design_patterns_glossary.md | L6 | 323 | 4 | 0 | 0 | 1 | 1 | 6 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\15_design_patterns_faq.md | L6 | 564 | 4 | 0 | 0 | 0 | 1 | 5 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\16_pattern_composition_algebra.md | L6 | 792 | 3 | 0 | 0 | 2 | 1 | 15 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\17_workflow_theory.md | L6 | 1481 | 3 | 0 | 0 | 2 | 1 | 17 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\18_api_design_patterns.md | L6 | 1408 | 3 | 0 | 0 | 3 | 1 | 21 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\01_distributed_systems.md | L6 | 853 | 3 | 0 | 0 | 2 | 2 | 9 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\02_cloud_native.md | L6 | 848 | 3 | 0 | 0 | 2 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\03_web_frameworks.md | L6 | 1107 | 4 | 0 | 0 | 3 | 4 | 11 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\04_http_client_development.md | L6 | 246 | 0 | 0 | 0 | 0 | 1 | 10 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\05_glommio_and_thread_per_core.md | L6 | 285 | 3 | 0 | 0 | 0 | 1 | 7 | 6 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\06_websocket_realtime_communication.md | L6 | 857 | 4 | 0 | 0 | 0 | 1 | 12 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\07_network_protocols.md | L6 | 591 | 3 | 0 | 0 | 1 | 1 | 9 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\08_high_performance_network_service_architecture.md | L6 | 2189 | 3 | 0 | 0 | 0 | 1 | 21 | 6 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\09_reactive_programming.md | L6 | 1142 | 3 | 0 | 0 | 2 | 1 | 14 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\10_tokio_runtime_internals.md | L6 | 358 | 8 | 0 | 0 | 1 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\01_wasi.md | L6 | 699 | 4 | 0 | 0 | 4 | 3 | 11 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\02_cross_compilation.md | L6 | 690 | 3 | 0 | 0 | 2 | 2 | 5 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\03_embedded_systems.md | L6 | 1013 | 3 | 0 | 0 | 2 | 2 | 10 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\04_cli_development.md | L6 | 832 | 3 | 0 | 0 | 2 | 2 | 9 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\05_os_kernel.md | L6 | 550 | 3 | 0 | 0 | 1 | 1 | 12 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\06_robotics.md | L6 | 1093 | 3 | 0 | 0 | 2 | 1 | 15 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\07_embedded_graphics.md | L6 | 1212 | 3 | 0 | 0 | 3 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\08_c_to_rust_translation.md | L6 | 499 | 3 | 0 | 0 | 1 | 1 | 4 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\09_embedded_hal_1_0_migration.md | L6 | 330 | 3 | 0 | 0 | 0 | 1 | 6 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\10_target_tier_platform_support.md | L6 | 145 | 0 | 0 | 0 | 1 | 1 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\11_async_no_std_embedded.md | L6 | 228 | 0 | 0 | 0 | 2 | 2 | 3 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\12_gpu_programming_and_hpc.md | L6 | 852 | 0 | 0 | 0 | 6 | 1 | 10 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\01_application_domains.md | L6 | 1564 | 8 | 0 | 0 | 2 | 7 | 12 | 3 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\02_database_access.md | L6 | 871 | 3 | 0 | 0 | 2 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\03_stream_processing_ecosystem.md | L6 | 637 | 3 | 0 | 0 | 1 | 1 | 12 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\04_database_systems.md | L6 | 617 | 3 | 0 | 0 | 1 | 1 | 11 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\05_data_engineering.md | L6 | 1031 | 3 | 0 | 0 | 2 | 1 | 13 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\06_distributed_consensus.md | L6 | 994 | 4 | 0 | 0 | 2 | 1 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\07_rust_for_data_science.md | L6 | 683 | 3 | 0 | 0 | 2 | 1 | 10 | 0 | ✅ | ✅ | ✅ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\08_crdt_type_zoo.md | L6 | 367 | 17 | 0 | 0 | 6 | 1 | 6 | 4 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\09_causal_ordering_vector_clocks.md | L6 | 329 | 9 | 0 | 0 | 5 | 1 | 1 | 4 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\07_security_and_cryptography\01_security_practices.md | L6 | 1105 | 3 | 0 | 0 | 2 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\07_security_and_cryptography\02_security_cryptography.md | L6 | 1035 | 3 | 0 | 0 | 3 | 1 | 18 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\07_security_and_cryptography\03_cargo_vet_supply_chain.md | L6 | 256 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\08_formal_verification\01_formal_ecosystem_tower.md | L6 | 639 | 1 | 0 | 0 | 1 | 3 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\08_formal_verification\02_formal_verification_tools.md | L6 | 1054 | 3 | 0 | 0 | 3 | 1 | 14 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_testing_and_quality\01_testing_strategies.md | L6 | 759 | 3 | 0 | 0 | 2 | 3 | 9 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_testing_and_quality\02_documentation.md | L6 | 713 | 3 | 0 | 0 | 3 | 3 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_testing_and_quality\03_testing.md | L6 | 807 | 3 | 0 | 0 | 3 | 3 | 10 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_testing_and_quality\04_benchmarking.md | L6 | 250 | 0 | 0 | 0 | 0 | 1 | 7 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\10_performance\01_performance_optimization.md | L6 | 1186 | 3 | 0 | 0 | 2 | 2 | 13 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\01_blockchain.md | L6 | 972 | 7 | 0 | 0 | 0 | 3 | 15 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\02_game_ecs.md | L6 | 1415 | 1 | 0 | 0 | 1 | 8 | 25 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\03_webassembly.md | L6 | 712 | 3 | 0 | 0 | 2 | 4 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\04_licensing_and_compliance.md | L6 | 701 | 3 | 0 | 0 | 2 | 2 | 6 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\05_game_development.md | L6 | 709 | 3 | 0 | 0 | 2 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\06_game_development.md | L6 | 23 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\07_algorithms_competitive_programming.md | L6 | 1349 | 0 | 0 | 0 | 1 | 1 | 31 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\08_algorithm_engineering_practice.md | L6 | 2181 | 3 | 0 | 0 | 1 | 1 | 25 | 6 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\09_data_structures_in_rust.md | L6 | 337 | 3 | 0 | 0 | 0 | 2 | 10 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\10_algorithm_complexity_analysis.md | L6 | 243 | 0 | 0 | 0 | 0 | 1 | 6 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\11_cutting_edge_algorithms.md | L6 | 290 | 3 | 0 | 0 | 0 | 1 | 4 | 6 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\12_formal_algorithm_theory.md | L6 | 337 | 3 | 0 | 0 | 0 | 1 | 6 | 6 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\13_machine_learning_ecosystem.md | L6 | 1031 | 3 | 0 | 0 | 2 | 1 | 14 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\14_industrial_case_studies.md | L6 | 541 | 3 | 0 | 0 | 1 | 1 | 7 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\15_game_engine_internals.md | L6 | 1200 | 3 | 0 | 0 | 2 | 1 | 13 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\16_quantum_computing_rust.md | L6 | 1075 | 3 | 0 | 0 | 2 | 1 | 12 | 0 | ✅ | ✅ | ✅ | 研究者 | 实验级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\17_webassembly_advanced.md | L6 | 1251 | 3 | 0 | 0 | 2 | 1 | 16 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\18_wasm_glossary.md | L6 | 443 | 4 | 0 | 0 | 0 | 1 | 0 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\19_wasm_faq.md | L6 | 546 | 4 | 0 | 0 | 0 | 1 | 7 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\20_wasm_javascript_interop.md | L6 | 603 | 4 | 0 | 0 | 1 | 1 | 7 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\21_safety_critical_topic_index.md | L6 | 49 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\22_autosar_and_rust.md | L6 | 205 | 0 | 0 | 0 | 0 | 2 | 1 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\12_networking\01_advanced_network_protocols.md | L6 | 332 | 3 | 0 | 0 | 0 | 3 | 8 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\12_networking\02_network_security.md | L6 | 407 | 3 | 0 | 0 | 0 | 1 | 8 | 6 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\12_networking\03_custom_protocol_implementation.md | L6 | 228 | 0 | 0 | 0 | 0 | 1 | 4 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\12_networking\04_network_programming_quick_start.md | L6 | 329 | 3 | 0 | 0 | 0 | 3 | 7 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\12_networking\05_networking_basics.md | L6 | 1040 | 4 | 0 | 0 | 1 | 1 | 18 | 6 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\12_networking\06_formal_network_protocol_theory.md | L6 | 671 | 3 | 0 | 0 | 1 | 1 | 16 | 6 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\13_quizzes\01_quiz_networking_async_ecosystem.md | L6 | 337 | 0 | 0 | 0 | 0 | 0 | 2 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\13_quizzes\02_quiz_database_storage.md | L6 | 318 | 5 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\13_quizzes\03_quiz_security_testing.md | L6 | 327 | 1 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\13_quizzes\04_quiz_domain_applications.md | L6 | 337 | 1 | 0 | 0 | 0 | 0 | 2 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\01_rust_version_tracking.md | L7 | 2630 | 3 | 0 | 0 | 0 | 3 | 9 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\02_editions.md | L7 | 361 | 4 | 0 | 0 | 1 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\03_rust_release_process.md | L7 | 195 | 0 | 0 | 0 | 1 | 2 | 2 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\04_nightly_rust.md | L7 | 276 | 3 | 0 | 0 | 0 | 1 | 2 | 6 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\feature_domain_matrix_197.md | L7 | 292 | 0 | 0 | 0 | 0 | 2 | 0 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\migration_197_decision_tree.md | L7 | 798 | 0 | 0 | 0 | 0 | 9 | 17 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_90_stabilized.md | L7 | 972 | 4 | 0 | 0 | 1 | 1 | 17 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_91_stabilized.md | L7 | 2792 | 3 | 0 | 0 | 0 | 1 | 83 | 6 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_92_stabilized.md | L7 | 2778 | 3 | 0 | 0 | 0 | 1 | 74 | 6 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_93_stabilized.md | L7 | 263 | 3 | 0 | 0 | 1 | 1 | 10 | 6 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_94_stabilized.md | L7 | 265 | 4 | 0 | 0 | 0 | 1 | 6 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_95_stabilized.md | L7 | 426 | 0 | 0 | 0 | 0 | 1 | 15 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_96_stabilized.md | L7 | 432 | 0 | 0 | 0 | 1 | 1 | 7 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_97_1.md | L7 | 193 | 0 | 0 | 0 | 3 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_97_preview.md | L7 | 147 | 0 | 0 | 0 | 0 | 1 | 3 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_97_stabilized.md | L7 | 570 | 0 | 0 | 0 | 0 | 1 | 15 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_98_preview.md | L7 | 724 | 0 | 0 | 0 | 0 | 1 | 8 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_98_stabilized.md | L7 | 249 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_99_preview.md | L7 | 143 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\01_edition_roadmap\01_rust_edition_preview.md | L7 | 166 | 0 | 0 | 0 | 0 | 1 | 5 | 0 | ❌ | ✅ | ✅ | 进阶 | 研究者级 |
| E:\_src\rust-lang\concept\07_future\01_edition_roadmap\02_edition_guide.md | L7 | 933 | 3 | 0 | 0 | 2 | 2 | 13 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\01_edition_roadmap\03_rust_edition_guide.md | L7 | 20 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\07_future\01_edition_roadmap\04_roadmap.md | L7 | 1133 | 3 | 0 | 0 | 2 | 3 | 17 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\01_effects_system.md | L7 | 1774 | 4 | 0 | 0 | 0 | 4 | 26 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\02_mcdc_coverage_preview.md | L7 | 639 | 3 | 0 | 0 | 2 | 4 | 6 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\03_safety_tags_preview.md | L7 | 719 | 3 | 0 | 0 | 3 | 4 | 6 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\04_parallel_frontend_preview.md | L7 | 718 | 3 | 0 | 0 | 3 | 4 | 6 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\05_derive_coerce_pointee_preview.md | L7 | 689 | 3 | 0 | 0 | 2 | 4 | 8 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\06_const_trait_impl_preview.md | L7 | 704 | 3 | 0 | 0 | 2 | 3 | 7 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\07_stable_abi_preview.md | L7 | 274 | 3 | 0 | 0 | 0 | 1 | 4 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\08_inline_const_pattern_preview.md | L7 | 307 | 3 | 0 | 0 | 0 | 1 | 9 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\09_return_type_notation_preview.md | L7 | 561 | 0 | 0 | 0 | 3 | 1 | 10 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\10_must_not_suspend_preview.md | L7 | 258 | 3 | 0 | 0 | 0 | 1 | 4 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\11_unsafe_fields_preview.md | L7 | 702 | 3 | 0 | 0 | 2 | 4 | 8 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\12_ferrocene_preview.md | L7 | 332 | 0 | 0 | 0 | 0 | 3 | 0 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\13_lifetime_capture_preview.md | L7 | 268 | 3 | 0 | 0 | 0 | 1 | 4 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\14_pin_ergonomics_preview.md | L7 | 400 | 0 | 0 | 0 | 2 | 3 | 10 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\15_rpitit_preview.md | L7 | 311 | 3 | 0 | 0 | 0 | 1 | 8 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\16_cranelift_backend_preview.md | L7 | 808 | 3 | 0 | 0 | 2 | 4 | 9 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\17_type_alias_impl_trait_preview.md | L7 | 261 | 3 | 0 | 0 | 0 | 1 | 4 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\18_arbitrary_self_types_preview.md | L7 | 455 | 3 | 0 | 0 | 1 | 1 | 11 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\19_const_trait_preview.md | L7 | 19 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\20_ergonomic_ref_counting_preview.md | L7 | 346 | 0 | 0 | 0 | 0 | 1 | 7 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\21_rust_specification_preview.md | L7 | 689 | 3 | 0 | 0 | 2 | 4 | 6 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\22_async_drop_preview.md | L7 | 822 | 3 | 0 | 0 | 2 | 3 | 7 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\23_field_projections_preview.md | L7 | 452 | 3 | 0 | 0 | 1 | 1 | 10 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\24_borrow_sanitizer.md | L7 | 421 | 0 | 0 | 0 | 1 | 2 | 4 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\25_gen_blocks_preview.md | L7 | 704 | 3 | 0 | 0 | 2 | 4 | 8 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\26_std_autodiff_preview.md | L7 | 377 | 3 | 0 | 0 | 1 | 1 | 7 | 0 | ✅ | ✅ | ✅ | 研究者 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\27_cargo_semver_checks_preview.md | L7 | 269 | 0 | 0 | 0 | 0 | 1 | 2 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\28_wasm_target_evolution.md | L7 | 291 | 3 | 0 | 0 | 0 | 1 | 1 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\29_aarch64_sve_sme_preview.md | L7 | 338 | 0 | 0 | 0 | 0 | 1 | 5 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\30_rust_in_space.md | L7 | 283 | 3 | 0 | 0 | 0 | 1 | 4 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\31_specialization_preview.md | L7 | 804 | 3 | 0 | 0 | 2 | 3 | 8 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\32_compile_time_execution.md | L7 | 789 | 3 | 0 | 0 | 2 | 2 | 6 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\33_autoverus_preview.md | L7 | 115 | 0 | 0 | 0 | 0 | 1 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\34_open_enums_preview.md | L7 | 861 | 3 | 0 | 0 | 2 | 4 | 13 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\35_f16_f128_preview.md | L7 | 188 | 0 | 0 | 0 | 1 | 1 | 3 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\36_unsafe_pinned_preview.md | L7 | 162 | 0 | 0 | 0 | 1 | 1 | 3 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\37_default_field_values_preview.md | L7 | 156 | 0 | 0 | 0 | 1 | 1 | 4 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\38_complex_numbers_preview.md | L7 | 152 | 0 | 0 | 0 | 1 | 1 | 3 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\01_ai_integration.md | L7 | 1035 | 1 | 0 | 0 | 2 | 3 | 9 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\02_formal_methods.md | L7 | 1754 | 9 | 0 | 0 | 1 | 10 | 9 | 3 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\03_evolution.md | L7 | 2213 | 8 | 0 | 0 | 1 | 6 | 19 | 3 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\04_rust_for_linux.md | L7 | 1109 | 3 | 0 | 0 | 2 | 3 | 11 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\05_rust_in_ai.md | L7 | 811 | 3 | 0 | 0 | 2 | 2 | 7 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\06_rust_for_webassembly.md | L7 | 1000 | 3 | 0 | 0 | 3 | 3 | 11 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\07_ebpf_rust.md | L7 | 1042 | 3 | 0 | 0 | 0 | 4 | 15 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\05_quizzes\01_quiz_version_and_preview.md | L7 | 356 | 0 | 0 | 0 | 1 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 进阶 | 实验级 |
