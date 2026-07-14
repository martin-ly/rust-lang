# 知识体系质量仪表盘 (KB Quality Dashboard)

> 生成时间: 2026-07-14T03:16:00.574088+00:00
> 扫描文件数: 496

## 全局指标

| 指标 | 数值 | 目标 | 状态 |
|:---|:---|:---|:---|
| 总文件数 | 496 | 27 | ✅ |
| 总定理链 (⟹) | 2094 | ≥270 | ✅ |
| 总反命题 | 635 | ≥40 | ✅ |
| 总 Mermaid 图 | 772 | ≥50 | ✅ |
| 编译验证代码块 | 4997 | ≥150 | ✅ |
| 定理矩阵总行 | 23364 | — | — |
| 死链数量 | 0 | 0 | ✅ |
| 反向推理 (⟸) | 317 | ≥50 | ✅ |
| 模板化 ⟹ | 0 | 0 | ✅ |
| 前置概念覆盖率 | 426/430 | 100% | ⚠️ |
| 后置概念覆盖率 | 421/430 | 100% | ⚠️ |
| 双标签覆盖率 | 417/430 | >=95% | ✅ |
| 非法标签组合 | 0 | 0 | ✅ |

## 按层级分布

| 层级 | 文件数 | 平均 ⟹/文件 | 平均过渡段/文件 | 认知路径 | ⟸/文件 | 模板化 | 前置覆盖 | 后置覆盖 | 双标签 |
|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|
| L0 | 66 | 7.4 | 3.0 | 35/66 (53%) | 0.6 | 0 | 15/66 | 13/66 | 46/66 |
| L1 | 55 | 4.3 | 2.4 | 40/55 (72%) | 1.5 | 0 | 55/55 | 55/55 | 55/55 |
| L2 | 38 | 5.6 | 1.3 | 25/38 (65%) | 1.9 | 0 | 38/38 | 38/38 | 38/38 |
| L3 | 65 | 6.3 | 2.4 | 53/65 (81%) | 1.8 | 0 | 65/65 | 65/65 | 65/65 |
| L4 | 57 | 3.4 | 1.1 | 35/57 (61%) | 0.1 | 0 | 55/57 | 55/57 | 55/57 |
| L5 | 20 | 4.0 | 1.9 | 18/20 (90%) | 0.0 | 0 | 20/20 | 20/20 | 20/20 |
| L6 | 128 | 2.6 | 1.4 | 61/128 (47%) | 0.0 | 0 | 126/128 | 122/128 | 118/128 |
| L7 | 67 | 2.1 | 0.6 | 39/67 (58%) | 0.0 | 0 | 67/67 | 66/67 | 66/67 |

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
| E:\_src\rust-lang\concept\01_foundation\04_control_flow\03_statements_and_expressions.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
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
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\24_quiz_type_system.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\25_quiz_error_handling.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\26_quiz_modules_testing.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\27_quiz_closures_iterators.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\29_quiz_pl_foundations.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\33_quiz_ownership_borrowing.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\03_serde_patterns.md | L2 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\04_advanced_traits.md | L2 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\05_construction_and_initialization.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (1 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\06_derive_traits.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (2 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\07_generic_associated_types.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\02_const_generics.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (2 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\04_quiz_traits_and_generics.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
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
| E:\_src\rust-lang\concept\02_intermediate\09_quizzes\30_quiz_cpp_rust_foundations.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\01_concurrency.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\02_send_sync_auto_traits.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\03_concurrency_patterns.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\05_atomics_and_memory_ordering.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\06_lock_free.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\07_parallel_distributed_pattern_spectrum.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\08_quiz_concurrency_async.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
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
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\00_before_formal.md | L3 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\02_unsafe_boundary_panorama.md | L3 | 过渡段落不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\03_nll_and_polonius.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\05_quiz_unsafe.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\02_proc_macro.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\10_quiz_macros.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\11_conditional_compilation.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\01_rust_ffi.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\02_ffi_advanced.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\03_linkage.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (1 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\05_inline_assembly\01_inline_assembly.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\01_custom_allocators.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\02_zero_copy_parsing.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\03_type_erasure.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\04_network_programming.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\05_stream_processing_semantics.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\06_ownership_performance_optimization.md | L3 | 过渡段落不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\08_memory_allocation_and_lifetime.md | L3 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\09_variables.md | L3 | 缺失认知路径; 缺失反命题 |
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
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\03_linear_logic_applications.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\04_borrow_checking_decidability.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\05_tree_borrows_deep_dive.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\06_behavior_considered_undefined.md | L4 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\02_separation_logic.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\03_safety_tags_in_formal.md | L4 | 缺失认知路径; 缺失反命题; 缺失前置概念; 缺失后置概念; 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\04_borrow_sanitizer_in_formal.md | L4 | 缺失认知路径 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\01_denotational_semantics.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\02_hoare_logic.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\03_operational_semantics.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\04_evaluation_strategies.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\05_axiomatic_semantics.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\06_aeneas_symbolic_semantics.md | L4 | 过渡段落不足 (0 < 3); 定理链不足 (1 < 3); 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\07_constant_evaluation.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\01_verification_toolchain.md | L4 | 过渡段落不足 (0 < 3); 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\02_formal_methods.md | L4 | 缺失认知路径; 缺失反命题; 缺失前置概念; 缺失后置概念; 缺失受众标签; 缺失内容分级标签 |
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
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\08_type_layout.md | L4 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\09_destructors.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\15_generics_compiler_behavior.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\06_notation\01_notation.md | L4 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\05_comparative\00_paradigms\02_execution_model_isomorphism.md | L5 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\00_paradigms\03_cpp_rust_surface_features.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\01_rust_vs_cpp.md | L5 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\02_cpp_abi_object_model.md | L5 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\04_rust_vs_ruby.md | L5 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\05_rust_vs_swift.md | L5 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\06_rust_vs_zig.md | L5 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\01_rust_vs_java.md | L5 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\02_rust_vs_python.md | L5 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\03_rust_vs_javascript.md | L5 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\04_rust_vs_kotlin.md | L5 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\05_rust_vs_scala.md | L5 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\06_rust_vs_csharp.md | L5 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\07_rust_vs_elixir.md | L5 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\08_rust_vs_typescript.md | L5 | 过渡段落不足 (0 < 3) |
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
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\15_z_flags_reference.md | L6 | 缺失受众标签; 缺失内容分级标签 |
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
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\20_cargo_manifest_targets.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\22_build_std.md | L6 | 缺失内容分级标签 |
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
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\09_embedded_hal_1_0_migration.md | L6 | 缺失内容分级标签 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\10_target_tier_platform_support.md | L6 | 缺失受众标签; 缺失内容分级标签 |
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
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\06_game_development.md | L6 | 缺失前置概念; 缺失后置概念; 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\07_algorithms_competitive_programming.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\10_algorithm_complexity_analysis.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\13_machine_learning_ecosystem.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\14_industrial_case_studies.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\15_game_engine_internals.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\16_quantum_computing_rust.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\17_webassembly_advanced.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\21_safety_critical_topic_index.md | L6 | 缺失前置概念; 缺失后置概念; 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\06_ecosystem\12_networking\03_custom_protocol_implementation.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\13_quizzes\01_quiz_networking_async_ecosystem.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失后置概念; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\06_ecosystem\13_quizzes\02_quiz_database_storage.md | L6 | 过渡段落不足 (0 < 3); 缺失后置概念; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\06_ecosystem\13_quizzes\03_quiz_security_testing.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (1 < 3); 缺失后置概念; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\06_ecosystem\13_quizzes\04_quiz_domain_applications.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (1 < 3); 缺失后置概念; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\01_rust_version_tracking.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\02_editions.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\feature_domain_matrix_197.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\migration_197_decision_tree.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_95_stabilized.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_96_stabilized.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_97_stabilized.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_98_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\01_edition_roadmap\02_edition_guide.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\01_edition_roadmap\04_roadmap.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\01_effects_system.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\02_mcdc_coverage_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\03_safety_tags_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\04_parallel_frontend_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\05_derive_coerce_pointee_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\06_const_trait_impl_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\07_stable_abi_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\08_inline_const_pattern_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\09_return_type_notation_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\10_must_not_suspend_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\11_unsafe_fields_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\12_ferrocene_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\13_lifetime_capture_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\14_pin_ergonomics_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\15_rpitit_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\16_cranelift_backend_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\17_type_alias_impl_trait_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\18_arbitrary_self_types_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\19_const_trait_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\20_ergonomic_ref_counting_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\21_rust_specification_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\22_async_drop_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\23_field_projections_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\24_borrow_sanitizer.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\25_gen_blocks_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\26_std_autodiff_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\27_cargo_semver_checks_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\28_wasm_target_evolution.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\29_aarch64_sve_sme_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\30_rust_in_space.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\31_specialization_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\32_compile_time_execution.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\34_open_enums_preview.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\01_ai_integration.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (1 < 3) |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\04_rust_for_linux.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\05_rust_in_ai.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\06_rust_for_webassembly.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\07_ebpf_rust.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\05_quizzes\01_quiz_version_and_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失后置概念; 缺失内容分级标签 |

## 文件详细统计

| 文件 | 层级 | 行数 | ⟹ | ⟸ | 模板 | 反命题 | Mermaid | 代码块 | 过渡段 | 认知路径 | 前置 | 后置 | 受众 | 分级 |
|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|
| E:\_src\rust-lang\concept\00_meta\00_framework\bloom_taxonomy.md | L0 | 201 | 1 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\boundary_extension_tree.md | L0 | 362 | 1 | 0 | 0 | 1 | 3 | 1 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\cognitive_dimension_matrix.md | L0 | 401 | 1 | 0 | 0 | 1 | 2 | 0 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\competency_graph.md | L0 | 429 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\comprehensive_rust_mapping.md | L0 | 240 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 → 进阶 | None |
| E:\_src\rust-lang\concept\00_meta\00_framework\concept_definition_decision_forest.md | L0 | 1175 | 3 | 0 | 0 | 1 | 10 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\cpp_rust_engineering_roadmap.md | L0 | 258 | 0 | 0 | 0 | 0 | 2 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 | None |
| E:\_src\rust-lang\concept\00_meta\00_framework\decidability_spectrum.md | L0 | 963 | 2 | 0 | 0 | 1 | 6 | 2 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\expressiveness_multiview.md | L0 | 829 | 0 | 0 | 0 | 1 | 7 | 7 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\fault_tree_analysis_collection.md | L0 | 806 | 1 | 0 | 0 | 1 | 7 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\knowledge_mindmap.md | L0 | 308 | 1 | 0 | 0 | 1 | 2 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\methodology.md | L0 | 582 | 1 | 0 | 0 | 2 | 5 | 1 | 6 | ✅ | ✅ | ✅ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\paradigm_transition_matrix.md | L0 | 330 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\pattern_semantic_space_index.md | L0 | 197 | 0 | 0 | 0 | 0 | 2 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | None |
| E:\_src\rust-lang\concept\00_meta\00_framework\pl_foundations_roadmap.md | L0 | 178 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 | None |
| E:\_src\rust-lang\concept\00_meta\00_framework\semantic_bridge_algorithms_patterns.md | L0 | 735 | 1 | 0 | 0 | 1 | 0 | 7 | 6 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\semantic_expressiveness.md | L0 | 1133 | 1 | 0 | 0 | 1 | 2 | 1 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\semantic_space.md | L0 | 1357 | 10 | 0 | 0 | 2 | 5 | 9 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\theorem_inference_forest.md | L0 | 557 | 15 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\theorem_registry.md | L0 | 207 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\00_meta\00_framework\todos.md | L0 | 349 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\01_terminology\01_terminology_glossary.md | L0 | 466 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\01_terminology\02_bilingual_template_v2.md | L0 | 326 | 0 | 2 | 0 | 5 | 1 | 5 | 0 | ✅ | ✅ | ✅ | 初学者 | 进阶 | 研究者 | None |
| E:\_src\rust-lang\concept\00_meta\01_terminology\03_bilingual_template.md | L0 | 165 | 0 | 0 | 0 | 1 | 1 | 1 | 0 | ❌ | ✅ | ✅ | 初学者 | 进阶 | 研究者 | None |
| E:\_src\rust-lang\concept\00_meta\01_trpl_3rd_ed_mapping.md | L0 | 11 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\00_meta\02_sources\01_authority_source_map.md | L0 | 216 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\02_sources\02_rustbelt_predicate_map.md | L0 | 435 | 9 | 0 | 0 | 1 | 6 | 0 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\02_sources\03_sources.md | L0 | 493 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 研究者级 |
| E:\_src\rust-lang\concept\00_meta\02_sources\04_topic_authority_alignment_map.md | L0 | 388 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\00_meta\02_sources\05_international_authority_index.md | L0 | 243 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 研究者 / 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\01_concept_audit_guide.md | L0 | 107 | 1 | 0 | 0 | 1 | 1 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\02_asp_marking_guide.md | L0 | 552 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\03_audit_checklist.md | L0 | 476 | 2 | 1 | 0 | 2 | 1 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\04_concept_consistency_audit_checklist.md | L0 | 14 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\00_meta\03_audit\05_template_deduplication_guide.md | L0 | 94 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 贡献者 | None |
| E:\_src\rust-lang\concept\00_meta\03_audit\06_grading_system.md | L0 | 162 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\07_quality_dashboard_v2.md | L0 | 330 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\01_cross_reference_matrix.md | L0 | 15 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\00_meta\04_navigation\02_career_landscape.md | L0 | 236 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 入门 → 进阶 | 元层 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\03_concept_index.md | L0 | 795 | 4 | 0 | 0 | 2 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\04_inter_layer_map.md | L0 | 634 | 12 | 0 | 0 | 1 | 2 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\05_inter_layer_topology.md | L0 | 16 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ✅ | ❌ | ❌ | None | 专家级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\06_intra_layer_model_map.md | L0 | 367 | 11 | 0 | 0 | 1 | 5 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\07_learning_guide.md | L0 | 692 | 3 | 0 | 0 | 1 | 1 | 0 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\08_learning_mvp_path.md | L0 | 372 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ✅ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\09_navigation.md | L0 | 295 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\10_problem_graph.md | L0 | 552 | 1 | 0 | 0 | 1 | 7 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\11_quick_reference.md | L0 | 859 | 1 | 0 | 0 | 1 | 0 | 25 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\12_self_assessment.md | L0 | 2295 | 1 | 0 | 0 | 1 | 0 | 56 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\13_foundations_gap_closure_index.md | L0 | 146 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | None |
| E:\_src\rust-lang\concept\00_meta\04_navigation\14_learning_mvp_path_en.md | L0 | 290 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\00_meta\04_navigation\15_quiz_registry.md | L0 | 146 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\00_meta\05_quizzes\01_quiz_meta_framework.md | L0 | 372 | 0 | 0 | 0 | 0 | 0 | 2 | 0 | ❌ | ✅ | ❌ | 进阶 | None |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\01_concept_definition_atlas.md | L0 | 566 | 1 | 1 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\02_attribute_relationship_atlas.md | L0 | 561 | 27 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\03_scenario_decision_tree_atlas.md | L0 | 620 | 0 | 0 | 0 | 0 | 9 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\04_example_counterexample_atlas.md | L0 | 541 | 1 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\05_logical_reasoning_atlas.md | L0 | 191 | 17 | 2 | 0 | 0 | 4 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\06_inter_layer_mapping_atlas.md | L0 | 203 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\07_intra_layer_mapping_atlas.md | L0 | 594 | 347 | 33 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\08_concept_source_alignment_atlas.md | L0 | 52 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\09_reasoning_judgment_tree_atlas.md | L0 | 696 | 4 | 0 | 0 | 0 | 6 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\10_gap_and_action_plan.md | L0 | 78 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\kg_ontology_v2.md | L0 | 329 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | None |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\kg_tlo_alignment.md | L0 | 263 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\00_meta\placeholders\01_placeholder_generic.md | L0 | 23 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\01_foundation\00_start\00_start.md | L1 | 284 | 4 | 2 | 0 | 1 | 1 | 1 | 6 | ✅ | ✅ | ✅ | 初学者 | 初学者 |
| E:\_src\rust-lang\concept\01_foundation\00_start\01_pl_prerequisites.md | L1 | 534 | 3 | 2 | 0 | 0 | 0 | 12 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\02_zero_cost_abstractions.md | L1 | 915 | 3 | 2 | 0 | 2 | 3 | 14 | 2 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\03_closure_basics.md | L1 | 951 | 4 | 2 | 0 | 2 | 2 | 18 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\04_effects_and_purity.md | L1 | 827 | 0 | 0 | 0 | 2 | 0 | 17 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\05_std_io_and_process.md | L1 | 503 | 4 | 4 | 0 | 4 | 2 | 10 | 0 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\06_keywords.md | L1 | 278 | 0 | 0 | 0 | 0 | 0 | 4 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\07_operators_and_symbols.md | L1 | 267 | 0 | 0 | 0 | 0 | 0 | 2 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\00_ownership_borrow_lifetime_knowledge_map.md | L1 | 434 | 5 | 2 | 0 | 1 | 5 | 0 | 5 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\01_ownership.md | L1 | 2016 | 27 | 2 | 0 | 3 | 8 | 46 | 16 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\02_borrowing.md | L1 | 2150 | 13 | 3 | 0 | 3 | 7 | 53 | 20 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\03_lifetimes.md | L1 | 1557 | 23 | 2 | 0 | 3 | 6 | 40 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\04_lifetimes_advanced.md | L1 | 1897 | 3 | 2 | 0 | 1 | 1 | 49 | 10 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\05_move_semantics.md | L1 | 363 | 3 | 0 | 0 | 0 | 1 | 6 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\06_ownership_inventories_brown_book.md | L1 | 209 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\01_type_system.md | L1 | 3375 | 23 | 2 | 0 | 3 | 13 | 63 | 16 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\02_never_type.md | L1 | 678 | 3 | 2 | 0 | 0 | 1 | 16 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\03_numerics.md | L1 | 1131 | 3 | 2 | 0 | 2 | 2 | 19 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\04_coercion_and_casting.md | L1 | 1065 | 3 | 2 | 0 | 2 | 2 | 18 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\05_data_abstraction_spectrum.md | L1 | 876 | 0 | 0 | 0 | 2 | 1 | 14 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\03_values_and_references\01_reference_semantics.md | L1 | 1511 | 4 | 2 | 0 | 3 | 8 | 35 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\03_values_and_references\02_value_vs_reference_semantics.md | L1 | 275 | 0 | 0 | 0 | 0 | 1 | 5 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\03_values_and_references\03_variable_model.md | L1 | 756 | 0 | 0 | 0 | 2 | 1 | 12 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\04_control_flow\01_control_flow.md | L1 | 1737 | 3 | 2 | 0 | 2 | 6 | 25 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\04_control_flow\02_patterns.md | L1 | 390 | 0 | 0 | 0 | 0 | 1 | 14 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\04_control_flow\03_statements_and_expressions.md | L1 | 277 | 0 | 0 | 0 | 0 | 0 | 7 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\05_collections\01_collections.md | L1 | 924 | 3 | 2 | 0 | 2 | 3 | 16 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\05_collections\02_collections_advanced.md | L1 | 1042 | 6 | 2 | 0 | 2 | 2 | 11 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\06_strings_and_text\01_strings_and_text.md | L1 | 928 | 3 | 2 | 0 | 2 | 2 | 19 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\06_strings_and_text\02_strings_and_encoding.md | L1 | 902 | 4 | 2 | 0 | 2 | 3 | 9 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\06_strings_and_text\03_formatting_and_display.md | L1 | 453 | 4 | 3 | 0 | 4 | 1 | 9 | 0 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\01_modules_and_paths.md | L1 | 989 | 10 | 2 | 0 | 2 | 2 | 11 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\02_functions.md | L1 | 434 | 4 | 2 | 0 | 1 | 1 | 10 | 6 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\03_use_declarations.md | L1 | 304 | 4 | 2 | 0 | 1 | 0 | 10 | 0 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\04_structs.md | L1 | 395 | 9 | 2 | 0 | 1 | 1 | 8 | 6 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\05_enumerations.md | L1 | 392 | 9 | 2 | 0 | 1 | 1 | 10 | 6 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\06_implementations.md | L1 | 377 | 5 | 2 | 0 | 1 | 1 | 8 | 6 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\07_type_aliases.md | L1 | 440 | 4 | 3 | 0 | 4 | 1 | 10 | 0 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\08_static_items.md | L1 | 429 | 4 | 3 | 0 | 4 | 1 | 8 | 0 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\09_const_items_and_const_fn.md | L1 | 473 | 5 | 3 | 0 | 4 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\10_preludes.md | L1 | 243 | 0 | 0 | 0 | 0 | 0 | 6 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\11_crates_and_source_files.md | L1 | 300 | 4 | 2 | 0 | 1 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\12_items.md | L1 | 410 | 4 | 2 | 0 | 1 | 1 | 14 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\08_error_handling\01_error_handling_basics.md | L1 | 1072 | 3 | 2 | 0 | 2 | 2 | 15 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\08_error_handling\02_error_handling_control_flow.md | L1 | 382 | 3 | 3 | 0 | 1 | 2 | 11 | 7 | ✅ | ✅ | ✅ | 初学者 | 入门实践级 |
| E:\_src\rust-lang\concept\01_foundation\08_error_handling\03_panic_and_abort.md | L1 | 1020 | 8 | 2 | 0 | 2 | 2 | 12 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\09_macros_basics\01_attributes_and_macros.md | L1 | 986 | 3 | 2 | 0 | 2 | 2 | 14 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\10_testing_basics\01_testing_basics.md | L1 | 815 | 3 | 2 | 0 | 2 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\10_testing_basics\02_useful_development_tools.md | L1 | 325 | 4 | 2 | 0 | 1 | 2 | 2 | 6 | ✅ | ✅ | ✅ | 初学者 | 参考级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\24_quiz_type_system.md | L1 | 604 | 0 | 0 | 0 | 0 | 0 | 14 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\25_quiz_error_handling.md | L1 | 708 | 0 | 0 | 0 | 0 | 0 | 18 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\26_quiz_modules_testing.md | L1 | 796 | 0 | 0 | 0 | 0 | 0 | 22 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\27_quiz_closures_iterators.md | L1 | 782 | 0 | 0 | 0 | 0 | 0 | 33 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\29_quiz_pl_foundations.md | L1 | 258 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\33_quiz_ownership_borrowing.md | L1 | 597 | 0 | 0 | 0 | 0 | 0 | 18 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\01_traits.md | L2 | 3198 | 15 | 2 | 0 | 7 | 6 | 76 | 10 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\02_dispatch_mechanisms.md | L2 | 2338 | 14 | 2 | 0 | 1 | 1 | 42 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\03_serde_patterns.md | L2 | 936 | 3 | 3 | 0 | 2 | 3 | 9 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\04_advanced_traits.md | L2 | 1041 | 3 | 3 | 0 | 2 | 2 | 21 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\05_construction_and_initialization.md | L2 | 332 | 1 | 0 | 0 | 0 | 1 | 7 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\06_derive_traits.md | L2 | 399 | 2 | 0 | 0 | 0 | 1 | 12 | 0 | ❌ | ✅ | ✅ | 初学者 | 参考级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\07_generic_associated_types.md | L2 | 667 | 0 | 0 | 0 | 0 | 3 | 14 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\01_generics.md | L2 | 3350 | 23 | 2 | 0 | 7 | 7 | 74 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\02_const_generics.md | L2 | 616 | 2 | 0 | 0 | 4 | 1 | 15 | 0 | ❌ | ✅ | ✅ | 进阶 | 进阶级 |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\03_type_level_programming.md | L2 | 885 | 8 | 2 | 0 | 1 | 1 | 13 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\04_quiz_traits_and_generics.md | L2 | 762 | 0 | 0 | 0 | 0 | 0 | 20 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\01_memory_management.md | L2 | 2249 | 23 | 3 | 0 | 7 | 5 | 57 | 7 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\02_interior_mutability.md | L2 | 937 | 9 | 3 | 0 | 2 | 2 | 11 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\03_cow_and_borrowed.md | L2 | 795 | 4 | 3 | 0 | 2 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\04_smart_pointers.md | L2 | 949 | 9 | 3 | 0 | 2 | 2 | 12 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\05_quiz_memory_management.md | L2 | 805 | 0 | 0 | 0 | 0 | 0 | 27 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\03_error_handling\01_error_handling.md | L2 | 2900 | 22 | 4 | 0 | 7 | 8 | 63 | 7 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\03_error_handling\02_error_handling_deep_dive.md | L2 | 820 | 3 | 3 | 0 | 2 | 1 | 9 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\03_error_handling\03_panic.md | L2 | 240 | 0 | 0 | 0 | 0 | 0 | 4 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\02_intermediate\03_error_handling\04_exception_safety_rust_cpp.md | L2 | 346 | 2 | 0 | 0 | 0 | 0 | 6 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\01_range_types.md | L2 | 687 | 3 | 3 | 0 | 2 | 2 | 12 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\02_closure_types.md | L2 | 854 | 11 | 3 | 0 | 2 | 3 | 17 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\03_newtype_and_wrapper.md | L2 | 832 | 3 | 3 | 0 | 2 | 1 | 12 | 2 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\04_type_system_advanced.md | L2 | 1283 | 3 | 3 | 0 | 2 | 1 | 18 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\05_rtti_and_dynamic_typing.md | L2 | 331 | 0 | 0 | 0 | 0 | 0 | 7 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\06_unions.md | L2 | 453 | 4 | 3 | 0 | 4 | 1 | 7 | 0 | ✅ | ✅ | ✅ | 进阶 | 进阶 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\07_type_conversions.md | L2 | 485 | 4 | 4 | 0 | 4 | 1 | 10 | 0 | ✅ | ✅ | ✅ | 进阶 | 进阶 |
| E:\_src\rust-lang\concept\02_intermediate\05_modules_and_visibility\01_module_system.md | L2 | 893 | 8 | 3 | 0 | 2 | 3 | 15 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\05_modules_and_visibility\02_friend_vs_module_privacy.md | L2 | 295 | 0 | 0 | 0 | 0 | 0 | 5 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\02_intermediate\05_modules_and_visibility\03_api_naming_conventions.md | L2 | 493 | 0 | 0 | 0 | 0 | 0 | 15 | 2 | ❌ | ✅ | ✅ | 进阶 | 中级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\01_assert_matches.md | L2 | 757 | 3 | 3 | 0 | 2 | 3 | 18 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\02_dsl_and_embedding.md | L2 | 868 | 5 | 3 | 0 | 2 | 1 | 11 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\03_macro_patterns.md | L2 | 855 | 4 | 3 | 0 | 2 | 1 | 9 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\04_metaprogramming.md | L2 | 902 | 3 | 3 | 0 | 2 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\05_c_preprocessor_vs_rust_macros.md | L2 | 280 | 0 | 0 | 0 | 0 | 0 | 6 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\06_attributes_by_category.md | L2 | 499 | 4 | 4 | 0 | 4 | 1 | 10 | 0 | ✅ | ✅ | ✅ | 进阶 | 进阶 |
| E:\_src\rust-lang\concept\02_intermediate\07_iterators_and_closures\01_iterator_patterns.md | L2 | 1435 | 13 | 2 | 0 | 1 | 1 | 23 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\09_quizzes\30_quiz_cpp_rust_foundations.md | L2 | 307 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\01_concurrency.md | L3 | 2185 | 21 | 2 | 0 | 3 | 13 | 27 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\02_send_sync_auto_traits.md | L3 | 587 | 10 | 1 | 0 | 4 | 1 | 13 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\03_concurrency_patterns.md | L3 | 2370 | 3 | 3 | 0 | 2 | 4 | 34 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\04_cross_platform_concurrency.md | L3 | 256 | 6 | 2 | 0 | 1 | 0 | 5 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\05_atomics_and_memory_ordering.md | L3 | 1525 | 8 | 3 | 0 | 2 | 2 | 24 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\06_lock_free.md | L3 | 1246 | 3 | 3 | 0 | 2 | 1 | 20 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\07_parallel_distributed_pattern_spectrum.md | L3 | 1121 | 3 | 3 | 0 | 2 | 0 | 18 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\08_quiz_concurrency_async.md | L3 | 793 | 0 | 0 | 0 | 0 | 0 | 19 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\01_async.md | L3 | 3491 | 21 | 3 | 0 | 6 | 9 | 63 | 3 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\02_async_advanced.md | L3 | 675 | 5 | 3 | 0 | 0 | 0 | 14 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\03_async_patterns.md | L3 | 1308 | 3 | 3 | 0 | 2 | 1 | 22 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\04_future_and_executor_mechanisms.md | L3 | 1233 | 8 | 2 | 0 | 2 | 0 | 20 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\05_async_cancellation_safety.md | L3 | 544 | 0 | 0 | 0 | 5 | 1 | 11 | 0 | ❌ | ✅ | ✅ | 进阶-专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\06_async_boundary_panorama.md | L3 | 525 | 26 | 0 | 0 | 6 | 2 | 10 | 0 | ✅ | ✅ | ✅ | 进阶-专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\07_async_closures.md | L3 | 644 | 3 | 0 | 0 | 1 | 0 | 20 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\08_pin_unpin.md | L3 | 1009 | 6 | 3 | 0 | 2 | 2 | 22 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\09_stream_algebra_and_backpressure.md | L3 | 477 | 5 | 2 | 0 | 1 | 2 | 7 | 6 | ✅ | ✅ | ✅ | 进阶-专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\10_executor_fairness_and_scheduling.md | L3 | 359 | 11 | 3 | 0 | 1 | 1 | 5 | 2 | ✅ | ✅ | ✅ | 进阶-专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\11_pin_projection_counterexamples.md | L3 | 442 | 5 | 2 | 0 | 5 | 2 | 8 | 2 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\12_waker_contract_deep_dive.md | L3 | 382 | 11 | 0 | 0 | 3 | 3 | 4 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\13_async_trait_object_safety.md | L3 | 337 | 4 | 0 | 0 | 0 | 2 | 7 | 0 | ✅ | ✅ | ✅ | 进阶-专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\00_before_formal.md | L3 | 173 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\01_unsafe.md | L3 | 3506 | 18 | 2 | 0 | 4 | 10 | 63 | 3 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\02_unsafe_boundary_panorama.md | L3 | 487 | 19 | 0 | 0 | 5 | 2 | 12 | 0 | ✅ | ✅ | ✅ | 进阶-专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\03_nll_and_polonius.md | L3 | 891 | 3 | 3 | 0 | 3 | 1 | 13 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\04_unsafe_rust_patterns.md | L3 | 73 | 3 | 0 | 0 | 1 | 0 | 2 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\05_quiz_unsafe.md | L3 | 704 | 0 | 0 | 0 | 0 | 0 | 21 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\06_memory_model.md | L3 | 475 | 5 | 2 | 0 | 1 | 0 | 9 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\07_unsafe_reference.md | L3 | 319 | 3 | 2 | 0 | 1 | 0 | 6 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\01_macros.md | L3 | 2545 | 26 | 3 | 0 | 8 | 8 | 59 | 8 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\02_proc_macro.md | L3 | 1156 | 3 | 3 | 0 | 2 | 2 | 14 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\03_proc_macro_code_generation_optimization.md | L3 | 384 | 7 | 2 | 0 | 1 | 0 | 11 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\04_macro_debugging_and_diagnostics.md | L3 | 387 | 7 | 2 | 0 | 1 | 0 | 7 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\05_production_grade_macro_development.md | L3 | 408 | 7 | 2 | 0 | 1 | 0 | 8 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\06_macro_glossary.md | L3 | 723 | 8 | 2 | 0 | 1 | 0 | 27 | 6 | ✅ | ✅ | ✅ | 研究者 | 参考级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\07_macro_faq.md | L3 | 807 | 8 | 2 | 0 | 1 | 0 | 35 | 6 | ✅ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\08_syn_quote_reference.md | L3 | 1236 | 8 | 3 | 0 | 2 | 0 | 36 | 6 | ✅ | ✅ | ✅ | 专家 | 参考级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\09_macro_hygiene.md | L3 | 985 | 8 | 2 | 0 | 2 | 0 | 32 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\10_quiz_macros.md | L3 | 771 | 0 | 0 | 0 | 0 | 0 | 24 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\11_conditional_compilation.md | L3 | 327 | 0 | 0 | 0 | 0 | 0 | 11 | 0 | ❌ | ✅ | ✅ | 中级 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\01_rust_ffi.md | L3 | 987 | 3 | 3 | 0 | 2 | 3 | 18 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\02_ffi_advanced.md | L3 | 954 | 3 | 3 | 0 | 2 | 1 | 12 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\03_linkage.md | L3 | 436 | 1 | 0 | 0 | 1 | 0 | 16 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\05_inline_assembly\01_inline_assembly.md | L3 | 856 | 0 | 0 | 0 | 1 | 0 | 27 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\01_custom_allocators.md | L3 | 889 | 3 | 3 | 0 | 2 | 1 | 12 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\02_zero_copy_parsing.md | L3 | 931 | 3 | 3 | 0 | 2 | 1 | 13 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\03_type_erasure.md | L3 | 903 | 4 | 3 | 0 | 2 | 1 | 11 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\04_network_programming.md | L3 | 1093 | 3 | 3 | 0 | 2 | 2 | 16 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\05_stream_processing_semantics.md | L3 | 931 | 3 | 3 | 0 | 1 | 0 | 8 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\06_ownership_performance_optimization.md | L3 | 218 | 4 | 0 | 0 | 1 | 0 | 10 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\07_rust_runtime.md | L3 | 303 | 3 | 2 | 0 | 1 | 0 | 8 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\08_memory_allocation_and_lifetime.md | L3 | 192 | 0 | 0 | 0 | 0 | 0 | 8 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\09_variables.md | L3 | 195 | 0 | 0 | 0 | 0 | 0 | 8 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\10_visibility_and_privacy.md | L3 | 225 | 0 | 0 | 0 | 0 | 1 | 8 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\07_unsafe_internals\01_unsafe_collections_internals.md | L3 | 531 | 4 | 4 | 0 | 4 | 1 | 8 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\01_process_model_and_lifecycle.md | L3 | 498 | 8 | 2 | 0 | 2 | 1 | 5 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\02_advanced_process_management.md | L3 | 323 | 8 | 2 | 0 | 1 | 1 | 3 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\03_async_process_management.md | L3 | 427 | 8 | 2 | 0 | 2 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\04_cross_platform_process_management.md | L3 | 353 | 8 | 2 | 0 | 2 | 1 | 7 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\05_ipc_mechanisms.md | L3 | 315 | 8 | 2 | 0 | 1 | 1 | 8 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\06_process_monitoring_and_diagnostics.md | L3 | 298 | 8 | 2 | 0 | 1 | 1 | 5 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\07_process_security_and_sandboxing.md | L3 | 264 | 8 | 2 | 0 | 1 | 1 | 7 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\08_process_performance_engineering.md | L3 | 237 | 8 | 2 | 0 | 1 | 1 | 3 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\09_process_testing_and_benchmarking.md | L3 | 284 | 8 | 2 | 0 | 1 | 1 | 7 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\10_modern_process_libraries.md | L3 | 246 | 8 | 2 | 0 | 1 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\01_type_theory.md | L4 | 1830 | 29 | 0 | 0 | 4 | 6 | 27 | 3 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\02_subtype_variance.md | L4 | 646 | 5 | 0 | 0 | 2 | 2 | 10 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\03_type_inference.md | L4 | 788 | 3 | 0 | 0 | 2 | 3 | 9 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\04_category_theory.md | L4 | 830 | 3 | 0 | 0 | 2 | 1 | 11 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\05_lambda_calculus.md | L4 | 764 | 3 | 0 | 0 | 2 | 1 | 11 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\06_type_semantics.md | L4 | 977 | 5 | 0 | 0 | 3 | 1 | 18 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\07_type_checking_and_inference.md | L4 | 476 | 1 | 0 | 0 | 2 | 1 | 12 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\08_type_inference_complexity.md | L4 | 451 | 0 | 0 | 0 | 2 | 1 | 8 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\09_type_system_reference.md | L4 | 442 | 0 | 0 | 0 | 1 | 0 | 3 | 6 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\01_linear_logic.md | L4 | 1291 | 14 | 0 | 0 | 4 | 6 | 13 | 3 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\02_ownership_formal.md | L4 | 1696 | 11 | 0 | 0 | 1 | 6 | 17 | 3 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\03_linear_logic_applications.md | L4 | 755 | 3 | 0 | 0 | 2 | 1 | 10 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\04_borrow_checking_decidability.md | L4 | 467 | 3 | 0 | 0 | 1 | 3 | 10 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\05_tree_borrows_deep_dive.md | L4 | 203 | 0 | 0 | 0 | 1 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\06_behavior_considered_undefined.md | L4 | 192 | 0 | 0 | 0 | 0 | 0 | 2 | 0 | ❌ | ✅ | ✅ | 专家 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\01_rustbelt.md | L4 | 1469 | 5 | 0 | 0 | 1 | 6 | 16 | 10 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\02_separation_logic.md | L4 | 848 | 4 | 0 | 0 | 2 | 1 | 10 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\03_safety_tags_in_formal.md | L4 | 14 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\04_borrow_sanitizer_in_formal.md | L4 | 194 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\01_denotational_semantics.md | L4 | 686 | 3 | 0 | 0 | 4 | 1 | 9 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\02_hoare_logic.md | L4 | 923 | 3 | 0 | 0 | 2 | 3 | 8 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\03_operational_semantics.md | L4 | 1123 | 3 | 0 | 0 | 2 | 2 | 13 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\04_evaluation_strategies.md | L4 | 720 | 0 | 0 | 0 | 2 | 1 | 14 | 0 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\05_axiomatic_semantics.md | L4 | 1062 | 5 | 0 | 0 | 4 | 1 | 15 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\06_aeneas_symbolic_semantics.md | L4 | 490 | 1 | 0 | 0 | 0 | 2 | 4 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\07_constant_evaluation.md | L4 | 206 | 0 | 0 | 0 | 0 | 0 | 6 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\01_verification_toolchain.md | L4 | 1585 | 3 | 0 | 0 | 0 | 5 | 17 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\02_formal_methods.md | L4 | 22 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\03_aerospace_certification_formal_methods.md | L4 | 1147 | 3 | 0 | 0 | 1 | 2 | 7 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\04_modern_verification_tools.md | L4 | 580 | 3 | 0 | 0 | 1 | 1 | 10 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\05_programming_language_foundations.md | L4 | 509 | 3 | 0 | 0 | 1 | 1 | 12 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\06_quiz_formal_methods.md | L4 | 684 | 0 | 0 | 0 | 0 | 0 | 10 | 0 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\07_autoverus.md | L4 | 223 | 1 | 0 | 0 | 1 | 0 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\08_miri.md | L4 | 366 | 0 | 0 | 0 | 3 | 2 | 4 | 0 | ❌ | ✅ | ✅ | 进阶 / 工程 / 形式化 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\09_kani.md | L4 | 426 | 0 | 0 | 0 | 1 | 1 | 11 | 0 | ❌ | ✅ | ✅ | 进阶 / 工程 / 形式化 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\10_certified_toolchains_and_packages.md | L4 | 266 | 0 | 0 | 0 | 1 | 2 | 2 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\01_rustc_query_system.md | L4 | 639 | 1 | 0 | 0 | 1 | 4 | 5 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\02_mir_codegen_llvm_primer.md | L4 | 404 | 8 | 3 | 0 | 2 | 1 | 3 | 0 | ✅ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\03_trait_solver_in_rustc.md | L4 | 458 | 3 | 3 | 0 | 1 | 1 | 10 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\04_name_resolution_and_hir.md | L4 | 374 | 0 | 0 | 0 | 3 | 2 | 7 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\05_application_binary_interface.md | L4 | 283 | 0 | 0 | 0 | 1 | 1 | 8 | 0 | ❌ | ✅ | ✅ | 专家 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\06_names_and_resolution.md | L4 | 247 | 2 | 0 | 0 | 1 | 0 | 4 | 6 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\07_special_types_and_traits.md | L4 | 225 | 2 | 0 | 0 | 0 | 0 | 2 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\08_type_layout.md | L4 | 189 | 0 | 0 | 0 | 0 | 0 | 6 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\09_destructors.md | L4 | 220 | 0 | 0 | 0 | 0 | 0 | 5 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\10_lexical_structure.md | L4 | 287 | 3 | 0 | 0 | 1 | 0 | 8 | 6 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\11_items_reference.md | L4 | 259 | 3 | 0 | 0 | 1 | 0 | 9 | 6 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\12_attributes.md | L4 | 191 | 3 | 0 | 0 | 1 | 0 | 5 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\13_statements_and_expressions_reference.md | L4 | 196 | 3 | 0 | 0 | 1 | 0 | 7 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\14_patterns_reference.md | L4 | 194 | 3 | 0 | 0 | 1 | 0 | 6 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\15_generics_compiler_behavior.md | L4 | 211 | 4 | 0 | 0 | 1 | 0 | 7 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\16_names_reference.md | L4 | 192 | 3 | 0 | 0 | 1 | 0 | 4 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\17_reference_appendices.md | L4 | 171 | 2 | 0 | 0 | 1 | 0 | 1 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\06_notation\01_notation.md | L4 | 138 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\07_concurrency_semantics\01_process_calculi_for_rust.md | L4 | 351 | 6 | 0 | 0 | 4 | 1 | 6 | 8 | ✅ | ✅ | ✅ | 进阶 / 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\07_concurrency_semantics\02_linearizability_and_consistency.md | L4 | 347 | 10 | 0 | 0 | 3 | 1 | 2 | 6 | ✅ | ✅ | ✅ | 进阶 / 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\07_concurrency_semantics\03_actor_semantics.md | L4 | 331 | 18 | 0 | 0 | 3 | 1 | 4 | 6 | ✅ | ✅ | ✅ | 进阶 / 研究者 | 专家级 |
| E:\_src\rust-lang\concept\05_comparative\00_paradigms\01_paradigm_matrix.md | L5 | 1300 | 8 | 0 | 0 | 5 | 9 | 12 | 16 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\00_paradigms\02_execution_model_isomorphism.md | L5 | 1049 | 3 | 0 | 0 | 1 | 6 | 13 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\05_comparative\00_paradigms\03_cpp_rust_surface_features.md | L5 | 261 | 0 | 0 | 0 | 0 | 0 | 4 | 0 | ❌ | ✅ | ✅ | 进阶 | 研究级 |
| E:\_src\rust-lang\concept\05_comparative\00_paradigms\04_five_models_definition_matrix.md | L5 | 145 | 10 | 0 | 0 | 0 | 1 | 0 | 6 | ✅ | ✅ | ✅ | 初学者 / 进阶 | 导航级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\01_rust_vs_cpp.md | L5 | 2223 | 9 | 0 | 0 | 3 | 11 | 14 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\02_cpp_abi_object_model.md | L5 | 975 | 4 | 0 | 0 | 2 | 1 | 18 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\03_rust_vs_go.md | L5 | 1016 | 3 | 0 | 0 | 3 | 6 | 11 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\04_rust_vs_ruby.md | L5 | 770 | 3 | 0 | 0 | 2 | 1 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\05_rust_vs_swift.md | L5 | 750 | 3 | 0 | 0 | 2 | 1 | 6 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\06_rust_vs_zig.md | L5 | 784 | 3 | 0 | 0 | 2 | 1 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\01_rust_vs_java.md | L5 | 638 | 3 | 0 | 0 | 2 | 3 | 7 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\02_rust_vs_python.md | L5 | 728 | 3 | 0 | 0 | 2 | 2 | 6 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\03_rust_vs_javascript.md | L5 | 739 | 3 | 0 | 0 | 2 | 2 | 5 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\04_rust_vs_kotlin.md | L5 | 819 | 3 | 0 | 0 | 2 | 1 | 6 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\05_rust_vs_scala.md | L5 | 779 | 3 | 0 | 0 | 2 | 1 | 6 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\06_rust_vs_csharp.md | L5 | 876 | 4 | 0 | 0 | 2 | 1 | 6 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\07_rust_vs_elixir.md | L5 | 924 | 3 | 0 | 0 | 3 | 1 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\08_rust_vs_typescript.md | L5 | 956 | 3 | 0 | 0 | 2 | 2 | 6 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\03_domain_comparisons\01_safety_boundaries.md | L5 | 1047 | 8 | 0 | 0 | 1 | 7 | 9 | 9 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\05_comparative\03_domain_comparisons\02_quiz_rust_vs_systems.md | L5 | 798 | 0 | 0 | 0 | 0 | 0 | 14 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\01_toolchain.md | L6 | 1973 | 13 | 0 | 0 | 2 | 10 | 16 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\02_logging_observability.md | L6 | 706 | 3 | 0 | 0 | 2 | 3 | 9 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\03_devops_and_ci_cd.md | L6 | 904 | 3 | 0 | 0 | 2 | 3 | 7 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\04_compiler_internals.md | L6 | 918 | 3 | 0 | 0 | 2 | 1 | 7 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\05_compiler_infrastructure.md | L6 | 320 | 3 | 0 | 0 | 1 | 0 | 1 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\06_quiz_toolchain.md | L6 | 644 | 0 | 0 | 0 | 0 | 0 | 7 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\07_rustdoc_196_changes.md | L6 | 360 | 0 | 0 | 0 | 0 | 1 | 4 | 0 | ❌ | ✅ | ✅ | 进阶 / 工程 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\08_platform_rust_integration.md | L6 | 327 | 0 | 0 | 0 | 0 | 1 | 4 | 2 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\09_llvm_backend_and_codegen.md | L6 | 317 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\10_rustc_driver_and_stable_mir.md | L6 | 280 | 0 | 0 | 0 | 0 | 0 | 4 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\11_compiler_diagnostics_and_ui_tests.md | L6 | 292 | 0 | 0 | 0 | 0 | 0 | 5 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\12_rustc_bootstrap.md | L6 | 249 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\13_compiler_testing.md | L6 | 291 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\14_development_tools.md | L6 | 244 | 0 | 0 | 0 | 0 | 1 | 5 | 0 | ❌ | ✅ | ✅ | 初学者 | 研究级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\15_z_flags_reference.md | L6 | 184 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | ❌ | ✅ | ✅ | None | None |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\01_cargo_script.md | L6 | 776 | 3 | 0 | 0 | 1 | 3 | 12 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\02_public_private_deps.md | L6 | 306 | 4 | 0 | 0 | 1 | 2 | 2 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\03_resolver_v3_public_feature_unification.md | L6 | 216 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 实践级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\04_cargo_196_features.md | L6 | 308 | 0 | 0 | 0 | 0 | 1 | 1 | 0 | ❌ | ✅ | ✅ | 进阶 / 工程 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\05_cargo_build_scripts.md | L6 | 571 | 0 | 0 | 0 | 3 | 3 | 16 | 0 | ❌ | ✅ | ✅ | 进阶 / 工程 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\06_cargo_dependency_resolution.md | L6 | 584 | 0 | 0 | 0 | 1 | 1 | 2 | 0 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\07_cargo_source_replacement.md | L6 | 310 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\08_cargo_registries_and_publishing.md | L6 | 329 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\09_cargo_authentication_and_cache.md | L6 | 309 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\10_cargo_manifest_reference.md | L6 | 316 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 中级 → 高级 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\11_cargo_profiles_and_lints.md | L6 | 362 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\12_cargo_subcommands_and_plugins.md | L6 | 244 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\13_cargo_security_cves.md | L6 | 557 | 4 | 0 | 0 | 4 | 2 | 2 | 2 | ✅ | ✅ | ✅ | 进阶 / 工程 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\14_cargo_workspaces.md | L6 | 292 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\15_cargo_getting_started.md | L6 | 178 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\16_cargo_workflow.md | L6 | 179 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\17_cargo_guide_practices.md | L6 | 178 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\18_cargo_configuration.md | L6 | 195 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\19_cargo_commands_reference.md | L6 | 181 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\20_cargo_manifest_targets.md | L6 | 205 | 0 | 0 | 0 | 0 | 0 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\21_cargo_registry_internals.md | L6 | 169 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 专家 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\22_build_std.md | L6 | 379 | 3 | 0 | 0 | 0 | 3 | 3 | 6 | ❌ | ✅ | ✅ | 进阶 / 工程 | None |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\23_cargo_197_features.md | L6 | 261 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 / 工程 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\02_core_crates\01_core_crates.md | L6 | 1406 | 8 | 0 | 0 | 2 | 7 | 17 | 3 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\01_patterns.md | L6 | 3200 | 17 | 0 | 0 | 2 | 6 | 47 | 8 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\02_idioms_spectrum.md | L6 | 1493 | 4 | 0 | 0 | 1 | 5 | 37 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\03_system_design_principles.md | L6 | 828 | 3 | 0 | 0 | 1 | 7 | 10 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\04_system_composability.md | L6 | 823 | 0 | 0 | 0 | 0 | 5 | 23 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\05_microservice_patterns.md | L6 | 1035 | 3 | 0 | 0 | 1 | 7 | 15 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\06_event_driven_architecture.md | L6 | 1053 | 3 | 0 | 0 | 1 | 5 | 15 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\07_cqrs_event_sourcing.md | L6 | 1563 | 3 | 0 | 0 | 3 | 2 | 20 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\08_architecture_patterns.md | L6 | 1364 | 3 | 0 | 0 | 2 | 1 | 13 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\09_pattern_implementation_comparison.md | L6 | 1011 | 4 | 0 | 0 | 1 | 1 | 19 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\10_pattern_selection_best_practices.md | L6 | 849 | 4 | 0 | 0 | 1 | 1 | 13 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\11_formal_design_pattern_theory.md | L6 | 1142 | 4 | 0 | 0 | 1 | 1 | 18 | 6 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\12_frontier_research_and_innovative_patterns.md | L6 | 1086 | 4 | 0 | 0 | 1 | 1 | 19 | 6 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\13_engineering_and_production_patterns.md | L6 | 364 | 3 | 0 | 0 | 1 | 0 | 9 | 6 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\14_design_patterns_glossary.md | L6 | 295 | 4 | 0 | 0 | 0 | 1 | 4 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\15_design_patterns_faq.md | L6 | 510 | 4 | 0 | 0 | 0 | 0 | 4 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\16_pattern_composition_algebra.md | L6 | 792 | 3 | 0 | 0 | 2 | 1 | 15 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\17_workflow_theory.md | L6 | 1468 | 3 | 0 | 0 | 2 | 1 | 17 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\18_api_design_patterns.md | L6 | 1395 | 3 | 0 | 0 | 3 | 1 | 21 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\01_distributed_systems.md | L6 | 846 | 3 | 0 | 0 | 2 | 2 | 9 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\02_cloud_native.md | L6 | 834 | 3 | 0 | 0 | 2 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\03_web_frameworks.md | L6 | 1085 | 4 | 0 | 0 | 3 | 4 | 11 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\04_http_client_development.md | L6 | 226 | 0 | 0 | 0 | 0 | 0 | 10 | 0 | ❌ | ✅ | ✅ | 进阶 | 进阶 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\05_glommio_and_thread_per_core.md | L6 | 270 | 3 | 0 | 0 | 0 | 0 | 7 | 6 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\06_websocket_realtime_communication.md | L6 | 844 | 4 | 0 | 0 | 0 | 1 | 12 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\07_network_protocols.md | L6 | 591 | 3 | 0 | 0 | 1 | 1 | 9 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\08_high_performance_network_service_architecture.md | L6 | 2189 | 3 | 0 | 0 | 0 | 1 | 21 | 6 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\09_reactive_programming.md | L6 | 1142 | 3 | 0 | 0 | 2 | 1 | 14 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\10_tokio_runtime_internals.md | L6 | 345 | 8 | 0 | 0 | 1 | 1 | 8 | 0 | ✅ | ✅ | ✅ | 进阶-专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\01_wasi.md | L6 | 699 | 4 | 0 | 0 | 4 | 3 | 11 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\02_cross_compilation.md | L6 | 670 | 3 | 0 | 0 | 2 | 1 | 5 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\03_embedded_systems.md | L6 | 1005 | 3 | 0 | 0 | 2 | 2 | 10 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\04_cli_development.md | L6 | 817 | 3 | 0 | 0 | 2 | 2 | 9 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\05_os_kernel.md | L6 | 545 | 3 | 0 | 0 | 1 | 1 | 12 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\06_robotics.md | L6 | 1080 | 3 | 0 | 0 | 2 | 1 | 15 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\07_embedded_graphics.md | L6 | 1185 | 3 | 0 | 0 | 3 | 1 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\08_c_to_rust_translation.md | L6 | 499 | 3 | 0 | 0 | 1 | 1 | 4 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\09_embedded_hal_1_0_migration.md | L6 | 323 | 3 | 0 | 0 | 0 | 1 | 6 | 6 | ❌ | ✅ | ✅ | 进阶 / 工程 | None |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\10_target_tier_platform_support.md | L6 | 94 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | None | None |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\01_application_domains.md | L6 | 1564 | 8 | 0 | 0 | 2 | 7 | 12 | 3 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\02_database_access.md | L6 | 857 | 3 | 0 | 0 | 2 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\03_stream_processing_ecosystem.md | L6 | 630 | 3 | 0 | 0 | 1 | 1 | 12 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\04_database_systems.md | L6 | 604 | 3 | 0 | 0 | 1 | 1 | 11 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\05_data_engineering.md | L6 | 1025 | 3 | 0 | 0 | 2 | 1 | 13 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\06_distributed_consensus.md | L6 | 974 | 3 | 0 | 0 | 2 | 1 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\07_rust_for_data_science.md | L6 | 683 | 3 | 0 | 0 | 2 | 1 | 10 | 0 | ✅ | ✅ | ✅ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\08_crdt_type_zoo.md | L6 | 355 | 17 | 0 | 0 | 6 | 0 | 6 | 4 | ✅ | ✅ | ✅ | 进阶 / 工程 / 研究者 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\09_causal_ordering_vector_clocks.md | L6 | 307 | 9 | 0 | 0 | 5 | 0 | 1 | 4 | ✅ | ✅ | ✅ | 进阶 / 工程 / 研究者 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\07_security_and_cryptography\01_security_practices.md | L6 | 1104 | 3 | 0 | 0 | 2 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\07_security_and_cryptography\02_security_cryptography.md | L6 | 1028 | 3 | 0 | 0 | 3 | 1 | 18 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\07_security_and_cryptography\03_cargo_vet_supply_chain.md | L6 | 238 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 / 工程 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\08_formal_verification\01_formal_ecosystem_tower.md | L6 | 627 | 1 | 0 | 0 | 1 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\08_formal_verification\02_formal_verification_tools.md | L6 | 1048 | 3 | 0 | 0 | 3 | 1 | 14 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_testing_and_quality\01_testing_strategies.md | L6 | 758 | 3 | 0 | 0 | 2 | 3 | 9 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_testing_and_quality\02_documentation.md | L6 | 687 | 3 | 0 | 0 | 3 | 2 | 7 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_testing_and_quality\03_testing.md | L6 | 805 | 3 | 0 | 0 | 3 | 3 | 10 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_testing_and_quality\04_benchmarking.md | L6 | 244 | 0 | 0 | 0 | 0 | 1 | 7 | 0 | ❌ | ✅ | ✅ | 进阶 | 指南级 |
| E:\_src\rust-lang\concept\06_ecosystem\10_performance\01_performance_optimization.md | L6 | 1157 | 3 | 0 | 0 | 2 | 1 | 13 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\01_blockchain.md | L6 | 964 | 7 | 0 | 0 | 0 | 3 | 15 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\02_game_ecs.md | L6 | 1395 | 1 | 0 | 0 | 1 | 7 | 25 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\03_webassembly.md | L6 | 676 | 3 | 0 | 0 | 2 | 3 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\04_licensing_and_compliance.md | L6 | 687 | 3 | 0 | 0 | 2 | 1 | 6 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\05_game_development.md | L6 | 689 | 3 | 0 | 0 | 2 | 1 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\06_game_development.md | L6 | 17 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\07_algorithms_competitive_programming.md | L6 | 1313 | 0 | 0 | 0 | 1 | 0 | 31 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\08_algorithm_engineering_practice.md | L6 | 2158 | 3 | 0 | 0 | 1 | 0 | 25 | 6 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\09_data_structures_in_rust.md | L6 | 316 | 3 | 0 | 0 | 0 | 1 | 10 | 6 | ❌ | ✅ | ✅ | 进阶 | 进阶 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\10_algorithm_complexity_analysis.md | L6 | 224 | 0 | 0 | 0 | 0 | 0 | 6 | 0 | ❌ | ✅ | ✅ | 进阶 | 进阶 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\11_cutting_edge_algorithms.md | L6 | 246 | 3 | 0 | 0 | 0 | 0 | 3 | 6 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\12_formal_algorithm_theory.md | L6 | 309 | 3 | 0 | 0 | 0 | 0 | 6 | 6 | ❌ | ✅ | ✅ | 专家 | 形式化级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\13_machine_learning_ecosystem.md | L6 | 999 | 3 | 0 | 0 | 2 | 0 | 14 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\14_industrial_case_studies.md | L6 | 506 | 3 | 0 | 0 | 1 | 0 | 7 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\15_game_engine_internals.md | L6 | 1177 | 3 | 0 | 0 | 2 | 0 | 13 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\16_quantum_computing_rust.md | L6 | 1046 | 3 | 0 | 0 | 2 | 0 | 12 | 0 | ✅ | ✅ | ✅ | 研究者 | 实验级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\17_webassembly_advanced.md | L6 | 1228 | 3 | 0 | 0 | 2 | 0 | 16 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\18_wasm_glossary.md | L6 | 407 | 4 | 0 | 0 | 0 | 0 | 0 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\19_wasm_faq.md | L6 | 495 | 4 | 0 | 0 | 0 | 0 | 6 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\20_wasm_javascript_interop.md | L6 | 537 | 4 | 0 | 0 | 0 | 0 | 5 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\21_safety_critical_topic_index.md | L6 | 43 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\22_autosar_and_rust.md | L6 | 167 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 / 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\12_networking\01_advanced_network_protocols.md | L6 | 314 | 3 | 0 | 0 | 0 | 2 | 8 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\12_networking\02_network_security.md | L6 | 384 | 3 | 0 | 0 | 0 | 0 | 8 | 6 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\12_networking\03_custom_protocol_implementation.md | L6 | 216 | 0 | 0 | 0 | 0 | 0 | 4 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\12_networking\04_network_programming_quick_start.md | L6 | 317 | 3 | 0 | 0 | 0 | 2 | 7 | 6 | ❌ | ✅ | ✅ | 进阶 | 指南级 |
| E:\_src\rust-lang\concept\06_ecosystem\12_networking\05_networking_basics.md | L6 | 1016 | 4 | 0 | 0 | 1 | 0 | 18 | 6 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\12_networking\06_formal_network_protocol_theory.md | L6 | 640 | 3 | 0 | 0 | 1 | 0 | 16 | 6 | ❌ | ✅ | ✅ | 研究者 / 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\13_quizzes\01_quiz_networking_async_ecosystem.md | L6 | 334 | 0 | 0 | 0 | 0 | 0 | 2 | 0 | ❌ | ✅ | ❌ | 进阶 | None |
| E:\_src\rust-lang\concept\06_ecosystem\13_quizzes\02_quiz_database_storage.md | L6 | 316 | 5 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ❌ | 进阶 | None |
| E:\_src\rust-lang\concept\06_ecosystem\13_quizzes\03_quiz_security_testing.md | L6 | 325 | 1 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ❌ | 进阶 | None |
| E:\_src\rust-lang\concept\06_ecosystem\13_quizzes\04_quiz_domain_applications.md | L6 | 335 | 1 | 0 | 0 | 0 | 0 | 2 | 0 | ❌ | ✅ | ❌ | 进阶 | None |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\01_rust_version_tracking.md | L7 | 2625 | 3 | 0 | 0 | 0 | 3 | 9 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\02_editions.md | L7 | 349 | 4 | 0 | 0 | 1 | 1 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\03_rust_release_process.md | L7 | 168 | 0 | 0 | 0 | 1 | 1 | 1 | 0 | ✅ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\04_nightly_rust.md | L7 | 260 | 3 | 0 | 0 | 0 | 1 | 1 | 6 | ❌ | ✅ | ✅ | 初学者 | 研究级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\feature_domain_matrix_197.md | L7 | 277 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\migration_197_decision_tree.md | L7 | 777 | 0 | 0 | 0 | 0 | 9 | 17 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_90_stabilized.md | L7 | 919 | 4 | 0 | 0 | 0 | 0 | 15 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_91_stabilized.md | L7 | 2744 | 3 | 0 | 0 | 0 | 0 | 81 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_92_stabilized.md | L7 | 2734 | 3 | 0 | 0 | 0 | 0 | 72 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_93_stabilized.md | L7 | 215 | 3 | 0 | 0 | 0 | 0 | 8 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_94_stabilized.md | L7 | 223 | 4 | 0 | 0 | 0 | 0 | 4 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_95_stabilized.md | L7 | 348 | 0 | 0 | 0 | 0 | 0 | 14 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_96_stabilized.md | L7 | 358 | 0 | 0 | 0 | 0 | 0 | 5 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_97_preview.md | L7 | 110 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_97_stabilized.md | L7 | 470 | 0 | 0 | 0 | 0 | 0 | 14 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_98_preview.md | L7 | 668 | 0 | 0 | 0 | 0 | 0 | 7 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_98_stabilized.md | L7 | 135 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\01_edition_roadmap\01_rust_edition_preview.md | L7 | 147 | 0 | 0 | 0 | 0 | 0 | 5 | 0 | ❌ | ✅ | ✅ | 进阶 | 研究级 |
| E:\_src\rust-lang\concept\07_future\01_edition_roadmap\02_edition_guide.md | L7 | 904 | 3 | 0 | 0 | 2 | 1 | 13 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\01_edition_roadmap\03_rust_edition_guide.md | L7 | 20 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\07_future\01_edition_roadmap\04_roadmap.md | L7 | 1097 | 3 | 0 | 0 | 2 | 2 | 17 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\01_effects_system.md | L7 | 1763 | 4 | 0 | 0 | 0 | 4 | 26 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\02_mcdc_coverage_preview.md | L7 | 578 | 3 | 0 | 0 | 2 | 3 | 5 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\03_safety_tags_preview.md | L7 | 677 | 3 | 0 | 0 | 3 | 3 | 6 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\04_parallel_frontend_preview.md | L7 | 688 | 3 | 0 | 0 | 3 | 3 | 6 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\05_derive_coerce_pointee_preview.md | L7 | 651 | 3 | 0 | 0 | 2 | 3 | 8 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\06_const_trait_impl_preview.md | L7 | 674 | 3 | 0 | 0 | 2 | 2 | 7 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\07_stable_abi_preview.md | L7 | 248 | 3 | 0 | 0 | 0 | 0 | 3 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\08_inline_const_pattern_preview.md | L7 | 281 | 3 | 0 | 0 | 0 | 0 | 8 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\09_return_type_notation_preview.md | L7 | 516 | 0 | 0 | 0 | 3 | 0 | 10 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\10_must_not_suspend_preview.md | L7 | 237 | 3 | 0 | 0 | 0 | 0 | 4 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\11_unsafe_fields_preview.md | L7 | 654 | 3 | 0 | 0 | 2 | 3 | 8 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\12_ferrocene_preview.md | L7 | 303 | 0 | 0 | 0 | 0 | 2 | 0 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\13_lifetime_capture_preview.md | L7 | 247 | 3 | 0 | 0 | 0 | 0 | 4 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\14_pin_ergonomics_preview.md | L7 | 368 | 0 | 0 | 0 | 2 | 2 | 10 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\15_rpitit_preview.md | L7 | 280 | 3 | 0 | 0 | 0 | 0 | 8 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\16_cranelift_backend_preview.md | L7 | 769 | 3 | 0 | 0 | 2 | 3 | 9 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\17_type_alias_impl_trait_preview.md | L7 | 242 | 3 | 0 | 0 | 0 | 0 | 4 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\18_arbitrary_self_types_preview.md | L7 | 421 | 3 | 0 | 0 | 1 | 0 | 11 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\19_const_trait_preview.md | L7 | 263 | 3 | 0 | 0 | 0 | 0 | 6 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\20_ergonomic_ref_counting_preview.md | L7 | 326 | 0 | 0 | 0 | 0 | 0 | 7 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\21_rust_specification_preview.md | L7 | 642 | 3 | 0 | 0 | 2 | 3 | 6 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\22_async_drop_preview.md | L7 | 777 | 3 | 0 | 0 | 2 | 2 | 7 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\23_field_projections_preview.md | L7 | 419 | 3 | 0 | 0 | 1 | 0 | 10 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\24_borrow_sanitizer.md | L7 | 374 | 0 | 0 | 0 | 1 | 1 | 3 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\25_gen_blocks_preview.md | L7 | 676 | 3 | 0 | 0 | 2 | 3 | 8 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\26_std_autodiff_preview.md | L7 | 358 | 3 | 0 | 0 | 1 | 0 | 7 | 0 | ✅ | ✅ | ✅ | 研究者 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\27_cargo_semver_checks_preview.md | L7 | 211 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\28_wasm_target_evolution.md | L7 | 248 | 3 | 0 | 0 | 0 | 0 | 1 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\29_aarch64_sve_sme_preview.md | L7 | 292 | 0 | 0 | 0 | 0 | 0 | 5 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\30_rust_in_space.md | L7 | 259 | 3 | 0 | 0 | 0 | 0 | 4 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\31_specialization_preview.md | L7 | 775 | 3 | 0 | 0 | 2 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\32_compile_time_execution.md | L7 | 759 | 3 | 0 | 0 | 2 | 1 | 6 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\33_autoverus_preview.md | L7 | 105 | 0 | 0 | 0 | 0 | 0 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\34_open_enums_preview.md | L7 | 825 | 3 | 0 | 0 | 2 | 3 | 13 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\35_f16_f128_preview.md | L7 | 164 | 0 | 0 | 0 | 1 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\36_unsafe_pinned_preview.md | L7 | 149 | 0 | 0 | 0 | 1 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\37_default_field_values_preview.md | L7 | 144 | 0 | 0 | 0 | 1 | 0 | 4 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\38_complex_numbers_preview.md | L7 | 139 | 0 | 0 | 0 | 1 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\01_ai_integration.md | L7 | 1005 | 1 | 0 | 0 | 2 | 2 | 9 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\02_formal_methods.md | L7 | 1696 | 9 | 0 | 0 | 1 | 9 | 9 | 3 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\03_evolution.md | L7 | 2206 | 8 | 0 | 0 | 1 | 6 | 19 | 3 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\04_rust_for_linux.md | L7 | 1072 | 3 | 0 | 0 | 2 | 2 | 11 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\05_rust_in_ai.md | L7 | 764 | 3 | 0 | 0 | 2 | 1 | 7 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\06_rust_for_webassembly.md | L7 | 970 | 3 | 0 | 0 | 3 | 2 | 11 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\07_ebpf_rust.md | L7 | 984 | 3 | 0 | 0 | 0 | 3 | 15 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\05_quizzes\01_quiz_version_and_preview.md | L7 | 332 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ❌ | 进阶 | None |
