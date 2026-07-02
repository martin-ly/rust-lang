# 知识体系质量仪表盘 (KB Quality Dashboard)

> 生成时间: 2026-07-02T21:44:13.166253+00:00
> 扫描文件数: 382

## 全局指标

| 指标 | 数值 | 目标 | 状态 |
|:---|:---|:---|:---|
| 总文件数 | 382 | 27 | ✅ |
| 总定理链 (⟹) | 874 | ≥270 | ✅ |
| 总反命题 | 427 | ≥40 | ✅ |
| 总 Mermaid 图 | 540 | ≥50 | ✅ |
| 编译验证代码块 | 3491 | ≥150 | ✅ |
| 定理矩阵总行 | 16542 | — | — |
| 死链数量 | 0 | 0 | ✅ |
| 反向推理 (⟸) | 64 | ≥50 | ✅ |
| 模板化 ⟹ | 0 | 0 | ✅ |
| 前置概念覆盖率 | 322/322 | 100% | ✅ |
| 后置概念覆盖率 | 322/322 | 100% | ✅ |
| 双标签覆盖率 | 320/322 | >=95% | ✅ |
| 非法标签组合 | 0 | 0 | ✅ |

## 按层级分布

| 层级 | 文件数 | 平均 ⟹/文件 | 平均过渡段/文件 | 认知路径 | ⟸/文件 | 模板化 | 前置覆盖 | 后置覆盖 | 双标签 |
|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|
| L0 | 60 | 5.4 | 3.3 | 34/60 (56%) | 0.0 | 0 | 12/60 | 11/60 | 45/60 |
| L1 | 43 | 1.3 | 1.6 | 7/43 (16%) | 0.2 | 0 | 43/43 | 43/43 | 43/43 |
| L2 | 33 | 1.7 | 1.0 | 4/33 (12%) | 0.8 | 0 | 33/33 | 33/33 | 31/33 |
| L3 | 36 | 2.2 | 0.6 | 6/36 (16%) | 0.7 | 0 | 36/36 | 36/36 | 36/36 |
| L4 | 51 | 1.3 | 0.7 | 10/51 (19%) | 0.0 | 0 | 51/51 | 51/51 | 51/51 |
| L5 | 19 | 1.4 | 1.9 | 4/19 (21%) | 0.0 | 0 | 19/19 | 19/19 | 19/19 |
| L6 | 86 | 2.2 | 3.8 | 12/86 (13%) | 0.0 | 0 | 86/86 | 86/86 | 86/86 |
| L7 | 54 | 1.4 | 1.7 | 5/54 (9%) | 0.0 | 0 | 54/54 | 54/54 | 54/54 |

## 风险文件

| 文件 | 层级 | 未通过项 |
|:---|:---|:---|
| concept\01_foundation\00_start.md | L1 | 缺失认知路径; 缺失反命题 |
| concept\01_foundation\05_reference_semantics.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\06_zero_cost_abstractions.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\07_control_flow.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\08_collections.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\09_strings_and_text.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\10_numerics.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\11_modules_and_paths.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\12_attributes_and_macros.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\13_panic_and_abort.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\14_coercion_and_casting.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\15_closure_basics.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\16_testing_basics.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\17_collections_advanced.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\18_strings_and_encoding.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\19_value_vs_reference_semantics.md | L1 | 缺失认知路径; 缺失反命题 |
| concept\01_foundation\20_variable_model.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\21_effects_and_purity.md | L1 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\22_data_abstraction_spectrum.md | L1 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\23_move_semantics.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\24_quiz_type_system.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\25_quiz_error_handling.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\26_quiz_modules_testing.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\27_quiz_closures_iterators.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\28_ownership_inventories_brown_book.md | L1 | 缺失认知路径; 缺失反命题 |
| concept\01_foundation\29_quiz_pl_foundations.md | L1 | 缺失认知路径; 缺失反命题 |
| concept\01_foundation\31_never_type.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\32_error_handling_basics.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\33_quiz_ownership_borrowing.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\34_pl_prerequisites.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\35_preludes.md | L1 | 缺失认知路径; 缺失反命题 |
| concept\01_foundation\36_keywords.md | L1 | 缺失认知路径; 缺失反命题 |
| concept\01_foundation\37_operators_and_symbols.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\38_crates_and_source_files.md | L1 | 缺失认知路径; 缺失反命题 |
| concept\01_foundation\39_items.md | L1 | 缺失认知路径; 缺失反命题 |
| concept\01_foundation\40_patterns.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\41_statements_and_expressions.md | L1 | 缺失认知路径; 缺失反命题 |
| concept\01_foundation\42_useful_development_tools.md | L1 | 缺失认知路径; 缺失反命题 |
| concept\02_intermediate\01_traits.md | L2 | 缺失内容分级标签 |
| concept\02_intermediate\02_generics.md | L2 | 缺失内容分级标签 |
| concept\02_intermediate\05_assert_matches.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| concept\02_intermediate\06_range_types.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| concept\02_intermediate\07_closure_types.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| concept\02_intermediate\08_interior_mutability.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| concept\02_intermediate\09_serde_patterns.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| concept\02_intermediate\10_module_system.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| concept\02_intermediate\11_cow_and_borrowed.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| concept\02_intermediate\12_smart_pointers.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| concept\02_intermediate\13_dsl_and_embedding.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| concept\02_intermediate\14_newtype_and_wrapper.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| concept\02_intermediate\15_iterator_patterns.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (1 < 3); 反向推理不足 (⟸ 0 < 2) |
| concept\02_intermediate\16_error_handling_deep_dive.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| concept\02_intermediate\17_macro_patterns.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| concept\02_intermediate\18_lifetimes_advanced.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| concept\02_intermediate\19_advanced_traits.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| concept\02_intermediate\20_type_system_advanced.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| concept\02_intermediate\21_metaprogramming.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| concept\02_intermediate\22_api_naming_conventions.md | L2 | 缺失认知路径; 过渡段落不足 (2 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| concept\02_intermediate\23_quiz_traits_and_generics.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| concept\02_intermediate\24_quiz_memory_management.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| concept\02_intermediate\25_rtti_and_dynamic_typing.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| concept\02_intermediate\26_c_preprocessor_vs_rust_macros.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| concept\02_intermediate\27_exception_safety_rust_cpp.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (2 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| concept\02_intermediate\28_construction_and_initialization.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| concept\02_intermediate\29_friend_vs_module_privacy.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| concept\02_intermediate\30_quiz_cpp_rust_foundations.md | L2 | 缺失认知路径; 缺失反命题 |
| concept\02_intermediate\31_derive_traits.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| concept\02_intermediate\32_editions.md | L2 | 缺失认知路径; 缺失反命题 |
| concept\02_intermediate\33_rust_release_process.md | L2 | 缺失认知路径; 缺失反命题 |
| concept\03_advanced\00_before_formal.md | L3 | 缺失认知路径; 缺失反命题 |
| concept\03_advanced\05_rust_ffi.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| concept\03_advanced\06_pin_unpin.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| concept\03_advanced\07_proc_macro.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| concept\03_advanced\08_nll_and_polonius.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| concept\03_advanced\09_ffi_advanced.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| concept\03_advanced\10_concurrency_patterns.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| concept\03_advanced\11_atomics_and_memory_ordering.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| concept\03_advanced\12_unsafe_rust_patterns.md | L3 | 缺失反命题 |
| concept\03_advanced\13_inline_assembly.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| concept\03_advanced\14_custom_allocators.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| concept\03_advanced\15_zero_copy_parsing.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| concept\03_advanced\16_lock_free.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| concept\03_advanced\17_type_erasure.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| concept\03_advanced\18_network_programming.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| concept\03_advanced\19_parallel_distributed_pattern_spectrum.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| concept\03_advanced\20_stream_processing_semantics.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| concept\03_advanced\21_quiz_concurrency_async.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| concept\03_advanced\22_quiz_unsafe.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| concept\03_advanced\23_quiz_macros.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| concept\03_advanced\24_async_closures.md | L3 | 过渡段落不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| concept\03_advanced\25_async_advanced.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (1 < 3); 缺失反命题; 反向推理不足 (⟸ 1 < 2) |
| concept\03_advanced\26_async_patterns.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| concept\03_advanced\27_linkage.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| concept\03_advanced\28_conditional_compilation.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| concept\03_advanced\29_memory_model.md | L3 | 缺失认知路径; 缺失反命题 |
| concept\03_advanced\30_rust_runtime.md | L3 | 缺失认知路径; 缺失反命题 |
| concept\03_advanced\31_panic.md | L3 | 缺失认知路径; 缺失反命题 |
| concept\03_advanced\32_memory_allocation_and_lifetime.md | L3 | 缺失认知路径; 缺失反命题 |
| concept\03_advanced\33_variables.md | L3 | 缺失认知路径; 缺失反命题 |
| concept\03_advanced\34_visibility_and_privacy.md | L3 | 缺失认知路径; 缺失反命题 |
| concept\03_advanced\35_unsafe_reference.md | L3 | 缺失认知路径; 缺失反命题 |
| concept\04_formal\05_verification_toolchain.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题 |
| concept\04_formal\06_subtype_variance.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\04_formal\09_linear_logic_applications.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\04_formal\10_category_theory.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\04_formal\11_separation_logic.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\04_formal\12_denotational_semantics.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\04_formal\13_formal_methods.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\04_formal\14_lambda_calculus.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\04_formal\15_hoare_logic.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\04_formal\16_aerospace_certification_formal_methods.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题 |
| concept\04_formal\17_operational_semantics.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\04_formal\18_evaluation_strategies.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\04_formal\19_rustc_query_system.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题 |
| concept\04_formal\22_modern_verification_tools.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题 |
| concept\04_formal\23_programming_language_foundations.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题 |
| concept\04_formal\24_autoverus.md | L4 | 缺失认知路径 |
| concept\04_formal\25_quiz_formal_methods.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题 |
| concept\04_formal\26_trait_solver_in_rustc.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题 |
| concept\04_formal\27_type_checking_and_inference.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题 |
| concept\04_formal\28_borrow_checking_decidability.md | L4 | 过渡段落不足 (0 < 3); 定理链不足 (1 < 3); 缺失反命题 |
| concept\04_formal\29_type_inference_complexity.md | L4 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题 |
| concept\04_formal\30_aeneas_symbolic_semantics.md | L4 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题 |
| concept\04_formal\31_miri.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\04_formal\32_kani.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题 |
| concept\04_formal\33_safety_tags_in_formal.md | L4 | 缺失认知路径 |
| concept\04_formal\34_borrow_sanitizer_in_formal.md | L4 | 缺失认知路径 |
| concept\04_formal\35_name_resolution_and_hir.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\04_formal\36_tree_borrows_deep_dive.md | L4 | 缺失认知路径 |
| concept\04_formal\37_behavior_considered_undefined.md | L4 | 缺失认知路径; 缺失反命题 |
| concept\04_formal\38_application_binary_interface.md | L4 | 缺失认知路径; 缺失反命题 |
| concept\04_formal\39_constant_evaluation.md | L4 | 缺失认知路径; 缺失反命题 |
| concept\04_formal\40_names_and_resolution.md | L4 | 缺失认知路径; 缺失反命题 |
| concept\04_formal\41_special_types_and_traits.md | L4 | 缺失认知路径; 缺失反命题 |
| concept\04_formal\42_type_layout.md | L4 | 缺失认知路径; 缺失反命题 |
| concept\04_formal\43_destructors.md | L4 | 缺失认知路径; 缺失反命题 |
| concept\04_formal\44_notation.md | L4 | 缺失认知路径; 缺失反命题 |
| concept\04_formal\45_lexical_structure.md | L4 | 缺失认知路径; 缺失反命题 |
| concept\04_formal\46_items_reference.md | L4 | 缺失认知路径; 缺失反命题 |
| concept\04_formal\47_attributes.md | L4 | 缺失认知路径; 缺失反命题 |
| concept\04_formal\48_statements_and_expressions_reference.md | L4 | 缺失认知路径; 缺失反命题 |
| concept\04_formal\49_patterns_reference.md | L4 | 缺失认知路径; 缺失反命题 |
| concept\04_formal\50_type_system_reference.md | L4 | 缺失认知路径; 缺失反命题 |
| concept\04_formal\51_names_reference.md | L4 | 缺失认知路径; 缺失反命题 |
| concept\04_formal\52_reference_appendices.md | L4 | 缺失认知路径; 缺失反命题 |
| concept\05_comparative\05_execution_model_isomorphism.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\05_comparative\06_rust_vs_java.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\05_comparative\07_rust_vs_python.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\05_comparative\08_rust_vs_javascript.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\05_comparative\09_rust_vs_swift.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\05_comparative\10_rust_vs_zig.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\05_comparative\11_rust_vs_kotlin.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\05_comparative\12_rust_vs_scala.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\05_comparative\13_rust_vs_csharp.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\05_comparative\14_rust_vs_elixir.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\05_comparative\15_rust_vs_typescript.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\05_comparative\16_cpp_rust_surface_features.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\05_comparative\17_quiz_rust_vs_systems.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\05_comparative\18_cpp_abi_object_model.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\05_comparative\19_rust_vs_ruby.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\06_ecosystem\09_cargo_script.md | L6 | 过渡段落不足 (2 < 3); 定理链不足 (1 < 3) |
| concept\06_ecosystem\14_documentation.md | L6 | 过渡段落不足 (2 < 3); 定理链不足 (1 < 3) |
| concept\06_ecosystem\16_testing.md | L6 | 过渡段落不足 (2 < 3); 定理链不足 (1 < 3) |
| concept\06_ecosystem\17_cross_compilation.md | L6 | 过渡段落不足 (2 < 3) |
| concept\06_ecosystem\22_embedded_systems.md | L6 | 过渡段落不足 (2 < 3) |
| concept\06_ecosystem\32_event_driven_architecture.md | L6 | 过渡段落不足 (2 < 3) |
| concept\06_ecosystem\47_compiler_infrastructure.md | L6 | 过渡段落不足 (2 < 3); 定理链不足 (1 < 3) |
| concept\06_ecosystem\51_quantum_computing_rust.md | L6 | 定理链不足 (1 < 3) |
| concept\06_ecosystem\57_quiz_toolchain.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\06_ecosystem\58_platform_rust_integration.md | L6 | 过渡段落不足 (2 < 3); 定理链不足 (0 < 3) |
| concept\06_ecosystem\59_cargo_build_scripts.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\06_ecosystem\60_cargo_dependency_resolution.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\06_ecosystem\61_cargo_source_replacement.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\06_ecosystem\62_cargo_registries_and_publishing.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\06_ecosystem\63_cargo_authentication_and_cache.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\06_ecosystem\64_cargo_manifest_reference.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\06_ecosystem\65_cargo_profiles_and_lints.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\06_ecosystem\66_cargo_subcommands_and_plugins.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\06_ecosystem\67_llvm_backend_and_codegen.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\06_ecosystem\68_rustc_driver_and_stable_mir.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\06_ecosystem\69_compiler_diagnostics_and_ui_tests.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\06_ecosystem\70_rustc_bootstrap.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\06_ecosystem\71_compiler_testing.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\06_ecosystem\72_cargo_security_cves.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\06_ecosystem\76_cargo_196_features.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\06_ecosystem\77_rustdoc_196_changes.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\06_ecosystem\78_cargo_workspaces.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\07_future\01_ai_integration.md | L7 | 过渡段落不足 (2 < 3); 定理链不足 (2 < 3) |
| concept\07_future\05_rust_version_tracking.md | L7 | 过渡段落不足 (2 < 3) |
| concept\07_future\07_mcdc_coverage_preview.md | L7 | 过渡段落不足 (2 < 3); 定理链不足 (1 < 3) |
| concept\07_future\08_safety_tags_preview.md | L7 | 过渡段落不足 (2 < 3); 定理链不足 (1 < 3) |
| concept\07_future\09_parallel_frontend_preview.md | L7 | 过渡段落不足 (2 < 3) |
| concept\07_future\10_derive_coerce_pointee_preview.md | L7 | 过渡段落不足 (2 < 3); 定理链不足 (1 < 3) |
| concept\07_future\11_const_trait_impl_preview.md | L7 | 过渡段落不足 (2 < 3) |
| concept\07_future\12_return_type_notation_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\07_future\15_pin_ergonomics_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\07_future\18_async_drop_preview.md | L7 | 过渡段落不足 (2 < 3) |
| concept\07_future\20_borrowsanitizer_preview.md | L7 | 过渡段落不足 (2 < 3); 定理链不足 (1 < 3) |
| concept\07_future\24_roadmap.md | L7 | 过渡段落不足 (2 < 3) |
| concept\07_future\25_open_enums_preview.md | L7 | 过渡段落不足 (2 < 3); 定理链不足 (1 < 3) |
| concept\07_future\26_specialization_preview.md | L7 | 定理链不足 (1 < 3) |
| concept\07_future\27_compile_time_execution.md | L7 | 过渡段落不足 (2 < 3); 定理链不足 (1 < 3) |
| concept\07_future\28_rust_for_webassembly.md | L7 | 过渡段落不足 (2 < 3); 定理链不足 (1 < 3) |
| concept\07_future\29_ebpf_rust.md | L7 | 过渡段落不足 (2 < 3) |
| concept\07_future\35_ferrocene_preview.md | L7 | 过渡段落不足 (2 < 3) |
| concept\07_future\38_cranelift_backend_preview.md | L7 | 过渡段落不足 (2 < 3) |
| concept\07_future\40_ergonomic_ref_counting_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\07_future\41_rust_specification_preview.md | L7 | 过渡段落不足 (2 < 3) |
| concept\07_future\42_field_projections_preview.md | L7 | 过渡段落不足 (2 < 3); 定理链不足 (1 < 3) |
| concept\07_future\43_rust_for_linux.md | L7 | 过渡段落不足 (2 < 3); 定理链不足 (1 < 3) |
| concept\07_future\44_edition_guide.md | L7 | 过渡段落不足 (2 < 3); 定理链不足 (1 < 3) |
| concept\07_future\46_cargo_semver_checks_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\07_future\48_aarch64_sve_sme_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\07_future\borrow_sanitizer.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\07_future\rust_1_95_stabilized.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\07_future\rust_1_96_stabilized.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\07_future\rust_1_97_preview.md | L7 | 过渡段落不足 (2 < 3); 定理链不足 (0 < 3) |
| concept\07_future\rust_1_97_stabilized.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\07_future\rust_1_98_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |

## 文件详细统计

| 文件 | 层级 | 行数 | ⟹ | ⟸ | 模板 | 反命题 | Mermaid | 代码块 | 过渡段 | 认知路径 | 前置 | 后置 | 受众 | 分级 |
|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|
| concept\00_meta\03_bloom_taxonomy.md | L0 | 178 | 1 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| concept\00_meta\05_cross_reference_matrix.md | L0 | 11 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| concept\00_meta\08_concept_audit_guide.md | L0 | 80 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| concept\00_meta\asp_marking_guide.md | L0 | 522 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| concept\00_meta\audit_checklist.md | L0 | 442 | 1 | 0 | 0 | 2 | 1 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| concept\00_meta\authority_source_map.md | L0 | 188 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| concept\00_meta\bilingual_template.md | L0 | 164 | 0 | 0 | 0 | 1 | 1 | 1 | 0 | ❌ | ✅ | ✅ | 初学者 | 进阶 | 研究者 | None |
| concept\00_meta\boundary_extension_tree.md | L0 | 350 | 1 | 0 | 0 | 1 | 3 | 1 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| concept\00_meta\career_landscape.md | L0 | 231 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 入门 → 进阶 | None |
| concept\00_meta\cognitive_dimension_matrix.md | L0 | 394 | 1 | 0 | 0 | 1 | 2 | 0 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| concept\00_meta\competency_graph.md | L0 | 408 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| concept\00_meta\comprehensive_rust_mapping.md | L0 | 231 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 → 进阶 | 元层 |
| concept\00_meta\concept_consistency_audit_checklist.md | L0 | 9 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | 专家级 |
| concept\00_meta\concept_definition_decision_forest.md | L0 | 1117 | 3 | 0 | 0 | 1 | 10 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| concept\00_meta\concept_index.md | L0 | 785 | 4 | 0 | 0 | 2 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| concept\00_meta\cpp_rust_engineering_roadmap.md | L0 | 140 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | None |
| concept\00_meta\decidability_spectrum.md | L0 | 886 | 1 | 0 | 0 | 1 | 6 | 2 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| concept\00_meta\expressiveness_multiview.md | L0 | 769 | 0 | 0 | 0 | 1 | 7 | 7 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| concept\00_meta\fault_tree_analysis_collection.md | L0 | 769 | 1 | 0 | 0 | 1 | 7 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| concept\00_meta\foundations_gap_closure_index.md | L0 | 135 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | None |
| concept\00_meta\grading_system.md | L0 | 142 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 初学者 | 综述级 |
| concept\00_meta\inter_layer_map.md | L0 | 626 | 12 | 0 | 0 | 1 | 2 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| concept\00_meta\inter_layer_topology.md | L0 | 13 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ✅ | ❌ | ❌ | None | 专家级 |
| concept\00_meta\intra_layer_model_map.md | L0 | 335 | 11 | 0 | 0 | 1 | 5 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| concept\00_meta\kg_ontology_v2.md | L0 | 319 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | None |
| concept\00_meta\kg_tlo_alignment.md | L0 | 238 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| concept\00_meta\knowledge_mindmap.md | L0 | 296 | 1 | 0 | 0 | 1 | 2 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| concept\00_meta\knowledge_topology\01_concept_definition_atlas.md | L0 | 473 | 1 | 1 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| concept\00_meta\knowledge_topology\02_attribute_relationship_atlas.md | L0 | 450 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| concept\00_meta\knowledge_topology\03_scenario_decision_tree_atlas.md | L0 | 25 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| concept\00_meta\knowledge_topology\04_example_counterexample_atlas.md | L0 | 25 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| concept\00_meta\knowledge_topology\05_logical_reasoning_atlas.md | L0 | 25 | 1 | 1 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| concept\00_meta\knowledge_topology\06_inter_layer_mapping_atlas.md | L0 | 98 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| concept\00_meta\knowledge_topology\07_intra_layer_mapping_atlas.md | L0 | 314 | 244 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| concept\00_meta\knowledge_topology\08_concept_source_alignment_atlas.md | L0 | 50 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| concept\00_meta\knowledge_topology\09_reasoning_judgment_tree_atlas.md | L0 | 25 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| concept\00_meta\knowledge_topology\10_gap_and_action_plan.md | L0 | 82 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| concept\00_meta\learning_guide.md | L0 | 659 | 3 | 0 | 0 | 1 | 1 | 1 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| concept\00_meta\learning_mvp_path.md | L0 | 366 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ✅ | ❌ | 初学者 | 综述级 |
| concept\00_meta\learning_mvp_path_en.md | L0 | 266 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| concept\00_meta\methodology.md | L0 | 530 | 1 | 0 | 0 | 2 | 5 | 1 | 6 | ✅ | ✅ | ✅ | 研究者 | 综述级 |
| concept\00_meta\navigation.md | L0 | 289 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| concept\00_meta\paradigm_transition_matrix.md | L0 | 310 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| concept\00_meta\pattern_semantic_space_index.md | L0 | 134 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | None |
| concept\00_meta\pl_foundations_roadmap.md | L0 | 129 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 | None |
| concept\00_meta\placeholders\placeholder_generic.md | L0 | 22 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| concept\00_meta\problem_graph.md | L0 | 509 | 1 | 0 | 0 | 1 | 7 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| concept\00_meta\quality_dashboard_v2.md | L0 | 324 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| concept\00_meta\quick_reference.md | L0 | 817 | 1 | 0 | 0 | 1 | 0 | 25 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| concept\00_meta\rustbelt_predicate_map.md | L0 | 412 | 9 | 0 | 0 | 1 | 6 | 0 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| concept\00_meta\self_assessment.md | L0 | 2219 | 0 | 0 | 0 | 1 | 0 | 55 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| concept\00_meta\semantic_bridge_algorithms_patterns.md | L0 | 702 | 1 | 0 | 0 | 1 | 0 | 7 | 6 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| concept\00_meta\semantic_expressiveness.md | L0 | 1127 | 1 | 0 | 0 | 1 | 2 | 1 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| concept\00_meta\semantic_space.md | L0 | 1325 | 10 | 0 | 0 | 2 | 5 | 9 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| concept\00_meta\sources.md | L0 | 488 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 研究者级 |
| concept\00_meta\template_deduplication_guide.md | L0 | 75 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 贡献者 | None |
| concept\00_meta\terminology_glossary.md | L0 | 463 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| concept\00_meta\theorem_inference_forest.md | L0 | 510 | 3 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| concept\00_meta\todos.md | L0 | 324 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| concept\00_meta\topic_authority_alignment_map.md | L0 | 12 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| concept\01_foundation\00_start.md | L1 | 117 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 | 初学者 |
| concept\01_foundation\01_ownership.md | L1 | 1810 | 12 | 2 | 0 | 3 | 7 | 43 | 16 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\02_borrowing.md | L1 | 1944 | 4 | 2 | 0 | 3 | 6 | 49 | 20 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\03_lifetimes.md | L1 | 1435 | 19 | 2 | 0 | 3 | 5 | 40 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\04_type_system.md | L1 | 2837 | 18 | 2 | 0 | 3 | 12 | 54 | 16 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\05_reference_semantics.md | L1 | 1417 | 0 | 0 | 0 | 3 | 7 | 35 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\06_zero_cost_abstractions.md | L1 | 813 | 0 | 0 | 0 | 2 | 2 | 14 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\07_control_flow.md | L1 | 1552 | 0 | 0 | 0 | 2 | 5 | 25 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\08_collections.md | L1 | 842 | 0 | 0 | 0 | 2 | 2 | 16 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\09_strings_and_text.md | L1 | 821 | 0 | 0 | 0 | 2 | 1 | 17 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\10_numerics.md | L1 | 990 | 0 | 0 | 0 | 2 | 1 | 16 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\11_modules_and_paths.md | L1 | 865 | 0 | 0 | 0 | 2 | 1 | 11 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\12_attributes_and_macros.md | L1 | 890 | 0 | 0 | 0 | 2 | 1 | 14 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\13_panic_and_abort.md | L1 | 916 | 0 | 0 | 0 | 2 | 1 | 12 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\14_coercion_and_casting.md | L1 | 892 | 0 | 0 | 0 | 2 | 1 | 15 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\15_closure_basics.md | L1 | 864 | 0 | 0 | 0 | 2 | 1 | 18 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\16_testing_basics.md | L1 | 719 | 0 | 0 | 0 | 2 | 1 | 8 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\17_collections_advanced.md | L1 | 974 | 0 | 0 | 0 | 2 | 2 | 11 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\18_strings_and_encoding.md | L1 | 808 | 0 | 0 | 0 | 2 | 2 | 9 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\19_value_vs_reference_semantics.md | L1 | 172 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\20_variable_model.md | L1 | 587 | 0 | 0 | 0 | 2 | 0 | 12 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\21_effects_and_purity.md | L1 | 671 | 0 | 0 | 0 | 2 | 0 | 17 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\22_data_abstraction_spectrum.md | L1 | 727 | 0 | 0 | 0 | 2 | 0 | 14 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\23_move_semantics.md | L1 | 235 | 0 | 0 | 0 | 0 | 0 | 4 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\24_quiz_type_system.md | L1 | 495 | 0 | 0 | 0 | 0 | 0 | 14 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\25_quiz_error_handling.md | L1 | 608 | 0 | 0 | 0 | 0 | 0 | 18 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\26_quiz_modules_testing.md | L1 | 697 | 0 | 0 | 0 | 0 | 0 | 22 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\27_quiz_closures_iterators.md | L1 | 683 | 0 | 0 | 0 | 0 | 0 | 33 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\28_ownership_inventories_brown_book.md | L1 | 181 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\29_quiz_pl_foundations.md | L1 | 145 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\30_lifetimes_advanced.md | L1 | 1501 | 3 | 2 | 0 | 1 | 0 | 43 | 10 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\31_never_type.md | L1 | 531 | 0 | 0 | 0 | 0 | 0 | 15 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\32_error_handling_basics.md | L1 | 952 | 0 | 0 | 0 | 2 | 1 | 15 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\33_quiz_ownership_borrowing.md | L1 | 482 | 0 | 0 | 0 | 0 | 0 | 17 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\34_pl_prerequisites.md | L1 | 477 | 0 | 0 | 0 | 0 | 0 | 12 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\35_preludes.md | L1 | 179 | 0 | 0 | 0 | 0 | 0 | 4 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\36_keywords.md | L1 | 137 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\37_operators_and_symbols.md | L1 | 214 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\38_crates_and_source_files.md | L1 | 127 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\39_items.md | L1 | 100 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\40_patterns.md | L1 | 215 | 0 | 0 | 0 | 0 | 0 | 10 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\41_statements_and_expressions.md | L1 | 144 | 0 | 0 | 0 | 0 | 0 | 4 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\42_useful_development_tools.md | L1 | 67 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 | 参考级 |
| concept\02_intermediate\01_traits.md | L2 | 2562 | 15 | 2 | 0 | 7 | 5 | 63 | 10 | ✅ | ✅ | ✅ | 进阶 | None |
| concept\02_intermediate\02_generics.md | L2 | 2680 | 16 | 2 | 0 | 7 | 6 | 64 | 8 | ✅ | ✅ | ✅ | 进阶 | None |
| concept\02_intermediate\03_memory_management.md | L2 | 2039 | 13 | 3 | 0 | 7 | 5 | 50 | 7 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\04_error_handling.md | L2 | 2530 | 9 | 3 | 0 | 7 | 8 | 53 | 7 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\05_assert_matches.md | L2 | 660 | 0 | 1 | 0 | 2 | 3 | 18 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\06_range_types.md | L2 | 605 | 0 | 1 | 0 | 2 | 2 | 12 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\07_closure_types.md | L2 | 725 | 0 | 1 | 0 | 2 | 3 | 15 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\08_interior_mutability.md | L2 | 814 | 0 | 1 | 0 | 2 | 2 | 11 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\09_serde_patterns.md | L2 | 879 | 0 | 1 | 0 | 2 | 2 | 9 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\10_module_system.md | L2 | 800 | 0 | 1 | 0 | 2 | 3 | 15 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\11_cow_and_borrowed.md | L2 | 739 | 0 | 1 | 0 | 2 | 2 | 8 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\12_smart_pointers.md | L2 | 841 | 0 | 1 | 0 | 2 | 2 | 12 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\13_dsl_and_embedding.md | L2 | 770 | 0 | 1 | 0 | 2 | 1 | 11 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\14_newtype_and_wrapper.md | L2 | 743 | 0 | 1 | 0 | 2 | 1 | 10 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\15_iterator_patterns.md | L2 | 1247 | 1 | 0 | 0 | 1 | 1 | 19 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\16_error_handling_deep_dive.md | L2 | 748 | 0 | 1 | 0 | 2 | 1 | 9 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\17_macro_patterns.md | L2 | 791 | 0 | 1 | 0 | 2 | 1 | 9 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\18_lifetimes_advanced.md | L2 | 876 | 0 | 1 | 0 | 2 | 1 | 13 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\19_advanced_traits.md | L2 | 844 | 0 | 1 | 0 | 2 | 1 | 17 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\20_type_system_advanced.md | L2 | 952 | 0 | 1 | 0 | 2 | 1 | 17 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\21_metaprogramming.md | L2 | 789 | 0 | 1 | 0 | 2 | 2 | 8 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\22_api_naming_conventions.md | L2 | 400 | 0 | 0 | 0 | 0 | 0 | 15 | 2 | ❌ | ✅ | ✅ | 进阶 | 中级 |
| concept\02_intermediate\23_quiz_traits_and_generics.md | L2 | 660 | 0 | 0 | 0 | 0 | 0 | 19 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\24_quiz_memory_management.md | L2 | 699 | 0 | 0 | 0 | 0 | 0 | 26 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\25_rtti_and_dynamic_typing.md | L2 | 215 | 0 | 0 | 0 | 0 | 0 | 5 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| concept\02_intermediate\26_c_preprocessor_vs_rust_macros.md | L2 | 208 | 0 | 0 | 0 | 0 | 0 | 4 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| concept\02_intermediate\27_exception_safety_rust_cpp.md | L2 | 213 | 2 | 0 | 0 | 0 | 0 | 4 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| concept\02_intermediate\28_construction_and_initialization.md | L2 | 224 | 0 | 0 | 0 | 0 | 0 | 5 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| concept\02_intermediate\29_friend_vs_module_privacy.md | L2 | 207 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| concept\02_intermediate\30_quiz_cpp_rust_foundations.md | L2 | 188 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| concept\02_intermediate\31_derive_traits.md | L2 | 224 | 0 | 0 | 0 | 0 | 0 | 10 | 0 | ❌ | ✅ | ✅ | 初学者 | 参考级 |
| concept\02_intermediate\32_editions.md | L2 | 67 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| concept\02_intermediate\33_rust_release_process.md | L2 | 71 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| concept\03_advanced\00_before_formal.md | L3 | 149 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\03_advanced\01_concurrency.md | L3 | 1610 | 21 | 2 | 0 | 3 | 10 | 23 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\02_async.md | L3 | 3126 | 17 | 3 | 0 | 6 | 9 | 56 | 3 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\03_unsafe.md | L3 | 3427 | 14 | 2 | 0 | 4 | 10 | 63 | 3 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\04_macros.md | L3 | 2477 | 22 | 3 | 0 | 8 | 8 | 59 | 8 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\05_rust_ffi.md | L3 | 853 | 0 | 1 | 0 | 2 | 3 | 16 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\06_pin_unpin.md | L3 | 853 | 0 | 1 | 0 | 2 | 2 | 19 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\07_proc_macro.md | L3 | 873 | 0 | 1 | 0 | 2 | 2 | 10 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\08_nll_and_polonius.md | L3 | 805 | 0 | 1 | 0 | 2 | 1 | 11 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\09_ffi_advanced.md | L3 | 894 | 0 | 1 | 0 | 2 | 1 | 12 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\10_concurrency_patterns.md | L3 | 1113 | 0 | 1 | 0 | 2 | 1 | 22 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\11_atomics_and_memory_ordering.md | L3 | 1186 | 0 | 1 | 0 | 2 | 2 | 21 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\12_unsafe_rust_patterns.md | L3 | 21 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\13_inline_assembly.md | L3 | 767 | 0 | 0 | 0 | 0 | 0 | 25 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\14_custom_allocators.md | L3 | 838 | 0 | 1 | 0 | 2 | 1 | 12 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\15_zero_copy_parsing.md | L3 | 881 | 0 | 1 | 0 | 2 | 1 | 13 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\16_lock_free.md | L3 | 1163 | 0 | 1 | 0 | 2 | 1 | 20 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\17_type_erasure.md | L3 | 850 | 0 | 1 | 0 | 2 | 1 | 11 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\18_network_programming.md | L3 | 950 | 0 | 1 | 0 | 2 | 2 | 11 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\19_parallel_distributed_pattern_spectrum.md | L3 | 871 | 0 | 1 | 0 | 2 | 0 | 17 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\20_stream_processing_semantics.md | L3 | 820 | 0 | 1 | 0 | 1 | 0 | 8 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\21_quiz_concurrency_async.md | L3 | 696 | 0 | 0 | 0 | 0 | 0 | 19 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\22_quiz_unsafe.md | L3 | 602 | 0 | 0 | 0 | 0 | 0 | 21 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\23_quiz_macros.md | L3 | 662 | 0 | 0 | 0 | 0 | 0 | 23 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\24_async_closures.md | L3 | 554 | 3 | 0 | 0 | 1 | 0 | 20 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\25_async_advanced.md | L3 | 1645 | 1 | 1 | 0 | 0 | 1 | 40 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\26_async_patterns.md | L3 | 1116 | 0 | 1 | 0 | 2 | 1 | 20 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\27_linkage.md | L3 | 243 | 0 | 0 | 0 | 0 | 0 | 10 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| concept\03_advanced\28_conditional_compilation.md | L3 | 231 | 0 | 0 | 0 | 0 | 0 | 8 | 0 | ❌ | ✅ | ✅ | 中级 | 专家级 |
| concept\03_advanced\29_memory_model.md | L3 | 86 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\30_rust_runtime.md | L3 | 117 | 0 | 0 | 0 | 0 | 0 | 2 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\31_panic.md | L3 | 141 | 0 | 0 | 0 | 0 | 0 | 2 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\32_memory_allocation_and_lifetime.md | L3 | 74 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\33_variables.md | L3 | 106 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\34_visibility_and_privacy.md | L3 | 126 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\35_unsafe_reference.md | L3 | 76 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| concept\04_formal\01_linear_logic.md | L4 | 1240 | 14 | 0 | 0 | 4 | 5 | 13 | 3 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\02_type_theory.md | L4 | 1481 | 27 | 0 | 0 | 4 | 5 | 27 | 3 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\03_ownership_formal.md | L4 | 1640 | 11 | 0 | 0 | 1 | 5 | 17 | 3 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\04_rustbelt.md | L4 | 1423 | 5 | 0 | 0 | 1 | 5 | 16 | 10 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\05_verification_toolchain.md | L4 | 1515 | 0 | 0 | 0 | 0 | 4 | 17 | 0 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\06_subtype_variance.md | L4 | 615 | 0 | 0 | 0 | 2 | 2 | 10 | 0 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\08_type_inference.md | L4 | 720 | 3 | 0 | 0 | 3 | 2 | 8 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\09_linear_logic_applications.md | L4 | 724 | 0 | 0 | 0 | 2 | 1 | 10 | 0 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\10_category_theory.md | L4 | 789 | 0 | 0 | 0 | 2 | 1 | 11 | 0 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\11_separation_logic.md | L4 | 818 | 0 | 0 | 0 | 2 | 1 | 10 | 0 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\12_denotational_semantics.md | L4 | 615 | 0 | 0 | 0 | 2 | 1 | 7 | 0 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\13_formal_methods.md | L4 | 723 | 0 | 0 | 0 | 2 | 1 | 7 | 0 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\14_lambda_calculus.md | L4 | 733 | 0 | 0 | 0 | 2 | 1 | 11 | 0 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\15_hoare_logic.md | L4 | 888 | 0 | 0 | 0 | 2 | 2 | 8 | 0 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\16_aerospace_certification_formal_methods.md | L4 | 1069 | 0 | 0 | 0 | 0 | 1 | 5 | 0 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\17_operational_semantics.md | L4 | 1056 | 0 | 0 | 0 | 2 | 1 | 13 | 0 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\18_evaluation_strategies.md | L4 | 614 | 0 | 0 | 0 | 2 | 0 | 14 | 0 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\19_rustc_query_system.md | L4 | 373 | 0 | 0 | 0 | 0 | 2 | 1 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| concept\04_formal\20_axiomatic_semantics.md | L4 | 897 | 3 | 0 | 0 | 3 | 0 | 13 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\21_type_semantics.md | L4 | 849 | 3 | 0 | 0 | 3 | 0 | 18 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\22_modern_verification_tools.md | L4 | 494 | 0 | 0 | 0 | 0 | 0 | 8 | 0 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\23_programming_language_foundations.md | L4 | 370 | 0 | 0 | 0 | 0 | 0 | 10 | 0 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\24_autoverus.md | L4 | 171 | 0 | 0 | 0 | 1 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| concept\04_formal\25_quiz_formal_methods.md | L4 | 578 | 0 | 0 | 0 | 0 | 0 | 10 | 0 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\26_trait_solver_in_rustc.md | L4 | 271 | 0 | 0 | 0 | 0 | 1 | 5 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| concept\04_formal\27_type_checking_and_inference.md | L4 | 270 | 0 | 0 | 0 | 0 | 0 | 7 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| concept\04_formal\28_borrow_checking_decidability.md | L4 | 385 | 1 | 0 | 0 | 0 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\29_type_inference_complexity.md | L4 | 380 | 0 | 0 | 0 | 0 | 0 | 6 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\30_aeneas_symbolic_semantics.md | L4 | 416 | 0 | 0 | 0 | 0 | 1 | 4 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\31_miri.md | L4 | 272 | 0 | 0 | 0 | 2 | 1 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 / 工程 / 形式化 | 综述级 |
| concept\04_formal\32_kani.md | L4 | 330 | 0 | 0 | 0 | 0 | 0 | 9 | 0 | ❌ | ✅ | ✅ | 进阶 / 工程 / 形式化 | 综述级 |
| concept\04_formal\33_safety_tags_in_formal.md | L4 | 155 | 0 | 0 | 0 | 1 | 0 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| concept\04_formal\34_borrow_sanitizer_in_formal.md | L4 | 155 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| concept\04_formal\35_name_resolution_and_hir.md | L4 | 302 | 0 | 0 | 0 | 2 | 1 | 5 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| concept\04_formal\36_tree_borrows_deep_dive.md | L4 | 146 | 0 | 0 | 0 | 1 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| concept\04_formal\37_behavior_considered_undefined.md | L4 | 142 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 专家 | 研究级 |
| concept\04_formal\38_application_binary_interface.md | L4 | 144 | 0 | 0 | 0 | 0 | 0 | 4 | 0 | ❌ | ✅ | ✅ | 专家 | 研究级 |
| concept\04_formal\39_constant_evaluation.md | L4 | 120 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| concept\04_formal\40_names_and_resolution.md | L4 | 119 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| concept\04_formal\41_special_types_and_traits.md | L4 | 163 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| concept\04_formal\42_type_layout.md | L4 | 139 | 0 | 0 | 0 | 0 | 0 | 4 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| concept\04_formal\43_destructors.md | L4 | 157 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| concept\04_formal\44_notation.md | L4 | 93 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| concept\04_formal\45_lexical_structure.md | L4 | 93 | 0 | 0 | 0 | 0 | 0 | 2 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| concept\04_formal\46_items_reference.md | L4 | 93 | 0 | 0 | 0 | 0 | 0 | 2 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| concept\04_formal\47_attributes.md | L4 | 83 | 0 | 0 | 0 | 0 | 0 | 4 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| concept\04_formal\48_statements_and_expressions_reference.md | L4 | 83 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| concept\04_formal\49_patterns_reference.md | L4 | 79 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| concept\04_formal\50_type_system_reference.md | L4 | 102 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| concept\04_formal\51_names_reference.md | L4 | 82 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| concept\04_formal\52_reference_appendices.md | L4 | 83 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| concept\05_comparative\01_rust_vs_cpp.md | L5 | 2127 | 9 | 0 | 0 | 2 | 10 | 12 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\05_comparative\02_rust_vs_go.md | L5 | 975 | 3 | 0 | 0 | 3 | 6 | 11 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\03_paradigm_matrix.md | L5 | 957 | 6 | 0 | 0 | 5 | 8 | 7 | 16 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\04_safety_boundaries.md | L5 | 1004 | 8 | 0 | 0 | 1 | 7 | 9 | 9 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\05_comparative\05_execution_model_isomorphism.md | L5 | 974 | 0 | 0 | 0 | 0 | 5 | 13 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| concept\05_comparative\06_rust_vs_java.md | L5 | 588 | 0 | 0 | 0 | 2 | 3 | 7 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\07_rust_vs_python.md | L5 | 666 | 0 | 0 | 0 | 2 | 2 | 6 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\08_rust_vs_javascript.md | L5 | 664 | 0 | 0 | 0 | 2 | 2 | 5 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\09_rust_vs_swift.md | L5 | 705 | 0 | 0 | 0 | 2 | 1 | 6 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\10_rust_vs_zig.md | L5 | 744 | 0 | 0 | 0 | 2 | 1 | 8 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\11_rust_vs_kotlin.md | L5 | 785 | 0 | 0 | 0 | 2 | 1 | 6 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\12_rust_vs_scala.md | L5 | 746 | 0 | 0 | 0 | 2 | 1 | 6 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\13_rust_vs_csharp.md | L5 | 802 | 0 | 0 | 0 | 2 | 1 | 6 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\14_rust_vs_elixir.md | L5 | 797 | 0 | 0 | 0 | 2 | 1 | 6 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\15_rust_vs_typescript.md | L5 | 897 | 0 | 0 | 0 | 2 | 2 | 6 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\16_cpp_rust_surface_features.md | L5 | 201 | 0 | 0 | 0 | 0 | 0 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 | 研究级 |
| concept\05_comparative\17_quiz_rust_vs_systems.md | L5 | 697 | 0 | 0 | 0 | 0 | 0 | 14 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\18_cpp_abi_object_model.md | L5 | 766 | 0 | 0 | 0 | 2 | 0 | 17 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| concept\05_comparative\19_rust_vs_ruby.md | L5 | 713 | 0 | 0 | 0 | 2 | 1 | 8 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\01_toolchain.md | L6 | 1868 | 10 | 0 | 0 | 1 | 9 | 15 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\02_patterns.md | L6 | 1851 | 8 | 0 | 0 | 1 | 5 | 34 | 8 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\03_core_crates.md | L6 | 1342 | 8 | 0 | 0 | 2 | 6 | 17 | 3 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\04_application_domains.md | L6 | 1526 | 8 | 0 | 0 | 2 | 6 | 12 | 3 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\05_system_design_principles.md | L6 | 722 | 3 | 0 | 0 | 0 | 6 | 8 | 6 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\06_blockchain.md | L6 | 919 | 5 | 0 | 0 | 0 | 3 | 14 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\07_game_ecs.md | L6 | 1363 | 3 | 0 | 0 | 0 | 7 | 23 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\08_wasi.md | L6 | 632 | 3 | 0 | 0 | 4 | 2 | 11 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\09_cargo_script.md | L6 | 676 | 1 | 0 | 0 | 0 | 2 | 10 | 2 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\10_public_private_deps.md | L6 | 611 | 3 | 0 | 0 | 0 | 2 | 11 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\11_webassembly.md | L6 | 621 | 3 | 0 | 0 | 2 | 3 | 8 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\12_testing_strategies.md | L6 | 681 | 3 | 0 | 0 | 2 | 2 | 9 | 6 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\13_logging_observability.md | L6 | 660 | 3 | 0 | 0 | 2 | 3 | 9 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\14_documentation.md | L6 | 655 | 1 | 0 | 0 | 2 | 2 | 7 | 2 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\15_performance_optimization.md | L6 | 727 | 3 | 0 | 0 | 2 | 1 | 10 | 6 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\16_testing.md | L6 | 717 | 1 | 0 | 0 | 2 | 2 | 8 | 2 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\17_cross_compilation.md | L6 | 651 | 3 | 0 | 0 | 2 | 1 | 5 | 2 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\18_distributed_systems.md | L6 | 751 | 3 | 0 | 0 | 2 | 1 | 8 | 6 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\19_security_practices.md | L6 | 1070 | 3 | 0 | 0 | 2 | 1 | 8 | 6 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\20_licensing_and_compliance.md | L6 | 681 | 3 | 0 | 0 | 2 | 1 | 6 | 6 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\21_game_development.md | L6 | 678 | 3 | 0 | 0 | 2 | 1 | 8 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\22_embedded_systems.md | L6 | 930 | 3 | 0 | 0 | 2 | 1 | 10 | 2 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\23_database_access.md | L6 | 799 | 3 | 0 | 0 | 2 | 1 | 8 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\24_cloud_native.md | L6 | 732 | 3 | 0 | 0 | 2 | 1 | 8 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\25_cli_development.md | L6 | 768 | 3 | 0 | 0 | 2 | 1 | 9 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\26_game_development.md | L6 | 701 | 3 | 0 | 0 | 2 | 1 | 7 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\27_web_frameworks.md | L6 | 984 | 3 | 0 | 0 | 3 | 3 | 11 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\28_devops_and_ci_cd.md | L6 | 854 | 3 | 0 | 0 | 2 | 2 | 7 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\29_algorithms_competitive_programming.md | L6 | 1033 | 3 | 0 | 0 | 0 | 0 | 26 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\30_system_composability.md | L6 | 802 | 3 | 0 | 0 | 0 | 4 | 23 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\31_microservice_patterns.md | L6 | 952 | 3 | 0 | 0 | 1 | 6 | 15 | 6 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\32_event_driven_architecture.md | L6 | 1030 | 3 | 0 | 0 | 1 | 4 | 15 | 2 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\33_cqrs_event_sourcing.md | L6 | 1441 | 3 | 0 | 0 | 2 | 1 | 18 | 6 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\34_idioms_spectrum.md | L6 | 1373 | 3 | 0 | 0 | 0 | 5 | 35 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\35_architecture_patterns.md | L6 | 1186 | 3 | 0 | 0 | 2 | 0 | 13 | 6 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\36_stream_processing_ecosystem.md | L6 | 549 | 3 | 0 | 0 | 0 | 0 | 10 | 6 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\37_database_systems.md | L6 | 523 | 3 | 0 | 0 | 0 | 0 | 9 | 6 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\38_network_protocols.md | L6 | 399 | 3 | 0 | 0 | 0 | 0 | 7 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\39_os_kernel.md | L6 | 394 | 3 | 0 | 0 | 0 | 0 | 7 | 6 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| concept\06_ecosystem\40_reactive_programming.md | L6 | 1059 | 3 | 0 | 0 | 2 | 0 | 14 | 6 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\41_workflow_theory.md | L6 | 1370 | 3 | 0 | 0 | 2 | 0 | 17 | 6 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\42_api_design_patterns.md | L6 | 1277 | 3 | 0 | 0 | 2 | 0 | 19 | 6 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\43_security_cryptography.md | L6 | 907 | 3 | 0 | 0 | 2 | 0 | 16 | 6 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\44_formal_ecosystem_tower.md | L6 | 600 | 3 | 0 | 0 | 0 | 2 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\45_compiler_internals.md | L6 | 821 | 3 | 0 | 0 | 2 | 0 | 7 | 6 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| concept\06_ecosystem\46_machine_learning_ecosystem.md | L6 | 923 | 3 | 0 | 0 | 2 | 0 | 14 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\47_compiler_infrastructure.md | L6 | 348 | 1 | 0 | 0 | 1 | 0 | 1 | 2 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| concept\06_ecosystem\48_data_engineering.md | L6 | 919 | 3 | 0 | 0 | 2 | 0 | 12 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\49_game_engine_internals.md | L6 | 1112 | 3 | 0 | 0 | 2 | 0 | 13 | 6 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\50_distributed_consensus.md | L6 | 804 | 3 | 0 | 0 | 2 | 0 | 6 | 6 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\51_quantum_computing_rust.md | L6 | 886 | 1 | 0 | 0 | 2 | 0 | 9 | 6 | ❌ | ✅ | ✅ | 研究者 | 实验级 |
| concept\06_ecosystem\52_robotics.md | L6 | 978 | 3 | 0 | 0 | 2 | 0 | 15 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\53_embedded_graphics.md | L6 | 1024 | 3 | 0 | 0 | 2 | 1 | 3 | 6 | ❌ | ✅ | ✅ | 研究者 | 综述级 |
| concept\06_ecosystem\54_webassembly_advanced.md | L6 | 856 | 3 | 0 | 0 | 1 | 0 | 12 | 6 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| concept\06_ecosystem\55_rust_for_data_science.md | L6 | 592 | 3 | 0 | 0 | 2 | 0 | 8 | 6 | ❌ | ✅ | ✅ | 研究者 | 综述级 |
| concept\06_ecosystem\56_c_to_rust_translation.md | L6 | 435 | 3 | 0 | 0 | 0 | 0 | 2 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\57_quiz_toolchain.md | L6 | 544 | 0 | 0 | 0 | 0 | 0 | 7 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\58_platform_rust_integration.md | L6 | 292 | 0 | 0 | 0 | 0 | 0 | 4 | 2 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| concept\06_ecosystem\59_cargo_build_scripts.md | L6 | 496 | 0 | 0 | 0 | 2 | 2 | 14 | 0 | ❌ | ✅ | ✅ | 进阶 / 工程 | 综述级 |
| concept\06_ecosystem\60_cargo_dependency_resolution.md | L6 | 493 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| concept\06_ecosystem\61_cargo_source_replacement.md | L6 | 279 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| concept\06_ecosystem\62_cargo_registries_and_publishing.md | L6 | 283 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| concept\06_ecosystem\63_cargo_authentication_and_cache.md | L6 | 278 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| concept\06_ecosystem\64_cargo_manifest_reference.md | L6 | 309 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 中级 → 高级 | 参考级 |
| concept\06_ecosystem\65_cargo_profiles_and_lints.md | L6 | 292 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| concept\06_ecosystem\66_cargo_subcommands_and_plugins.md | L6 | 235 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| concept\06_ecosystem\67_llvm_backend_and_codegen.md | L6 | 284 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| concept\06_ecosystem\68_rustc_driver_and_stable_mir.md | L6 | 249 | 0 | 0 | 0 | 0 | 0 | 2 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| concept\06_ecosystem\69_compiler_diagnostics_and_ui_tests.md | L6 | 274 | 0 | 0 | 0 | 0 | 0 | 5 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| concept\06_ecosystem\70_rustc_bootstrap.md | L6 | 233 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| concept\06_ecosystem\71_compiler_testing.md | L6 | 265 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| concept\06_ecosystem\72_cargo_security_cves.md | L6 | 449 | 0 | 0 | 0 | 2 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 / 工程 | 综述级 |
| concept\06_ecosystem\73_pattern_composition_algebra.md | L6 | 706 | 3 | 0 | 0 | 2 | 0 | 15 | 6 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\74_formal_verification_tools.md | L6 | 922 | 3 | 0 | 0 | 2 | 0 | 12 | 6 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\75_industrial_case_studies.md | L6 | 337 | 3 | 0 | 0 | 0 | 0 | 2 | 6 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| concept\06_ecosystem\76_cargo_196_features.md | L6 | 247 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 进阶 / 工程 | 专家级 |
| concept\06_ecosystem\77_rustdoc_196_changes.md | L6 | 219 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 进阶 / 工程 | 专家级 |
| concept\06_ecosystem\78_cargo_workspaces.md | L6 | 252 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| concept\06_ecosystem\79_development_tools.md | L6 | 192 | 0 | 0 | 0 | 0 | 0 | 5 | 0 | ❌ | ✅ | ✅ | 初学者 | 研究级 |
| concept\06_ecosystem\80_cargo_getting_started.md | L6 | 88 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 | 参考级 |
| concept\06_ecosystem\81_cargo_workflow.md | L6 | 97 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| concept\06_ecosystem\82_cargo_guide_practices.md | L6 | 91 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| concept\06_ecosystem\83_cargo_configuration.md | L6 | 90 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| concept\06_ecosystem\84_cargo_commands_reference.md | L6 | 82 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| concept\06_ecosystem\85_cargo_manifest_targets.md | L6 | 100 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| concept\06_ecosystem\86_cargo_registry_internals.md | L6 | 97 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 专家 | 参考级 |
| concept\07_future\01_ai_integration.md | L7 | 993 | 2 | 0 | 0 | 2 | 2 | 9 | 2 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\02_formal_methods.md | L7 | 1663 | 9 | 0 | 0 | 1 | 9 | 9 | 3 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\03_evolution.md | L7 | 2174 | 8 | 0 | 0 | 1 | 6 | 19 | 3 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\04_effects_system.md | L7 | 1742 | 3 | 0 | 0 | 0 | 4 | 26 | 6 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\05_rust_version_tracking.md | L7 | 2561 | 3 | 0 | 0 | 0 | 3 | 9 | 2 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\07_mcdc_coverage_preview.md | L7 | 543 | 1 | 0 | 0 | 2 | 3 | 5 | 2 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\08_safety_tags_preview.md | L7 | 626 | 1 | 0 | 0 | 2 | 3 | 6 | 2 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\09_parallel_frontend_preview.md | L7 | 638 | 3 | 0 | 0 | 2 | 3 | 6 | 2 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\10_derive_coerce_pointee_preview.md | L7 | 566 | 1 | 0 | 0 | 2 | 3 | 7 | 2 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\11_const_trait_impl_preview.md | L7 | 601 | 3 | 0 | 0 | 2 | 2 | 6 | 2 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\12_return_type_notation_preview.md | L7 | 463 | 0 | 0 | 0 | 2 | 0 | 10 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\13_unsafe_fields_preview.md | L7 | 599 | 3 | 0 | 0 | 2 | 3 | 6 | 6 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\14_lifetime_capture_preview.md | L7 | 122 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\15_pin_ergonomics_preview.md | L7 | 296 | 0 | 0 | 0 | 2 | 2 | 8 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\16_type_alias_impl_trait_preview.md | L7 | 126 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\17_const_trait_preview.md | L7 | 123 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\18_async_drop_preview.md | L7 | 738 | 3 | 0 | 0 | 2 | 2 | 6 | 2 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\19_rust_edition_preview.md | L7 | 66 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 研究级 |
| concept\07_future\20_borrowsanitizer_preview.md | L7 | 640 | 1 | 0 | 0 | 2 | 3 | 7 | 2 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\21_rust_in_ai.md | L7 | 757 | 3 | 0 | 0 | 2 | 1 | 7 | 6 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\22_gen_blocks_preview.md | L7 | 723 | 4 | 0 | 0 | 3 | 3 | 6 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\23_rust_edition_guide.md | L7 | 15 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| concept\07_future\24_roadmap.md | L7 | 1047 | 3 | 0 | 0 | 2 | 2 | 17 | 2 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\25_open_enums_preview.md | L7 | 779 | 1 | 0 | 0 | 2 | 3 | 13 | 2 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\26_specialization_preview.md | L7 | 723 | 1 | 0 | 0 | 2 | 2 | 7 | 6 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\27_compile_time_execution.md | L7 | 719 | 1 | 0 | 0 | 2 | 1 | 6 | 2 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\28_rust_for_webassembly.md | L7 | 926 | 1 | 0 | 0 | 2 | 2 | 11 | 2 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\29_ebpf_rust.md | L7 | 972 | 3 | 0 | 0 | 0 | 3 | 15 | 2 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\30_stable_abi_preview.md | L7 | 128 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\31_safety_tags_preview.md | L7 | 155 | 0 | 0 | 0 | 1 | 0 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| concept\07_future\32_inline_const_pattern_preview.md | L7 | 128 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\33_autoverus_preview.md | L7 | 171 | 0 | 0 | 0 | 1 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| concept\07_future\34_must_not_suspend_preview.md | L7 | 124 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\35_ferrocene_preview.md | L7 | 633 | 3 | 0 | 0 | 2 | 3 | 5 | 2 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\37_rpitit_preview.md | L7 | 129 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\38_cranelift_backend_preview.md | L7 | 744 | 3 | 0 | 0 | 2 | 3 | 9 | 2 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\39_arbitrary_self_types_preview.md | L7 | 330 | 3 | 0 | 0 | 1 | 0 | 7 | 6 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\40_ergonomic_ref_counting_preview.md | L7 | 264 | 0 | 0 | 0 | 0 | 0 | 5 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\41_rust_specification_preview.md | L7 | 623 | 3 | 0 | 0 | 2 | 3 | 6 | 2 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\42_field_projections_preview.md | L7 | 372 | 1 | 0 | 0 | 1 | 0 | 8 | 2 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\43_rust_for_linux.md | L7 | 998 | 1 | 0 | 0 | 2 | 2 | 9 | 2 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\44_edition_guide.md | L7 | 762 | 1 | 0 | 0 | 2 | 1 | 10 | 2 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\45_std_autodiff_preview.md | L7 | 306 | 3 | 0 | 0 | 1 | 0 | 5 | 6 | ❌ | ✅ | ✅ | 研究者 | 实验级 |
| concept\07_future\46_cargo_semver_checks_preview.md | L7 | 204 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\47_wasm_target_evolution.md | L7 | 122 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\48_aarch64_sve_sme_preview.md | L7 | 252 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\49_rust_in_space.md | L7 | 80 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\50_nightly_rust.md | L7 | 128 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 初学者 | 研究级 |
| concept\07_future\borrow_sanitizer.md | L7 | 299 | 0 | 0 | 0 | 1 | 1 | 1 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\rust_1_95_stabilized.md | L7 | 311 | 0 | 0 | 0 | 0 | 0 | 14 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| concept\07_future\rust_1_96_stabilized.md | L7 | 299 | 0 | 0 | 0 | 0 | 0 | 5 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| concept\07_future\rust_1_97_preview.md | L7 | 761 | 0 | 0 | 0 | 0 | 0 | 17 | 2 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\rust_1_97_stabilized.md | L7 | 274 | 0 | 0 | 0 | 0 | 0 | 11 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| concept\07_future\rust_1_98_preview.md | L7 | 545 | 0 | 0 | 0 | 0 | 0 | 6 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
