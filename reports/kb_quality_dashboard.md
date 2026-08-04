# 知识体系质量仪表盘 (KB Quality Dashboard)

> 生成时间: 2026-08-04T05:20:54.829750+00:00
> 扫描文件数: 745

## 全局指标

| 指标 | 数值 | 目标 | 状态 |
|:---|:---|:---|:---|
| 总文件数 | 745 | 27 | ✅ |
| 总定理链 (⟹) | 2181 | ≥270 | ✅ |
| 总反命题 | 1368 | ≥40 | ✅ |
| 总 Mermaid 图 | 1500 | ≥50 | ✅ |
| 编译验证代码块 | 7578 | ≥150 | ✅ |
| 定理矩阵总行 | 30950 | — | — |
| 死链数量 | 0 | 0 | ✅ |
| docs/content/knowledge 死链数量 | 0 | 0 | ✅ |
| 反向推理 (⟸) | 361 | ≥50 | ✅ |
| 模板化 ⟹ | 0 | 0 | ✅ |
| 前置概念覆盖率 | 647/667 | 100% | ⚠️ |
| 后置概念覆盖率 | 647/667 | 100% | ⚠️ |
| 双标签覆盖率 | 545/667 | >=95% | ⚠️ |
| 非法标签组合 | 0 | 0 | ✅ |

## 按层级分布

| 层级 | 文件数 | 平均 ⟹/文件 | 平均过渡段/文件 | 认知路径 | ⟸/文件 | 模板化 | 前置覆盖 | 后置覆盖 | 双标签 |
|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|
| L0 | 78 | 6.3 | 2.6 | 39/78 (50%) | 0.5 | 0 | 23/78 | 21/78 | 77/78 |
| L1 | 60 | 4.9 | 6.4 | 57/60 (95%) | 2.2 | 0 | 60/60 | 60/60 | 60/60 |
| L2 | 45 | 4.6 | 1.1 | 26/45 (57%) | 1.6 | 0 | 44/45 | 44/45 | 45/45 |
| L3 | 79 | 5.2 | 2.0 | 54/79 (68%) | 1.4 | 0 | 78/79 | 78/79 | 78/79 |
| L4 | 124 | 2.0 | 0.8 | 40/124 (32%) | 0.1 | 0 | 116/124 | 116/124 | 80/124 |
| L5 | 29 | 2.9 | 1.3 | 19/29 (65%) | 0.0 | 0 | 27/29 | 27/29 | 27/29 |
| L6 | 252 | 1.3 | 0.7 | 59/252 (23%) | 0.0 | 0 | 245/252 | 245/252 | 180/252 |
| L7 | 78 | 1.8 | 0.6 | 40/78 (51%) | 0.0 | 0 | 77/78 | 77/78 | 75/78 |

## 风险文件

| 文件 | 层级 | 未通过项 |
|:---|:---|:---|
| E:\_src\rust-lang\concept\01_foundation\00_start\08_compile_time_correctness.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\00_start\09_fearless_refactoring.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\05_collections\03_iterator_idioms.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
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
| E:\_src\rust-lang\concept\02_intermediate\03_error_handling\05_error_idioms.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\01_range_types.md | L2 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\02_closure_types.md | L2 | 缺失认知路径; 缺失反命题; 缺失前置概念; 缺失后置概念 |
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
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\03_macro_patterns.md | L2 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\04_declarative_macros.md | L2 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\05_procedural_macros.md | L2 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\06_metaprogramming.md | L2 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\07_c_preprocessor_vs_rust_macros.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\08_attributes_by_category.md | L2 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\02_intermediate\07_iterators_and_closures\01_iterator_patterns.md | L2 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\02_intermediate\07_iterators_and_closures\02_closures.md | L2 | 过渡段落不足 (0 < 3) |
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
| E:\_src\rust-lang\concept\03_advanced\01_async\16_structured_concurrency.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\00_before_formal.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\02_unsafe_boundary_panorama.md | L3 | 过渡段落不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\03_nll_and_polonius.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\05_quiz_unsafe.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\08_async_in_unsafe_contexts.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\09_sanitizers.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\10_std_unsafe_internals.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\11_in_place_pinned_initialization.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\02_proc_macro.md | L3 | 缺失认知路径; 缺失反命题; 缺失前置概念; 缺失后置概念; 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\10_quiz_macros.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\11_conditional_compilation.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\01_rust_ffi.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\02_ffi_advanced.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\03_linkage.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (1 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\04_async_ffi_boundary.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\05_unsafe_extern_blocks.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\06_ffi_deep_dive.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\07_ffi_patterns.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\05_inline_assembly\01_inline_assembly.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\05_inline_assembly\02_inline_assembly_extended.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
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
| E:\_src\rust-lang\concept\04_formal\00_type_theory\11_formal_design_pattern_theory.md | L4 | 缺失认知路径 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\12_pattern_composition_algebra.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\13_formal_algorithm_theory.md | L4 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\14_flux.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\15_parametricity_and_theorems_for_free.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\16_expressive_power.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失前置概念; 缺失后置概念; 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\17_system_f.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\03_linear_logic_applications.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\04_borrow_checking_decidability.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\05_tree_borrows_deep_dive.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\06_behavior_considered_undefined.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\07_unsafe_contracts_formal.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\02_separation_logic.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\03_safety_tags_in_formal.md | L4 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\04_borrow_sanitizer_in_formal.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\01_denotational_semantics.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\02_hoare_logic.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\03_operational_semantics.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\04_evaluation_strategies.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\05_axiomatic_semantics.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\06_observational_equivalence.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\07_aeneas_symbolic_semantics.md | L4 | 过渡段落不足 (0 < 3); 定理链不足 (1 < 3); 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\08_constant_evaluation.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\09_llvm_ir_poison_ub.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失前置概念; 缺失后置概念; 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\10_minirust.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\11_async_state_machine_semantics.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (1 < 3); 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\12_pin_and_self_referential_semantics.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\13_in_place_initialization_semantics.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
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
| E:\_src\rust-lang\concept\04_formal\04_model_checking\11_creusot.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\12_rust_contracts.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签; 缺失内容分级标签 |
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
| E:\_src\rust-lang\concept\04_formal\07_concurrency_semantics\07_session_types.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\04_formal\07_concurrency_semantics\08_send_sync_semantics.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\04_formal\08_algorithm_semantics\01_hoare_logic_for_rust.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\08_algorithm_semantics\02_refinement_calculus.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\08_algorithm_semantics\03_iterator_correctness.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\08_algorithm_semantics\04_unsafe_algorithm_invariants.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\04_formal\08_algorithm_semantics\05_algorithm_equivalence.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\04_formal\09_system_semantics\01_actor_model_semantics.md | L4 | 缺失认知路径 |
| E:\_src\rust-lang\concept\04_formal\09_system_semantics\02_pi_calculus_for_rust.md | L4 | 缺失认知路径 |
| E:\_src\rust-lang\concept\04_formal\09_system_semantics\04_distributed_systems_semantics.md | L4 | 定理链不足 (1 < 3) |
| E:\_src\rust-lang\concept\04_formal\09_system_semantics\05_reactive_systems_semantics.md | L4 | 缺失认知路径; 定理链不足 (2 < 3) |
| E:\_src\rust-lang\concept\04_formal\09_system_semantics\06_systems_engineering_standards.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\09_system_semantics\07_concurrent_and_parallel_semantics.md | L4 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\09_system_semantics\08_memory_ordering_and_atomics.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (2 < 3) |
| E:\_src\rust-lang\concept\04_formal\10_architecture_semantics\01_software_architecture_formalization.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\04_formal\10_architecture_semantics\02_architecture_pattern_semantics.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\04_formal\10_architecture_semantics\03_architecture_refinement.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\04_formal\10_architecture_semantics\04_rust_architecture_constraints.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\04_formal\10_architecture_semantics\05_architecture_styles_formal_constraints.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\04_formal\11_computational_models\01_computational_semantics_framework.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\04_formal\11_computational_models\02_computability_theory.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\04_formal\11_computational_models\03_formal_languages_and_automata.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\04_formal\11_computational_models\04_mathematical_functions_of_computation.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\04_formal\11_computational_models\05_equivalence_of_computational_models.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\04_formal\11_computational_models\06_computational_equivalence_in_rust.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\04_formal\11_computational_models\07_type_theory_and_rust.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\04_formal\11_computational_models\08_separation_logic_for_rust.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\04_formal\11_computational_models\09_concurrency_models_actors_csp.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\04_formal\12_concurrency_models\01_models_of_concurrency.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\04_formal\12_concurrency_models\02_expressiveness_of_concurrent_models.md | L4 | 过渡段落不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\04_formal\12_concurrency_models\03_parallel_concurrent_async_distributed_semantics.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\04_formal\13_semantic_engineering\01_ontology_engineering.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\04_formal\13_semantic_engineering\02_description_logic_and_owl.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\04_formal\13_semantic_engineering\03_knowledge_graph_construction.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\04_formal\13_semantic_engineering\04_semantic_interoperability.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\04_formal\13_semantic_engineering\05_knowledge_graph_reasoning.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\04_formal\13_semantic_engineering\06_ai_ontology_and_rust_semantics.md | L4 | 缺失认知路径; 过渡段落不足 (2 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\04_formal\13_semantic_engineering\07_kg_owl_shacl_semantics.md | L4 | 缺失认知路径; 过渡段落不足 (2 < 3); 定理链不足 (0 < 3); 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\04_formal\13_semantic_engineering\08_computational_semantic_models.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\04_formal\14_embedded_semantics\01_embedded_formal_memory_model.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\15_language_specification\00_language_specification_overview.md | L4 | 缺失认知路径; 缺失前置概念; 缺失后置概念; 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\04_formal\15_language_specification\01_rust_reference_and_normative_gap.md | L4 | 缺失认知路径; 缺失前置概念; 缺失后置概念; 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\04_formal\15_language_specification\02_ferrocene_language_specification.md | L4 | 缺失认知路径; 缺失前置概念; 缺失后置概念; 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\04_formal\15_language_specification\03_executable_specification_minirust.md | L4 | 缺失认知路径; 缺失前置概念; 缺失后置概念; 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\04_formal\15_language_specification\04_a_mir_formality_type_system_spec.md | L4 | 缺失认知路径; 缺失前置概念; 缺失后置概念; 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\04_formal\15_language_specification\05_specification_evidence_from_rustc_tests.md | L4 | 缺失认知路径; 缺失前置概念; 缺失后置概念; 缺失受众标签; 缺失内容分级标签 |
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
| E:\_src\rust-lang\concept\05_comparative\04_verification_and_contracts\00_verification_and_contracts_overview.md | L5 | 缺失认知路径; 缺失前置概念; 缺失后置概念; 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\05_comparative\04_verification_and_contracts\01_contracts_comparison.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失前置概念; 缺失后置概念; 缺失受众标签; 缺失内容分级标签 |
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
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\16_rustdoc_internals.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
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
| E:\_src\rust-lang\concept\06_ecosystem\02_core_crates\01_core_crates.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\02_core_crates\02_serde.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\06_ecosystem\02_core_crates\03_tokio.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\06_ecosystem\02_core_crates\04_clap.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\06_ecosystem\02_core_crates\05_tracing.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\06_ecosystem\02_core_crates\06_reqwest.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\06_ecosystem\02_core_crates\07_axum.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\06_ecosystem\02_core_crates\08_sqlx.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\02_idioms_spectrum.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\03_system_design_principles.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\04_system_composability.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\05_microservice_patterns.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\06_event_driven_architecture.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\07_cqrs_event_sourcing.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\08_architecture_patterns.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\11_formal_design_pattern_theory.md | L6 | 缺失前置概念; 缺失后置概念; 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\16_pattern_composition_algebra.md | L6 | 缺失前置概念; 缺失后置概念; 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\17_workflow_theory.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\18_api_design_patterns.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\19_model_driven_engineering.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\21_microkernel_architecture.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\22_embedded_safety_critical_patterns.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\23_pipeline_filter_blackboard_interpreter.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\24_repository_and_unit_of_work.md | L6 | 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\25_hexagonal_ports_and_adapters.md | L6 | 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\26_circuit_breaker.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\27_bulkhead.md | L6 | 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\28_retry.md | L6 | 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\29_saga.md | L6 | 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\30_outbox.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\31_object_pool.md | L6 | 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\32_typestate_deep_dive.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\33_anti_patterns.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\34_ownership_as_resource_management.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (1 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\35_scope_guard_and_deferred_cleanup.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\36_enterprise_and_software_architecture_alignment.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\37_event_sourcing_engine_patterns.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\38_api_gateway_and_service_mesh_patterns.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\39_api_design_and_semver_idioms.md | L6 | 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\40_testing_and_mocking_idioms.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\41_ecs_and_data_oriented_design_patterns.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\42_actor_model_and_message_passing_patterns.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\43_rejection_type_pattern.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\44_configuration_management_patterns.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\45_dependency_injection_in_rust.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\47_rust_design_and_architecture_patterns_semantic_atlas.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\48_api_guidelines_idioms.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\49_gof_patterns_in_rust.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\50_rust_idioms_atlas.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\51_anti_patterns_and_pitfalls.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\52_performance_idioms.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\01_distributed_systems.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\02_cloud_native.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\03_web_frameworks.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\04_http_client_development.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\07_network_protocols.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\09_reactive_programming.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\10_tokio_runtime_internals.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\11_kubernetes_rust.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
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
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\13_bare_metal_boot_linker_script.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\14_interrupt_and_exception_model.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\15_no_std_synchronization_primitives.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\16_embedded_memory_allocators.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\17_pac_hal_implementation.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\18_panic_runtime_no_std.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\19_safety_critical_bare_metal_os.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\20_embedded_debugging_logging.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\21_riscv_avr_embedded.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\22_embedded_protocol_drivers.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失内容分级标签 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\23_no_std_and_bare_metal_idioms.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\24_embedded_hal_and_driver_idioms.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\25_memory_mapped_peripherals_and_typestate.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\26_embedded_rtos_and_safety_critical_frameworks.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\27_no_std_startup_runtime_deep_dive.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\28_custom_bare_metal_async_executor.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\29_embedded_memory_layout_and_heap_safety.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\30_misra_rust_safety_critical_guidelines.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\31_embedded_networking_and_iot_protocols.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\32_embedded_testing_and_ci_strategies.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\33_sei_cert_c_to_rust_mapping.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\34_embassy_framework_deep_dive.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\35_rtic_framework_deep_dive.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\36_defmt_probe_rs_architecture.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\37_fallible_allocation_and_no_alloc_collections.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\38_no_std_bare_metal_rust.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\39_no_std_hardware_measurement_and_validation.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\41_embedded_hal_and_mmio.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失前置概念; 缺失后置概念; 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\42_interrupts_and_concurrency_on_bare_metal.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失前置概念; 缺失后置概念; 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\43_rust_safety_critical_systems.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\45_embedded_hardware_validation.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\46_rtos_and_scheduling_in_rust.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\47_bare_metal_rust.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\48_no_std_alloc_crate_ecosystem.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\49_embedded_hal_driver_patterns.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\02_database_access.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\03_stream_processing_ecosystem.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\04_database_systems.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\05_data_engineering.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\06_distributed_consensus.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\07_rust_for_data_science.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\10_data_intensive_systems_design.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\11_distributed_systems_protocols.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\07_security_and_cryptography\01_security_practices.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\07_security_and_cryptography\02_security_cryptography.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\07_security_and_cryptography\03_cargo_vet_supply_chain.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\07_security_and_cryptography\04_security_architecture.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\08_formal_verification\01_formal_ecosystem_tower.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (1 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\08_formal_verification\02_formal_verification_tools.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\09_testing_and_quality\01_testing_strategies.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\09_testing_and_quality\02_documentation.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\09_testing_and_quality\03_testing.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\09_testing_and_quality\04_benchmarking.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\10_performance\01_performance_optimization.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\10_performance\02_performance_engineering_architecture.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\10_performance\03_algorithms_and_complexity_idioms.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\01_blockchain.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\02_game_ecs.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (1 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\03_webassembly.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\04_licensing_and_compliance.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\05_game_development.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\07_algorithms_competitive_programming.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\09_data_structures_in_rust.md | L6 | 缺失前置概念; 缺失后置概念; 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\10_algorithm_complexity_analysis.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\12_formal_algorithm_theory.md | L6 | 缺失前置概念; 缺失后置概念; 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\13_machine_learning_ecosystem.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\14_industrial_case_studies.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\15_game_engine_internals.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\16_quantum_computing_rust.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\17_webassembly_advanced.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\22_autosar_and_rust.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\23_safety_critical_systems_engineering.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\24_advanced_data_structures_implementation.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\25_parallel_algorithms.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\26_zero_copy_parsing_in_rust.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\27_ownership_aware_algorithms.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\28_unsafe_algorithm_invariants.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\12_networking\03_custom_protocol_implementation.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\13_quizzes\01_quiz_networking_async_ecosystem.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\13_quizzes\02_quiz_database_storage.md | L6 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\13_quizzes\03_quiz_security_testing.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (1 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\13_quizzes\04_quiz_domain_applications.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (1 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\14_enterprise_architecture\01_enterprise_architecture_frameworks.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\14_enterprise_architecture\02_architecture_governance_and_adrs.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\14_enterprise_architecture\03_architecture_standards_alignment.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\14_enterprise_architecture\04_domain_driven_design_in_rust.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\14_enterprise_architecture\05_strategic_domain_driven_design_in_rust.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\14_enterprise_architecture\06_clean_architecture_in_rust.md | L6 | 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\14_enterprise_architecture\07_hexagonal_architecture_in_rust.md | L6 | 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\14_enterprise_architecture\08_microservices_patterns_in_rust.md | L6 | 缺失前置概念; 缺失后置概念; 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\14_enterprise_architecture\09_observability_and_sre_patterns.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\14_enterprise_architecture\10_production_rust_web_service_patterns.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\14_enterprise_architecture\11_event_driven_and_cqrs_patterns.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\14_enterprise_architecture\12_cloud_native_and_serverless_patterns.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\14_enterprise_architecture\13_microservices_patterns_in_rust.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\14_enterprise_architecture\14_data_intensive_patterns.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\14_enterprise_architecture\15_security_and_zero_trust_patterns.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\00_algorithm_patterns_overview.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\01_algorithmic_paradigms.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\02_ownership_aware_data_structures.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\03_graph_algorithms_in_rust.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\04_cache_friendly_and_simd_algorithms.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\05_greedy_and_approximation_algorithms.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\06_dynamic_programming_in_rust.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\07_string_algorithms_in_rust.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\08_data_structures_in_rust.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\09_randomized_and_probabilistic_algorithms.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\10_computational_geometry_algorithms.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\11_online_and_streaming_algorithms.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\12_number_theoretic_algorithms.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\13_advanced_string_algorithms.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\14_network_flow_and_matching.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\15_probabilistic_data_structures.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\16_persistent_data_structures.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\17_rust_algorithm_patterns_semantic_atlas.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\18_competitive_programming_idioms.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\19_parallel_and_gpu_algorithms.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\01_rust_version_tracking.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\02_editions.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\feature_domain_matrix_197.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\feature_domain_matrix_198.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\migration_197_decision_tree.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\migration_198_decision_tree.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_100_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_95_stabilized.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_96_stabilized.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_97_1.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (1 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_97_stabilized.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_98_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_98_stabilized.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_99_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
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
| E:\_src\rust-lang\concept\07_future\02_preview_features\21_rust_specification_preview.md | L7 | 缺失前置概念; 缺失后置概念; 缺失受众标签; 缺失内容分级标签 |
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
| E:\_src\rust-lang\concept\07_future\02_preview_features\39_async_ioring_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_edition_differences\01_edition_2021_to_2024.md | L7 | 过渡段落不足 (2 < 3); 定理链不足 (0 < 3); 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\01_ai_integration.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (1 < 3) |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\04_rust_for_linux.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\05_rust_in_ai.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\06_rust_for_webassembly.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\07_ebpf_rust.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\08_llm_system_architecture.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\09_mlops_and_llmops.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\10_ai_safety_and_alignment.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\11_rust_for_ai_model_serving.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失受众标签 |
| E:\_src\rust-lang\concept\07_future\05_quizzes\01_quiz_version_and_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |

## docs/content/knowledge 死链检查

> 扫描范围：`docs/`、`content/`、`knowledge/` 下所有 `.md` 文件中的本地 markdown 链接。
> 排除：`http/https`、`mailto:`、纯锚点 `#`、跨仓库绝对路径 `/`。

✅ 无死链。

## 文件详细统计

| 文件 | 层级 | 行数 | ⟹ | ⟸ | 模板 | 反命题 | Mermaid | 代码块 | 过渡段 | 认知路径 | 前置 | 后置 | 受众 | 分级 |
|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|
| E:\_src\rust-lang\concept\00_meta\00_framework\bloom_taxonomy.md | L0 | 202 | 1 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\boundary_extension_tree.md | L0 | 362 | 1 | 0 | 0 | 1 | 3 | 1 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\cognitive_dimension_matrix.md | L0 | 403 | 1 | 0 | 0 | 1 | 2 | 0 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\competency_graph.md | L0 | 429 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\comprehensive_rust_mapping.md | L0 | 240 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\concept_definition_decision_forest.md | L0 | 1175 | 3 | 0 | 0 | 1 | 10 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\cpp_rust_engineering_roadmap.md | L0 | 263 | 0 | 0 | 0 | 0 | 2 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\decidability_spectrum.md | L0 | 963 | 2 | 0 | 0 | 1 | 6 | 2 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\expressiveness_multiview.md | L0 | 830 | 0 | 0 | 0 | 1 | 7 | 7 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\fault_tree_analysis_collection.md | L0 | 806 | 1 | 0 | 0 | 1 | 7 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\knowledge_mindmap.md | L0 | 308 | 1 | 0 | 0 | 1 | 2 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\methodology.md | L0 | 612 | 1 | 0 | 0 | 2 | 5 | 1 | 6 | ✅ | ✅ | ✅ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\paradigm_transition_matrix.md | L0 | 334 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\pattern_semantic_space_index.md | L0 | 220 | 0 | 0 | 0 | 0 | 2 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\pl_foundations_roadmap.md | L0 | 186 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\rust_api_guidelines_canonical.md | L0 | 1800 | 0 | 0 | 0 | 1 | 1 | 128 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\semantic_bridge_algorithms_patterns.md | L0 | 737 | 1 | 0 | 0 | 1 | 0 | 7 | 6 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\semantic_expressiveness.md | L0 | 1133 | 1 | 0 | 0 | 1 | 2 | 1 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\semantic_layer_alignment_index.md | L0 | 214 | 2 | 0 | 0 | 3 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 研究者 / 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\semantic_model_reasoning_methodology.md | L0 | 292 | 1 | 0 | 0 | 1 | 2 | 2 | 0 | ✅ | ✅ | ✅ | 研究者 / 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\semantic_space.md | L0 | 1559 | 12 | 0 | 0 | 2 | 5 | 10 | 8 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\theorem_inference_forest.md | L0 | 558 | 15 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\theorem_registry.md | L0 | 244 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\todos.md | L0 | 349 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\01_terminology\01_terminology_glossary.md | L0 | 506 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\01_terminology\02_bilingual_template_v2.md | L0 | 327 | 0 | 2 | 0 | 5 | 1 | 5 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\01_terminology\03_bilingual_template.md | L0 | 167 | 0 | 0 | 0 | 1 | 1 | 1 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\02_sources\01_authority_source_map.md | L0 | 215 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\02_sources\02_rustbelt_predicate_map.md | L0 | 435 | 9 | 0 | 0 | 1 | 6 | 0 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\02_sources\03_sources.md | L0 | 495 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 研究者级 |
| E:\_src\rust-lang\concept\00_meta\02_sources\04_topic_authority_alignment_map.md | L0 | 394 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\00_meta\02_sources\05_international_authority_index.md | L0 | 390 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 研究者 / 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\02_sources\06_external_authority_topic_index.md | L0 | 413 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 维护者 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\01_concept_audit_guide.md | L0 | 107 | 1 | 0 | 0 | 1 | 1 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\02_asp_marking_guide.md | L0 | 552 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\03_audit_checklist.md | L0 | 484 | 2 | 1 | 0 | 2 | 1 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\04_concept_consistency_audit_checklist.md | L0 | 16 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\05_template_deduplication_guide.md | L0 | 96 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\06_grading_system.md | L0 | 163 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\07_quality_dashboard_v2.md | L0 | 330 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\08_feature_inventory_methodology.md | L0 | 49 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\09_kg_shacl_engine_validation.md | L0 | 111 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ❌ | ❌ | 维护者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\01_cross_reference_matrix.md | L0 | 18 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\02_career_landscape.md | L0 | 236 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\03_concept_index.md | L0 | 804 | 4 | 0 | 0 | 2 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\04_inter_layer_map.md | L0 | 736 | 12 | 0 | 0 | 1 | 2 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\05_inter_layer_topology.md | L0 | 18 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ✅ | ❌ | ❌ | 初学者 | 专家级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\06_intra_layer_model_map.md | L0 | 367 | 11 | 0 | 0 | 1 | 5 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\07_learning_guide.md | L0 | 692 | 3 | 0 | 0 | 1 | 1 | 0 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\08_learning_mvp_path.md | L0 | 372 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ✅ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\09_navigation.md | L0 | 295 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\10_problem_graph.md | L0 | 552 | 1 | 0 | 0 | 1 | 7 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\11_quick_reference.md | L0 | 859 | 1 | 0 | 0 | 1 | 0 | 25 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\12_self_assessment.md | L0 | 2298 | 0 | 0 | 0 | 1 | 0 | 57 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\13_foundations_gap_closure_index.md | L0 | 147 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\14_learning_mvp_path_en.md | L0 | 293 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\15_quiz_registry.md | L0 | 152 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\05_ai_semantic_engineering\01_knowledge_graph_design.md | L0 | 314 | 0 | 0 | 0 | 3 | 2 | 0 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\00_meta\05_ai_semantic_engineering\02_llm_rag_for_rust.md | L0 | 263 | 0 | 0 | 0 | 3 | 2 | 0 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\00_meta\06_trpl_3rd_ed_mapping.md | L0 | 14 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\07_placeholders\01_placeholder_generic.md | L0 | 26 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\07_trpl_3rd_edition_alignment.md | L0 | 83 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\08_usability_testing_framework.md | L0 | 132 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\09_quizzes\01_quiz_meta_framework.md | L0 | 373 | 0 | 0 | 0 | 0 | 0 | 2 | 0 | ❌ | ✅ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\01_concept_definition_atlas.md | L0 | 567 | 1 | 1 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\02_attribute_relationship_atlas.md | L0 | 562 | 27 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\03_scenario_decision_tree_atlas.md | L0 | 621 | 0 | 0 | 0 | 0 | 9 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\04_example_counterexample_atlas.md | L0 | 542 | 1 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\05_logical_reasoning_atlas.md | L0 | 192 | 17 | 2 | 0 | 0 | 4 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\06_inter_layer_mapping_atlas.md | L0 | 204 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\07_intra_layer_mapping_atlas.md | L0 | 595 | 347 | 33 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\08_concept_source_alignment_atlas.md | L0 | 53 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\09_reasoning_judgment_tree_atlas.md | L0 | 882 | 4 | 0 | 0 | 0 | 12 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\10_gap_and_action_plan.md | L0 | 80 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\11_semantic_model_atlas.md | L0 | 541 | 0 | 0 | 0 | 1 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\12_semantic_properties_atlas.md | L0 | 163 | 0 | 0 | 0 | 1 | 1 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\kg_ontology_v2.md | L0 | 937 | 0 | 0 | 0 | 4 | 4 | 1 | 0 | ✅ | ✅ | ✅ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\kg_tlo_alignment.md | L0 | 265 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\00_start.md | L1 | 343 | 4 | 2 | 0 | 1 | 2 | 3 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\01_pl_prerequisites.md | L1 | 613 | 3 | 4 | 0 | 1 | 1 | 14 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\02_zero_cost_abstractions.md | L1 | 921 | 3 | 2 | 0 | 2 | 3 | 14 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\03_closure_basics.md | L1 | 966 | 4 | 4 | 0 | 3 | 2 | 18 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\04_effects_and_purity.md | L1 | 880 | 3 | 2 | 0 | 3 | 1 | 17 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\05_std_io_and_process.md | L1 | 518 | 4 | 6 | 0 | 5 | 2 | 10 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\06_keywords.md | L1 | 323 | 3 | 2 | 0 | 1 | 1 | 4 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\07_operators_and_symbols.md | L1 | 307 | 3 | 2 | 0 | 1 | 1 | 2 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\08_compile_time_correctness.md | L1 | 313 | 0 | 0 | 0 | 1 | 2 | 7 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\09_fearless_refactoring.md | L1 | 340 | 0 | 0 | 0 | 1 | 2 | 8 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\00_ownership_borrow_lifetime_knowledge_map.md | L1 | 482 | 5 | 2 | 0 | 4 | 6 | 2 | 5 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\01_ownership.md | L1 | 2043 | 27 | 4 | 0 | 3 | 8 | 46 | 22 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\02_borrowing.md | L1 | 2171 | 13 | 3 | 0 | 3 | 7 | 53 | 20 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\03_lifetimes.md | L1 | 1637 | 23 | 2 | 0 | 3 | 6 | 42 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\04_lifetimes_advanced.md | L1 | 1894 | 3 | 2 | 0 | 1 | 1 | 49 | 10 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\05_move_semantics.md | L1 | 389 | 6 | 2 | 0 | 1 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\06_ownership_inventories_brown_book.md | L1 | 254 | 3 | 2 | 0 | 1 | 1 | 3 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\01_type_system.md | L1 | 3380 | 23 | 2 | 0 | 3 | 13 | 63 | 16 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\02_never_type.md | L1 | 690 | 3 | 2 | 0 | 1 | 1 | 16 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\03_numerics.md | L1 | 1209 | 3 | 2 | 0 | 2 | 2 | 21 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\04_coercion_and_casting.md | L1 | 1076 | 3 | 2 | 0 | 2 | 2 | 18 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\05_data_abstraction_spectrum.md | L1 | 908 | 3 | 2 | 0 | 3 | 1 | 14 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\03_values_and_references\01_reference_semantics.md | L1 | 1526 | 4 | 2 | 0 | 3 | 8 | 35 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\03_values_and_references\02_value_vs_reference_semantics.md | L1 | 309 | 3 | 2 | 0 | 1 | 1 | 5 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\03_values_and_references\03_variable_model.md | L1 | 788 | 3 | 2 | 0 | 3 | 1 | 12 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\04_control_flow\01_control_flow.md | L1 | 1755 | 3 | 2 | 0 | 2 | 6 | 25 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\04_control_flow\02_patterns.md | L1 | 428 | 3 | 2 | 0 | 1 | 1 | 14 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\04_control_flow\03_let_chains.md | L1 | 546 | 3 | 2 | 0 | 5 | 1 | 24 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\04_control_flow\04_statements_and_expressions.md | L1 | 334 | 3 | 2 | 0 | 1 | 1 | 7 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\04_control_flow\05_let_else.md | L1 | 408 | 3 | 2 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\05_collections\01_collections.md | L1 | 942 | 3 | 2 | 0 | 2 | 3 | 16 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\05_collections\02_collections_advanced.md | L1 | 1071 | 6 | 2 | 0 | 2 | 3 | 11 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\05_collections\03_iterator_idioms.md | L1 | 525 | 0 | 0 | 0 | 4 | 1 | 24 | 0 | ❌ | ✅ | ✅ | 进阶 | 进阶 |
| E:\_src\rust-lang\concept\01_foundation\06_strings_and_text\01_strings_and_text.md | L1 | 951 | 3 | 2 | 0 | 2 | 2 | 19 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\06_strings_and_text\02_strings_and_encoding.md | L1 | 979 | 4 | 2 | 0 | 2 | 3 | 11 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\06_strings_and_text\03_formatting_and_display.md | L1 | 485 | 4 | 3 | 0 | 4 | 2 | 9 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\01_modules_and_paths.md | L1 | 997 | 10 | 2 | 0 | 2 | 2 | 11 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\02_functions.md | L1 | 447 | 4 | 2 | 0 | 1 | 1 | 10 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\03_use_declarations.md | L1 | 322 | 4 | 2 | 0 | 1 | 1 | 10 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\04_structs.md | L1 | 395 | 9 | 2 | 0 | 1 | 1 | 8 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\05_enumerations.md | L1 | 392 | 9 | 2 | 0 | 1 | 1 | 10 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\06_implementations.md | L1 | 377 | 5 | 2 | 0 | 1 | 1 | 8 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\07_type_aliases.md | L1 | 464 | 4 | 3 | 0 | 4 | 2 | 10 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\08_static_items.md | L1 | 453 | 4 | 3 | 0 | 4 | 2 | 8 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\09_const_items_and_const_fn.md | L1 | 477 | 5 | 3 | 0 | 4 | 2 | 8 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\10_preludes.md | L1 | 295 | 3 | 2 | 0 | 1 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\11_crates_and_source_files.md | L1 | 378 | 4 | 2 | 0 | 2 | 3 | 7 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\12_items.md | L1 | 434 | 4 | 2 | 0 | 1 | 2 | 14 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\08_error_handling\01_error_handling_basics.md | L1 | 1082 | 3 | 2 | 0 | 2 | 2 | 15 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\08_error_handling\02_error_handling_control_flow.md | L1 | 382 | 3 | 3 | 0 | 1 | 2 | 11 | 7 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\08_error_handling\03_panic_and_abort.md | L1 | 1024 | 8 | 2 | 0 | 2 | 2 | 12 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\09_macros_basics\01_attributes_and_macros.md | L1 | 1000 | 3 | 2 | 0 | 2 | 2 | 14 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\10_testing_basics\01_testing_basics.md | L1 | 819 | 3 | 2 | 0 | 2 | 2 | 8 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\10_testing_basics\02_useful_development_tools.md | L1 | 341 | 4 | 2 | 0 | 1 | 3 | 2 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\01_quiz_type_system.md | L1 | 638 | 3 | 2 | 0 | 1 | 0 | 14 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\02_quiz_error_handling.md | L1 | 772 | 3 | 2 | 0 | 2 | 0 | 20 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\03_quiz_modules_testing.md | L1 | 828 | 3 | 2 | 0 | 1 | 0 | 22 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\04_quiz_closures_iterators.md | L1 | 816 | 3 | 2 | 0 | 1 | 0 | 33 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\05_quiz_pl_foundations.md | L1 | 297 | 3 | 2 | 0 | 1 | 0 | 0 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\06_quiz_ownership_borrowing.md | L1 | 625 | 3 | 2 | 0 | 1 | 0 | 18 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\01_traits.md | L2 | 3264 | 15 | 2 | 0 | 7 | 6 | 78 | 10 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\02_dispatch_mechanisms.md | L2 | 2338 | 14 | 2 | 0 | 1 | 1 | 42 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\03_serde_patterns.md | L2 | 941 | 3 | 3 | 0 | 2 | 3 | 9 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\04_advanced_traits.md | L2 | 1152 | 3 | 3 | 0 | 2 | 2 | 24 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\05_construction_and_initialization.md | L2 | 346 | 1 | 0 | 0 | 0 | 1 | 7 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\06_derive_traits.md | L2 | 471 | 2 | 0 | 0 | 0 | 1 | 15 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\07_generic_associated_types.md | L2 | 676 | 0 | 0 | 0 | 0 | 3 | 14 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\08_negative_impls.md | L2 | 381 | 0 | 0 | 0 | 2 | 1 | 13 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\09_associated_type_defaults.md | L2 | 440 | 0 | 0 | 0 | 5 | 1 | 14 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\01_generics.md | L2 | 3358 | 23 | 2 | 0 | 7 | 7 | 74 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\02_const_generics.md | L2 | 618 | 2 | 0 | 0 | 4 | 1 | 15 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\03_type_level_programming.md | L2 | 885 | 8 | 2 | 0 | 1 | 1 | 13 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\04_quiz_traits_and_generics.md | L2 | 762 | 0 | 0 | 0 | 0 | 0 | 20 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\05_const_generics_and_trait_objects.md | L2 | 249 | 0 | 0 | 0 | 1 | 2 | 4 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\01_memory_management.md | L2 | 2266 | 23 | 3 | 0 | 7 | 6 | 55 | 7 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\02_interior_mutability.md | L2 | 973 | 9 | 3 | 0 | 2 | 3 | 11 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\03_cow_and_borrowed.md | L2 | 819 | 4 | 3 | 0 | 2 | 3 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\04_smart_pointers.md | L2 | 993 | 9 | 3 | 0 | 2 | 3 | 12 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\05_quiz_memory_management.md | L2 | 810 | 0 | 0 | 0 | 0 | 0 | 27 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\03_error_handling\01_error_handling.md | L2 | 2935 | 22 | 4 | 0 | 7 | 9 | 63 | 7 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\03_error_handling\02_error_handling_deep_dive.md | L2 | 861 | 3 | 3 | 0 | 2 | 2 | 9 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\03_error_handling\03_panic.md | L2 | 309 | 0 | 0 | 0 | 0 | 1 | 5 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\02_intermediate\03_error_handling\04_exception_safety_rust_cpp.md | L2 | 371 | 2 | 0 | 0 | 0 | 1 | 6 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\03_error_handling\05_error_idioms.md | L2 | 487 | 0 | 0 | 0 | 4 | 1 | 17 | 0 | ❌ | ✅ | ✅ | 进阶 | 进阶 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\01_range_types.md | L2 | 723 | 3 | 3 | 0 | 2 | 3 | 12 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\02_closure_types.md | L2 | 79 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\03_newtype_and_wrapper.md | L2 | 858 | 3 | 3 | 0 | 2 | 2 | 12 | 2 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\04_type_system_advanced.md | L2 | 1307 | 3 | 3 | 0 | 2 | 2 | 18 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\05_rtti_and_dynamic_typing.md | L2 | 352 | 0 | 0 | 0 | 0 | 1 | 7 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\06_unions.md | L2 | 468 | 4 | 3 | 0 | 4 | 2 | 7 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\07_type_conversions.md | L2 | 692 | 4 | 4 | 0 | 4 | 2 | 17 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\02_intermediate\05_modules_and_visibility\01_module_system.md | L2 | 967 | 8 | 3 | 0 | 2 | 4 | 17 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\05_modules_and_visibility\02_friend_vs_module_privacy.md | L2 | 323 | 0 | 0 | 0 | 0 | 1 | 5 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\05_modules_and_visibility\03_api_naming_conventions.md | L2 | 592 | 0 | 0 | 0 | 0 | 1 | 17 | 2 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\01_assert_matches.md | L2 | 786 | 3 | 3 | 0 | 2 | 4 | 18 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\02_dsl_and_embedding.md | L2 | 893 | 5 | 3 | 0 | 2 | 2 | 11 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\03_macro_patterns.md | L2 | 105 | 0 | 0 | 0 | 0 | 2 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\04_declarative_macros.md | L2 | 666 | 3 | 2 | 0 | 2 | 2 | 15 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\05_procedural_macros.md | L2 | 666 | 3 | 2 | 0 | 2 | 2 | 15 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\06_metaprogramming.md | L2 | 923 | 3 | 3 | 0 | 2 | 3 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\07_c_preprocessor_vs_rust_macros.md | L2 | 308 | 0 | 0 | 0 | 0 | 1 | 6 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\08_attributes_by_category.md | L2 | 514 | 4 | 4 | 0 | 4 | 2 | 10 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\02_intermediate\07_iterators_and_closures\01_iterator_patterns.md | L2 | 1468 | 13 | 2 | 0 | 1 | 2 | 23 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\07_iterators_and_closures\02_closures.md | L2 | 784 | 3 | 2 | 0 | 2 | 2 | 18 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\08_quizzes\30_quiz_cpp_rust_foundations.md | L2 | 307 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\01_concurrency.md | L3 | 2194 | 21 | 2 | 0 | 3 | 13 | 27 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\02_send_sync_auto_traits.md | L3 | 646 | 10 | 1 | 0 | 4 | 2 | 13 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\03_concurrency_patterns.md | L3 | 2376 | 3 | 3 | 0 | 2 | 4 | 34 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\04_send_sync_boundaries.md | L3 | 517 | 0 | 0 | 0 | 4 | 1 | 10 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\05_cross_platform_concurrency.md | L3 | 269 | 6 | 2 | 0 | 1 | 1 | 5 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\06_atomics_and_memory_ordering.md | L3 | 1563 | 8 | 3 | 0 | 2 | 3 | 24 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\07_lock_free.md | L3 | 1272 | 3 | 3 | 0 | 2 | 2 | 20 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\08_parallel_distributed_pattern_spectrum.md | L3 | 1152 | 3 | 3 | 0 | 2 | 1 | 18 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\09_quiz_concurrency_async.md | L3 | 799 | 0 | 0 | 0 | 0 | 0 | 19 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\10_quiz_semantic_models.md | L3 | 437 | 1 | 0 | 0 | 0 | 0 | 4 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\01_async.md | L3 | 3651 | 21 | 3 | 0 | 6 | 10 | 67 | 3 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\02_async_advanced.md | L3 | 704 | 5 | 3 | 0 | 0 | 1 | 14 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\03_async_patterns.md | L3 | 1327 | 3 | 3 | 0 | 2 | 2 | 22 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\04_future_and_executor_mechanisms.md | L3 | 1284 | 8 | 2 | 0 | 2 | 1 | 20 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\05_async_cancellation_safety.md | L3 | 570 | 0 | 0 | 0 | 5 | 2 | 11 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\06_async_boundary_panorama.md | L3 | 545 | 26 | 0 | 0 | 6 | 3 | 10 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\07_async_closures.md | L3 | 673 | 3 | 0 | 0 | 1 | 1 | 20 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\08_pin_unpin.md | L3 | 1220 | 6 | 3 | 0 | 2 | 4 | 26 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\09_stream_algebra_and_backpressure.md | L3 | 504 | 5 | 2 | 0 | 1 | 3 | 7 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\10_executor_fairness_and_scheduling.md | L3 | 377 | 11 | 3 | 0 | 1 | 2 | 5 | 2 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\11_pin_projection_counterexamples.md | L3 | 456 | 5 | 2 | 0 | 5 | 3 | 8 | 2 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\12_waker_contract_deep_dive.md | L3 | 397 | 11 | 0 | 0 | 3 | 4 | 4 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\13_async_trait_object_safety.md | L3 | 353 | 4 | 0 | 0 | 0 | 3 | 7 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\14_gat_async_boundary.md | L3 | 532 | 0 | 0 | 0 | 0 | 2 | 12 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\15_state_machine_semantics.md | L3 | 216 | 0 | 0 | 0 | 1 | 1 | 5 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\16_structured_concurrency.md | L3 | 223 | 0 | 0 | 0 | 2 | 1 | 3 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\00_before_formal.md | L3 | 210 | 0 | 0 | 0 | 3 | 2 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\01_unsafe.md | L3 | 3482 | 18 | 2 | 0 | 4 | 10 | 62 | 3 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\02_unsafe_boundary_panorama.md | L3 | 506 | 19 | 0 | 0 | 5 | 3 | 12 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\03_nll_and_polonius.md | L3 | 912 | 3 | 3 | 0 | 3 | 2 | 13 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\04_unsafe_rust_patterns.md | L3 | 87 | 3 | 0 | 0 | 1 | 1 | 2 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\05_quiz_unsafe.md | L3 | 704 | 0 | 0 | 0 | 0 | 0 | 21 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\06_memory_model.md | L3 | 689 | 5 | 2 | 0 | 1 | 1 | 15 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\07_unsafe_reference.md | L3 | 331 | 3 | 2 | 0 | 1 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\08_async_in_unsafe_contexts.md | L3 | 285 | 0 | 0 | 0 | 4 | 2 | 5 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\09_sanitizers.md | L3 | 426 | 0 | 0 | 0 | 3 | 1 | 3 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\10_std_unsafe_internals.md | L3 | 571 | 0 | 0 | 0 | 4 | 2 | 13 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\11_in_place_pinned_initialization.md | L3 | 628 | 0 | 0 | 0 | 5 | 2 | 15 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\01_macros.md | L3 | 2573 | 26 | 3 | 0 | 8 | 9 | 59 | 8 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\02_proc_macro.md | L3 | 11 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\03_proc_macro_code_generation_optimization.md | L3 | 447 | 7 | 2 | 0 | 1 | 1 | 13 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\04_macro_debugging_and_diagnostics.md | L3 | 439 | 7 | 2 | 0 | 1 | 1 | 9 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\05_production_grade_macro_development.md | L3 | 459 | 7 | 2 | 0 | 1 | 1 | 10 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\06_macro_glossary.md | L3 | 782 | 8 | 2 | 0 | 4 | 1 | 29 | 6 | ✅ | ✅ | ✅ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\07_macro_faq.md | L3 | 871 | 8 | 2 | 0 | 1 | 1 | 37 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\08_syn_quote_reference.md | L3 | 1266 | 8 | 3 | 0 | 2 | 1 | 36 | 6 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\09_macro_hygiene.md | L3 | 1008 | 8 | 2 | 0 | 2 | 1 | 32 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\10_quiz_macros.md | L3 | 771 | 0 | 0 | 0 | 0 | 0 | 24 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\11_conditional_compilation.md | L3 | 345 | 0 | 0 | 0 | 0 | 1 | 11 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\01_rust_ffi.md | L3 | 1155 | 3 | 3 | 0 | 2 | 4 | 22 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\02_ffi_advanced.md | L3 | 983 | 3 | 3 | 0 | 2 | 2 | 12 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\03_linkage.md | L3 | 491 | 1 | 0 | 0 | 1 | 1 | 16 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\04_async_ffi_boundary.md | L3 | 246 | 0 | 0 | 0 | 2 | 2 | 2 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\05_unsafe_extern_blocks.md | L3 | 572 | 0 | 0 | 0 | 3 | 2 | 14 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\06_ffi_deep_dive.md | L3 | 722 | 0 | 0 | 0 | 4 | 2 | 19 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\07_ffi_patterns.md | L3 | 635 | 0 | 0 | 0 | 6 | 2 | 14 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\05_inline_assembly\01_inline_assembly.md | L3 | 998 | 0 | 0 | 0 | 1 | 1 | 31 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\05_inline_assembly\02_inline_assembly_extended.md | L3 | 558 | 0 | 0 | 0 | 3 | 2 | 11 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\01_custom_allocators.md | L3 | 912 | 3 | 3 | 0 | 2 | 2 | 12 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\02_zero_copy_parsing.md | L3 | 952 | 3 | 3 | 0 | 2 | 2 | 13 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\03_type_erasure.md | L3 | 923 | 4 | 3 | 0 | 2 | 2 | 11 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\04_network_programming.md | L3 | 1111 | 3 | 3 | 0 | 2 | 3 | 16 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\05_stream_processing_semantics.md | L3 | 952 | 3 | 3 | 0 | 1 | 1 | 8 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\06_ownership_performance_optimization.md | L3 | 231 | 4 | 0 | 0 | 1 | 1 | 10 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\07_rust_runtime.md | L3 | 315 | 3 | 2 | 0 | 1 | 1 | 8 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\08_memory_allocation_and_lifetime.md | L3 | 208 | 0 | 0 | 0 | 0 | 1 | 8 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\09_variables.md | L3 | 209 | 0 | 0 | 0 | 0 | 1 | 8 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\10_visibility_and_privacy.md | L3 | 239 | 0 | 0 | 0 | 0 | 2 | 8 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\07_unsafe_internals\01_unsafe_collections_internals.md | L3 | 552 | 4 | 4 | 0 | 4 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\01_process_model_and_lifecycle.md | L3 | 526 | 8 | 2 | 0 | 2 | 2 | 5 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\02_advanced_process_management.md | L3 | 366 | 8 | 2 | 0 | 1 | 2 | 5 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\03_async_process_management.md | L3 | 441 | 8 | 2 | 0 | 2 | 2 | 11 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\04_cross_platform_process_management.md | L3 | 365 | 8 | 2 | 0 | 2 | 2 | 7 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\05_ipc_mechanisms.md | L3 | 327 | 8 | 2 | 0 | 1 | 2 | 8 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\06_process_monitoring_and_diagnostics.md | L3 | 349 | 8 | 2 | 0 | 1 | 2 | 7 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\07_process_security_and_sandboxing.md | L3 | 310 | 8 | 2 | 0 | 1 | 2 | 9 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\08_process_performance_engineering.md | L3 | 284 | 8 | 2 | 0 | 1 | 2 | 5 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\09_process_testing_and_benchmarking.md | L3 | 299 | 8 | 2 | 0 | 1 | 2 | 7 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\10_modern_process_libraries.md | L3 | 281 | 8 | 2 | 0 | 1 | 2 | 8 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\01_type_theory.md | L4 | 2563 | 29 | 0 | 0 | 12 | 6 | 40 | 3 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\02_subtype_variance.md | L4 | 715 | 6 | 0 | 0 | 2 | 3 | 11 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\03_type_inference.md | L4 | 794 | 3 | 0 | 0 | 2 | 3 | 9 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\04_category_theory.md | L4 | 862 | 3 | 0 | 0 | 2 | 2 | 11 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\05_lambda_calculus.md | L4 | 794 | 3 | 0 | 0 | 2 | 2 | 11 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\06_type_semantics.md | L4 | 980 | 5 | 0 | 0 | 3 | 1 | 18 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\07_type_checking_and_inference.md | L4 | 484 | 1 | 0 | 0 | 2 | 1 | 12 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\08_type_inference_complexity.md | L4 | 452 | 0 | 0 | 0 | 2 | 1 | 8 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\09_type_system_reference.md | L4 | 469 | 0 | 0 | 0 | 1 | 1 | 3 | 6 | ❌ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\10_dependent_refinement_types.md | L4 | 964 | 0 | 0 | 0 | 5 | 1 | 14 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\11_formal_design_pattern_theory.md | L4 | 1142 | 4 | 0 | 0 | 1 | 1 | 18 | 6 | ❌ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\12_pattern_composition_algebra.md | L4 | 792 | 3 | 0 | 0 | 2 | 1 | 15 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\13_formal_algorithm_theory.md | L4 | 339 | 3 | 0 | 0 | 0 | 1 | 6 | 6 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\14_flux.md | L4 | 507 | 0 | 0 | 0 | 6 | 1 | 18 | 0 | ❌ | ✅ | ✅ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\15_parametricity_and_theorems_for_free.md | L4 | 367 | 0 | 0 | 0 | 5 | 1 | 9 | 0 | ❌ | ✅ | ✅ | None | None |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\16_expressive_power.md | L4 | 362 | 0 | 0 | 0 | 4 | 1 | 9 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\17_system_f.md | L4 | 274 | 0 | 0 | 0 | 3 | 1 | 6 | 0 | ❌ | ✅ | ✅ | None | None |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\01_linear_logic.md | L4 | 1291 | 14 | 0 | 0 | 4 | 6 | 13 | 3 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\02_ownership_formal.md | L4 | 1722 | 11 | 0 | 0 | 1 | 6 | 18 | 3 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\03_linear_logic_applications.md | L4 | 778 | 3 | 0 | 0 | 2 | 2 | 10 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\04_borrow_checking_decidability.md | L4 | 467 | 3 | 0 | 0 | 1 | 3 | 10 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\05_tree_borrows_deep_dive.md | L4 | 309 | 0 | 0 | 0 | 1 | 1 | 6 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\06_behavior_considered_undefined.md | L4 | 290 | 0 | 0 | 0 | 0 | 1 | 2 | 0 | ❌ | ✅ | ✅ | 专家 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\07_unsafe_contracts_formal.md | L4 | 230 | 0 | 0 | 0 | 1 | 1 | 5 | 0 | ❌ | ✅ | ✅ | None | None |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\01_rustbelt.md | L4 | 1502 | 5 | 0 | 0 | 1 | 6 | 17 | 10 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\02_separation_logic.md | L4 | 871 | 4 | 0 | 0 | 2 | 2 | 10 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\03_safety_tags_in_formal.md | L4 | 23 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\04_borrow_sanitizer_in_formal.md | L4 | 229 | 0 | 0 | 0 | 1 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\01_denotational_semantics.md | L4 | 745 | 3 | 0 | 0 | 4 | 2 | 10 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\02_hoare_logic.md | L4 | 930 | 3 | 0 | 0 | 2 | 3 | 8 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\03_operational_semantics.md | L4 | 1224 | 3 | 0 | 0 | 2 | 2 | 15 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\04_evaluation_strategies.md | L4 | 721 | 0 | 0 | 0 | 2 | 1 | 14 | 0 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\05_axiomatic_semantics.md | L4 | 1135 | 5 | 0 | 0 | 4 | 1 | 15 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\06_observational_equivalence.md | L4 | 899 | 0 | 0 | 0 | 2 | 1 | 19 | 0 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\07_aeneas_symbolic_semantics.md | L4 | 491 | 1 | 0 | 0 | 0 | 2 | 4 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\08_constant_evaluation.md | L4 | 240 | 0 | 0 | 0 | 1 | 1 | 8 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\09_llvm_ir_poison_ub.md | L4 | 292 | 0 | 0 | 0 | 1 | 1 | 1 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\10_minirust.md | L4 | 269 | 0 | 0 | 0 | 1 | 1 | 4 | 0 | ❌ | ✅ | ✅ | None | None |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\11_async_state_machine_semantics.md | L4 | 313 | 1 | 0 | 0 | 1 | 1 | 7 | 0 | ❌ | ✅ | ✅ | None | None |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\12_pin_and_self_referential_semantics.md | L4 | 252 | 0 | 0 | 0 | 1 | 1 | 7 | 0 | ❌ | ✅ | ✅ | None | None |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\13_in_place_initialization_semantics.md | L4 | 290 | 0 | 0 | 0 | 3 | 1 | 1 | 0 | ❌ | ✅ | ✅ | 形式化 / 专家 | 形式化 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\01_verification_toolchain.md | L4 | 1601 | 3 | 0 | 0 | 0 | 5 | 17 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\02_formal_methods.md | L4 | 34 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\03_aerospace_certification_formal_methods.md | L4 | 1155 | 3 | 0 | 0 | 1 | 2 | 7 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\04_modern_verification_tools.md | L4 | 800 | 3 | 0 | 0 | 1 | 1 | 10 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\05_programming_language_foundations.md | L4 | 529 | 3 | 0 | 0 | 1 | 1 | 12 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\06_quiz_formal_methods.md | L4 | 715 | 0 | 0 | 0 | 0 | 1 | 10 | 0 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\07_autoverus.md | L4 | 250 | 1 | 0 | 0 | 1 | 1 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\08_miri.md | L4 | 379 | 0 | 0 | 0 | 3 | 2 | 4 | 0 | ❌ | ✅ | ✅ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\09_kani.md | L4 | 439 | 0 | 0 | 0 | 1 | 1 | 11 | 0 | ❌ | ✅ | ✅ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\10_certified_toolchains_and_packages.md | L4 | 274 | 0 | 0 | 0 | 1 | 2 | 2 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\11_creusot.md | L4 | 601 | 0 | 0 | 0 | 1 | 2 | 11 | 0 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\12_rust_contracts.md | L4 | 366 | 0 | 0 | 0 | 3 | 1 | 12 | 0 | ❌ | ✅ | ✅ | None | None |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\01_rustc_query_system.md | L4 | 653 | 1 | 0 | 0 | 1 | 4 | 5 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\02_mir_codegen_llvm_primer.md | L4 | 486 | 8 | 3 | 0 | 2 | 2 | 3 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\03_trait_solver_in_rustc.md | L4 | 484 | 3 | 3 | 0 | 1 | 2 | 10 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\04_name_resolution_and_hir.md | L4 | 375 | 0 | 0 | 0 | 3 | 2 | 7 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\05_application_binary_interface.md | L4 | 311 | 0 | 0 | 0 | 1 | 1 | 8 | 0 | ❌ | ✅ | ✅ | 专家 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\06_names_and_resolution.md | L4 | 291 | 2 | 0 | 0 | 1 | 1 | 4 | 6 | ✅ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\07_special_types_and_traits.md | L4 | 256 | 2 | 0 | 0 | 0 | 1 | 2 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\08_type_layout.md | L4 | 206 | 0 | 0 | 0 | 0 | 1 | 6 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\09_destructors.md | L4 | 241 | 0 | 0 | 0 | 0 | 1 | 5 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\10_lexical_structure.md | L4 | 301 | 3 | 0 | 0 | 1 | 1 | 8 | 6 | ✅ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\11_items_reference.md | L4 | 302 | 3 | 0 | 0 | 1 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\12_attributes.md | L4 | 233 | 3 | 0 | 0 | 1 | 1 | 7 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\13_statements_and_expressions_reference.md | L4 | 213 | 3 | 0 | 0 | 1 | 1 | 7 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\14_patterns_reference.md | L4 | 209 | 3 | 0 | 0 | 1 | 1 | 6 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\15_generics_compiler_behavior.md | L4 | 227 | 4 | 0 | 0 | 1 | 1 | 7 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\16_names_reference.md | L4 | 207 | 3 | 0 | 0 | 1 | 1 | 4 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\17_reference_appendices.md | L4 | 215 | 2 | 0 | 0 | 1 | 1 | 3 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\06_notation\01_notation.md | L4 | 190 | 0 | 0 | 0 | 0 | 2 | 2 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\07_concurrency_semantics\01_process_calculi_for_rust.md | L4 | 388 | 6 | 0 | 0 | 4 | 2 | 6 | 8 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\07_concurrency_semantics\02_linearizability_and_consistency.md | L4 | 372 | 10 | 0 | 0 | 3 | 2 | 2 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\07_concurrency_semantics\03_actor_semantics.md | L4 | 353 | 18 | 0 | 0 | 3 | 2 | 4 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\07_concurrency_semantics\04_algebraic_effects.md | L4 | 825 | 0 | 0 | 0 | 4 | 1 | 5 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\07_concurrency_semantics\05_stm_semantics.md | L4 | 858 | 1 | 0 | 0 | 5 | 1 | 5 | 2 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\07_concurrency_semantics\06_distributed_consensus_theory.md | L4 | 905 | 26 | 0 | 0 | 7 | 1 | 3 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\07_concurrency_semantics\07_session_types.md | L4 | 313 | 0 | 0 | 0 | 3 | 1 | 4 | 0 | ❌ | ✅ | ✅ | None | None |
| E:\_src\rust-lang\concept\04_formal\07_concurrency_semantics\08_send_sync_semantics.md | L4 | 241 | 0 | 0 | 0 | 1 | 1 | 3 | 0 | ❌ | ✅ | ✅ | None | None |
| E:\_src\rust-lang\concept\04_formal\08_algorithm_semantics\01_hoare_logic_for_rust.md | L4 | 440 | 0 | 0 | 0 | 0 | 1 | 10 | 0 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\08_algorithm_semantics\02_refinement_calculus.md | L4 | 758 | 0 | 0 | 0 | 2 | 2 | 7 | 0 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\08_algorithm_semantics\03_iterator_correctness.md | L4 | 1003 | 0 | 0 | 0 | 2 | 1 | 14 | 0 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\08_algorithm_semantics\04_unsafe_algorithm_invariants.md | L4 | 580 | 0 | 0 | 0 | 2 | 1 | 11 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\04_formal\08_algorithm_semantics\05_algorithm_equivalence.md | L4 | 772 | 0 | 0 | 0 | 2 | 2 | 9 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\04_formal\09_system_semantics\01_actor_model_semantics.md | L4 | 88 | 0 | 0 | 0 | 1 | 1 | 1 | 0 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\09_system_semantics\02_pi_calculus_for_rust.md | L4 | 122 | 0 | 0 | 0 | 1 | 1 | 2 | 0 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\09_system_semantics\03_component_based_semantics.md | L4 | 601 | 5 | 0 | 0 | 2 | 1 | 7 | 4 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\09_system_semantics\04_distributed_systems_semantics.md | L4 | 461 | 1 | 0 | 0 | 2 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\09_system_semantics\05_reactive_systems_semantics.md | L4 | 562 | 2 | 0 | 0 | 2 | 1 | 7 | 8 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\09_system_semantics\06_systems_engineering_standards.md | L4 | 718 | 0 | 0 | 0 | 2 | 1 | 5 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\09_system_semantics\07_concurrent_and_parallel_semantics.md | L4 | 251 | 0 | 0 | 0 | 2 | 1 | 4 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\09_system_semantics\08_memory_ordering_and_atomics.md | L4 | 638 | 2 | 0 | 0 | 3 | 2 | 13 | 0 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\10_architecture_semantics\01_software_architecture_formalization.md | L4 | 620 | 0 | 0 | 0 | 2 | 1 | 2 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\04_formal\10_architecture_semantics\02_architecture_pattern_semantics.md | L4 | 679 | 0 | 0 | 0 | 2 | 1 | 7 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\04_formal\10_architecture_semantics\03_architecture_refinement.md | L4 | 502 | 0 | 0 | 0 | 2 | 1 | 4 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\04_formal\10_architecture_semantics\04_rust_architecture_constraints.md | L4 | 302 | 0 | 0 | 0 | 4 | 1 | 5 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\04_formal\10_architecture_semantics\05_architecture_styles_formal_constraints.md | L4 | 431 | 0 | 0 | 0 | 3 | 2 | 3 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\04_formal\11_computational_models\01_computational_semantics_framework.md | L4 | 363 | 0 | 0 | 0 | 1 | 1 | 4 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\04_formal\11_computational_models\02_computability_theory.md | L4 | 986 | 0 | 0 | 0 | 1 | 1 | 14 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\04_formal\11_computational_models\03_formal_languages_and_automata.md | L4 | 1182 | 0 | 0 | 0 | 2 | 2 | 15 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\04_formal\11_computational_models\04_mathematical_functions_of_computation.md | L4 | 852 | 0 | 0 | 0 | 1 | 1 | 19 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\04_formal\11_computational_models\05_equivalence_of_computational_models.md | L4 | 1221 | 0 | 0 | 0 | 1 | 1 | 17 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\04_formal\11_computational_models\06_computational_equivalence_in_rust.md | L4 | 581 | 0 | 0 | 0 | 1 | 2 | 6 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\04_formal\11_computational_models\07_type_theory_and_rust.md | L4 | 504 | 0 | 1 | 0 | 5 | 1 | 11 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\04_formal\11_computational_models\08_separation_logic_for_rust.md | L4 | 506 | 0 | 0 | 0 | 5 | 1 | 10 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\04_formal\11_computational_models\09_concurrency_models_actors_csp.md | L4 | 502 | 0 | 0 | 0 | 4 | 1 | 9 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\04_formal\12_concurrency_models\01_models_of_concurrency.md | L4 | 454 | 0 | 0 | 0 | 6 | 1 | 11 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\04_formal\12_concurrency_models\02_expressiveness_of_concurrent_models.md | L4 | 598 | 4 | 0 | 0 | 4 | 1 | 9 | 0 | ✅ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\04_formal\12_concurrency_models\03_parallel_concurrent_async_distributed_semantics.md | L4 | 565 | 0 | 0 | 0 | 3 | 2 | 10 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\04_formal\13_semantic_engineering\01_ontology_engineering.md | L4 | 356 | 0 | 0 | 0 | 3 | 1 | 3 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\04_formal\13_semantic_engineering\02_description_logic_and_owl.md | L4 | 487 | 0 | 0 | 0 | 4 | 2 | 5 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\04_formal\13_semantic_engineering\03_knowledge_graph_construction.md | L4 | 417 | 0 | 0 | 0 | 3 | 1 | 5 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\04_formal\13_semantic_engineering\04_semantic_interoperability.md | L4 | 353 | 0 | 0 | 0 | 3 | 1 | 3 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\04_formal\13_semantic_engineering\05_knowledge_graph_reasoning.md | L4 | 322 | 0 | 0 | 0 | 3 | 1 | 3 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\04_formal\13_semantic_engineering\06_ai_ontology_and_rust_semantics.md | L4 | 603 | 0 | 0 | 0 | 4 | 1 | 0 | 2 | ❌ | ✅ | ✅ | None | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\13_semantic_engineering\07_kg_owl_shacl_semantics.md | L4 | 486 | 0 | 0 | 0 | 4 | 1 | 0 | 2 | ❌ | ✅ | ✅ | None | None |
| E:\_src\rust-lang\concept\04_formal\13_semantic_engineering\08_computational_semantic_models.md | L4 | 655 | 0 | 0 | 0 | 5 | 1 | 9 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\04_formal\14_embedded_semantics\01_embedded_formal_memory_model.md | L4 | 365 | 0 | 0 | 0 | 1 | 2 | 9 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\04_formal\15_language_specification\00_language_specification_overview.md | L4 | 142 | 0 | 0 | 0 | 1 | 1 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\04_formal\15_language_specification\01_rust_reference_and_normative_gap.md | L4 | 159 | 0 | 0 | 0 | 1 | 1 | 2 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\04_formal\15_language_specification\02_ferrocene_language_specification.md | L4 | 186 | 0 | 0 | 0 | 1 | 1 | 2 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\04_formal\15_language_specification\03_executable_specification_minirust.md | L4 | 199 | 0 | 0 | 0 | 1 | 1 | 3 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\04_formal\15_language_specification\04_a_mir_formality_type_system_spec.md | L4 | 199 | 0 | 0 | 0 | 1 | 1 | 2 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\04_formal\15_language_specification\05_specification_evidence_from_rustc_tests.md | L4 | 171 | 0 | 0 | 0 | 1 | 1 | 1 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\05_comparative\00_paradigms\01_paradigm_matrix.md | L5 | 1307 | 8 | 0 | 0 | 5 | 9 | 12 | 16 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\00_paradigms\02_execution_model_isomorphism.md | L5 | 1059 | 3 | 0 | 0 | 1 | 6 | 13 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\05_comparative\00_paradigms\03_cpp_rust_surface_features.md | L5 | 296 | 0 | 0 | 0 | 0 | 1 | 4 | 0 | ❌ | ✅ | ✅ | 进阶 | 研究者级 |
| E:\_src\rust-lang\concept\05_comparative\00_paradigms\04_five_models_definition_matrix.md | L5 | 156 | 10 | 0 | 0 | 0 | 2 | 0 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\00_paradigms\05_language_semantic_model_matrix.md | L5 | 625 | 4 | 0 | 0 | 11 | 2 | 0 | 2 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\01_rust_vs_cpp.md | L5 | 2281 | 9 | 0 | 0 | 3 | 11 | 14 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\02_cpp_abi_object_model.md | L5 | 975 | 4 | 0 | 0 | 2 | 1 | 18 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\03_rust_vs_go.md | L5 | 1038 | 3 | 0 | 0 | 3 | 7 | 11 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\04_rust_vs_ruby.md | L5 | 786 | 3 | 0 | 0 | 2 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\05_rust_vs_swift.md | L5 | 766 | 3 | 0 | 0 | 2 | 2 | 6 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\06_rust_vs_zig.md | L5 | 800 | 3 | 0 | 0 | 2 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\07_rust_vs_ada_spark.md | L5 | 676 | 0 | 0 | 0 | 5 | 1 | 4 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\08_rust_vs_d.md | L5 | 790 | 0 | 0 | 0 | 5 | 1 | 8 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\09_rust_vs_nim.md | L5 | 727 | 0 | 0 | 0 | 5 | 1 | 4 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\01_rust_vs_java.md | L5 | 658 | 3 | 0 | 0 | 2 | 4 | 7 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\02_rust_vs_python.md | L5 | 747 | 3 | 0 | 0 | 2 | 3 | 6 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\03_rust_vs_javascript.md | L5 | 758 | 3 | 0 | 0 | 2 | 3 | 5 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\04_rust_vs_kotlin.md | L5 | 850 | 3 | 0 | 0 | 2 | 2 | 6 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\05_rust_vs_scala.md | L5 | 810 | 3 | 0 | 0 | 2 | 2 | 6 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\06_rust_vs_csharp.md | L5 | 904 | 4 | 0 | 0 | 2 | 2 | 6 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\07_rust_vs_elixir.md | L5 | 987 | 3 | 0 | 0 | 3 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\08_rust_vs_typescript.md | L5 | 974 | 3 | 0 | 0 | 2 | 3 | 6 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\09_rust_vs_haskell.md | L5 | 866 | 0 | 0 | 0 | 2 | 1 | 9 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\10_rust_vs_ocaml.md | L5 | 837 | 0 | 0 | 0 | 2 | 2 | 10 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\11_rust_vs_fsharp.md | L5 | 893 | 0 | 0 | 0 | 7 | 2 | 8 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\03_domain_comparisons\01_safety_boundaries.md | L5 | 1182 | 8 | 0 | 0 | 1 | 8 | 9 | 9 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\05_comparative\03_domain_comparisons\02_quiz_rust_vs_systems.md | L5 | 803 | 0 | 0 | 0 | 0 | 0 | 14 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\04_verification_and_contracts\00_verification_and_contracts_overview.md | L5 | 167 | 0 | 0 | 0 | 2 | 1 | 1 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\05_comparative\04_verification_and_contracts\01_contracts_comparison.md | L5 | 275 | 0 | 0 | 0 | 2 | 1 | 6 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\01_toolchain.md | L6 | 2068 | 13 | 0 | 0 | 2 | 10 | 16 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\02_logging_observability.md | L6 | 784 | 3 | 0 | 0 | 2 | 4 | 9 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\03_devops_and_ci_cd.md | L6 | 1148 | 3 | 0 | 0 | 2 | 3 | 7 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\04_compiler_internals.md | L6 | 918 | 3 | 0 | 0 | 2 | 1 | 7 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\05_compiler_infrastructure.md | L6 | 334 | 3 | 0 | 0 | 1 | 1 | 1 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\06_quiz_toolchain.md | L6 | 668 | 0 | 0 | 0 | 1 | 0 | 9 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\07_rustdoc_196_changes.md | L6 | 368 | 0 | 0 | 0 | 0 | 1 | 4 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\08_platform_rust_integration.md | L6 | 361 | 0 | 0 | 0 | 1 | 1 | 6 | 2 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\09_llvm_backend_and_codegen.md | L6 | 368 | 0 | 0 | 0 | 0 | 1 | 1 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\10_rustc_driver_and_stable_mir.md | L6 | 295 | 0 | 0 | 0 | 0 | 1 | 4 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\11_compiler_diagnostics_and_ui_tests.md | L6 | 308 | 0 | 0 | 0 | 0 | 1 | 5 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\12_rustc_bootstrap.md | L6 | 293 | 0 | 0 | 0 | 1 | 1 | 3 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\13_compiler_testing.md | L6 | 309 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\14_development_tools.md | L6 | 273 | 0 | 0 | 0 | 1 | 1 | 7 | 0 | ❌ | ✅ | ✅ | 初学者 | 入门级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\15_z_flags_reference.md | L6 | 198 | 0 | 0 | 0 | 1 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\16_rustdoc_internals.md | L6 | 655 | 0 | 0 | 0 | 3 | 1 | 13 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\01_cargo_script.md | L6 | 782 | 3 | 0 | 0 | 1 | 3 | 12 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\02_public_private_deps.md | L6 | 317 | 4 | 0 | 0 | 1 | 2 | 2 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\03_resolver_v3_public_feature_unification.md | L6 | 231 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\04_cargo_196_features.md | L6 | 355 | 0 | 0 | 0 | 1 | 1 | 3 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\05_cargo_build_scripts.md | L6 | 573 | 0 | 0 | 0 | 3 | 3 | 16 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\06_cargo_dependency_resolution.md | L6 | 596 | 0 | 0 | 0 | 1 | 1 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
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
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\23_cargo_197_features.md | L6 | 304 | 0 | 0 | 0 | 1 | 1 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\02_core_crates\01_core_crates.md | L6 | 413 | 0 | 0 | 0 | 1 | 3 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\02_core_crates\02_serde.md | L6 | 452 | 0 | 0 | 0 | 0 | 1 | 10 | 0 | ❌ | ✅ | ✅ | None | None |
| E:\_src\rust-lang\concept\06_ecosystem\02_core_crates\03_tokio.md | L6 | 412 | 0 | 0 | 0 | 0 | 1 | 11 | 0 | ❌ | ✅ | ✅ | None | None |
| E:\_src\rust-lang\concept\06_ecosystem\02_core_crates\04_clap.md | L6 | 486 | 0 | 0 | 0 | 0 | 1 | 9 | 0 | ❌ | ✅ | ✅ | None | None |
| E:\_src\rust-lang\concept\06_ecosystem\02_core_crates\05_tracing.md | L6 | 409 | 0 | 0 | 0 | 0 | 1 | 9 | 0 | ❌ | ✅ | ✅ | None | None |
| E:\_src\rust-lang\concept\06_ecosystem\02_core_crates\06_reqwest.md | L6 | 415 | 0 | 0 | 0 | 0 | 1 | 9 | 0 | ❌ | ✅ | ✅ | None | None |
| E:\_src\rust-lang\concept\06_ecosystem\02_core_crates\07_axum.md | L6 | 471 | 0 | 0 | 0 | 0 | 1 | 8 | 0 | ❌ | ✅ | ✅ | None | None |
| E:\_src\rust-lang\concept\06_ecosystem\02_core_crates\08_sqlx.md | L6 | 345 | 0 | 0 | 0 | 0 | 1 | 5 | 0 | ❌ | ✅ | ✅ | None | None |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\01_patterns.md | L6 | 5166 | 18 | 0 | 0 | 2 | 16 | 85 | 8 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\02_idioms_spectrum.md | L6 | 4004 | 4 | 0 | 0 | 1 | 42 | 100 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\03_system_design_principles.md | L6 | 860 | 3 | 0 | 0 | 1 | 7 | 10 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\04_system_composability.md | L6 | 848 | 0 | 0 | 0 | 0 | 5 | 23 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\05_microservice_patterns.md | L6 | 1046 | 3 | 0 | 0 | 1 | 7 | 15 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\06_event_driven_architecture.md | L6 | 1061 | 3 | 0 | 0 | 1 | 5 | 15 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\07_cqrs_event_sourcing.md | L6 | 1580 | 3 | 0 | 0 | 3 | 2 | 20 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\08_architecture_patterns.md | L6 | 1551 | 3 | 0 | 0 | 2 | 1 | 13 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\09_pattern_implementation_comparison.md | L6 | 1011 | 4 | 0 | 0 | 1 | 1 | 19 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\10_pattern_selection_best_practices.md | L6 | 849 | 4 | 0 | 0 | 1 | 1 | 13 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\11_formal_design_pattern_theory.md | L6 | 15 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\12_frontier_research_and_innovative_patterns.md | L6 | 1086 | 4 | 0 | 0 | 1 | 1 | 19 | 6 | ❌ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\13_engineering_and_production_patterns.md | L6 | 380 | 3 | 0 | 0 | 1 | 1 | 9 | 6 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\14_design_patterns_glossary.md | L6 | 323 | 4 | 0 | 0 | 1 | 1 | 6 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\15_design_patterns_faq.md | L6 | 566 | 4 | 0 | 0 | 0 | 1 | 5 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\16_pattern_composition_algebra.md | L6 | 15 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\17_workflow_theory.md | L6 | 1481 | 3 | 0 | 0 | 2 | 1 | 17 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\18_api_design_patterns.md | L6 | 1408 | 3 | 0 | 0 | 3 | 1 | 21 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\19_model_driven_engineering.md | L6 | 543 | 0 | 0 | 0 | 6 | 1 | 5 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\21_microkernel_architecture.md | L6 | 320 | 0 | 0 | 0 | 0 | 1 | 5 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\22_embedded_safety_critical_patterns.md | L6 | 475 | 0 | 0 | 0 | 0 | 1 | 11 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\23_pipeline_filter_blackboard_interpreter.md | L6 | 460 | 0 | 0 | 0 | 0 | 1 | 7 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\24_repository_and_unit_of_work.md | L6 | 189 | 0 | 0 | 0 | 2 | 2 | 3 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\25_hexagonal_ports_and_adapters.md | L6 | 188 | 0 | 0 | 0 | 2 | 2 | 4 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\26_circuit_breaker.md | L6 | 234 | 0 | 0 | 0 | 2 | 2 | 2 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\27_bulkhead.md | L6 | 182 | 0 | 0 | 0 | 2 | 2 | 3 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\28_retry.md | L6 | 183 | 0 | 0 | 0 | 2 | 2 | 2 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\29_saga.md | L6 | 198 | 0 | 0 | 0 | 2 | 2 | 3 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\30_outbox.md | L6 | 203 | 0 | 0 | 0 | 2 | 2 | 3 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\31_object_pool.md | L6 | 169 | 0 | 0 | 0 | 2 | 2 | 2 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\32_typestate_deep_dive.md | L6 | 201 | 0 | 0 | 0 | 2 | 2 | 3 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\33_anti_patterns.md | L6 | 776 | 0 | 0 | 0 | 8 | 2 | 21 | 0 | ❌ | ✅ | ✅ | 进阶 | 进阶 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\34_ownership_as_resource_management.md | L6 | 457 | 1 | 0 | 0 | 1 | 2 | 11 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\35_scope_guard_and_deferred_cleanup.md | L6 | 476 | 0 | 0 | 0 | 1 | 2 | 11 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\36_enterprise_and_software_architecture_alignment.md | L6 | 631 | 0 | 0 | 0 | 5 | 3 | 9 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\37_event_sourcing_engine_patterns.md | L6 | 721 | 0 | 0 | 0 | 4 | 2 | 13 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\38_api_gateway_and_service_mesh_patterns.md | L6 | 584 | 0 | 0 | 0 | 4 | 2 | 14 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\39_api_design_and_semver_idioms.md | L6 | 599 | 0 | 0 | 0 | 4 | 2 | 8 | 4 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\40_testing_and_mocking_idioms.md | L6 | 831 | 0 | 0 | 0 | 1 | 2 | 18 | 0 | ❌ | ✅ | ✅ | None | None |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\41_ecs_and_data_oriented_design_patterns.md | L6 | 487 | 0 | 0 | 0 | 3 | 3 | 5 | 0 | ❌ | ✅ | ✅ | None | None |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\42_actor_model_and_message_passing_patterns.md | L6 | 382 | 0 | 0 | 0 | 2 | 2 | 4 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\43_rejection_type_pattern.md | L6 | 543 | 0 | 0 | 0 | 3 | 2 | 8 | 0 | ❌ | ✅ | ✅ | None | 进阶级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\44_configuration_management_patterns.md | L6 | 905 | 0 | 0 | 0 | 5 | 2 | 19 | 0 | ❌ | ✅ | ✅ | None | 进阶级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\45_dependency_injection_in_rust.md | L6 | 529 | 0 | 0 | 0 | 4 | 2 | 9 | 0 | ❌ | ✅ | ✅ | None | 进阶级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\47_rust_design_and_architecture_patterns_semantic_atlas.md | L6 | 1879 | 0 | 0 | 0 | 1 | 2 | 43 | 0 | ❌ | ✅ | ✅ | None | None |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\48_api_guidelines_idioms.md | L6 | 770 | 0 | 0 | 0 | 3 | 1 | 32 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\49_gof_patterns_in_rust.md | L6 | 1383 | 0 | 0 | 0 | 1 | 2 | 30 | 0 | ❌ | ✅ | ✅ | None | None |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\50_rust_idioms_atlas.md | L6 | 211 | 0 | 0 | 0 | 1 | 2 | 1 | 0 | ❌ | ✅ | ✅ | None | None |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\51_anti_patterns_and_pitfalls.md | L6 | 445 | 0 | 0 | 0 | 0 | 2 | 18 | 0 | ❌ | ✅ | ✅ | None | None |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\52_performance_idioms.md | L6 | 494 | 0 | 0 | 0 | 0 | 2 | 19 | 0 | ❌ | ✅ | ✅ | None | None |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\01_distributed_systems.md | L6 | 853 | 3 | 0 | 0 | 2 | 2 | 9 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\02_cloud_native.md | L6 | 848 | 3 | 0 | 0 | 2 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\03_web_frameworks.md | L6 | 1165 | 4 | 0 | 0 | 3 | 4 | 12 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\04_http_client_development.md | L6 | 247 | 0 | 0 | 0 | 0 | 1 | 10 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\05_glommio_and_thread_per_core.md | L6 | 285 | 3 | 0 | 0 | 0 | 1 | 7 | 6 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\06_websocket_realtime_communication.md | L6 | 857 | 4 | 0 | 0 | 0 | 1 | 12 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\07_network_protocols.md | L6 | 591 | 3 | 0 | 0 | 1 | 1 | 9 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\08_high_performance_network_service_architecture.md | L6 | 2471 | 3 | 0 | 0 | 0 | 1 | 28 | 6 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\09_reactive_programming.md | L6 | 1142 | 3 | 0 | 0 | 2 | 1 | 14 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\10_tokio_runtime_internals.md | L6 | 358 | 8 | 0 | 0 | 1 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\11_kubernetes_rust.md | L6 | 669 | 0 | 0 | 0 | 4 | 1 | 4 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\01_wasi.md | L6 | 699 | 4 | 0 | 0 | 4 | 3 | 11 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\02_cross_compilation.md | L6 | 696 | 3 | 0 | 0 | 2 | 2 | 5 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\03_embedded_systems.md | L6 | 1038 | 3 | 0 | 0 | 2 | 2 | 10 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\04_cli_development.md | L6 | 832 | 3 | 0 | 0 | 2 | 2 | 9 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\05_os_kernel.md | L6 | 552 | 3 | 0 | 0 | 1 | 1 | 12 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\06_robotics.md | L6 | 1093 | 3 | 0 | 0 | 2 | 1 | 15 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\07_embedded_graphics.md | L6 | 1217 | 3 | 0 | 0 | 3 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\08_c_to_rust_translation.md | L6 | 499 | 3 | 0 | 0 | 1 | 1 | 4 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\09_embedded_hal_1_0_migration.md | L6 | 330 | 3 | 0 | 0 | 0 | 1 | 6 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\10_target_tier_platform_support.md | L6 | 188 | 0 | 0 | 0 | 1 | 1 | 3 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\11_async_no_std_embedded.md | L6 | 248 | 0 | 0 | 0 | 2 | 2 | 3 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\12_gpu_programming_and_hpc.md | L6 | 908 | 0 | 0 | 0 | 6 | 1 | 10 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\13_bare_metal_boot_linker_script.md | L6 | 564 | 0 | 0 | 0 | 1 | 3 | 11 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\14_interrupt_and_exception_model.md | L6 | 385 | 0 | 0 | 0 | 1 | 2 | 9 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\15_no_std_synchronization_primitives.md | L6 | 469 | 0 | 0 | 0 | 1 | 3 | 11 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\16_embedded_memory_allocators.md | L6 | 497 | 0 | 0 | 0 | 1 | 3 | 10 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\17_pac_hal_implementation.md | L6 | 440 | 0 | 0 | 0 | 1 | 2 | 14 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\18_panic_runtime_no_std.md | L6 | 388 | 0 | 0 | 0 | 1 | 3 | 10 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\19_safety_critical_bare_metal_os.md | L6 | 615 | 0 | 0 | 0 | 1 | 1 | 8 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\20_embedded_debugging_logging.md | L6 | 736 | 0 | 0 | 0 | 2 | 1 | 10 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\21_riscv_avr_embedded.md | L6 | 626 | 0 | 0 | 0 | 0 | 1 | 10 | 0 | ❌ | ✅ | ✅ | 进阶 | 专题级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\22_embedded_protocol_drivers.md | L6 | 972 | 0 | 0 | 0 | 2 | 1 | 25 | 0 | ❌ | ✅ | ✅ | 进阶 | None |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\23_no_std_and_bare_metal_idioms.md | L6 | 1340 | 0 | 0 | 0 | 1 | 3 | 24 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\24_embedded_hal_and_driver_idioms.md | L6 | 621 | 0 | 0 | 0 | 1 | 3 | 15 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\25_memory_mapped_peripherals_and_typestate.md | L6 | 635 | 0 | 0 | 0 | 1 | 4 | 13 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\26_embedded_rtos_and_safety_critical_frameworks.md | L6 | 520 | 0 | 0 | 0 | 4 | 3 | 6 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\27_no_std_startup_runtime_deep_dive.md | L6 | 563 | 0 | 0 | 0 | 1 | 3 | 6 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\28_custom_bare_metal_async_executor.md | L6 | 450 | 0 | 0 | 0 | 1 | 2 | 8 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\29_embedded_memory_layout_and_heap_safety.md | L6 | 426 | 0 | 0 | 0 | 1 | 2 | 4 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\30_misra_rust_safety_critical_guidelines.md | L6 | 327 | 0 | 0 | 0 | 1 | 2 | 3 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\31_embedded_networking_and_iot_protocols.md | L6 | 676 | 0 | 0 | 0 | 1 | 3 | 9 | 0 | ❌ | ✅ | ✅ | 专家 | 专题深度 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\32_embedded_testing_and_ci_strategies.md | L6 | 629 | 0 | 0 | 0 | 2 | 2 | 5 | 0 | ❌ | ✅ | ✅ | 进阶/专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\33_sei_cert_c_to_rust_mapping.md | L6 | 474 | 0 | 0 | 0 | 3 | 2 | 14 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\34_embassy_framework_deep_dive.md | L6 | 855 | 0 | 0 | 0 | 3 | 3 | 15 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\35_rtic_framework_deep_dive.md | L6 | 587 | 0 | 0 | 0 | 4 | 3 | 9 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\36_defmt_probe_rs_architecture.md | L6 | 669 | 0 | 0 | 0 | 4 | 3 | 7 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\37_fallible_allocation_and_no_alloc_collections.md | L6 | 451 | 0 | 0 | 0 | 5 | 2 | 12 | 0 | ❌ | ✅ | ✅ | None | 进阶级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\38_no_std_bare_metal_rust.md | L6 | 1987 | 0 | 0 | 0 | 9 | 4 | 46 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\39_no_std_hardware_measurement_and_validation.md | L6 | 751 | 0 | 0 | 0 | 6 | 3 | 12 | 0 | ❌ | ✅ | ✅ | 进阶/专家 | 进阶/专家 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\41_embedded_hal_and_mmio.md | L6 | 1098 | 0 | 0 | 0 | 8 | 2 | 48 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\42_interrupts_and_concurrency_on_bare_metal.md | L6 | 1093 | 0 | 0 | 0 | 9 | 3 | 37 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\43_rust_safety_critical_systems.md | L6 | 1352 | 0 | 0 | 0 | 1 | 3 | 24 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\45_embedded_hardware_validation.md | L6 | 635 | 0 | 0 | 0 | 6 | 4 | 5 | 0 | ❌ | ✅ | ✅ | 进阶/专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\46_rtos_and_scheduling_in_rust.md | L6 | 558 | 0 | 0 | 0 | 5 | 4 | 9 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\47_bare_metal_rust.md | L6 | 749 | 0 | 0 | 0 | 4 | 3 | 18 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\48_no_std_alloc_crate_ecosystem.md | L6 | 603 | 0 | 0 | 0 | 3 | 3 | 15 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\49_embedded_hal_driver_patterns.md | L6 | 596 | 0 | 0 | 0 | 0 | 3 | 10 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\01_application_domains.md | L6 | 1617 | 8 | 0 | 0 | 2 | 7 | 12 | 3 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\02_database_access.md | L6 | 883 | 3 | 0 | 0 | 2 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\03_stream_processing_ecosystem.md | L6 | 637 | 3 | 0 | 0 | 1 | 1 | 12 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\04_database_systems.md | L6 | 617 | 3 | 0 | 0 | 1 | 1 | 11 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\05_data_engineering.md | L6 | 1211 | 3 | 0 | 0 | 2 | 1 | 16 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\06_distributed_consensus.md | L6 | 994 | 4 | 0 | 0 | 2 | 1 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\07_rust_for_data_science.md | L6 | 683 | 3 | 0 | 0 | 2 | 1 | 10 | 0 | ✅ | ✅ | ✅ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\08_crdt_type_zoo.md | L6 | 367 | 17 | 0 | 0 | 6 | 1 | 6 | 4 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\09_causal_ordering_vector_clocks.md | L6 | 329 | 9 | 0 | 0 | 5 | 1 | 1 | 4 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\10_data_intensive_systems_design.md | L6 | 691 | 0 | 0 | 0 | 3 | 2 | 5 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\11_distributed_systems_protocols.md | L6 | 757 | 0 | 0 | 0 | 3 | 2 | 6 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\07_security_and_cryptography\01_security_practices.md | L6 | 1324 | 3 | 0 | 0 | 2 | 2 | 14 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\07_security_and_cryptography\02_security_cryptography.md | L6 | 1035 | 3 | 0 | 0 | 3 | 1 | 18 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\07_security_and_cryptography\03_cargo_vet_supply_chain.md | L6 | 256 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\07_security_and_cryptography\04_security_architecture.md | L6 | 832 | 0 | 0 | 0 | 3 | 2 | 8 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\08_formal_verification\01_formal_ecosystem_tower.md | L6 | 639 | 1 | 0 | 0 | 1 | 3 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\08_formal_verification\02_formal_verification_tools.md | L6 | 1023 | 3 | 0 | 0 | 3 | 1 | 13 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_testing_and_quality\01_testing_strategies.md | L6 | 759 | 3 | 0 | 0 | 2 | 3 | 9 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_testing_and_quality\02_documentation.md | L6 | 713 | 3 | 0 | 0 | 3 | 3 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_testing_and_quality\03_testing.md | L6 | 807 | 3 | 0 | 0 | 3 | 3 | 10 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_testing_and_quality\04_benchmarking.md | L6 | 250 | 0 | 0 | 0 | 0 | 1 | 7 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\10_performance\01_performance_optimization.md | L6 | 1406 | 3 | 0 | 0 | 2 | 2 | 18 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\10_performance\02_performance_engineering_architecture.md | L6 | 1102 | 0 | 0 | 0 | 3 | 2 | 17 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\10_performance\03_algorithms_and_complexity_idioms.md | L6 | 222 | 0 | 0 | 0 | 2 | 2 | 5 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\01_blockchain.md | L6 | 978 | 7 | 0 | 0 | 0 | 3 | 15 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\02_game_ecs.md | L6 | 1415 | 1 | 0 | 0 | 1 | 8 | 25 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\03_webassembly.md | L6 | 716 | 3 | 0 | 0 | 2 | 4 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\04_licensing_and_compliance.md | L6 | 706 | 3 | 0 | 0 | 2 | 2 | 6 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\05_game_development.md | L6 | 709 | 3 | 0 | 0 | 2 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\06_game_development.md | L6 | 34 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\07_algorithms_competitive_programming.md | L6 | 1366 | 0 | 0 | 0 | 1 | 1 | 31 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\08_algorithm_engineering_practice.md | L6 | 2440 | 3 | 0 | 0 | 1 | 2 | 30 | 6 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\09_data_structures_in_rust.md | L6 | 11 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\10_algorithm_complexity_analysis.md | L6 | 335 | 0 | 0 | 0 | 0 | 2 | 8 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\11_cutting_edge_algorithms.md | L6 | 291 | 3 | 0 | 0 | 0 | 1 | 4 | 6 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\12_formal_algorithm_theory.md | L6 | 23 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\13_machine_learning_ecosystem.md | L6 | 1141 | 3 | 0 | 0 | 2 | 1 | 17 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\14_industrial_case_studies.md | L6 | 543 | 3 | 0 | 0 | 1 | 1 | 7 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\15_game_engine_internals.md | L6 | 1205 | 3 | 0 | 0 | 2 | 1 | 13 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\16_quantum_computing_rust.md | L6 | 1082 | 3 | 0 | 0 | 2 | 1 | 12 | 0 | ✅ | ✅ | ✅ | 研究者 | 实验级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\17_webassembly_advanced.md | L6 | 1257 | 3 | 0 | 0 | 2 | 1 | 16 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\18_wasm_glossary.md | L6 | 482 | 4 | 0 | 0 | 4 | 1 | 0 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\19_wasm_faq.md | L6 | 546 | 4 | 0 | 0 | 0 | 1 | 7 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\20_wasm_javascript_interop.md | L6 | 603 | 4 | 0 | 0 | 1 | 1 | 7 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\21_safety_critical_topic_index.md | L6 | 60 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\22_autosar_and_rust.md | L6 | 215 | 0 | 0 | 0 | 0 | 2 | 1 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\23_safety_critical_systems_engineering.md | L6 | 487 | 0 | 0 | 0 | 6 | 1 | 5 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\24_advanced_data_structures_implementation.md | L6 | 506 | 0 | 0 | 0 | 4 | 1 | 17 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\25_parallel_algorithms.md | L6 | 675 | 0 | 0 | 0 | 5 | 3 | 20 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\26_zero_copy_parsing_in_rust.md | L6 | 565 | 0 | 0 | 0 | 4 | 2 | 16 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\27_ownership_aware_algorithms.md | L6 | 487 | 0 | 0 | 0 | 4 | 2 | 13 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\28_unsafe_algorithm_invariants.md | L6 | 466 | 0 | 0 | 0 | 4 | 2 | 9 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\12_networking\01_advanced_network_protocols.md | L6 | 332 | 3 | 0 | 0 | 0 | 3 | 8 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\12_networking\02_network_security.md | L6 | 416 | 3 | 0 | 0 | 0 | 1 | 8 | 6 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\12_networking\03_custom_protocol_implementation.md | L6 | 229 | 0 | 0 | 0 | 0 | 1 | 4 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\12_networking\04_network_programming_quick_start.md | L6 | 329 | 3 | 0 | 0 | 0 | 3 | 7 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\12_networking\05_networking_basics.md | L6 | 1040 | 4 | 0 | 0 | 1 | 1 | 18 | 6 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\12_networking\06_formal_network_protocol_theory.md | L6 | 677 | 3 | 0 | 0 | 1 | 1 | 16 | 6 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\13_quizzes\01_quiz_networking_async_ecosystem.md | L6 | 354 | 0 | 0 | 0 | 0 | 0 | 2 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\13_quizzes\02_quiz_database_storage.md | L6 | 323 | 5 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\13_quizzes\03_quiz_security_testing.md | L6 | 335 | 1 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\13_quizzes\04_quiz_domain_applications.md | L6 | 337 | 1 | 0 | 0 | 0 | 0 | 2 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\14_enterprise_architecture\01_enterprise_architecture_frameworks.md | L6 | 399 | 0 | 0 | 0 | 3 | 1 | 1 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\14_enterprise_architecture\02_architecture_governance_and_adrs.md | L6 | 380 | 0 | 0 | 0 | 3 | 1 | 0 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\14_enterprise_architecture\03_architecture_standards_alignment.md | L6 | 359 | 0 | 0 | 0 | 3 | 1 | 0 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\14_enterprise_architecture\04_domain_driven_design_in_rust.md | L6 | 354 | 0 | 0 | 0 | 1 | 1 | 9 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\14_enterprise_architecture\05_strategic_domain_driven_design_in_rust.md | L6 | 210 | 0 | 0 | 0 | 1 | 1 | 1 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\14_enterprise_architecture\06_clean_architecture_in_rust.md | L6 | 186 | 0 | 0 | 0 | 2 | 2 | 3 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\14_enterprise_architecture\07_hexagonal_architecture_in_rust.md | L6 | 178 | 0 | 0 | 0 | 2 | 2 | 3 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\14_enterprise_architecture\08_microservices_patterns_in_rust.md | L6 | 12 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\14_enterprise_architecture\09_observability_and_sre_patterns.md | L6 | 779 | 0 | 0 | 0 | 1 | 3 | 7 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\14_enterprise_architecture\10_production_rust_web_service_patterns.md | L6 | 417 | 0 | 0 | 0 | 4 | 2 | 5 | 0 | ❌ | ✅ | ✅ | None | 进阶级 |
| E:\_src\rust-lang\concept\06_ecosystem\14_enterprise_architecture\11_event_driven_and_cqrs_patterns.md | L6 | 698 | 0 | 0 | 0 | 4 | 3 | 6 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\14_enterprise_architecture\12_cloud_native_and_serverless_patterns.md | L6 | 572 | 0 | 0 | 0 | 4 | 3 | 5 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\14_enterprise_architecture\13_microservices_patterns_in_rust.md | L6 | 536 | 0 | 0 | 0 | 4 | 2 | 5 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\14_enterprise_architecture\14_data_intensive_patterns.md | L6 | 461 | 0 | 0 | 0 | 4 | 2 | 4 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\14_enterprise_architecture\15_security_and_zero_trust_patterns.md | L6 | 465 | 0 | 0 | 0 | 4 | 2 | 5 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\00_algorithm_patterns_overview.md | L6 | 640 | 0 | 0 | 0 | 5 | 3 | 16 | 0 | ❌ | ✅ | ✅ | None | None |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\01_algorithmic_paradigms.md | L6 | 1012 | 0 | 0 | 0 | 1 | 1 | 32 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\02_ownership_aware_data_structures.md | L6 | 489 | 0 | 0 | 0 | 4 | 2 | 9 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\03_graph_algorithms_in_rust.md | L6 | 1094 | 0 | 0 | 0 | 4 | 2 | 18 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\04_cache_friendly_and_simd_algorithms.md | L6 | 423 | 0 | 0 | 0 | 5 | 2 | 11 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\05_greedy_and_approximation_algorithms.md | L6 | 473 | 0 | 0 | 0 | 4 | 2 | 7 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\06_dynamic_programming_in_rust.md | L6 | 669 | 0 | 0 | 0 | 4 | 2 | 15 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\07_string_algorithms_in_rust.md | L6 | 483 | 0 | 0 | 0 | 4 | 2 | 10 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\08_data_structures_in_rust.md | L6 | 740 | 0 | 0 | 0 | 6 | 2 | 14 | 0 | ❌ | ✅ | ✅ | None | None |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\09_randomized_and_probabilistic_algorithms.md | L6 | 785 | 0 | 0 | 0 | 1 | 2 | 13 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\10_computational_geometry_algorithms.md | L6 | 601 | 0 | 0 | 0 | 5 | 2 | 11 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\11_online_and_streaming_algorithms.md | L6 | 312 | 0 | 0 | 0 | 2 | 2 | 4 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\12_number_theoretic_algorithms.md | L6 | 524 | 0 | 0 | 0 | 5 | 2 | 10 | 0 | ❌ | ✅ | ✅ | None | 进阶 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\13_advanced_string_algorithms.md | L6 | 662 | 0 | 0 | 0 | 5 | 2 | 11 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\14_network_flow_and_matching.md | L6 | 841 | 0 | 0 | 0 | 5 | 2 | 12 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\15_probabilistic_data_structures.md | L6 | 686 | 0 | 0 | 0 | 5 | 2 | 10 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\16_persistent_data_structures.md | L6 | 464 | 0 | 0 | 0 | 5 | 2 | 8 | 0 | ❌ | ✅ | ✅ | None | 进阶级 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\17_rust_algorithm_patterns_semantic_atlas.md | L6 | 1115 | 0 | 0 | 0 | 7 | 3 | 18 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\18_competitive_programming_idioms.md | L6 | 583 | 0 | 0 | 0 | 6 | 2 | 18 | 0 | ❌ | ✅ | ✅ | None | None |
| E:\_src\rust-lang\concept\06_ecosystem\16_algorithm_patterns\19_parallel_and_gpu_algorithms.md | L6 | 475 | 0 | 0 | 0 | 5 | 2 | 13 | 0 | ❌ | ✅ | ✅ | None | None |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\01_rust_version_tracking.md | L7 | 2699 | 3 | 0 | 0 | 0 | 3 | 9 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\02_editions.md | L7 | 373 | 4 | 0 | 0 | 1 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\03_rust_release_process.md | L7 | 195 | 0 | 0 | 0 | 1 | 2 | 2 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\04_nightly_rust.md | L7 | 283 | 3 | 0 | 0 | 0 | 1 | 2 | 6 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\feature_domain_matrix_197.md | L7 | 305 | 0 | 0 | 0 | 1 | 2 | 0 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\feature_domain_matrix_198.md | L7 | 299 | 0 | 0 | 0 | 0 | 2 | 0 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\migration_197_decision_tree.md | L7 | 808 | 0 | 0 | 0 | 0 | 9 | 17 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\migration_198_decision_tree.md | L7 | 892 | 0 | 0 | 0 | 0 | 16 | 18 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_100_preview.md | L7 | 277 | 0 | 0 | 0 | 1 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_90_stabilized.md | L7 | 972 | 4 | 0 | 0 | 1 | 1 | 17 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_91_stabilized.md | L7 | 2792 | 3 | 0 | 0 | 0 | 1 | 83 | 6 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_92_stabilized.md | L7 | 2778 | 3 | 0 | 0 | 0 | 1 | 74 | 6 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_93_stabilized.md | L7 | 263 | 3 | 0 | 0 | 1 | 1 | 10 | 6 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_94_stabilized.md | L7 | 265 | 4 | 0 | 0 | 0 | 1 | 6 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_95_stabilized.md | L7 | 422 | 0 | 0 | 0 | 0 | 1 | 15 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_96_stabilized.md | L7 | 432 | 0 | 0 | 0 | 1 | 1 | 7 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_97_1.md | L7 | 514 | 1 | 0 | 0 | 3 | 1 | 3 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_97_preview.md | L7 | 147 | 0 | 0 | 0 | 0 | 1 | 3 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_97_stabilized.md | L7 | 574 | 0 | 0 | 0 | 0 | 1 | 15 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_98_preview.md | L7 | 1156 | 0 | 0 | 0 | 0 | 1 | 21 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_98_stabilized.md | L7 | 1086 | 0 | 0 | 0 | 1 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_99_preview.md | L7 | 358 | 0 | 0 | 0 | 1 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\01_edition_roadmap\01_rust_edition_preview.md | L7 | 166 | 0 | 0 | 0 | 0 | 1 | 5 | 0 | ❌ | ✅ | ✅ | 进阶 | 研究者级 |
| E:\_src\rust-lang\concept\07_future\01_edition_roadmap\02_edition_guide.md | L7 | 1062 | 3 | 0 | 0 | 2 | 2 | 14 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\01_edition_roadmap\03_rust_edition_guide.md | L7 | 20 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究者级 |
| E:\_src\rust-lang\concept\07_future\01_edition_roadmap\04_roadmap.md | L7 | 1133 | 3 | 0 | 0 | 2 | 3 | 17 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\01_effects_system.md | L7 | 1774 | 4 | 0 | 0 | 0 | 4 | 26 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\02_mcdc_coverage_preview.md | L7 | 639 | 3 | 0 | 0 | 2 | 4 | 6 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\03_safety_tags_preview.md | L7 | 733 | 3 | 0 | 0 | 3 | 4 | 6 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
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
| E:\_src\rust-lang\concept\07_future\02_preview_features\19_const_trait_preview.md | L7 | 20 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\20_ergonomic_ref_counting_preview.md | L7 | 346 | 0 | 0 | 0 | 0 | 1 | 7 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\21_rust_specification_preview.md | L7 | 12 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\07_future\02_preview_features\22_async_drop_preview.md | L7 | 822 | 3 | 0 | 0 | 2 | 3 | 7 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\23_field_projections_preview.md | L7 | 452 | 3 | 0 | 0 | 1 | 1 | 10 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\24_borrow_sanitizer.md | L7 | 421 | 0 | 0 | 0 | 1 | 2 | 4 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\25_gen_blocks_preview.md | L7 | 704 | 3 | 0 | 0 | 2 | 4 | 8 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\26_std_autodiff_preview.md | L7 | 377 | 3 | 0 | 0 | 1 | 1 | 7 | 0 | ✅ | ✅ | ✅ | 研究者 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\27_cargo_semver_checks_preview.md | L7 | 269 | 0 | 0 | 0 | 0 | 1 | 2 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\28_wasm_target_evolution.md | L7 | 291 | 3 | 0 | 0 | 0 | 1 | 1 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\29_aarch64_sve_sme_preview.md | L7 | 338 | 0 | 0 | 0 | 0 | 1 | 5 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\30_rust_in_space.md | L7 | 284 | 3 | 0 | 0 | 0 | 1 | 4 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\31_specialization_preview.md | L7 | 804 | 3 | 0 | 0 | 2 | 3 | 8 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\32_compile_time_execution.md | L7 | 789 | 3 | 0 | 0 | 2 | 2 | 6 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\33_autoverus_preview.md | L7 | 115 | 0 | 0 | 0 | 0 | 1 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\34_open_enums_preview.md | L7 | 861 | 3 | 0 | 0 | 2 | 4 | 13 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\35_f16_f128_preview.md | L7 | 188 | 0 | 0 | 0 | 1 | 1 | 3 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\36_unsafe_pinned_preview.md | L7 | 162 | 0 | 0 | 0 | 1 | 1 | 3 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\37_default_field_values_preview.md | L7 | 156 | 0 | 0 | 0 | 1 | 1 | 4 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\38_complex_numbers_preview.md | L7 | 152 | 0 | 0 | 0 | 1 | 1 | 3 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\02_preview_features\39_async_ioring_preview.md | L7 | 252 | 0 | 0 | 0 | 2 | 1 | 2 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\07_future\03_edition_differences\01_edition_2021_to_2024.md | L7 | 365 | 0 | 0 | 0 | 4 | 1 | 11 | 2 | ❌ | ✅ | ✅ | None | None |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\01_ai_integration.md | L7 | 1040 | 1 | 0 | 0 | 2 | 3 | 9 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\02_formal_methods.md | L7 | 1754 | 9 | 0 | 0 | 1 | 10 | 9 | 3 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\03_evolution.md | L7 | 2213 | 8 | 0 | 0 | 1 | 6 | 19 | 3 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\04_rust_for_linux.md | L7 | 1109 | 3 | 0 | 0 | 2 | 3 | 11 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\05_rust_in_ai.md | L7 | 811 | 3 | 0 | 0 | 2 | 2 | 7 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\06_rust_for_webassembly.md | L7 | 1000 | 3 | 0 | 0 | 3 | 3 | 11 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\07_ebpf_rust.md | L7 | 1042 | 3 | 0 | 0 | 0 | 4 | 15 | 0 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\08_llm_system_architecture.md | L7 | 562 | 0 | 0 | 0 | 3 | 1 | 5 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\09_mlops_and_llmops.md | L7 | 567 | 0 | 0 | 0 | 3 | 1 | 5 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\10_ai_safety_and_alignment.md | L7 | 434 | 0 | 0 | 0 | 3 | 1 | 1 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\11_rust_for_ai_model_serving.md | L7 | 419 | 0 | 0 | 0 | 4 | 1 | 4 | 0 | ❌ | ✅ | ✅ | None | 专家级 |
| E:\_src\rust-lang\concept\07_future\05_quizzes\01_quiz_version_and_preview.md | L7 | 362 | 0 | 0 | 0 | 1 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 进阶 | 实验级 |
