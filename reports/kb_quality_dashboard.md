# 知识体系质量仪表盘 (KB Quality Dashboard)

> 生成时间: 2026-07-12T05:32:17.288311+00:00
> 扫描文件数: 465

## 全局指标

| 指标 | 数值 | 目标 | 状态 |
|:---|:---|:---|:---|
| 总文件数 | 465 | 27 | ✅ |
| 总定理链 (⟹) | 2084 | ≥270 | ✅ |
| 总反命题 | 695 | ≥40 | ✅ |
| 总 Mermaid 图 | 625 | ≥50 | ✅ |
| 编译验证代码块 | 4655 | ≥150 | ✅ |
| 定理矩阵总行 | 20647 | — | — |
| 死链数量 | 0 | 0 | ✅ |
| 反向推理 (⟸) | 273 | ≥50 | ✅ |
| 模板化 ⟹ | 0 | 0 | ✅ |
| 前置概念覆盖率 | 398/401 | 100% | ⚠️ |
| 后置概念覆盖率 | 398/401 | 100% | ⚠️ |
| 双标签覆盖率 | 396/401 | >=95% | ✅ |
| 非法标签组合 | 0 | 0 | ✅ |

## 按层级分布

| 层级 | 文件数 | 平均 ⟹/文件 | 平均过渡段/文件 | 认知路径 | ⟸/文件 | 模板化 | 前置覆盖 | 后置覆盖 | 双标签 |
|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|
| L0 | 64 | 7.5 | 3.1 | 35/64 (54%) | 0.1 | 0 | 14/64 | 13/64 | 46/64 |
| L1 | 55 | 3.9 | 4.2 | 40/55 (72%) | 1.5 | 0 | 55/55 | 55/55 | 55/55 |
| L2 | 38 | 4.9 | 3.7 | 25/38 (65%) | 1.9 | 0 | 38/38 | 38/38 | 38/38 |
| L3 | 60 | 6.1 | 4.1 | 48/60 (80%) | 1.8 | 0 | 60/60 | 60/60 | 60/60 |
| L4 | 53 | 2.7 | 2.4 | 32/53 (60%) | 0.1 | 0 | 51/53 | 51/53 | 51/53 |
| L5 | 19 | 3.4 | 6.1 | 17/19 (89%) | 0.0 | 0 | 19/19 | 19/19 | 19/19 |
| L6 | 115 | 3.8 | 6.6 | 58/115 (50%) | 0.0 | 0 | 114/115 | 114/115 | 112/115 |
| L7 | 61 | 3.2 | 5.3 | 40/61 (65%) | 0.0 | 0 | 61/61 | 61/61 | 61/61 |

## 风险文件

| 文件 | 层级 | 未通过项 |
|:---|:---|:---|
| E:\_src\rust-lang\concept\01_foundation\00_start\04_effects_and_purity.md | L1 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\00_start\05_std_io_and_process.md | L1 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\01_foundation\00_start\06_keywords.md | L1 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\01_foundation\00_start\07_operators_and_symbols.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\05_move_semantics.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\06_ownership_inventories_brown_book.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\05_data_abstraction_spectrum.md | L1 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\03_values_and_references\02_value_vs_reference_semantics.md | L1 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\01_foundation\03_values_and_references\03_variable_model.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\04_control_flow\02_patterns.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\04_control_flow\03_statements_and_expressions.md | L1 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\01_foundation\06_strings_and_text\03_formatting_and_display.md | L1 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\03_use_declarations.md | L1 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\07_type_aliases.md | L1 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\08_static_items.md | L1 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\09_const_items_and_const_fn.md | L1 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\10_preludes.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\24_quiz_type_system.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\25_quiz_error_handling.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\26_quiz_modules_testing.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\27_quiz_closures_iterators.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\29_quiz_pl_foundations.md | L1 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\33_quiz_ownership_borrowing.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\05_construction_and_initialization.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\06_derive_traits.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\07_generic_associated_types.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\02_const_generics.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (2 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\04_quiz_traits_and_generics.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\05_quiz_memory_management.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\03_error_handling\03_panic.md | L2 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\02_intermediate\03_error_handling\04_exception_safety_rust_cpp.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (2 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\05_rtti_and_dynamic_typing.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\06_unions.md | L2 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\07_type_conversions.md | L2 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\02_intermediate\05_modules_and_visibility\02_friend_vs_module_privacy.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\05_modules_and_visibility\03_api_naming_conventions.md | L2 | 缺失认知路径; 过渡段落不足 (2 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\05_c_preprocessor_vs_rust_macros.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\06_attributes_by_category.md | L2 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\02_intermediate\09_quizzes\30_quiz_cpp_rust_foundations.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\02_send_sync_auto_traits.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\08_quiz_concurrency_async.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\01_async\05_async_cancellation_safety.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\01_async\06_async_boundary_panorama.md | L3 | 过渡段落不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\01_async\07_async_closures.md | L3 | 过渡段落不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\00_before_formal.md | L3 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\02_unsafe_boundary_panorama.md | L3 | 过渡段落不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\05_quiz_unsafe.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\10_quiz_macros.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\11_conditional_compilation.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\03_linkage.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\05_inline_assembly\01_inline_assembly.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\08_memory_allocation_and_lifetime.md | L3 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\09_variables.md | L3 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\10_visibility_and_privacy.md | L3 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\03_advanced\07_unsafe_internals\01_unsafe_collections_internals.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\06_type_semantics.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\07_type_checking_and_inference.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (1 < 3) |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\08_type_inference_complexity.md | L4 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\09_type_system_reference.md | L4 | 缺失认知路径; 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\04_borrow_checking_decidability.md | L4 | 过渡段落不足 (0 < 3); 定理链不足 (1 < 3); 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\05_tree_borrows_deep_dive.md | L4 | 缺失认知路径 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\06_behavior_considered_undefined.md | L4 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\03_safety_tags_in_formal.md | L4 | 缺失认知路径; 缺失反命题; 缺失前置概念; 缺失后置概念; 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\04_borrow_sanitizer_in_formal.md | L4 | 缺失认知路径 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\04_evaluation_strategies.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\06_aeneas_symbolic_semantics.md | L4 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\07_constant_evaluation.md | L4 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\02_formal_methods.md | L4 | 缺失认知路径; 缺失反命题; 缺失前置概念; 缺失后置概念; 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\06_quiz_formal_methods.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\07_autoverus.md | L4 | 缺失认知路径 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\08_miri.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\09_kani.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\01_rustc_query_system.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\02_mir_codegen_llvm_primer.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\03_trait_solver_in_rustc.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\04_name_resolution_and_hir.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\05_application_binary_interface.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\06_names_and_resolution.md | L4 | 定理链不足 (2 < 3) |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\07_special_types_and_traits.md | L4 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\08_type_layout.md | L4 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\09_destructors.md | L4 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\06_notation\01_notation.md | L4 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\05_comparative\00_paradigms\03_cpp_rust_surface_features.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\03_domain_comparisons\02_quiz_rust_vs_systems.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\06_quiz_toolchain.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\07_rustdoc_196_changes.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\08_platform_rust_integration.md | L6 | 过渡段落不足 (2 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\09_llvm_backend_and_codegen.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\10_rustc_driver_and_stable_mir.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\11_compiler_diagnostics_and_ui_tests.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\12_rustc_bootstrap.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\13_compiler_testing.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\14_development_tools.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
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
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\22_build_std.md | L6 | 缺失内容分级标签 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\09_embedded_hal_1_0_migration.md | L6 | 缺失内容分级标签 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\06_game_development.md | L6 | 缺失前置概念; 缺失后置概念; 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\02_editions.md | L7 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\feature_domain_matrix_197.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\migration_197_decision_tree.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_95_stabilized.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_96_stabilized.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_97_stabilized.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_98_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\09_return_type_notation_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\14_pin_ergonomics_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\20_ergonomic_ref_counting_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\24_borrow_sanitizer.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\27_cargo_semver_checks_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\29_aarch64_sve_sme_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\01_ai_integration.md | L7 | 过渡段落不足 (2 < 3); 定理链不足 (2 < 3) |

## 文件详细统计

| 文件 | 层级 | 行数 | ⟹ | ⟸ | 模板 | 反命题 | Mermaid | 代码块 | 过渡段 | 认知路径 | 前置 | 后置 | 受众 | 分级 |
|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|
| E:\_src\rust-lang\concept\00_meta\00_framework\bloom_taxonomy.md | L0 | 200 | 1 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\boundary_extension_tree.md | L0 | 362 | 1 | 0 | 0 | 1 | 3 | 1 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\cognitive_dimension_matrix.md | L0 | 401 | 1 | 0 | 0 | 1 | 2 | 0 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\competency_graph.md | L0 | 417 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\comprehensive_rust_mapping.md | L0 | 240 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 → 进阶 | None |
| E:\_src\rust-lang\concept\00_meta\00_framework\concept_definition_decision_forest.md | L0 | 1136 | 3 | 0 | 0 | 1 | 10 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\cpp_rust_engineering_roadmap.md | L0 | 245 | 0 | 0 | 0 | 0 | 2 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 | None |
| E:\_src\rust-lang\concept\00_meta\00_framework\decidability_spectrum.md | L0 | 909 | 1 | 0 | 0 | 1 | 6 | 2 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\expressiveness_multiview.md | L0 | 792 | 0 | 0 | 0 | 1 | 7 | 7 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\fault_tree_analysis_collection.md | L0 | 784 | 1 | 0 | 0 | 1 | 7 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\knowledge_mindmap.md | L0 | 308 | 1 | 0 | 0 | 1 | 2 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\methodology.md | L0 | 548 | 1 | 0 | 0 | 2 | 5 | 1 | 6 | ✅ | ✅ | ✅ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\paradigm_transition_matrix.md | L0 | 330 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\pattern_semantic_space_index.md | L0 | 197 | 0 | 0 | 0 | 0 | 2 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | None |
| E:\_src\rust-lang\concept\00_meta\00_framework\pl_foundations_roadmap.md | L0 | 178 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 | None |
| E:\_src\rust-lang\concept\00_meta\00_framework\semantic_bridge_algorithms_patterns.md | L0 | 714 | 1 | 0 | 0 | 1 | 0 | 7 | 6 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\semantic_expressiveness.md | L0 | 1133 | 1 | 0 | 0 | 1 | 2 | 1 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\semantic_space.md | L0 | 1338 | 10 | 0 | 0 | 2 | 5 | 9 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\theorem_inference_forest.md | L0 | 527 | 3 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\theorem_registry.md | L0 | 207 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\00_meta\00_framework\todos.md | L0 | 349 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\01_terminology\01_terminology_glossary.md | L0 | 466 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\01_terminology\02_bilingual_template_v2.md | L0 | 322 | 0 | 2 | 0 | 5 | 1 | 5 | 0 | ✅ | ✅ | ✅ | 初学者 | 进阶 | 研究者 | None |
| E:\_src\rust-lang\concept\00_meta\01_terminology\03_bilingual_template.md | L0 | 166 | 0 | 0 | 0 | 1 | 1 | 1 | 0 | ❌ | ✅ | ✅ | 初学者 | 进阶 | 研究者 | None |
| E:\_src\rust-lang\concept\00_meta\01_trpl_3rd_ed_mapping.md | L0 | 11 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\00_meta\02_sources\01_authority_source_map.md | L0 | 216 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\02_sources\02_rustbelt_predicate_map.md | L0 | 423 | 9 | 0 | 0 | 1 | 6 | 0 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\02_sources\03_sources.md | L0 | 493 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 研究者级 |
| E:\_src\rust-lang\concept\00_meta\02_sources\04_topic_authority_alignment_map.md | L0 | 388 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\00_meta\02_sources\05_international_authority_index.md | L0 | 238 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 研究者 / 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\01_concept_audit_guide.md | L0 | 107 | 1 | 0 | 0 | 1 | 1 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\02_asp_marking_guide.md | L0 | 533 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\03_audit_checklist.md | L0 | 455 | 1 | 0 | 0 | 2 | 1 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\04_concept_consistency_audit_checklist.md | L0 | 14 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\00_meta\03_audit\05_template_deduplication_guide.md | L0 | 94 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 贡献者 | None |
| E:\_src\rust-lang\concept\00_meta\03_audit\06_grading_system.md | L0 | 162 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\07_quality_dashboard_v2.md | L0 | 330 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\01_cross_reference_matrix.md | L0 | 15 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\00_meta\04_navigation\02_career_landscape.md | L0 | 236 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 入门 → 进阶 | 元层 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\03_concept_index.md | L0 | 791 | 4 | 0 | 0 | 2 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\04_inter_layer_map.md | L0 | 634 | 12 | 0 | 0 | 1 | 2 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\05_inter_layer_topology.md | L0 | 16 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ✅ | ❌ | ❌ | None | 专家级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\06_intra_layer_model_map.md | L0 | 348 | 11 | 0 | 0 | 1 | 5 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\07_learning_guide.md | L0 | 670 | 3 | 0 | 0 | 1 | 1 | 1 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\08_learning_mvp_path.md | L0 | 372 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ✅ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\09_navigation.md | L0 | 295 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\10_problem_graph.md | L0 | 524 | 1 | 0 | 0 | 1 | 7 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\11_quick_reference.md | L0 | 859 | 1 | 0 | 0 | 1 | 0 | 25 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\12_self_assessment.md | L0 | 2256 | 1 | 0 | 0 | 1 | 0 | 56 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\13_foundations_gap_closure_index.md | L0 | 146 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | None |
| E:\_src\rust-lang\concept\00_meta\04_navigation\14_learning_mvp_path_en.md | L0 | 278 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\01_concept_definition_atlas.md | L0 | 561 | 1 | 1 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\02_attribute_relationship_atlas.md | L0 | 554 | 27 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\03_scenario_decision_tree_atlas.md | L0 | 293 | 0 | 0 | 0 | 0 | 9 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\04_example_counterexample_atlas.md | L0 | 141 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\05_logical_reasoning_atlas.md | L0 | 191 | 17 | 2 | 0 | 0 | 4 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\06_inter_layer_mapping_atlas.md | L0 | 99 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\07_intra_layer_mapping_atlas.md | L0 | 563 | 357 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\08_concept_source_alignment_atlas.md | L0 | 53 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\09_reasoning_judgment_tree_atlas.md | L0 | 265 | 0 | 0 | 0 | 0 | 6 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\10_gap_and_action_plan.md | L0 | 87 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\kg_ontology_v2.md | L0 | 329 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | None |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\kg_tlo_alignment.md | L0 | 254 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\00_meta\placeholders\01_placeholder_generic.md | L0 | 23 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\01_foundation\00_start\00_start.md | L1 | 284 | 4 | 2 | 0 | 1 | 1 | 1 | 6 | ✅ | ✅ | ✅ | 初学者 | 初学者 |
| E:\_src\rust-lang\concept\01_foundation\00_start\01_pl_prerequisites.md | L1 | 521 | 3 | 2 | 0 | 1 | 0 | 12 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\02_zero_cost_abstractions.md | L1 | 846 | 3 | 2 | 0 | 3 | 2 | 14 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\03_closure_basics.md | L1 | 899 | 3 | 2 | 0 | 3 | 1 | 18 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\04_effects_and_purity.md | L1 | 697 | 0 | 0 | 0 | 2 | 0 | 17 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\05_std_io_and_process.md | L1 | 463 | 4 | 4 | 0 | 4 | 1 | 10 | 0 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\06_keywords.md | L1 | 155 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\07_operators_and_symbols.md | L1 | 237 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\00_ownership_borrow_lifetime_knowledge_map.md | L1 | 403 | 3 | 2 | 0 | 1 | 5 | 0 | 5 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\01_ownership.md | L1 | 1939 | 19 | 2 | 0 | 3 | 7 | 46 | 16 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\02_borrowing.md | L1 | 2085 | 8 | 2 | 0 | 3 | 6 | 53 | 20 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\03_lifetimes.md | L1 | 1517 | 23 | 2 | 0 | 3 | 5 | 40 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\04_lifetimes_advanced.md | L1 | 1825 | 3 | 2 | 0 | 1 | 0 | 49 | 10 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\05_move_semantics.md | L1 | 277 | 3 | 0 | 0 | 0 | 0 | 4 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\06_ownership_inventories_brown_book.md | L1 | 209 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\01_type_system.md | L1 | 3309 | 23 | 2 | 0 | 3 | 12 | 63 | 16 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\02_never_type.md | L1 | 577 | 3 | 2 | 0 | 1 | 0 | 15 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\03_numerics.md | L1 | 1060 | 3 | 2 | 0 | 3 | 1 | 18 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\04_coercion_and_casting.md | L1 | 1017 | 3 | 2 | 0 | 3 | 1 | 18 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\05_data_abstraction_spectrum.md | L1 | 750 | 0 | 0 | 0 | 2 | 0 | 14 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\03_values_and_references\01_reference_semantics.md | L1 | 1436 | 3 | 2 | 0 | 4 | 7 | 35 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\03_values_and_references\02_value_vs_reference_semantics.md | L1 | 196 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\03_values_and_references\03_variable_model.md | L1 | 614 | 0 | 0 | 0 | 2 | 0 | 12 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\04_control_flow\01_control_flow.md | L1 | 1647 | 3 | 2 | 0 | 3 | 5 | 25 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\04_control_flow\02_patterns.md | L1 | 238 | 0 | 0 | 0 | 0 | 0 | 10 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\04_control_flow\03_statements_and_expressions.md | L1 | 166 | 0 | 0 | 0 | 0 | 0 | 4 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\05_collections\01_collections.md | L1 | 875 | 3 | 2 | 0 | 3 | 2 | 16 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\05_collections\02_collections_advanced.md | L1 | 1009 | 3 | 2 | 0 | 3 | 2 | 11 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\06_strings_and_text\01_strings_and_text.md | L1 | 856 | 3 | 2 | 0 | 3 | 1 | 17 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\06_strings_and_text\02_strings_and_encoding.md | L1 | 839 | 3 | 2 | 0 | 3 | 2 | 9 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\06_strings_and_text\03_formatting_and_display.md | L1 | 432 | 4 | 3 | 0 | 4 | 1 | 9 | 0 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\01_modules_and_paths.md | L1 | 923 | 10 | 2 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\02_functions.md | L1 | 316 | 4 | 2 | 0 | 1 | 0 | 9 | 6 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\03_use_declarations.md | L1 | 233 | 4 | 2 | 0 | 1 | 0 | 8 | 0 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\04_structs.md | L1 | 259 | 9 | 2 | 0 | 1 | 0 | 7 | 6 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\05_enumerations.md | L1 | 262 | 9 | 2 | 0 | 1 | 0 | 9 | 6 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\06_implementations.md | L1 | 243 | 4 | 2 | 0 | 1 | 0 | 7 | 6 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\07_type_aliases.md | L1 | 422 | 4 | 3 | 0 | 4 | 1 | 10 | 0 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\08_static_items.md | L1 | 411 | 4 | 3 | 0 | 4 | 1 | 8 | 0 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\09_const_items_and_const_fn.md | L1 | 432 | 4 | 3 | 0 | 4 | 1 | 8 | 0 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\10_preludes.md | L1 | 210 | 0 | 0 | 0 | 0 | 0 | 4 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\11_crates_and_source_files.md | L1 | 276 | 4 | 2 | 0 | 1 | 1 | 4 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\12_items.md | L1 | 313 | 4 | 2 | 0 | 1 | 1 | 12 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\08_error_handling\01_error_handling_basics.md | L1 | 1000 | 3 | 2 | 0 | 3 | 1 | 15 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\08_error_handling\02_error_handling_control_flow.md | L1 | 282 | 3 | 3 | 0 | 1 | 1 | 9 | 7 | ✅ | ✅ | ✅ | 初学者 | 入门实践级 |
| E:\_src\rust-lang\concept\01_foundation\08_error_handling\03_panic_and_abort.md | L1 | 961 | 8 | 2 | 0 | 3 | 1 | 12 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\09_macros_basics\01_attributes_and_macros.md | L1 | 935 | 3 | 2 | 0 | 3 | 1 | 14 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\10_testing_basics\01_testing_basics.md | L1 | 757 | 3 | 2 | 0 | 3 | 1 | 8 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\10_testing_basics\02_useful_development_tools.md | L1 | 237 | 4 | 2 | 0 | 1 | 2 | 0 | 6 | ✅ | ✅ | ✅ | 初学者 | 参考级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\24_quiz_type_system.md | L1 | 505 | 0 | 0 | 0 | 0 | 0 | 14 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\25_quiz_error_handling.md | L1 | 620 | 0 | 0 | 0 | 0 | 0 | 18 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\26_quiz_modules_testing.md | L1 | 707 | 0 | 0 | 0 | 0 | 0 | 22 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\27_quiz_closures_iterators.md | L1 | 693 | 0 | 0 | 0 | 0 | 0 | 33 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\29_quiz_pl_foundations.md | L1 | 167 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\33_quiz_ownership_borrowing.md | L1 | 503 | 0 | 0 | 0 | 0 | 0 | 17 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\01_traits.md | L2 | 3115 | 15 | 2 | 0 | 7 | 5 | 75 | 10 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\02_dispatch_mechanisms.md | L2 | 2079 | 10 | 2 | 0 | 1 | 0 | 40 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\03_serde_patterns.md | L2 | 911 | 3 | 3 | 0 | 3 | 2 | 9 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\04_advanced_traits.md | L2 | 982 | 3 | 3 | 0 | 3 | 1 | 21 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\05_construction_and_initialization.md | L2 | 245 | 0 | 0 | 0 | 0 | 0 | 5 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\06_derive_traits.md | L2 | 246 | 0 | 0 | 0 | 0 | 0 | 10 | 0 | ❌ | ✅ | ✅ | 初学者 | 参考级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\07_generic_associated_types.md | L2 | 538 | 0 | 0 | 0 | 0 | 2 | 14 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\01_generics.md | L2 | 3286 | 21 | 2 | 0 | 7 | 6 | 74 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\02_const_generics.md | L2 | 479 | 2 | 0 | 0 | 4 | 0 | 14 | 0 | ❌ | ✅ | ✅ | 进阶 | 进阶级 |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\03_type_level_programming.md | L2 | 676 | 7 | 2 | 0 | 1 | 0 | 8 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\04_quiz_traits_and_generics.md | L2 | 670 | 0 | 0 | 0 | 0 | 0 | 19 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\01_memory_management.md | L2 | 2209 | 19 | 3 | 0 | 7 | 5 | 57 | 7 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\02_interior_mutability.md | L2 | 896 | 9 | 3 | 0 | 3 | 2 | 11 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\03_cow_and_borrowed.md | L2 | 773 | 3 | 3 | 0 | 3 | 2 | 8 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\04_smart_pointers.md | L2 | 925 | 9 | 3 | 0 | 3 | 2 | 12 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\05_quiz_memory_management.md | L2 | 714 | 0 | 0 | 0 | 0 | 0 | 26 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\03_error_handling\01_error_handling.md | L2 | 2852 | 17 | 3 | 0 | 7 | 8 | 63 | 7 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\03_error_handling\02_error_handling_deep_dive.md | L2 | 784 | 3 | 3 | 0 | 3 | 1 | 9 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\03_error_handling\03_panic.md | L2 | 155 | 0 | 0 | 0 | 0 | 0 | 2 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\02_intermediate\03_error_handling\04_exception_safety_rust_cpp.md | L2 | 239 | 2 | 0 | 0 | 0 | 0 | 4 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\01_range_types.md | L2 | 649 | 3 | 3 | 0 | 3 | 2 | 12 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\02_closure_types.md | L2 | 820 | 10 | 3 | 0 | 3 | 3 | 17 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\03_newtype_and_wrapper.md | L2 | 774 | 3 | 3 | 0 | 3 | 1 | 10 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\04_type_system_advanced.md | L2 | 1269 | 3 | 3 | 0 | 3 | 1 | 18 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\05_rtti_and_dynamic_typing.md | L2 | 240 | 0 | 0 | 0 | 0 | 0 | 5 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\06_unions.md | L2 | 436 | 4 | 3 | 0 | 4 | 1 | 7 | 0 | ✅ | ✅ | ✅ | 进阶 | 进阶 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\07_type_conversions.md | L2 | 467 | 4 | 4 | 0 | 4 | 1 | 10 | 0 | ✅ | ✅ | ✅ | 进阶 | 进阶 |
| E:\_src\rust-lang\concept\02_intermediate\05_modules_and_visibility\01_module_system.md | L2 | 856 | 8 | 3 | 0 | 3 | 3 | 15 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\05_modules_and_visibility\02_friend_vs_module_privacy.md | L2 | 234 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\02_intermediate\05_modules_and_visibility\03_api_naming_conventions.md | L2 | 436 | 0 | 0 | 0 | 0 | 0 | 15 | 2 | ❌ | ✅ | ✅ | 进阶 | 中级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\01_assert_matches.md | L2 | 714 | 3 | 3 | 0 | 3 | 3 | 18 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\02_dsl_and_embedding.md | L2 | 842 | 3 | 3 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\03_macro_patterns.md | L2 | 830 | 3 | 3 | 0 | 3 | 1 | 9 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\04_metaprogramming.md | L2 | 878 | 3 | 3 | 0 | 3 | 2 | 8 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\05_c_preprocessor_vs_rust_macros.md | L2 | 242 | 0 | 0 | 0 | 0 | 0 | 4 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\06_attributes_by_category.md | L2 | 479 | 4 | 4 | 0 | 4 | 1 | 10 | 0 | ✅ | ✅ | ✅ | 进阶 | 进阶 |
| E:\_src\rust-lang\concept\02_intermediate\07_iterators_and_closures\01_iterator_patterns.md | L2 | 1374 | 13 | 2 | 0 | 2 | 1 | 22 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\09_quizzes\30_quiz_cpp_rust_foundations.md | L2 | 209 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\01_concurrency.md | L3 | 2139 | 21 | 2 | 0 | 3 | 13 | 27 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\02_send_sync_auto_traits.md | L3 | 487 | 8 | 1 | 0 | 4 | 1 | 13 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\03_concurrency_patterns.md | L3 | 2317 | 3 | 3 | 0 | 3 | 4 | 34 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\04_cross_platform_concurrency.md | L3 | 182 | 6 | 2 | 0 | 1 | 0 | 3 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\05_atomics_and_memory_ordering.md | L3 | 1448 | 8 | 3 | 0 | 3 | 2 | 23 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\06_lock_free.md | L3 | 1225 | 3 | 3 | 0 | 3 | 1 | 20 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\07_parallel_distributed_pattern_spectrum.md | L3 | 1067 | 3 | 3 | 0 | 3 | 0 | 18 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\08_quiz_concurrency_async.md | L3 | 705 | 0 | 0 | 0 | 0 | 0 | 19 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\01_async.md | L3 | 3465 | 21 | 3 | 0 | 6 | 9 | 63 | 3 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\02_async_advanced.md | L3 | 1708 | 4 | 3 | 0 | 1 | 1 | 40 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\03_async_patterns.md | L3 | 1230 | 3 | 3 | 0 | 3 | 1 | 22 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\04_future_and_executor_mechanisms.md | L3 | 1075 | 7 | 2 | 0 | 1 | 0 | 17 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\05_async_cancellation_safety.md | L3 | 439 | 0 | 0 | 0 | 5 | 1 | 11 | 0 | ❌ | ✅ | ✅ | 进阶-专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\06_async_boundary_panorama.md | L3 | 478 | 25 | 0 | 0 | 6 | 2 | 10 | 0 | ✅ | ✅ | ✅ | 进阶-专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\07_async_closures.md | L3 | 565 | 3 | 0 | 0 | 1 | 0 | 20 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\08_pin_unpin.md | L3 | 989 | 6 | 3 | 0 | 3 | 2 | 22 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\00_before_formal.md | L3 | 166 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\01_unsafe.md | L3 | 3459 | 18 | 2 | 0 | 4 | 10 | 63 | 3 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\02_unsafe_boundary_panorama.md | L3 | 444 | 18 | 0 | 0 | 5 | 2 | 12 | 0 | ✅ | ✅ | ✅ | 进阶-专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\03_nll_and_polonius.md | L3 | 838 | 3 | 3 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\04_unsafe_rust_patterns.md | L3 | 42 | 3 | 0 | 0 | 1 | 0 | 0 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\05_quiz_unsafe.md | L3 | 612 | 0 | 0 | 0 | 0 | 0 | 21 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\06_memory_model.md | L3 | 340 | 5 | 2 | 0 | 1 | 0 | 9 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\07_unsafe_reference.md | L3 | 237 | 3 | 2 | 0 | 1 | 0 | 4 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\01_macros.md | L3 | 2502 | 26 | 3 | 0 | 8 | 8 | 59 | 8 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\02_proc_macro.md | L3 | 1114 | 3 | 3 | 0 | 3 | 2 | 14 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\03_proc_macro_code_generation_optimization.md | L3 | 359 | 7 | 2 | 0 | 1 | 0 | 11 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\04_macro_debugging_and_diagnostics.md | L3 | 314 | 7 | 2 | 0 | 1 | 0 | 7 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\05_production_grade_macro_development.md | L3 | 362 | 7 | 2 | 0 | 1 | 0 | 8 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\06_macro_glossary.md | L3 | 687 | 8 | 2 | 0 | 1 | 0 | 27 | 6 | ✅ | ✅ | ✅ | 研究者 | 参考级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\07_macro_faq.md | L3 | 805 | 8 | 2 | 0 | 1 | 0 | 35 | 6 | ✅ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\08_syn_quote_reference.md | L3 | 1007 | 8 | 2 | 0 | 1 | 0 | 31 | 6 | ✅ | ✅ | ✅ | 专家 | 参考级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\09_macro_hygiene.md | L3 | 1070 | 8 | 2 | 0 | 1 | 0 | 35 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\10_quiz_macros.md | L3 | 672 | 0 | 0 | 0 | 0 | 0 | 23 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\11_conditional_compilation.md | L3 | 249 | 0 | 0 | 0 | 0 | 0 | 8 | 0 | ❌ | ✅ | ✅ | 中级 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\01_rust_ffi.md | L3 | 934 | 3 | 3 | 0 | 3 | 3 | 17 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\02_ffi_advanced.md | L3 | 929 | 3 | 3 | 0 | 3 | 1 | 12 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\03_linkage.md | L3 | 396 | 0 | 0 | 0 | 0 | 0 | 14 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\05_inline_assembly\01_inline_assembly.md | L3 | 794 | 0 | 0 | 0 | 0 | 0 | 25 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\01_custom_allocators.md | L3 | 874 | 3 | 3 | 0 | 3 | 1 | 12 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\02_zero_copy_parsing.md | L3 | 917 | 3 | 3 | 0 | 3 | 1 | 13 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\03_type_erasure.md | L3 | 885 | 3 | 3 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\04_network_programming.md | L3 | 1087 | 3 | 3 | 0 | 3 | 2 | 16 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\05_stream_processing_semantics.md | L3 | 867 | 3 | 3 | 0 | 2 | 0 | 8 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\06_ownership_performance_optimization.md | L3 | 191 | 4 | 0 | 0 | 1 | 0 | 8 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\07_rust_runtime.md | L3 | 281 | 3 | 2 | 0 | 1 | 0 | 6 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\08_memory_allocation_and_lifetime.md | L3 | 164 | 0 | 0 | 0 | 0 | 0 | 6 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\09_variables.md | L3 | 170 | 0 | 0 | 0 | 0 | 0 | 6 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\10_visibility_and_privacy.md | L3 | 194 | 0 | 0 | 0 | 0 | 1 | 6 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\07_unsafe_internals\01_unsafe_collections_internals.md | L3 | 502 | 4 | 4 | 0 | 4 | 1 | 8 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\01_process_model_and_lifecycle.md | L3 | 433 | 8 | 2 | 0 | 1 | 1 | 3 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\02_advanced_process_management.md | L3 | 318 | 8 | 2 | 0 | 1 | 1 | 3 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\03_async_process_management.md | L3 | 391 | 8 | 2 | 0 | 1 | 1 | 9 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\04_cross_platform_process_management.md | L3 | 320 | 8 | 2 | 0 | 1 | 1 | 5 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\05_ipc_mechanisms.md | L3 | 283 | 8 | 2 | 0 | 1 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\06_process_monitoring_and_diagnostics.md | L3 | 285 | 8 | 2 | 0 | 1 | 1 | 5 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\07_process_security_and_sandboxing.md | L3 | 253 | 8 | 2 | 0 | 1 | 1 | 7 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\08_process_performance_engineering.md | L3 | 231 | 8 | 2 | 0 | 1 | 1 | 3 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\09_process_testing_and_benchmarking.md | L3 | 253 | 8 | 2 | 0 | 1 | 1 | 5 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\08_process_ipc\10_modern_process_libraries.md | L3 | 246 | 8 | 2 | 0 | 1 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\01_type_theory.md | L4 | 1766 | 27 | 0 | 0 | 4 | 5 | 27 | 3 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\02_subtype_variance.md | L4 | 646 | 3 | 0 | 0 | 3 | 2 | 10 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\03_type_inference.md | L4 | 770 | 3 | 0 | 0 | 3 | 2 | 9 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\04_category_theory.md | L4 | 822 | 3 | 0 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\05_lambda_calculus.md | L4 | 766 | 3 | 0 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\06_type_semantics.md | L4 | 920 | 3 | 0 | 0 | 3 | 0 | 18 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\07_type_checking_and_inference.md | L4 | 412 | 1 | 0 | 0 | 1 | 0 | 10 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\08_type_inference_complexity.md | L4 | 400 | 0 | 0 | 0 | 1 | 0 | 6 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\09_type_system_reference.md | L4 | 418 | 0 | 0 | 0 | 1 | 0 | 1 | 6 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\01_linear_logic.md | L4 | 1250 | 14 | 0 | 0 | 4 | 5 | 13 | 3 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\02_ownership_formal.md | L4 | 1652 | 11 | 0 | 0 | 1 | 5 | 17 | 3 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\03_linear_logic_applications.md | L4 | 756 | 3 | 0 | 0 | 3 | 1 | 10 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\04_borrow_checking_decidability.md | L4 | 400 | 1 | 0 | 0 | 0 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\05_tree_borrows_deep_dive.md | L4 | 171 | 0 | 0 | 0 | 1 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\06_behavior_considered_undefined.md | L4 | 167 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 专家 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\01_rustbelt.md | L4 | 1430 | 5 | 0 | 0 | 1 | 5 | 16 | 10 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\02_separation_logic.md | L4 | 848 | 3 | 0 | 0 | 3 | 1 | 10 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\03_safety_tags_in_formal.md | L4 | 14 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\04_borrow_sanitizer_in_formal.md | L4 | 178 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\01_denotational_semantics.md | L4 | 649 | 3 | 0 | 0 | 3 | 1 | 7 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\02_hoare_logic.md | L4 | 914 | 3 | 0 | 0 | 3 | 2 | 8 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\03_operational_semantics.md | L4 | 1090 | 3 | 0 | 0 | 3 | 1 | 13 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\04_evaluation_strategies.md | L4 | 668 | 0 | 0 | 0 | 2 | 0 | 14 | 0 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\05_axiomatic_semantics.md | L4 | 981 | 3 | 0 | 0 | 3 | 0 | 13 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\06_aeneas_symbolic_semantics.md | L4 | 436 | 0 | 0 | 0 | 0 | 1 | 4 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\07_constant_evaluation.md | L4 | 183 | 0 | 0 | 0 | 0 | 0 | 4 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\01_verification_toolchain.md | L4 | 1548 | 3 | 0 | 0 | 1 | 4 | 17 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\02_formal_methods.md | L4 | 22 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\03_aerospace_certification_formal_methods.md | L4 | 1100 | 3 | 0 | 0 | 1 | 1 | 5 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\04_modern_verification_tools.md | L4 | 535 | 3 | 0 | 0 | 1 | 0 | 8 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\05_programming_language_foundations.md | L4 | 443 | 3 | 0 | 0 | 1 | 0 | 10 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\06_quiz_formal_methods.md | L4 | 594 | 0 | 0 | 0 | 0 | 0 | 10 | 0 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\07_autoverus.md | L4 | 188 | 0 | 0 | 0 | 1 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\08_miri.md | L4 | 293 | 0 | 0 | 0 | 2 | 1 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 / 工程 / 形式化 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\09_kani.md | L4 | 357 | 0 | 0 | 0 | 0 | 0 | 9 | 0 | ❌ | ✅ | ✅ | 进阶 / 工程 / 形式化 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\01_rustc_query_system.md | L4 | 571 | 0 | 0 | 0 | 0 | 3 | 3 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\02_mir_codegen_llvm_primer.md | L4 | 371 | 8 | 3 | 0 | 1 | 1 | 1 | 0 | ✅ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\03_trait_solver_in_rustc.md | L4 | 426 | 3 | 3 | 0 | 0 | 1 | 8 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\04_name_resolution_and_hir.md | L4 | 321 | 0 | 0 | 0 | 2 | 1 | 5 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\05_application_binary_interface.md | L4 | 241 | 0 | 0 | 0 | 0 | 0 | 6 | 0 | ❌ | ✅ | ✅ | 专家 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\06_names_and_resolution.md | L4 | 222 | 2 | 0 | 0 | 1 | 0 | 2 | 6 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\07_special_types_and_traits.md | L4 | 189 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\08_type_layout.md | L4 | 159 | 0 | 0 | 0 | 0 | 0 | 4 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\09_destructors.md | L4 | 177 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\10_lexical_structure.md | L4 | 268 | 3 | 0 | 0 | 1 | 0 | 6 | 6 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\11_items_reference.md | L4 | 258 | 3 | 0 | 0 | 1 | 0 | 9 | 6 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\12_attributes.md | L4 | 185 | 3 | 0 | 0 | 1 | 0 | 5 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\13_statements_and_expressions_reference.md | L4 | 170 | 3 | 0 | 0 | 1 | 0 | 5 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\14_patterns_reference.md | L4 | 169 | 3 | 0 | 0 | 1 | 0 | 4 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\15_generics_compiler_behavior.md | L4 | 184 | 4 | 0 | 0 | 1 | 0 | 5 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\16_names_reference.md | L4 | 169 | 3 | 0 | 0 | 1 | 0 | 2 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\17_reference_appendices.md | L4 | 171 | 2 | 0 | 0 | 1 | 0 | 1 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\06_notation\01_notation.md | L4 | 138 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\05_comparative\00_paradigms\01_paradigm_matrix.md | L5 | 1245 | 6 | 0 | 0 | 5 | 8 | 12 | 16 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\00_paradigms\02_execution_model_isomorphism.md | L5 | 1008 | 3 | 0 | 0 | 1 | 5 | 13 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\05_comparative\00_paradigms\03_cpp_rust_surface_features.md | L5 | 229 | 0 | 0 | 0 | 0 | 0 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 | 研究级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\01_rust_vs_cpp.md | L5 | 2153 | 9 | 0 | 0 | 2 | 10 | 12 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\02_cpp_abi_object_model.md | L5 | 884 | 3 | 0 | 0 | 3 | 0 | 17 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\03_rust_vs_go.md | L5 | 986 | 3 | 0 | 0 | 3 | 6 | 11 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\04_rust_vs_ruby.md | L5 | 751 | 3 | 0 | 0 | 3 | 1 | 8 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\05_rust_vs_swift.md | L5 | 734 | 3 | 0 | 0 | 3 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\06_rust_vs_zig.md | L5 | 773 | 3 | 0 | 0 | 3 | 1 | 8 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\01_rust_vs_java.md | L5 | 626 | 3 | 0 | 0 | 3 | 3 | 7 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\02_rust_vs_python.md | L5 | 706 | 3 | 0 | 0 | 3 | 2 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\03_rust_vs_javascript.md | L5 | 714 | 3 | 0 | 0 | 3 | 2 | 5 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\04_rust_vs_kotlin.md | L5 | 816 | 3 | 0 | 0 | 3 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\05_rust_vs_scala.md | L5 | 777 | 3 | 0 | 0 | 3 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\06_rust_vs_csharp.md | L5 | 845 | 3 | 0 | 0 | 3 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\07_rust_vs_elixir.md | L5 | 839 | 3 | 0 | 0 | 3 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\08_rust_vs_typescript.md | L5 | 928 | 3 | 0 | 0 | 3 | 2 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\03_domain_comparisons\01_safety_boundaries.md | L5 | 1030 | 8 | 0 | 0 | 1 | 7 | 9 | 9 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\05_comparative\03_domain_comparisons\02_quiz_rust_vs_systems.md | L5 | 709 | 0 | 0 | 0 | 0 | 0 | 14 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\01_toolchain.md | L6 | 1905 | 13 | 0 | 0 | 2 | 9 | 15 | 14 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\02_logging_observability.md | L6 | 729 | 6 | 0 | 0 | 3 | 3 | 9 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\03_devops_and_ci_cd.md | L6 | 905 | 6 | 0 | 0 | 3 | 2 | 7 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\04_compiler_internals.md | L6 | 871 | 6 | 0 | 0 | 3 | 0 | 7 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\05_compiler_infrastructure.md | L6 | 387 | 4 | 0 | 0 | 2 | 0 | 1 | 8 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\06_quiz_toolchain.md | L6 | 556 | 0 | 0 | 0 | 0 | 0 | 7 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\07_rustdoc_196_changes.md | L6 | 232 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 进阶 / 工程 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\08_platform_rust_integration.md | L6 | 304 | 0 | 0 | 0 | 0 | 0 | 4 | 2 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\09_llvm_backend_and_codegen.md | L6 | 300 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\10_rustc_driver_and_stable_mir.md | L6 | 256 | 0 | 0 | 0 | 0 | 0 | 2 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\11_compiler_diagnostics_and_ui_tests.md | L6 | 292 | 0 | 0 | 0 | 0 | 0 | 5 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\12_rustc_bootstrap.md | L6 | 249 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\13_compiler_testing.md | L6 | 274 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\14_development_tools.md | L6 | 202 | 0 | 0 | 0 | 0 | 0 | 5 | 0 | ❌ | ✅ | ✅ | 初学者 | 研究级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\01_cargo_script.md | L6 | 749 | 4 | 0 | 0 | 1 | 2 | 12 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\02_public_private_deps.md | L6 | 258 | 4 | 0 | 0 | 1 | 1 | 1 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\03_resolver_v3_public_feature_unification.md | L6 | 190 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 实践级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\04_cargo_196_features.md | L6 | 262 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 进阶 / 工程 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\05_cargo_build_scripts.md | L6 | 515 | 0 | 0 | 0 | 2 | 2 | 14 | 0 | ❌ | ✅ | ✅ | 进阶 / 工程 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\06_cargo_dependency_resolution.md | L6 | 519 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\07_cargo_source_replacement.md | L6 | 286 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\08_cargo_registries_and_publishing.md | L6 | 294 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\09_cargo_authentication_and_cache.md | L6 | 289 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\10_cargo_manifest_reference.md | L6 | 316 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 中级 → 高级 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\11_cargo_profiles_and_lints.md | L6 | 310 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\12_cargo_subcommands_and_plugins.md | L6 | 244 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\13_cargo_security_cves.md | L6 | 484 | 4 | 0 | 0 | 3 | 1 | 0 | 2 | ✅ | ✅ | ✅ | 进阶 / 工程 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\14_cargo_workspaces.md | L6 | 264 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\15_cargo_getting_started.md | L6 | 178 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\16_cargo_workflow.md | L6 | 179 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\17_cargo_guide_practices.md | L6 | 178 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\18_cargo_configuration.md | L6 | 191 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\19_cargo_commands_reference.md | L6 | 177 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\20_cargo_manifest_targets.md | L6 | 180 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\21_cargo_registry_internals.md | L6 | 169 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 专家 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\22_build_std.md | L6 | 302 | 3 | 0 | 0 | 0 | 2 | 3 | 6 | ❌ | ✅ | ✅ | 进阶 / 工程 | None |
| E:\_src\rust-lang\concept\06_ecosystem\02_core_crates\01_core_crates.md | L6 | 1353 | 8 | 0 | 0 | 2 | 6 | 17 | 3 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\01_patterns.md | L6 | 3100 | 17 | 0 | 0 | 2 | 5 | 45 | 14 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\02_idioms_spectrum.md | L6 | 1434 | 6 | 0 | 0 | 1 | 5 | 35 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\03_system_design_principles.md | L6 | 755 | 6 | 0 | 0 | 1 | 6 | 8 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\04_system_composability.md | L6 | 813 | 3 | 0 | 0 | 0 | 4 | 23 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\05_microservice_patterns.md | L6 | 1021 | 6 | 0 | 0 | 2 | 6 | 15 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\06_event_driven_architecture.md | L6 | 1047 | 6 | 0 | 0 | 2 | 4 | 15 | 8 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\07_cqrs_event_sourcing.md | L6 | 1478 | 6 | 0 | 0 | 3 | 1 | 18 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\08_architecture_patterns.md | L6 | 1298 | 6 | 0 | 0 | 3 | 0 | 13 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\09_pattern_implementation_comparison.md | L6 | 826 | 4 | 0 | 0 | 0 | 0 | 16 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\10_pattern_selection_best_practices.md | L6 | 774 | 4 | 0 | 0 | 0 | 0 | 11 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\11_formal_design_pattern_theory.md | L6 | 1024 | 4 | 0 | 0 | 0 | 0 | 16 | 6 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\12_frontier_research_and_innovative_patterns.md | L6 | 998 | 4 | 0 | 0 | 0 | 0 | 17 | 6 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\13_engineering_and_production_patterns.md | L6 | 327 | 3 | 0 | 0 | 0 | 0 | 7 | 6 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\14_design_patterns_glossary.md | L6 | 273 | 4 | 0 | 0 | 0 | 0 | 4 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\15_design_patterns_faq.md | L6 | 510 | 4 | 0 | 0 | 0 | 0 | 4 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\16_pattern_composition_algebra.md | L6 | 745 | 6 | 0 | 0 | 3 | 0 | 15 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\17_workflow_theory.md | L6 | 1426 | 6 | 0 | 0 | 3 | 0 | 17 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\18_api_design_patterns.md | L6 | 1314 | 6 | 0 | 0 | 3 | 0 | 19 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\01_distributed_systems.md | L6 | 825 | 6 | 0 | 0 | 3 | 1 | 9 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\02_cloud_native.md | L6 | 804 | 4 | 0 | 0 | 3 | 1 | 8 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\03_web_frameworks.md | L6 | 1064 | 7 | 0 | 0 | 4 | 3 | 11 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\04_http_client_development.md | L6 | 199 | 0 | 0 | 0 | 0 | 0 | 8 | 0 | ❌ | ✅ | ✅ | 进阶 | 进阶 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\05_glommio_and_thread_per_core.md | L6 | 235 | 3 | 0 | 0 | 0 | 0 | 5 | 6 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\06_websocket_realtime_communication.md | L6 | 748 | 4 | 0 | 0 | 0 | 0 | 10 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\07_network_protocols.md | L6 | 535 | 6 | 0 | 0 | 1 | 0 | 7 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\08_high_performance_network_service_architecture.md | L6 | 2088 | 3 | 0 | 0 | 0 | 0 | 19 | 6 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\09_reactive_programming.md | L6 | 1096 | 6 | 0 | 0 | 3 | 0 | 14 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\01_wasi.md | L6 | 678 | 6 | 0 | 0 | 5 | 2 | 11 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\02_cross_compilation.md | L6 | 689 | 6 | 0 | 0 | 3 | 1 | 5 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\03_embedded_systems.md | L6 | 984 | 6 | 0 | 0 | 3 | 1 | 10 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\04_cli_development.md | L6 | 799 | 6 | 0 | 0 | 3 | 1 | 9 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\05_os_kernel.md | L6 | 503 | 6 | 0 | 0 | 1 | 0 | 10 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\06_robotics.md | L6 | 1029 | 6 | 0 | 0 | 3 | 0 | 15 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\07_embedded_graphics.md | L6 | 1171 | 6 | 0 | 0 | 3 | 1 | 6 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\08_c_to_rust_translation.md | L6 | 463 | 6 | 0 | 0 | 1 | 0 | 2 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\09_embedded_hal_1_0_migration.md | L6 | 256 | 3 | 0 | 0 | 0 | 0 | 5 | 6 | ❌ | ✅ | ✅ | 进阶 / 工程 | None |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\01_application_domains.md | L6 | 1535 | 8 | 0 | 0 | 2 | 6 | 12 | 3 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\02_database_access.md | L6 | 832 | 6 | 0 | 0 | 3 | 1 | 8 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\03_stream_processing_ecosystem.md | L6 | 580 | 6 | 0 | 0 | 1 | 0 | 10 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\04_database_systems.md | L6 | 548 | 6 | 0 | 0 | 1 | 0 | 9 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\05_data_engineering.md | L6 | 956 | 6 | 0 | 0 | 3 | 0 | 12 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\06_distributed_consensus.md | L6 | 881 | 6 | 0 | 0 | 3 | 0 | 6 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\07_rust_for_data_science.md | L6 | 627 | 6 | 0 | 0 | 3 | 0 | 8 | 12 | ✅ | ✅ | ✅ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\07_security_and_cryptography\01_security_practices.md | L6 | 1099 | 6 | 0 | 0 | 3 | 1 | 8 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\07_security_and_cryptography\02_security_cryptography.md | L6 | 945 | 6 | 0 | 0 | 3 | 0 | 16 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\08_formal_verification\01_formal_ecosystem_tower.md | L6 | 609 | 3 | 0 | 0 | 0 | 2 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\08_formal_verification\02_formal_verification_tools.md | L6 | 960 | 6 | 0 | 0 | 3 | 0 | 12 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_testing_and_quality\01_testing_strategies.md | L6 | 757 | 6 | 0 | 0 | 3 | 2 | 9 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_testing_and_quality\02_documentation.md | L6 | 685 | 4 | 0 | 0 | 3 | 2 | 7 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_testing_and_quality\03_testing.md | L6 | 771 | 4 | 0 | 0 | 3 | 2 | 8 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_testing_and_quality\04_benchmarking.md | L6 | 177 | 0 | 0 | 0 | 0 | 0 | 5 | 0 | ❌ | ✅ | ✅ | 进阶 | 指南级 |
| E:\_src\rust-lang\concept\06_ecosystem\10_performance\01_performance_optimization.md | L6 | 1164 | 6 | 0 | 0 | 3 | 1 | 13 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\01_blockchain.md | L6 | 932 | 6 | 0 | 0 | 0 | 3 | 14 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\02_game_ecs.md | L6 | 1369 | 3 | 0 | 0 | 0 | 7 | 23 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\03_webassembly.md | L6 | 683 | 6 | 0 | 0 | 3 | 3 | 8 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\04_licensing_and_compliance.md | L6 | 710 | 6 | 0 | 0 | 3 | 1 | 6 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\05_game_development.md | L6 | 712 | 6 | 0 | 0 | 3 | 1 | 8 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\06_game_development.md | L6 | 18 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\07_algorithms_competitive_programming.md | L6 | 1272 | 3 | 0 | 0 | 0 | 0 | 29 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\08_algorithm_engineering_practice.md | L6 | 1986 | 3 | 0 | 0 | 0 | 0 | 22 | 6 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\09_data_structures_in_rust.md | L6 | 286 | 3 | 0 | 0 | 0 | 1 | 8 | 6 | ❌ | ✅ | ✅ | 进阶 | 进阶 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\10_algorithm_complexity_analysis.md | L6 | 194 | 0 | 0 | 0 | 0 | 0 | 4 | 0 | ❌ | ✅ | ✅ | 进阶 | 进阶 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\11_cutting_edge_algorithms.md | L6 | 246 | 3 | 0 | 0 | 0 | 0 | 3 | 6 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\12_formal_algorithm_theory.md | L6 | 281 | 3 | 0 | 0 | 0 | 0 | 4 | 6 | ❌ | ✅ | ✅ | 专家 | 形式化级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\13_machine_learning_ecosystem.md | L6 | 961 | 6 | 0 | 0 | 3 | 0 | 14 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\14_industrial_case_studies.md | L6 | 480 | 6 | 0 | 0 | 1 | 0 | 5 | 12 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\15_game_engine_internals.md | L6 | 1153 | 6 | 0 | 0 | 3 | 0 | 13 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\16_quantum_computing_rust.md | L6 | 1013 | 4 | 0 | 0 | 3 | 0 | 12 | 12 | ✅ | ✅ | ✅ | 研究者 | 实验级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\17_webassembly_advanced.md | L6 | 1168 | 6 | 0 | 0 | 2 | 0 | 14 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\18_wasm_glossary.md | L6 | 389 | 4 | 0 | 0 | 0 | 0 | 0 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\19_wasm_faq.md | L6 | 495 | 4 | 0 | 0 | 0 | 0 | 6 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\20_wasm_javascript_interop.md | L6 | 496 | 4 | 0 | 0 | 0 | 0 | 5 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\12_networking\01_advanced_network_protocols.md | L6 | 294 | 3 | 0 | 0 | 0 | 2 | 6 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\12_networking\02_network_security.md | L6 | 340 | 3 | 0 | 0 | 0 | 0 | 7 | 6 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\12_networking\03_custom_protocol_implementation.md | L6 | 196 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\12_networking\04_network_programming_quick_start.md | L6 | 280 | 3 | 0 | 0 | 0 | 2 | 5 | 6 | ❌ | ✅ | ✅ | 进阶 | 指南级 |
| E:\_src\rust-lang\concept\06_ecosystem\12_networking\05_networking_basics.md | L6 | 887 | 4 | 0 | 0 | 0 | 0 | 15 | 6 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\12_networking\06_formal_network_protocol_theory.md | L6 | 585 | 3 | 0 | 0 | 0 | 0 | 14 | 6 | ❌ | ✅ | ✅ | 研究者 / 专家 | 专家级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\01_rust_version_tracking.md | L7 | 2599 | 6 | 0 | 0 | 1 | 3 | 9 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\02_editions.md | L7 | 322 | 4 | 0 | 0 | 1 | 1 | 6 | 0 | ✅ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\03_rust_release_process.md | L7 | 162 | 0 | 0 | 0 | 1 | 1 | 1 | 0 | ✅ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\04_nightly_rust.md | L7 | 243 | 3 | 0 | 0 | 0 | 0 | 1 | 6 | ❌ | ✅ | ✅ | 初学者 | 研究级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\feature_domain_matrix_197.md | L7 | 277 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\migration_197_decision_tree.md | L7 | 746 | 0 | 0 | 0 | 0 | 8 | 17 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_90_stabilized.md | L7 | 784 | 4 | 0 | 0 | 0 | 0 | 14 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_91_stabilized.md | L7 | 2664 | 3 | 0 | 0 | 0 | 0 | 81 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_92_stabilized.md | L7 | 2650 | 3 | 0 | 0 | 0 | 0 | 72 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_93_stabilized.md | L7 | 195 | 3 | 0 | 0 | 0 | 0 | 8 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_94_stabilized.md | L7 | 445 | 4 | 0 | 0 | 0 | 0 | 9 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_95_stabilized.md | L7 | 327 | 0 | 0 | 0 | 0 | 0 | 14 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_96_stabilized.md | L7 | 320 | 0 | 0 | 0 | 0 | 0 | 5 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_97_preview.md | L7 | 110 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_97_stabilized.md | L7 | 435 | 0 | 0 | 0 | 0 | 0 | 14 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_98_preview.md | L7 | 594 | 0 | 0 | 0 | 0 | 0 | 7 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\01_edition_roadmap\01_rust_edition_preview.md | L7 | 123 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 进阶 | 研究级 |
| E:\_src\rust-lang\concept\07_future\01_edition_roadmap\02_edition_guide.md | L7 | 906 | 4 | 0 | 0 | 3 | 1 | 13 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\01_edition_roadmap\03_rust_edition_guide.md | L7 | 20 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\07_future\01_edition_roadmap\04_roadmap.md | L7 | 1084 | 6 | 0 | 0 | 3 | 2 | 17 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\01_effects_system.md | L7 | 1781 | 6 | 0 | 0 | 1 | 4 | 26 | 12 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\02_mcdc_coverage_preview.md | L7 | 574 | 4 | 0 | 0 | 3 | 3 | 5 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\03_safety_tags_preview.md | L7 | 667 | 4 | 0 | 0 | 3 | 3 | 6 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\04_parallel_frontend_preview.md | L7 | 678 | 6 | 0 | 0 | 3 | 3 | 6 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\05_derive_coerce_pointee_preview.md | L7 | 653 | 4 | 0 | 0 | 3 | 3 | 8 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\06_const_trait_impl_preview.md | L7 | 675 | 6 | 0 | 0 | 3 | 2 | 7 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\07_stable_abi_preview.md | L7 | 256 | 3 | 0 | 0 | 1 | 0 | 3 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\08_inline_const_pattern_preview.md | L7 | 265 | 3 | 0 | 0 | 1 | 0 | 6 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\09_return_type_notation_preview.md | L7 | 504 | 0 | 0 | 0 | 3 | 0 | 10 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\10_must_not_suspend_preview.md | L7 | 245 | 3 | 0 | 0 | 1 | 0 | 4 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\11_unsafe_fields_preview.md | L7 | 677 | 6 | 0 | 0 | 3 | 3 | 8 | 12 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\12_ferrocene_preview.md | L7 | 664 | 6 | 0 | 0 | 3 | 3 | 5 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\13_lifetime_capture_preview.md | L7 | 254 | 3 | 0 | 0 | 1 | 0 | 4 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\14_pin_ergonomics_preview.md | L7 | 318 | 0 | 0 | 0 | 2 | 2 | 8 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\15_rpitit_preview.md | L7 | 264 | 3 | 0 | 0 | 1 | 0 | 6 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\16_cranelift_backend_preview.md | L7 | 777 | 6 | 0 | 0 | 3 | 3 | 9 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\17_type_alias_impl_trait_preview.md | L7 | 250 | 3 | 0 | 0 | 1 | 0 | 4 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\18_arbitrary_self_types_preview.md | L7 | 414 | 6 | 0 | 0 | 2 | 0 | 9 | 12 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\19_const_trait_preview.md | L7 | 250 | 3 | 0 | 0 | 1 | 0 | 4 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\20_ergonomic_ref_counting_preview.md | L7 | 293 | 0 | 0 | 0 | 0 | 0 | 5 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\21_rust_specification_preview.md | L7 | 663 | 6 | 0 | 0 | 3 | 3 | 6 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\22_async_drop_preview.md | L7 | 798 | 6 | 0 | 0 | 3 | 2 | 7 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\23_field_projections_preview.md | L7 | 407 | 4 | 0 | 0 | 2 | 0 | 8 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\24_borrow_sanitizer.md | L7 | 355 | 0 | 0 | 0 | 1 | 1 | 3 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\25_gen_blocks_preview.md | L7 | 670 | 4 | 0 | 0 | 3 | 3 | 8 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\26_std_autodiff_preview.md | L7 | 336 | 6 | 0 | 0 | 2 | 0 | 5 | 12 | ✅ | ✅ | ✅ | 研究者 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\27_cargo_semver_checks_preview.md | L7 | 211 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\28_wasm_target_evolution.md | L7 | 256 | 3 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\29_aarch64_sve_sme_preview.md | L7 | 269 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\30_rust_in_space.md | L7 | 237 | 3 | 0 | 0 | 1 | 0 | 2 | 6 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\31_specialization_preview.md | L7 | 780 | 4 | 0 | 0 | 3 | 2 | 8 | 12 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\32_compile_time_execution.md | L7 | 752 | 4 | 0 | 0 | 3 | 1 | 6 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\33_autoverus_preview.md | L7 | 178 | 0 | 0 | 0 | 1 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\34_open_enums_preview.md | L7 | 821 | 4 | 0 | 0 | 3 | 3 | 13 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\01_ai_integration.md | L7 | 991 | 2 | 0 | 0 | 2 | 2 | 9 | 2 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\02_formal_methods.md | L7 | 1676 | 9 | 0 | 0 | 1 | 9 | 9 | 3 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\03_evolution.md | L7 | 2189 | 8 | 0 | 0 | 1 | 6 | 19 | 3 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\04_rust_for_linux.md | L7 | 1077 | 4 | 0 | 0 | 3 | 2 | 11 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\05_rust_in_ai.md | L7 | 787 | 6 | 0 | 0 | 3 | 1 | 7 | 12 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\06_rust_for_webassembly.md | L7 | 959 | 4 | 0 | 0 | 3 | 2 | 11 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\07_ebpf_rust.md | L7 | 1003 | 6 | 0 | 0 | 1 | 3 | 15 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
