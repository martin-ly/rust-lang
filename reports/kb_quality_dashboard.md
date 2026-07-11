# 知识体系质量仪表盘 (KB Quality Dashboard)

> 生成时间: 2026-07-11T21:09:57.655017+00:00
> 扫描文件数: 467

## 全局指标

| 指标 | 数值 | 目标 | 状态 |
|:---|:---|:---|:---|
| 总文件数 | 467 | 27 | ✅ |
| 总定理链 (⟹) | 1936 | ≥270 | ✅ |
| 总反命题 | 692 | ≥40 | ✅ |
| 总 Mermaid 图 | 625 | ≥50 | ✅ |
| 编译验证代码块 | 4649 | ≥150 | ✅ |
| 定理矩阵总行 | 20402 | — | — |
| 死链数量 | 1 | 0 | ❌ |
| 反向推理 (⟸) | 273 | ≥50 | ✅ |
| 模板化 ⟹ | 0 | 0 | ✅ |
| 前置概念覆盖率 | 398/403 | 100% | ⚠️ |
| 后置概念覆盖率 | 398/403 | 100% | ⚠️ |
| 双标签覆盖率 | 396/403 | >=95% | ✅ |
| 非法标签组合 | 0 | 0 | ✅ |

## 按层级分布

| 层级 | 文件数 | 平均 ⟹/文件 | 平均过渡段/文件 | 认知路径 | ⟸/文件 | 模板化 | 前置覆盖 | 后置覆盖 | 双标签 |
|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|
| L0 | 64 | 7.5 | 3.1 | 35/64 (54%) | 0.1 | 0 | 14/64 | 13/64 | 46/64 |
| L1 | 55 | 3.1 | 4.2 | 40/55 (72%) | 1.5 | 0 | 55/55 | 55/55 | 55/55 |
| L2 | 40 | 3.4 | 3.5 | 27/40 (67%) | 1.8 | 0 | 39/40 | 39/40 | 39/40 |
| L3 | 60 | 5.4 | 4.1 | 47/60 (78%) | 1.8 | 0 | 60/60 | 60/60 | 60/60 |
| L4 | 53 | 2.7 | 2.4 | 32/53 (60%) | 0.1 | 0 | 51/53 | 51/53 | 51/53 |
| L5 | 19 | 3.4 | 6.1 | 17/19 (89%) | 0.0 | 0 | 19/19 | 19/19 | 19/19 |
| L6 | 115 | 3.7 | 6.6 | 58/115 (50%) | 0.0 | 0 | 114/115 | 114/115 | 112/115 |
| L7 | 61 | 3.2 | 5.4 | 39/61 (63%) | 0.0 | 0 | 60/61 | 60/61 | 60/61 |

## 风险文件

| 文件 | 层级 | 未通过项 |
|:---|:---|:---|
| E:\_src\rust-lang\concept\01_foundation\00_start\21_effects_and_purity.md | L1 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\00_start\36_keywords.md | L1 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\01_foundation\00_start\37_operators_and_symbols.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\00_start\47_std_io_and_process.md | L1 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\23_move_semantics.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\28_ownership_inventories_brown_book.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\22_data_abstraction_spectrum.md | L1 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\03_values_and_references\19_value_vs_reference_semantics.md | L1 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\01_foundation\03_values_and_references\20_variable_model.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\04_control_flow\40_patterns.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\04_control_flow\41_statements_and_expressions.md | L1 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\01_foundation\06_strings_and_text\46_formatting_and_display.md | L1 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\13_use_declarations.md | L1 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\35_preludes.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\43_type_aliases.md | L1 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\44_static_items.md | L1 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\45_const_items_and_const_fn.md | L1 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\24_quiz_type_system.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\25_quiz_error_handling.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\26_quiz_modules_testing.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\27_quiz_closures_iterators.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\29_quiz_pl_foundations.md | L1 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\33_quiz_ownership_borrowing.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\18_lifetimes_advanced.md | L2 | 缺失认知路径; 缺失反命题; 缺失前置概念; 缺失后置概念; 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\28_construction_and_initialization.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\31_derive_traits.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\32_editions.md | L2 | 过渡段落不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\40_generic_associated_types.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\23_quiz_traits_and_generics.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\32_const_generics.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (2 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\24_quiz_memory_management.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\03_error_handling\27_exception_safety_rust_cpp.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (2 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\25_rtti_and_dynamic_typing.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\35_unions.md | L2 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\37_type_conversions.md | L2 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\02_intermediate\05_modules_and_visibility\22_api_naming_conventions.md | L2 | 缺失认知路径; 过渡段落不足 (2 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\05_modules_and_visibility\29_friend_vs_module_privacy.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\26_c_preprocessor_vs_rust_macros.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\36_attributes_by_category.md | L2 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\02_intermediate\09_quizzes\30_quiz_cpp_rust_foundations.md | L2 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\17_send_sync_auto_traits.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 反向推理不足 (⟸ 1 < 2) |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\21_quiz_concurrency_async.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\01_async\24_async_closures.md | L3 | 过渡段落不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\01_async\37_async_cancellation_safety.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\01_async\38_async_boundary_panorama.md | L3 | 过渡段落不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\00_before_formal.md | L3 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\22_quiz_unsafe.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\31_panic.md | L3 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\23_quiz_macros.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\28_conditional_compilation.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\27_linkage.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\05_inline_assembly\13_inline_assembly.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\32_memory_allocation_and_lifetime.md | L3 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\33_variables.md | L3 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\34_visibility_and_privacy.md | L3 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\03_advanced\07_unsafe_internals\37_unsafe_collections_internals.md | L3 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\21_type_semantics.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\27_type_checking_and_inference.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (1 < 3) |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\29_type_inference_complexity.md | L4 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\50_type_system_reference.md | L4 | 缺失认知路径; 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\28_borrow_checking_decidability.md | L4 | 过渡段落不足 (0 < 3); 定理链不足 (1 < 3); 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\36_tree_borrows_deep_dive.md | L4 | 缺失认知路径 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\37_behavior_considered_undefined.md | L4 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\33_safety_tags_in_formal.md | L4 | 缺失认知路径; 缺失反命题; 缺失前置概念; 缺失后置概念; 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\34_borrow_sanitizer_in_formal.md | L4 | 缺失认知路径 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\18_evaluation_strategies.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\30_aeneas_symbolic_semantics.md | L4 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\39_constant_evaluation.md | L4 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\13_formal_methods.md | L4 | 缺失认知路径; 缺失反命题; 缺失前置概念; 缺失后置概念; 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\24_autoverus.md | L4 | 缺失认知路径 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\25_quiz_formal_methods.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\31_miri.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\32_kani.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\19_rustc_query_system.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\20_mir_codegen_llvm_primer.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\26_trait_solver_in_rustc.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\35_name_resolution_and_hir.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\38_application_binary_interface.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\40_names_and_resolution.md | L4 | 定理链不足 (2 < 3) |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\41_special_types_and_traits.md | L4 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\42_type_layout.md | L4 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\43_destructors.md | L4 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\04_formal\06_notation\44_notation.md | L4 | 缺失认知路径; 缺失反命题 |
| E:\_src\rust-lang\concept\05_comparative\00_paradigms\16_cpp_rust_surface_features.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\05_comparative\03_domain_comparisons\17_quiz_rust_vs_systems.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\57_quiz_toolchain.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\58_platform_rust_integration.md | L6 | 过渡段落不足 (2 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\67_llvm_backend_and_codegen.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\68_rustc_driver_and_stable_mir.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\69_compiler_diagnostics_and_ui_tests.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\70_rustc_bootstrap.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\71_compiler_testing.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\77_rustdoc_196_changes.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\79_development_tools.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\59_cargo_build_scripts.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\60_cargo_dependency_resolution.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\61_cargo_source_replacement.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\62_cargo_registries_and_publishing.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\63_cargo_authentication_and_cache.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\64_cargo_manifest_reference.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\65_cargo_profiles_and_lints.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\66_cargo_subcommands_and_plugins.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\72_cargo_security_cves.md | L6 | 过渡段落不足 (2 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\76_cargo_196_features.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\78_cargo_workspaces.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\87_build_std.md | L6 | 缺失内容分级标签 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\57_embedded_hal_1_0_migration.md | L6 | 缺失内容分级标签 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\26_game_development.md | L6 | 缺失前置概念; 缺失后置概念; 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\feature_domain_matrix_197.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\migration_197_decision_tree.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_95_stabilized.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_96_stabilized.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_97_stabilized.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_98_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\02_stabilized_features\borrow_sanitizer.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\12_return_type_notation_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\15_pin_ergonomics_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\31_safety_tags_preview.md | L7 | 缺失前置概念; 缺失后置概念; 缺失受众标签; 缺失内容分级标签 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\40_ergonomic_ref_counting_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\46_cargo_semver_checks_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\03_preview_features\48_aarch64_sve_sme_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\01_ai_integration.md | L7 | 过渡段落不足 (2 < 3); 定理链不足 (2 < 3) |

## 死链检测

| 来源文件 | 引用路径 | 解析后的绝对路径 |
|:---|:---|:---|
| E:\_src\rust-lang\concept\03_advanced\01_async\38_async_boundary_panorama.md | ../02_unsafe/32_unsafe_boundary_panorama.md | E:\_src\rust-lang\concept\03_advanced\02_unsafe\32_unsafe_boundary_panorama.md |

## 文件详细统计

| 文件 | 层级 | 行数 | ⟹ | ⟸ | 模板 | 反命题 | Mermaid | 代码块 | 过渡段 | 认知路径 | 前置 | 后置 | 受众 | 分级 |
|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|
| E:\_src\rust-lang\concept\00_meta\00_framework\bloom_taxonomy.md | L0 | 197 | 1 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\boundary_extension_tree.md | L0 | 359 | 1 | 0 | 0 | 1 | 3 | 1 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\cognitive_dimension_matrix.md | L0 | 395 | 1 | 0 | 0 | 1 | 2 | 0 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\competency_graph.md | L0 | 409 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\comprehensive_rust_mapping.md | L0 | 234 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 → 进阶 | None |
| E:\_src\rust-lang\concept\00_meta\00_framework\concept_definition_decision_forest.md | L0 | 1118 | 3 | 0 | 0 | 1 | 10 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\cpp_rust_engineering_roadmap.md | L0 | 237 | 0 | 0 | 0 | 0 | 2 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 | None |
| E:\_src\rust-lang\concept\00_meta\00_framework\decidability_spectrum.md | L0 | 887 | 1 | 0 | 0 | 1 | 6 | 2 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\expressiveness_multiview.md | L0 | 770 | 0 | 0 | 0 | 1 | 7 | 7 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\fault_tree_analysis_collection.md | L0 | 770 | 1 | 0 | 0 | 1 | 7 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\knowledge_mindmap.md | L0 | 305 | 1 | 0 | 0 | 1 | 2 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\methodology.md | L0 | 531 | 1 | 0 | 0 | 2 | 5 | 1 | 6 | ✅ | ✅ | ✅ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\paradigm_transition_matrix.md | L0 | 323 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\pattern_semantic_space_index.md | L0 | 191 | 0 | 0 | 0 | 0 | 2 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | None |
| E:\_src\rust-lang\concept\00_meta\00_framework\pl_foundations_roadmap.md | L0 | 173 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 | None |
| E:\_src\rust-lang\concept\00_meta\00_framework\semantic_bridge_algorithms_patterns.md | L0 | 703 | 1 | 0 | 0 | 1 | 0 | 7 | 6 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\semantic_expressiveness.md | L0 | 1128 | 1 | 0 | 0 | 1 | 2 | 1 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\semantic_space.md | L0 | 1325 | 10 | 0 | 0 | 2 | 5 | 9 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\theorem_inference_forest.md | L0 | 511 | 3 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\theorem_registry.md | L0 | 204 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\00_meta\00_framework\todos.md | L0 | 344 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\01_terminology\bilingual_template.md | L0 | 165 | 0 | 0 | 0 | 1 | 1 | 1 | 0 | ❌ | ✅ | ✅ | 初学者 | 进阶 | 研究者 | None |
| E:\_src\rust-lang\concept\00_meta\01_terminology\bilingual_template_v2.md | L0 | 322 | 0 | 2 | 0 | 5 | 1 | 5 | 0 | ✅ | ✅ | ✅ | 初学者 | 进阶 | 研究者 | None |
| E:\_src\rust-lang\concept\00_meta\01_terminology\terminology_glossary.md | L0 | 464 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\02_sources\authority_source_map.md | L0 | 211 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\02_sources\international_authority_index.md | L0 | 233 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 研究者 / 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\02_sources\rustbelt_predicate_map.md | L0 | 413 | 9 | 0 | 0 | 1 | 6 | 0 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\02_sources\sources.md | L0 | 489 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 研究者级 |
| E:\_src\rust-lang\concept\00_meta\02_sources\topic_authority_alignment_map.md | L0 | 378 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\00_meta\03_audit\asp_marking_guide.md | L0 | 523 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\audit_checklist.md | L0 | 443 | 1 | 0 | 0 | 2 | 1 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\concept_audit_guide.md | L0 | 105 | 1 | 0 | 0 | 1 | 1 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\concept_consistency_audit_checklist.md | L0 | 14 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\00_meta\03_audit\grading_system.md | L0 | 159 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\quality_dashboard_v2.md | L0 | 325 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\template_deduplication_guide.md | L0 | 93 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 贡献者 | None |
| E:\_src\rust-lang\concept\00_meta\04_navigation\career_landscape.md | L0 | 230 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 入门 → 进阶 | 元层 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\concept_index.md | L0 | 786 | 4 | 0 | 0 | 2 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\cross_reference_matrix.md | L0 | 14 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\00_meta\04_navigation\foundations_gap_closure_index.md | L0 | 143 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | None |
| E:\_src\rust-lang\concept\00_meta\04_navigation\inter_layer_map.md | L0 | 627 | 12 | 0 | 0 | 1 | 2 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\inter_layer_topology.md | L0 | 16 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ✅ | ❌ | ❌ | None | 专家级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\intra_layer_model_map.md | L0 | 336 | 11 | 0 | 0 | 1 | 5 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\learning_guide.md | L0 | 659 | 3 | 0 | 0 | 1 | 1 | 1 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\learning_mvp_path.md | L0 | 367 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ✅ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\learning_mvp_path_en.md | L0 | 269 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\00_meta\04_navigation\navigation.md | L0 | 290 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\problem_graph.md | L0 | 510 | 1 | 0 | 0 | 1 | 7 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\quick_reference.md | L0 | 818 | 1 | 0 | 0 | 1 | 0 | 25 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\self_assessment.md | L0 | 2243 | 1 | 0 | 0 | 1 | 0 | 56 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\01_concept_definition_atlas.md | L0 | 554 | 1 | 1 | 0 | 0 | 0 | 2 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\02_attribute_relationship_atlas.md | L0 | 543 | 27 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\03_scenario_decision_tree_atlas.md | L0 | 288 | 0 | 0 | 0 | 0 | 9 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\04_example_counterexample_atlas.md | L0 | 139 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\05_logical_reasoning_atlas.md | L0 | 187 | 17 | 2 | 0 | 0 | 4 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\06_inter_layer_mapping_atlas.md | L0 | 98 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\07_intra_layer_mapping_atlas.md | L0 | 542 | 355 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\08_concept_source_alignment_atlas.md | L0 | 52 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\09_reasoning_judgment_tree_atlas.md | L0 | 263 | 0 | 0 | 0 | 0 | 6 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\10_gap_and_action_plan.md | L0 | 84 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\kg_ontology_v2.md | L0 | 328 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | None |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\kg_tlo_alignment.md | L0 | 247 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\00_meta\placeholders\placeholder_generic.md | L0 | 23 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\00_meta\trpl_3rd_ed_mapping.md | L0 | 10 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\01_foundation\00_start\00_start.md | L1 | 281 | 4 | 2 | 0 | 1 | 1 | 1 | 6 | ✅ | ✅ | ✅ | 初学者 | 初学者 |
| E:\_src\rust-lang\concept\01_foundation\00_start\06_zero_cost_abstractions.md | L1 | 836 | 3 | 2 | 0 | 3 | 2 | 14 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\15_closure_basics.md | L1 | 889 | 3 | 2 | 0 | 3 | 1 | 18 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\21_effects_and_purity.md | L1 | 681 | 0 | 0 | 0 | 2 | 0 | 17 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\34_pl_prerequisites.md | L1 | 513 | 3 | 2 | 0 | 1 | 0 | 12 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\36_keywords.md | L1 | 154 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\37_operators_and_symbols.md | L1 | 234 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\47_std_io_and_process.md | L1 | 451 | 4 | 4 | 0 | 4 | 1 | 10 | 0 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\00_ownership_borrow_lifetime_knowledge_map.md | L1 | 394 | 3 | 2 | 0 | 1 | 5 | 0 | 5 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\01_ownership.md | L1 | 1906 | 12 | 2 | 0 | 3 | 7 | 46 | 16 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\02_borrowing.md | L1 | 2051 | 4 | 2 | 0 | 3 | 6 | 53 | 20 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\03_lifetimes.md | L1 | 1492 | 19 | 2 | 0 | 3 | 5 | 40 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\23_move_semantics.md | L1 | 251 | 0 | 0 | 0 | 0 | 0 | 4 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\28_ownership_inventories_brown_book.md | L1 | 201 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\30_lifetimes_advanced.md | L1 | 1813 | 3 | 2 | 0 | 1 | 0 | 49 | 10 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\04_type_system.md | L1 | 3279 | 18 | 2 | 0 | 3 | 12 | 63 | 16 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\10_numerics.md | L1 | 1051 | 3 | 2 | 0 | 3 | 1 | 18 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\14_coercion_and_casting.md | L1 | 1008 | 3 | 2 | 0 | 3 | 1 | 18 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\22_data_abstraction_spectrum.md | L1 | 738 | 0 | 0 | 0 | 2 | 0 | 14 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\31_never_type.md | L1 | 563 | 3 | 2 | 0 | 1 | 0 | 15 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\03_values_and_references\05_reference_semantics.md | L1 | 1417 | 3 | 2 | 0 | 4 | 7 | 35 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\03_values_and_references\19_value_vs_reference_semantics.md | L1 | 193 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\03_values_and_references\20_variable_model.md | L1 | 598 | 0 | 0 | 0 | 2 | 0 | 12 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\04_control_flow\07_control_flow.md | L1 | 1619 | 3 | 2 | 0 | 3 | 5 | 25 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\04_control_flow\40_patterns.md | L1 | 232 | 0 | 0 | 0 | 0 | 0 | 10 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\04_control_flow\41_statements_and_expressions.md | L1 | 162 | 0 | 0 | 0 | 0 | 0 | 4 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\05_collections\08_collections.md | L1 | 867 | 3 | 2 | 0 | 3 | 2 | 16 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\05_collections\17_collections_advanced.md | L1 | 997 | 3 | 2 | 0 | 3 | 2 | 11 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\06_strings_and_text\09_strings_and_text.md | L1 | 849 | 3 | 2 | 0 | 3 | 1 | 17 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\06_strings_and_text\18_strings_and_encoding.md | L1 | 831 | 3 | 2 | 0 | 3 | 2 | 9 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\06_strings_and_text\46_formatting_and_display.md | L1 | 420 | 4 | 3 | 0 | 4 | 1 | 9 | 0 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\11_modules_and_paths.md | L1 | 899 | 3 | 2 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\12_functions.md | L1 | 313 | 4 | 2 | 0 | 1 | 0 | 9 | 6 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\13_use_declarations.md | L1 | 230 | 4 | 2 | 0 | 1 | 0 | 8 | 0 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\14_structs.md | L1 | 244 | 4 | 2 | 0 | 1 | 0 | 7 | 6 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\15_enumerations.md | L1 | 246 | 4 | 2 | 0 | 1 | 0 | 9 | 6 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\16_implementations.md | L1 | 240 | 4 | 2 | 0 | 1 | 0 | 7 | 6 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\35_preludes.md | L1 | 208 | 0 | 0 | 0 | 0 | 0 | 4 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\38_crates_and_source_files.md | L1 | 275 | 4 | 2 | 0 | 1 | 1 | 4 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\39_items.md | L1 | 308 | 4 | 2 | 0 | 1 | 1 | 12 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\43_type_aliases.md | L1 | 410 | 4 | 3 | 0 | 4 | 1 | 10 | 0 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\44_static_items.md | L1 | 399 | 4 | 3 | 0 | 4 | 1 | 8 | 0 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\45_const_items_and_const_fn.md | L1 | 420 | 4 | 3 | 0 | 4 | 1 | 8 | 0 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\08_error_handling\13_panic_and_abort.md | L1 | 939 | 3 | 2 | 0 | 3 | 1 | 12 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\08_error_handling\32_error_handling_basics.md | L1 | 986 | 3 | 2 | 0 | 3 | 1 | 15 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\08_error_handling\33_error_handling_control_flow.md | L1 | 280 | 3 | 3 | 0 | 1 | 1 | 9 | 7 | ✅ | ✅ | ✅ | 初学者 | 入门实践级 |
| E:\_src\rust-lang\concept\01_foundation\09_macros_basics\12_attributes_and_macros.md | L1 | 923 | 3 | 2 | 0 | 3 | 1 | 14 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\10_testing_basics\16_testing_basics.md | L1 | 751 | 3 | 2 | 0 | 3 | 1 | 8 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\10_testing_basics\42_useful_development_tools.md | L1 | 232 | 4 | 2 | 0 | 1 | 2 | 0 | 6 | ✅ | ✅ | ✅ | 初学者 | 参考级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\24_quiz_type_system.md | L1 | 494 | 0 | 0 | 0 | 0 | 0 | 14 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\25_quiz_error_handling.md | L1 | 607 | 0 | 0 | 0 | 0 | 0 | 18 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\26_quiz_modules_testing.md | L1 | 696 | 0 | 0 | 0 | 0 | 0 | 22 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\27_quiz_closures_iterators.md | L1 | 682 | 0 | 0 | 0 | 0 | 0 | 33 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\29_quiz_pl_foundations.md | L1 | 153 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\33_quiz_ownership_borrowing.md | L1 | 492 | 0 | 0 | 0 | 0 | 0 | 17 | 0 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\01_traits.md | L2 | 3094 | 15 | 2 | 0 | 7 | 5 | 75 | 10 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\09_serde_patterns.md | L2 | 902 | 3 | 3 | 0 | 3 | 2 | 9 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\18_lifetimes_advanced.md | L2 | 10 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\19_advanced_traits.md | L2 | 971 | 3 | 3 | 0 | 3 | 1 | 21 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\28_construction_and_initialization.md | L2 | 239 | 0 | 0 | 0 | 0 | 0 | 5 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\31_derive_traits.md | L2 | 237 | 0 | 0 | 0 | 0 | 0 | 10 | 0 | ❌ | ✅ | ✅ | 初学者 | 参考级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\32_editions.md | L2 | 321 | 4 | 0 | 0 | 1 | 1 | 6 | 0 | ✅ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\33_rust_release_process.md | L2 | 161 | 0 | 0 | 0 | 1 | 1 | 1 | 0 | ✅ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\39_dispatch_mechanisms.md | L2 | 2042 | 7 | 2 | 0 | 1 | 0 | 40 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\40_generic_associated_types.md | L2 | 530 | 0 | 0 | 0 | 0 | 2 | 14 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\02_generics.md | L2 | 3250 | 16 | 2 | 0 | 7 | 6 | 74 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\23_quiz_traits_and_generics.md | L2 | 660 | 0 | 0 | 0 | 0 | 0 | 19 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\32_const_generics.md | L2 | 470 | 2 | 0 | 0 | 4 | 0 | 14 | 0 | ❌ | ✅ | ✅ | 进阶 | 进阶级 |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\39_type_level_programming.md | L2 | 662 | 7 | 2 | 0 | 1 | 0 | 8 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\03_memory_management.md | L2 | 2177 | 13 | 3 | 0 | 7 | 5 | 57 | 7 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\08_interior_mutability.md | L2 | 873 | 3 | 3 | 0 | 3 | 2 | 11 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\11_cow_and_borrowed.md | L2 | 765 | 3 | 3 | 0 | 3 | 2 | 8 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\12_smart_pointers.md | L2 | 901 | 3 | 3 | 0 | 3 | 2 | 12 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\24_quiz_memory_management.md | L2 | 702 | 0 | 0 | 0 | 0 | 0 | 26 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\03_error_handling\04_error_handling.md | L2 | 2816 | 9 | 3 | 0 | 7 | 8 | 63 | 7 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\03_error_handling\16_error_handling_deep_dive.md | L2 | 775 | 3 | 3 | 0 | 3 | 1 | 9 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\03_error_handling\27_exception_safety_rust_cpp.md | L2 | 233 | 2 | 0 | 0 | 0 | 0 | 4 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\06_range_types.md | L2 | 637 | 3 | 3 | 0 | 3 | 2 | 12 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\07_closure_types.md | L2 | 799 | 3 | 3 | 0 | 3 | 3 | 17 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\14_newtype_and_wrapper.md | L2 | 766 | 3 | 3 | 0 | 3 | 1 | 10 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\20_type_system_advanced.md | L2 | 1255 | 3 | 3 | 0 | 3 | 1 | 18 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\25_rtti_and_dynamic_typing.md | L2 | 232 | 0 | 0 | 0 | 0 | 0 | 5 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\35_unions.md | L2 | 424 | 4 | 3 | 0 | 4 | 1 | 7 | 0 | ✅ | ✅ | ✅ | 进阶 | 进阶 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\37_type_conversions.md | L2 | 455 | 4 | 4 | 0 | 4 | 1 | 10 | 0 | ✅ | ✅ | ✅ | 进阶 | 进阶 |
| E:\_src\rust-lang\concept\02_intermediate\05_modules_and_visibility\10_module_system.md | L2 | 834 | 3 | 3 | 0 | 3 | 3 | 15 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\05_modules_and_visibility\22_api_naming_conventions.md | L2 | 416 | 0 | 0 | 0 | 0 | 0 | 15 | 2 | ❌ | ✅ | ✅ | 进阶 | 中级 |
| E:\_src\rust-lang\concept\02_intermediate\05_modules_and_visibility\29_friend_vs_module_privacy.md | L2 | 226 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\05_assert_matches.md | L2 | 704 | 3 | 3 | 0 | 3 | 3 | 18 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\13_dsl_and_embedding.md | L2 | 834 | 3 | 3 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\17_macro_patterns.md | L2 | 819 | 3 | 3 | 0 | 3 | 1 | 9 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\21_metaprogramming.md | L2 | 872 | 3 | 3 | 0 | 3 | 2 | 8 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\26_c_preprocessor_vs_rust_macros.md | L2 | 228 | 0 | 0 | 0 | 0 | 0 | 4 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\36_attributes_by_category.md | L2 | 467 | 4 | 4 | 0 | 4 | 1 | 10 | 0 | ✅ | ✅ | ✅ | 进阶 | 进阶 |
| E:\_src\rust-lang\concept\02_intermediate\07_iterators_and_closures\15_iterator_patterns.md | L2 | 1346 | 4 | 2 | 0 | 2 | 1 | 22 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\09_quizzes\30_quiz_cpp_rust_foundations.md | L2 | 192 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\01_concurrency.md | L3 | 2106 | 21 | 2 | 0 | 3 | 13 | 27 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\10_concurrency_patterns.md | L3 | 2299 | 3 | 3 | 0 | 3 | 4 | 34 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\11_atomics_and_memory_ordering.md | L3 | 1424 | 4 | 3 | 0 | 3 | 2 | 23 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\16_lock_free.md | L3 | 1218 | 3 | 3 | 0 | 3 | 1 | 20 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\17_send_sync_auto_traits.md | L3 | 482 | 8 | 1 | 0 | 4 | 1 | 13 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\19_parallel_distributed_pattern_spectrum.md | L3 | 1047 | 3 | 3 | 0 | 3 | 0 | 18 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\21_quiz_concurrency_async.md | L3 | 697 | 0 | 0 | 0 | 0 | 0 | 19 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\22_cross_platform_concurrency.md | L3 | 181 | 6 | 2 | 0 | 1 | 0 | 3 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\02_async.md | L3 | 3442 | 17 | 3 | 0 | 6 | 9 | 63 | 3 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\06_pin_unpin.md | L3 | 972 | 3 | 3 | 0 | 3 | 2 | 22 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\24_async_closures.md | L3 | 555 | 3 | 0 | 0 | 1 | 0 | 20 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\25_async_advanced.md | L3 | 1704 | 4 | 3 | 0 | 1 | 1 | 40 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\26_async_patterns.md | L3 | 1219 | 3 | 3 | 0 | 3 | 1 | 22 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\37_async_cancellation_safety.md | L3 | 424 | 0 | 0 | 0 | 5 | 1 | 11 | 0 | ❌ | ✅ | ✅ | 进阶-专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\38_async_boundary_panorama.md | L3 | 330 | 20 | 0 | 0 | 5 | 1 | 8 | 0 | ✅ | ✅ | ✅ | 进阶-专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\39_future_and_executor_mechanisms.md | L3 | 1058 | 7 | 2 | 0 | 1 | 0 | 17 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_process_ipc\01_process_model_and_lifecycle.md | L3 | 423 | 8 | 2 | 0 | 1 | 1 | 3 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_process_ipc\02_advanced_process_management.md | L3 | 316 | 8 | 2 | 0 | 1 | 1 | 3 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_process_ipc\03_async_process_management.md | L3 | 390 | 8 | 2 | 0 | 1 | 1 | 9 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_process_ipc\04_cross_platform_process_management.md | L3 | 319 | 8 | 2 | 0 | 1 | 1 | 5 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_process_ipc\05_ipc_mechanisms.md | L3 | 284 | 8 | 2 | 0 | 1 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_process_ipc\06_process_monitoring_and_diagnostics.md | L3 | 282 | 8 | 2 | 0 | 1 | 1 | 5 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_process_ipc\07_process_security_and_sandboxing.md | L3 | 246 | 8 | 2 | 0 | 1 | 1 | 7 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_process_ipc\08_process_performance_engineering.md | L3 | 230 | 8 | 2 | 0 | 1 | 1 | 3 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_process_ipc\09_process_testing_and_benchmarking.md | L3 | 252 | 8 | 2 | 0 | 1 | 1 | 5 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_process_ipc\10_modern_process_libraries.md | L3 | 247 | 8 | 2 | 0 | 1 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\00_before_formal.md | L3 | 161 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\03_unsafe.md | L3 | 3428 | 14 | 2 | 0 | 4 | 10 | 63 | 3 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\08_nll_and_polonius.md | L3 | 832 | 3 | 3 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\12_unsafe_rust_patterns.md | L3 | 43 | 3 | 0 | 0 | 1 | 0 | 0 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\22_quiz_unsafe.md | L3 | 601 | 0 | 0 | 0 | 0 | 0 | 21 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\29_memory_model.md | L3 | 336 | 5 | 2 | 0 | 1 | 0 | 9 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\30_rust_runtime.md | L3 | 280 | 3 | 2 | 0 | 1 | 0 | 6 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\31_panic.md | L3 | 153 | 0 | 0 | 0 | 0 | 0 | 2 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\35_unsafe_reference.md | L3 | 236 | 3 | 2 | 0 | 1 | 0 | 4 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\04_macros.md | L3 | 2477 | 22 | 3 | 0 | 8 | 8 | 59 | 8 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\07_proc_macro.md | L3 | 1106 | 3 | 3 | 0 | 3 | 2 | 14 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\23_quiz_macros.md | L3 | 661 | 0 | 0 | 0 | 0 | 0 | 23 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\28_conditional_compilation.md | L3 | 243 | 0 | 0 | 0 | 0 | 0 | 8 | 0 | ❌ | ✅ | ✅ | 中级 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\29_proc_macro_code_generation_optimization.md | L3 | 352 | 7 | 2 | 0 | 1 | 0 | 11 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\30_macro_debugging_and_diagnostics.md | L3 | 308 | 7 | 2 | 0 | 1 | 0 | 7 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\31_production_grade_macro_development.md | L3 | 353 | 7 | 2 | 0 | 1 | 0 | 8 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\32_macro_glossary.md | L3 | 673 | 8 | 2 | 0 | 1 | 0 | 27 | 6 | ✅ | ✅ | ✅ | 研究者 | 参考级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\33_macro_faq.md | L3 | 793 | 8 | 2 | 0 | 1 | 0 | 35 | 6 | ✅ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\34_syn_quote_reference.md | L3 | 987 | 8 | 2 | 0 | 1 | 0 | 31 | 6 | ✅ | ✅ | ✅ | 专家 | 参考级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\35_macro_hygiene.md | L3 | 1040 | 8 | 2 | 0 | 1 | 0 | 35 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\05_rust_ffi.md | L3 | 929 | 3 | 3 | 0 | 3 | 3 | 17 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\09_ffi_advanced.md | L3 | 921 | 3 | 3 | 0 | 3 | 1 | 12 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\27_linkage.md | L3 | 392 | 0 | 0 | 0 | 0 | 0 | 14 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\05_inline_assembly\13_inline_assembly.md | L3 | 781 | 0 | 0 | 0 | 0 | 0 | 25 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\14_custom_allocators.md | L3 | 865 | 3 | 3 | 0 | 3 | 1 | 12 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\15_zero_copy_parsing.md | L3 | 908 | 3 | 3 | 0 | 3 | 1 | 13 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\17_type_erasure.md | L3 | 876 | 3 | 3 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\18_network_programming.md | L3 | 1076 | 3 | 3 | 0 | 3 | 2 | 16 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\20_stream_processing_semantics.md | L3 | 847 | 3 | 3 | 0 | 2 | 0 | 8 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\32_memory_allocation_and_lifetime.md | L3 | 162 | 0 | 0 | 0 | 0 | 0 | 6 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\33_variables.md | L3 | 169 | 0 | 0 | 0 | 0 | 0 | 6 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\34_visibility_and_privacy.md | L3 | 190 | 0 | 0 | 0 | 0 | 1 | 6 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\36_ownership_performance_optimization.md | L3 | 190 | 4 | 0 | 0 | 1 | 0 | 8 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\07_unsafe_internals\37_unsafe_collections_internals.md | L3 | 490 | 4 | 4 | 0 | 4 | 1 | 8 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\02_type_theory.md | L4 | 1748 | 27 | 0 | 0 | 4 | 5 | 27 | 3 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\06_subtype_variance.md | L4 | 638 | 3 | 0 | 0 | 3 | 2 | 10 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\08_type_inference.md | L4 | 762 | 3 | 0 | 0 | 3 | 2 | 9 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\10_category_theory.md | L4 | 812 | 3 | 0 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\14_lambda_calculus.md | L4 | 756 | 3 | 0 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\21_type_semantics.md | L4 | 902 | 3 | 0 | 0 | 3 | 0 | 18 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\27_type_checking_and_inference.md | L4 | 403 | 1 | 0 | 0 | 1 | 0 | 10 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\29_type_inference_complexity.md | L4 | 394 | 0 | 0 | 0 | 1 | 0 | 6 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\50_type_system_reference.md | L4 | 413 | 0 | 0 | 0 | 1 | 0 | 1 | 6 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\01_linear_logic.md | L4 | 1242 | 14 | 0 | 0 | 4 | 5 | 13 | 3 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\03_ownership_formal.md | L4 | 1641 | 11 | 0 | 0 | 1 | 5 | 17 | 3 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\09_linear_logic_applications.md | L4 | 748 | 3 | 0 | 0 | 3 | 1 | 10 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\28_borrow_checking_decidability.md | L4 | 392 | 1 | 0 | 0 | 0 | 2 | 8 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\36_tree_borrows_deep_dive.md | L4 | 169 | 0 | 0 | 0 | 1 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\37_behavior_considered_undefined.md | L4 | 162 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 专家 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\04_rustbelt.md | L4 | 1424 | 5 | 0 | 0 | 1 | 5 | 16 | 10 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\11_separation_logic.md | L4 | 840 | 3 | 0 | 0 | 3 | 1 | 10 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\33_safety_tags_in_formal.md | L4 | 14 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\34_borrow_sanitizer_in_formal.md | L4 | 174 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\12_denotational_semantics.md | L4 | 639 | 3 | 0 | 0 | 3 | 1 | 7 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\15_hoare_logic.md | L4 | 910 | 3 | 0 | 0 | 3 | 2 | 8 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\17_operational_semantics.md | L4 | 1078 | 3 | 0 | 0 | 3 | 1 | 13 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\18_evaluation_strategies.md | L4 | 655 | 0 | 0 | 0 | 2 | 0 | 14 | 0 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\20_axiomatic_semantics.md | L4 | 963 | 3 | 0 | 0 | 3 | 0 | 13 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\30_aeneas_symbolic_semantics.md | L4 | 429 | 0 | 0 | 0 | 0 | 1 | 4 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\39_constant_evaluation.md | L4 | 182 | 0 | 0 | 0 | 0 | 0 | 4 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\05_verification_toolchain.md | L4 | 1536 | 3 | 0 | 0 | 1 | 4 | 17 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\13_formal_methods.md | L4 | 23 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\16_aerospace_certification_formal_methods.md | L4 | 1090 | 3 | 0 | 0 | 1 | 1 | 5 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\22_modern_verification_tools.md | L4 | 532 | 3 | 0 | 0 | 1 | 0 | 8 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\23_programming_language_foundations.md | L4 | 432 | 3 | 0 | 0 | 1 | 0 | 10 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\24_autoverus.md | L4 | 184 | 0 | 0 | 0 | 1 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\25_quiz_formal_methods.md | L4 | 582 | 0 | 0 | 0 | 0 | 0 | 10 | 0 | ❌ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\31_miri.md | L4 | 288 | 0 | 0 | 0 | 2 | 1 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 / 工程 / 形式化 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\32_kani.md | L4 | 350 | 0 | 0 | 0 | 0 | 0 | 9 | 0 | ❌ | ✅ | ✅ | 进阶 / 工程 / 形式化 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\19_rustc_query_system.md | L4 | 561 | 0 | 0 | 0 | 0 | 3 | 3 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\20_mir_codegen_llvm_primer.md | L4 | 368 | 8 | 3 | 0 | 1 | 1 | 1 | 0 | ✅ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\26_trait_solver_in_rustc.md | L4 | 420 | 3 | 3 | 0 | 0 | 1 | 8 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\35_name_resolution_and_hir.md | L4 | 313 | 0 | 0 | 0 | 2 | 1 | 5 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\38_application_binary_interface.md | L4 | 239 | 0 | 0 | 0 | 0 | 0 | 6 | 0 | ❌ | ✅ | ✅ | 专家 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\40_names_and_resolution.md | L4 | 221 | 2 | 0 | 0 | 1 | 0 | 2 | 6 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\41_special_types_and_traits.md | L4 | 181 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\42_type_layout.md | L4 | 157 | 0 | 0 | 0 | 0 | 0 | 4 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\43_destructors.md | L4 | 176 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\45_lexical_structure.md | L4 | 267 | 3 | 0 | 0 | 1 | 0 | 6 | 6 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\46_items_reference.md | L4 | 257 | 3 | 0 | 0 | 1 | 0 | 9 | 6 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\47_attributes.md | L4 | 184 | 3 | 0 | 0 | 1 | 0 | 5 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\48_statements_and_expressions_reference.md | L4 | 169 | 3 | 0 | 0 | 1 | 0 | 5 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\49_patterns_reference.md | L4 | 168 | 3 | 0 | 0 | 1 | 0 | 4 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\51_names_reference.md | L4 | 168 | 3 | 0 | 0 | 1 | 0 | 2 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\52_reference_appendices.md | L4 | 170 | 2 | 0 | 0 | 1 | 0 | 1 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\53_generics_compiler_behavior.md | L4 | 184 | 4 | 0 | 0 | 1 | 0 | 5 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\06_notation\44_notation.md | L4 | 138 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\05_comparative\00_paradigms\03_paradigm_matrix.md | L5 | 1215 | 6 | 0 | 0 | 5 | 8 | 11 | 16 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\00_paradigms\05_execution_model_isomorphism.md | L5 | 996 | 3 | 0 | 0 | 1 | 5 | 13 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\05_comparative\00_paradigms\16_cpp_rust_surface_features.md | L5 | 224 | 0 | 0 | 0 | 0 | 0 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 | 研究级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\01_rust_vs_cpp.md | L5 | 2136 | 9 | 0 | 0 | 2 | 10 | 12 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\02_rust_vs_go.md | L5 | 976 | 3 | 0 | 0 | 3 | 6 | 11 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\09_rust_vs_swift.md | L5 | 726 | 3 | 0 | 0 | 3 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\10_rust_vs_zig.md | L5 | 765 | 3 | 0 | 0 | 3 | 1 | 8 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\18_cpp_abi_object_model.md | L5 | 860 | 3 | 0 | 0 | 3 | 0 | 17 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\19_rust_vs_ruby.md | L5 | 743 | 3 | 0 | 0 | 3 | 1 | 8 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\06_rust_vs_java.md | L5 | 617 | 3 | 0 | 0 | 3 | 3 | 7 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\07_rust_vs_python.md | L5 | 695 | 3 | 0 | 0 | 3 | 2 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\08_rust_vs_javascript.md | L5 | 704 | 3 | 0 | 0 | 3 | 2 | 5 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\11_rust_vs_kotlin.md | L5 | 806 | 3 | 0 | 0 | 3 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\12_rust_vs_scala.md | L5 | 767 | 3 | 0 | 0 | 3 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\13_rust_vs_csharp.md | L5 | 834 | 3 | 0 | 0 | 3 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\14_rust_vs_elixir.md | L5 | 826 | 3 | 0 | 0 | 3 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\15_rust_vs_typescript.md | L5 | 918 | 3 | 0 | 0 | 3 | 2 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\03_domain_comparisons\04_safety_boundaries.md | L5 | 1018 | 8 | 0 | 0 | 1 | 7 | 9 | 9 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\05_comparative\03_domain_comparisons\17_quiz_rust_vs_systems.md | L5 | 697 | 0 | 0 | 0 | 0 | 0 | 14 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\01_toolchain.md | L6 | 1893 | 13 | 0 | 0 | 2 | 9 | 15 | 14 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\13_logging_observability.md | L6 | 721 | 6 | 0 | 0 | 3 | 3 | 9 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\28_devops_and_ci_cd.md | L6 | 897 | 6 | 0 | 0 | 3 | 2 | 7 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\45_compiler_internals.md | L6 | 852 | 6 | 0 | 0 | 3 | 0 | 7 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\47_compiler_infrastructure.md | L6 | 376 | 4 | 0 | 0 | 2 | 0 | 1 | 8 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\57_quiz_toolchain.md | L6 | 544 | 0 | 0 | 0 | 0 | 0 | 7 | 0 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\58_platform_rust_integration.md | L6 | 297 | 0 | 0 | 0 | 0 | 0 | 4 | 2 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\67_llvm_backend_and_codegen.md | L6 | 296 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\68_rustc_driver_and_stable_mir.md | L6 | 252 | 0 | 0 | 0 | 0 | 0 | 2 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\69_compiler_diagnostics_and_ui_tests.md | L6 | 286 | 0 | 0 | 0 | 0 | 0 | 5 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\70_rustc_bootstrap.md | L6 | 245 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\71_compiler_testing.md | L6 | 268 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\77_rustdoc_196_changes.md | L6 | 223 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 进阶 / 工程 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\79_development_tools.md | L6 | 202 | 0 | 0 | 0 | 0 | 0 | 5 | 0 | ❌ | ✅ | ✅ | 初学者 | 研究级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\09_cargo_script.md | L6 | 738 | 4 | 0 | 0 | 1 | 2 | 12 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\10_public_private_deps.md | L6 | 253 | 4 | 0 | 0 | 1 | 1 | 1 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\11_resolver_v3_public_feature_unification.md | L6 | 188 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 实践级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\59_cargo_build_scripts.md | L6 | 507 | 0 | 0 | 0 | 2 | 2 | 14 | 0 | ❌ | ✅ | ✅ | 进阶 / 工程 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\60_cargo_dependency_resolution.md | L6 | 513 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\61_cargo_source_replacement.md | L6 | 282 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\62_cargo_registries_and_publishing.md | L6 | 286 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\63_cargo_authentication_and_cache.md | L6 | 281 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\64_cargo_manifest_reference.md | L6 | 312 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 中级 → 高级 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\65_cargo_profiles_and_lints.md | L6 | 304 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\66_cargo_subcommands_and_plugins.md | L6 | 238 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\72_cargo_security_cves.md | L6 | 471 | 4 | 0 | 0 | 3 | 1 | 0 | 2 | ✅ | ✅ | ✅ | 进阶 / 工程 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\76_cargo_196_features.md | L6 | 251 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 进阶 / 工程 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\78_cargo_workspaces.md | L6 | 261 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\80_cargo_getting_started.md | L6 | 177 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\81_cargo_workflow.md | L6 | 179 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\82_cargo_guide_practices.md | L6 | 176 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\83_cargo_configuration.md | L6 | 189 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\84_cargo_commands_reference.md | L6 | 176 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\85_cargo_manifest_targets.md | L6 | 179 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\86_cargo_registry_internals.md | L6 | 168 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 专家 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\87_build_std.md | L6 | 294 | 3 | 0 | 0 | 0 | 2 | 3 | 6 | ❌ | ✅ | ✅ | 进阶 / 工程 | None |
| E:\_src\rust-lang\concept\06_ecosystem\02_core_crates\03_core_crates.md | L6 | 1343 | 8 | 0 | 0 | 2 | 6 | 17 | 3 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\02_patterns.md | L6 | 3070 | 11 | 0 | 0 | 2 | 5 | 45 | 14 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\05_system_design_principles.md | L6 | 743 | 6 | 0 | 0 | 1 | 6 | 8 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\30_system_composability.md | L6 | 803 | 3 | 0 | 0 | 0 | 4 | 23 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\31_microservice_patterns.md | L6 | 1009 | 6 | 0 | 0 | 2 | 6 | 15 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\32_event_driven_architecture.md | L6 | 1039 | 6 | 0 | 0 | 2 | 4 | 15 | 8 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\33_cqrs_event_sourcing.md | L6 | 1461 | 6 | 0 | 0 | 3 | 1 | 18 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\34_idioms_spectrum.md | L6 | 1412 | 6 | 0 | 0 | 1 | 5 | 35 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\35_architecture_patterns.md | L6 | 1276 | 6 | 0 | 0 | 3 | 0 | 13 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\36_pattern_implementation_comparison.md | L6 | 800 | 4 | 0 | 0 | 0 | 0 | 16 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\37_pattern_selection_best_practices.md | L6 | 762 | 4 | 0 | 0 | 0 | 0 | 11 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\38_formal_design_pattern_theory.md | L6 | 1008 | 4 | 0 | 0 | 0 | 0 | 16 | 6 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\39_frontier_research_and_innovative_patterns.md | L6 | 988 | 4 | 0 | 0 | 0 | 0 | 17 | 6 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\41_workflow_theory.md | L6 | 1409 | 6 | 0 | 0 | 3 | 0 | 17 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\42_api_design_patterns.md | L6 | 1298 | 6 | 0 | 0 | 3 | 0 | 19 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\73_pattern_composition_algebra.md | L6 | 727 | 6 | 0 | 0 | 3 | 0 | 15 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\82_engineering_and_production_patterns.md | L6 | 325 | 3 | 0 | 0 | 0 | 0 | 7 | 6 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\84_design_patterns_glossary.md | L6 | 266 | 4 | 0 | 0 | 0 | 0 | 4 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\85_design_patterns_faq.md | L6 | 496 | 4 | 0 | 0 | 0 | 0 | 4 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\18_distributed_systems.md | L6 | 815 | 6 | 0 | 0 | 3 | 1 | 9 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\24_cloud_native.md | L6 | 792 | 4 | 0 | 0 | 3 | 1 | 8 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\27_web_frameworks.md | L6 | 1040 | 6 | 0 | 0 | 4 | 3 | 11 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\38_network_protocols.md | L6 | 527 | 6 | 0 | 0 | 1 | 0 | 7 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\39_high_performance_network_service_architecture.md | L6 | 2068 | 3 | 0 | 0 | 0 | 0 | 19 | 6 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\40_reactive_programming.md | L6 | 1080 | 6 | 0 | 0 | 3 | 0 | 14 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\41_http_client_development.md | L6 | 196 | 0 | 0 | 0 | 0 | 0 | 8 | 0 | ❌ | ✅ | ✅ | 进阶 | 进阶 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\42_glommio_and_thread_per_core.md | L6 | 235 | 3 | 0 | 0 | 0 | 0 | 5 | 6 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\43_websocket_realtime_communication.md | L6 | 733 | 4 | 0 | 0 | 0 | 0 | 10 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\08_wasi.md | L6 | 673 | 6 | 0 | 0 | 5 | 2 | 11 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\17_cross_compilation.md | L6 | 681 | 6 | 0 | 0 | 3 | 1 | 5 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\22_embedded_systems.md | L6 | 974 | 6 | 0 | 0 | 3 | 1 | 10 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\25_cli_development.md | L6 | 789 | 6 | 0 | 0 | 3 | 1 | 9 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\39_os_kernel.md | L6 | 500 | 6 | 0 | 0 | 1 | 0 | 10 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\52_robotics.md | L6 | 1012 | 6 | 0 | 0 | 3 | 0 | 15 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\53_embedded_graphics.md | L6 | 1167 | 6 | 0 | 0 | 3 | 1 | 6 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\56_c_to_rust_translation.md | L6 | 455 | 6 | 0 | 0 | 1 | 0 | 2 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\57_embedded_hal_1_0_migration.md | L6 | 247 | 3 | 0 | 0 | 0 | 0 | 5 | 6 | ❌ | ✅ | ✅ | 进阶 / 工程 | None |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\04_application_domains.md | L6 | 1527 | 8 | 0 | 0 | 2 | 6 | 12 | 3 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\23_database_access.md | L6 | 820 | 6 | 0 | 0 | 3 | 1 | 8 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\36_stream_processing_ecosystem.md | L6 | 570 | 6 | 0 | 0 | 1 | 0 | 10 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\37_database_systems.md | L6 | 544 | 6 | 0 | 0 | 1 | 0 | 9 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\48_data_engineering.md | L6 | 940 | 6 | 0 | 0 | 3 | 0 | 12 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\50_distributed_consensus.md | L6 | 863 | 6 | 0 | 0 | 3 | 0 | 6 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\55_rust_for_data_science.md | L6 | 613 | 6 | 0 | 0 | 3 | 0 | 8 | 12 | ✅ | ✅ | ✅ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\07_security_and_cryptography\19_security_practices.md | L6 | 1091 | 6 | 0 | 0 | 3 | 1 | 8 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\07_security_and_cryptography\43_security_cryptography.md | L6 | 931 | 6 | 0 | 0 | 3 | 0 | 16 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\08_formal_verification\44_formal_ecosystem_tower.md | L6 | 601 | 3 | 0 | 0 | 0 | 2 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\08_formal_verification\74_formal_verification_tools.md | L6 | 942 | 6 | 0 | 0 | 3 | 0 | 12 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_networking\01_advanced_network_protocols.md | L6 | 292 | 3 | 0 | 0 | 0 | 2 | 6 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_networking\02_network_security.md | L6 | 331 | 3 | 0 | 0 | 0 | 0 | 7 | 6 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_networking\03_custom_protocol_implementation.md | L6 | 195 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_networking\04_network_programming_quick_start.md | L6 | 274 | 3 | 0 | 0 | 0 | 2 | 5 | 6 | ❌ | ✅ | ✅ | 进阶 | 指南级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_networking\05_formal_network_protocol_theory.md | L6 | 569 | 3 | 0 | 0 | 0 | 0 | 14 | 6 | ❌ | ✅ | ✅ | 研究者 / 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_networking\06_networking_basics.md | L6 | 870 | 4 | 0 | 0 | 0 | 0 | 15 | 6 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_testing_and_quality\12_testing_strategies.md | L6 | 749 | 6 | 0 | 0 | 3 | 2 | 9 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_testing_and_quality\14_documentation.md | L6 | 677 | 4 | 0 | 0 | 3 | 2 | 7 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_testing_and_quality\16_testing.md | L6 | 763 | 4 | 0 | 0 | 3 | 2 | 8 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_testing_and_quality\17_benchmarking.md | L6 | 168 | 0 | 0 | 0 | 0 | 0 | 5 | 0 | ❌ | ✅ | ✅ | 进阶 | 指南级 |
| E:\_src\rust-lang\concept\06_ecosystem\10_performance\15_performance_optimization.md | L6 | 1155 | 6 | 0 | 0 | 3 | 1 | 13 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\06_blockchain.md | L6 | 922 | 5 | 0 | 0 | 0 | 3 | 14 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\07_game_ecs.md | L6 | 1362 | 3 | 0 | 0 | 0 | 7 | 23 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\11_webassembly.md | L6 | 675 | 6 | 0 | 0 | 3 | 3 | 8 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\20_licensing_and_compliance.md | L6 | 702 | 6 | 0 | 0 | 3 | 1 | 6 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\21_game_development.md | L6 | 704 | 6 | 0 | 0 | 3 | 1 | 8 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\26_game_development.md | L6 | 18 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\29_algorithms_competitive_programming.md | L6 | 1258 | 3 | 0 | 0 | 0 | 0 | 29 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\46_machine_learning_ecosystem.md | L6 | 943 | 6 | 0 | 0 | 3 | 0 | 14 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\49_game_engine_internals.md | L6 | 1133 | 6 | 0 | 0 | 3 | 0 | 13 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\51_quantum_computing_rust.md | L6 | 997 | 4 | 0 | 0 | 3 | 0 | 12 | 12 | ✅ | ✅ | ✅ | 研究者 | 实验级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\54_webassembly_advanced.md | L6 | 1146 | 6 | 0 | 0 | 2 | 0 | 14 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\59_wasm_glossary.md | L6 | 378 | 4 | 0 | 0 | 0 | 0 | 0 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\60_wasm_faq.md | L6 | 480 | 4 | 0 | 0 | 0 | 0 | 6 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\61_wasm_javascript_interop.md | L6 | 479 | 4 | 0 | 0 | 0 | 0 | 5 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\75_industrial_case_studies.md | L6 | 468 | 6 | 0 | 0 | 1 | 0 | 5 | 12 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\76_algorithm_engineering_practice.md | L6 | 1950 | 3 | 0 | 0 | 0 | 0 | 22 | 6 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\77_data_structures_in_rust.md | L6 | 284 | 3 | 0 | 0 | 0 | 1 | 8 | 6 | ❌ | ✅ | ✅ | 进阶 | 进阶 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\78_algorithm_complexity_analysis.md | L6 | 192 | 0 | 0 | 0 | 0 | 0 | 4 | 0 | ❌ | ✅ | ✅ | 进阶 | 进阶 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\79_cutting_edge_algorithms.md | L6 | 246 | 3 | 0 | 0 | 0 | 0 | 3 | 6 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\80_formal_algorithm_theory.md | L6 | 276 | 3 | 0 | 0 | 0 | 0 | 4 | 6 | ❌ | ✅ | ✅ | 专家 | 形式化级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\05_rust_version_tracking.md | L7 | 2585 | 6 | 0 | 0 | 1 | 3 | 9 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\50_nightly_rust.md | L7 | 243 | 3 | 0 | 0 | 0 | 0 | 1 | 6 | ❌ | ✅ | ✅ | 初学者 | 研究级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\feature_domain_matrix_197.md | L7 | 277 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\migration_197_decision_tree.md | L7 | 738 | 0 | 0 | 0 | 0 | 8 | 17 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_90_stabilized.md | L7 | 764 | 4 | 0 | 0 | 0 | 0 | 14 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_91_stabilized.md | L7 | 2552 | 3 | 0 | 0 | 0 | 0 | 81 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_92_stabilized.md | L7 | 2545 | 3 | 0 | 0 | 0 | 0 | 72 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_93_stabilized.md | L7 | 193 | 3 | 0 | 0 | 0 | 0 | 8 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_94_stabilized.md | L7 | 420 | 4 | 0 | 0 | 0 | 0 | 9 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_95_stabilized.md | L7 | 320 | 0 | 0 | 0 | 0 | 0 | 14 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_96_stabilized.md | L7 | 307 | 0 | 0 | 0 | 0 | 0 | 5 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_97_preview.md | L7 | 108 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_97_stabilized.md | L7 | 422 | 0 | 0 | 0 | 0 | 0 | 14 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_98_preview.md | L7 | 580 | 0 | 0 | 0 | 0 | 0 | 7 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\01_edition_roadmap\19_rust_edition_preview.md | L7 | 119 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 进阶 | 研究级 |
| E:\_src\rust-lang\concept\07_future\01_edition_roadmap\23_rust_edition_guide.md | L7 | 18 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\07_future\01_edition_roadmap\44_edition_guide.md | L7 | 893 | 4 | 0 | 0 | 3 | 1 | 13 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\02_stabilized_features\borrow_sanitizer.md | L7 | 346 | 0 | 0 | 0 | 1 | 1 | 3 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\04_effects_system.md | L7 | 1777 | 6 | 0 | 0 | 1 | 4 | 26 | 12 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\07_mcdc_coverage_preview.md | L7 | 564 | 4 | 0 | 0 | 3 | 3 | 5 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\08_safety_tags_preview.md | L7 | 659 | 4 | 0 | 0 | 3 | 3 | 6 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\09_parallel_frontend_preview.md | L7 | 668 | 6 | 0 | 0 | 3 | 3 | 6 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\10_derive_coerce_pointee_preview.md | L7 | 646 | 4 | 0 | 0 | 3 | 3 | 8 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\11_const_trait_impl_preview.md | L7 | 665 | 6 | 0 | 0 | 3 | 2 | 7 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\12_return_type_notation_preview.md | L7 | 492 | 0 | 0 | 0 | 3 | 0 | 10 | 0 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\13_unsafe_fields_preview.md | L7 | 669 | 6 | 0 | 0 | 3 | 3 | 8 | 12 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\14_lifetime_capture_preview.md | L7 | 250 | 3 | 0 | 0 | 1 | 0 | 4 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\15_pin_ergonomics_preview.md | L7 | 305 | 0 | 0 | 0 | 2 | 2 | 8 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\16_type_alias_impl_trait_preview.md | L7 | 246 | 3 | 0 | 0 | 1 | 0 | 4 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\17_const_trait_preview.md | L7 | 243 | 3 | 0 | 0 | 1 | 0 | 4 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\18_async_drop_preview.md | L7 | 790 | 6 | 0 | 0 | 3 | 2 | 7 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\20_borrowsanitizer_preview.md | L7 | 665 | 4 | 0 | 0 | 3 | 3 | 7 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\22_gen_blocks_preview.md | L7 | 660 | 4 | 0 | 0 | 3 | 3 | 8 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\25_open_enums_preview.md | L7 | 809 | 4 | 0 | 0 | 3 | 3 | 13 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\26_specialization_preview.md | L7 | 773 | 4 | 0 | 0 | 3 | 2 | 8 | 12 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\27_compile_time_execution.md | L7 | 740 | 4 | 0 | 0 | 3 | 1 | 6 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\30_stable_abi_preview.md | L7 | 249 | 3 | 0 | 0 | 1 | 0 | 3 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\31_safety_tags_preview.md | L7 | 10 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\07_future\03_preview_features\32_inline_const_pattern_preview.md | L7 | 260 | 3 | 0 | 0 | 1 | 0 | 6 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\33_autoverus_preview.md | L7 | 173 | 0 | 0 | 0 | 1 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\34_must_not_suspend_preview.md | L7 | 240 | 3 | 0 | 0 | 1 | 0 | 4 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\35_ferrocene_preview.md | L7 | 654 | 6 | 0 | 0 | 3 | 3 | 5 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\37_rpitit_preview.md | L7 | 259 | 3 | 0 | 0 | 1 | 0 | 6 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\38_cranelift_backend_preview.md | L7 | 767 | 6 | 0 | 0 | 3 | 3 | 9 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\39_arbitrary_self_types_preview.md | L7 | 411 | 6 | 0 | 0 | 2 | 0 | 9 | 12 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\40_ergonomic_ref_counting_preview.md | L7 | 285 | 0 | 0 | 0 | 0 | 0 | 5 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\41_rust_specification_preview.md | L7 | 655 | 6 | 0 | 0 | 3 | 3 | 6 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\42_field_projections_preview.md | L7 | 402 | 4 | 0 | 0 | 2 | 0 | 8 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\45_std_autodiff_preview.md | L7 | 326 | 6 | 0 | 0 | 2 | 0 | 5 | 12 | ✅ | ✅ | ✅ | 研究者 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\46_cargo_semver_checks_preview.md | L7 | 204 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\47_wasm_target_evolution.md | L7 | 251 | 3 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\48_aarch64_sve_sme_preview.md | L7 | 260 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\49_rust_in_space.md | L7 | 232 | 3 | 0 | 0 | 1 | 0 | 2 | 6 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\01_ai_integration.md | L7 | 981 | 2 | 0 | 0 | 2 | 2 | 9 | 2 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\02_formal_methods.md | L7 | 1664 | 9 | 0 | 0 | 1 | 9 | 9 | 3 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\03_evolution.md | L7 | 2180 | 8 | 0 | 0 | 1 | 6 | 19 | 3 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\21_rust_in_ai.md | L7 | 779 | 6 | 0 | 0 | 3 | 1 | 7 | 12 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\28_rust_for_webassembly.md | L7 | 947 | 4 | 0 | 0 | 3 | 2 | 11 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\29_ebpf_rust.md | L7 | 993 | 6 | 0 | 0 | 1 | 3 | 15 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\43_rust_for_linux.md | L7 | 1067 | 4 | 0 | 0 | 3 | 2 | 11 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\05_roadmaps\24_roadmap.md | L7 | 1068 | 6 | 0 | 0 | 3 | 2 | 17 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
