# 概念知识体系自动化审计报告 v2.0

> 生成时间: 2026-06-07T07:42
> 扫描文件数: 266
> 版本对齐: Rust 1.96.0 stable

## 摘要

| 指标 | 数值 | 状态 |
|:---|:---|:---|
| 扫描文件数 | 266 | — |
| 跨文件链接 ≥3 | 263/266 | ⚠️ |
| 死链接文件 | 8 | ❌ |
| 命名规范符合 | 265/266 | ⚠️ |
| 代码块问题文件 | 0 | ✅ |
| 显式 Bloom 标注 | 261/266 | ✅ |
| 平均来源标注率 | 12.3% | ⚠️ |
| TODO 待完成 | 11 | ⚠️ |
| TODO 已完成 | 237 | — |

## 跨文件链接不足的文件

| 文件 | 链接数 | 现有链接目标 |
|:---|:---|:---|
| concept/00_meta/grading_system.md | 0 | 无 |
| concept/00_meta/terminology_glossary.md | 0 | 无 |
| concept/03_advanced/00_before_formal.md | 0 | 无 |

## 死链接检测

| 源文件 | 链接文本 | 死链接目标 |
|:---|:---|:---|
| concept/00_meta/LEARNING_MVP_PATH.md | exercises/rustlings_style/variables.rs | `../exercises/rustlings_style/variables.rs` |
| concept/00_meta/LEARNING_MVP_PATH.md | exercises/rustlings_style/move_semantics.rs | `../exercises/rustlings_style/move_semantics.rs` |
| concept/01_foundation/03_lifetimes.md | `exercises/rustlings_style/ex05_struct_lifetime.rs` | `../exercises/rustlings_style/ex05_struct_lifetime.rs` |
| concept/02_intermediate/02_generics.md | `exercises/rustlings_style/ex07_generic_type_fix.rs` | `../exercises/rustlings_style/ex07_generic_type_fix.rs` |
| concept/05_comparative/17_quiz_rust_vs_systems.md | Rust vs Go | `./03_rust_vs_go.md` |
| concept/05_comparative/17_quiz_rust_vs_systems.md | → Rust vs Go 详解 | `./03_rust_vs_go.md` |
| concept/05_comparative/17_quiz_rust_vs_systems.md | → Rust vs Go 详解 | `./03_rust_vs_go.md` |
| concept/05_comparative/17_quiz_rust_vs_systems.md | → Rust for Linux 详解 | `../06_ecosystem/19_rust_for_linux.md` |
| concept/05_comparative/17_quiz_rust_vs_systems.md | Rust vs Go | `./03_rust_vs_go.md` |
| concept/06_ecosystem/57_quiz_toolchain.md | Cargo Workspaces | `./02_cargo_workspace.md` |
| concept/06_ecosystem/57_quiz_toolchain.md | → Cargo Workspace 详解 | `./02_cargo_workspace.md` |
| concept/07_future/15_pin_ergonomics_preview.md | Async Drop | `./08_async_drop_preview.md` |
| concept/07_future/17_ergonomic_ref_counting_preview.md | Smart Pointers | `../02_intermediate/05_smart_pointers.md` |
| concept/07_future/17_ergonomic_ref_counting_preview.md | Smart Pointers | `../02_intermediate/05_smart_pointers.md` |
| concept/07_future/25_aarch64_sve_sme_preview.md | Rust for Linux | `../06_ecosystem/19_rust_for_linux.md` |

## 命名不规范的文件

- concept/07_future/rust_1_97_preview.md

## 缺少 Bloom 层级标注的文件

| 文件 | 检测到的 Bloom 关键词 |
|:---|:---|
| concept/00_meta/terminology_glossary.md | 分析, 应用, 理解, 评价 |
| concept/03_advanced/00_before_formal.md | 创造 |
| concept/04_formal/22_modern_verification_tools.md | 分析, 创造, 应用, 评价 |
| concept/07_future/17_ergonomic_ref_counting_preview.md | 创造, 理解 |
| concept/07_future/rust_1_97_preview.md | 分析, 创造, 应用, 理解 |

## 来源标注率偏低的文件 (< 10%)

| 文件 | 标注数 | 估算段落数 | 标注率 |
|:---|:---|:---|:---|
| concept/00_meta/05_cross_reference_matrix.md | 2 | 12 | 2.3% |
| concept/00_meta/08_concept_audit_guide.md | 2 | 10 | 2.7% |
| concept/00_meta/grading_system.md | 0 | 14 | 0.0% |
| concept/00_meta/LEARNING_MVP_PATH.md | 0 | 50 | 0.0% |
| concept/01_foundation/00_pl_prerequisites.md | 0 | 79 | 0.0% |
| concept/01_foundation/23_quiz_ownership_borrowing.md | 7 | 81 | 4.3% |
| concept/01_foundation/24_quiz_type_system.md | 7 | 80 | 4.8% |
| concept/01_foundation/25_quiz_error_handling.md | 6 | 99 | 3.6% |
| concept/01_foundation/26_quiz_modules_testing.md | 6 | 113 | 3.4% |
| concept/01_foundation/27_quiz_closures_iterators.md | 5 | 123 | 2.7% |
| concept/02_intermediate/05_assert_matches.md | 31 | 105 | 9.3% |
| concept/02_intermediate/08_interior_mutability.md | 35 | 114 | 9.0% |
| concept/02_intermediate/09_serde_patterns.md | 37 | 132 | 8.0% |
| concept/02_intermediate/11_cow_and_borrowed.md | 34 | 114 | 9.6% |
| concept/02_intermediate/23_quiz_traits_and_generics.md | 6 | 132 | 3.0% |
| concept/02_intermediate/24_quiz_memory_management.md | 6 | 128 | 3.1% |
| concept/03_advanced/09_ffi_advanced.md | 35 | 137 | 9.9% |
| concept/03_advanced/11_atomics_and_memory_ordering.md | 34 | 142 | 9.8% |
| concept/03_advanced/12_unsafe_rust_patterns.md | 44 | 140 | 9.6% |
| concept/03_advanced/16_lock_free.md | 32 | 131 | 9.8% |
| concept/03_advanced/19_parallel_distributed_pattern_spectrum.md | 27 | 136 | 6.9% |
| concept/03_advanced/20_stream_processing_semantics.md | 37 | 134 | 8.7% |
| concept/03_advanced/21_quiz_concurrency_async.md | 5 | 136 | 2.4% |
| concept/03_advanced/22_quiz_unsafe.md | 8 | 123 | 4.2% |
| concept/03_advanced/23_quiz_macros.md | 5 | 111 | 2.8% |
| concept/04_formal/18_evaluation_strategies.md | 26 | 91 | 8.0% |
| concept/04_formal/23_programming_language_foundations.md | 6 | 67 | 4.3% |
| concept/04_formal/24_quiz_formal_methods.md | 12 | 102 | 6.7% |
| concept/05_comparative/01_rust_vs_cpp.md | 77 | 487 | 9.7% |
| concept/05_comparative/17_quiz_rust_vs_systems.md | 4 | 109 | 2.3% |
| concept/06_ecosystem/16_testing.md | 35 | 106 | 9.9% |
| concept/06_ecosystem/21_game_development.md | 22 | 100 | 8.9% |
| concept/06_ecosystem/31_microservice_patterns.md | 27 | 134 | 8.9% |
| concept/06_ecosystem/33_cqrs_event_sourcing.md | 50 | 193 | 9.3% |
| concept/06_ecosystem/35_architecture_patterns.md | 48 | 170 | 9.9% |
| concept/06_ecosystem/35_pattern_composition_algebra.md | 22 | 116 | 8.7% |
| concept/06_ecosystem/36_stream_processing_ecosystem.md | 23 | 92 | 9.8% |
| concept/06_ecosystem/37_database_systems.md | 18 | 93 | 8.1% |
| concept/06_ecosystem/39_os_kernel.md | 19 | 79 | 8.3% |
| concept/06_ecosystem/40_reactive_programming.md | 44 | 180 | 9.6% |
| concept/06_ecosystem/41_workflow_theory.md | 55 | 159 | 9.7% |
| concept/06_ecosystem/42_api_design_patterns.md | 53 | 167 | 9.5% |
| concept/06_ecosystem/47_compiler_infrastructure.md | 9 | 55 | 6.3% |
| concept/06_ecosystem/48_data_engineering.md | 38 | 138 | 9.8% |
| concept/06_ecosystem/48_industrial_case_studies.md | 1 | 53 | 0.7% |
| concept/06_ecosystem/49_game_engine_internals.md | 40 | 162 | 9.6% |
| concept/06_ecosystem/57_quiz_toolchain.md | 3 | 90 | 1.9% |
| concept/07_future/04_effects_system.md | 84 | 325 | 9.2% |
| concept/07_future/07_mcdc_coverage_preview.md | 22 | 67 | 8.5% |
| concept/07_future/08_safety_tags_preview.md | 26 | 80 | 6.8% |
| concept/07_future/09_parallel_frontend_preview.md | 29 | 81 | 7.3% |
| concept/07_future/11_stable_abi_preview.md | 6 | 9 | 5.8% |
| concept/07_future/12_inline_const_pattern_preview.md | 6 | 9 | 6.2% |
| concept/07_future/12_return_type_notation_preview.md | 30 | 70 | 9.3% |
| concept/07_future/13_must_not_suspend_preview.md | 5 | 9 | 5.3% |
| concept/07_future/14_lifetime_capture_preview.md | 6 | 17 | 9.0% |
| concept/07_future/15_pin_ergonomics_preview.md | 3 | 42 | 3.1% |
| concept/07_future/15_rpitit_preview.md | 6 | 15 | 9.2% |
| concept/07_future/16_type_alias_impl_trait_preview.md | 6 | 9 | 9.8% |
| concept/07_future/17_const_trait_preview.md | 6 | 11 | 6.3% |
| concept/07_future/17_ergonomic_ref_counting_preview.md | 1 | 37 | 1.0% |
| concept/07_future/17_rust_specification_preview.md | 29 | 75 | 9.3% |
| concept/07_future/19_rust_edition_preview.md | 3 | 9 | 2.9% |
| concept/07_future/19_rust_for_linux.md | 27 | 111 | 7.4% |
| concept/07_future/20_borrowsanitizer_preview.md | 37 | 77 | 9.2% |
| concept/07_future/21_rust_in_ai.md | 30 | 109 | 8.1% |
| concept/07_future/22_gen_blocks_preview.md | 5 | 9 | 8.8% |
| concept/07_future/22_std_autodiff_preview.md | 4 | 42 | 3.0% |
| concept/07_future/24_cargo_semver_checks_preview.md | 3 | 26 | 4.1% |
| concept/07_future/24_wasm_target_evolution.md | 3 | 12 | 3.6% |
| concept/07_future/25_aarch64_sve_sme_preview.md | 1 | 31 | 1.1% |
| concept/07_future/26_rust_in_space.md | 3 | 9 | 3.3% |
| concept/07_future/28_rust_for_webassembly.md | 37 | 138 | 7.6% |
| concept/07_future/29_ebpf_rust.md | 29 | 149 | 6.3% |
| concept/07_future/rust_1_97_preview.md | 16 | 81 | 8.6% |

## 方法论说明

- **跨文件链接**: 检测指向其他 `.md` 文件的相对链接，目标文件必须存在
- **Bloom 层级**: 基于认知层级关键词的启发式检测 + 显式标注检查
- **来源标注率**: 标注数 / (段落数 + 论断数 × 2)，期望 ≥ 15%
- **命名规范**: `NN_english_name.md`，入口文件 (`00.md`–`07.md`) 除外

> 本报告与 `scripts/concept_consistency_auditor.py` 互补：本脚本做快速健康检查，后者做深度概念冲突检测。
