# 五件套属性/关系/反例补齐报告（P1-b）

> 日期：2026-07-13 ｜ 执行：P1-b 子代理 ｜ 依据：`.kimi/FOLLOW_UP_PLAN_P1_P5_2026_07_13.md`（P1-b 第 4–5 项）
> 约束遵守：仅追加新节（「📋 关键属性」「🔗 概念关系」「⚠️ 反例与陷阱」），未改动任何既有节正文，与并行 P1-a 占位回填代理无冲突面。

## 1. 任务 1+2：属性表与关系节（39 页）

对 L1–L3 缺「属性」结构的内容页补「📋 关键属性」节（3–6 行表格：属性 × 取值/判定 × 依据），同页补「🔗 概念关系」节（上位/下位/对偶/组合/依赖 + 指向既有 concept 页的链接）。

> 口径说明：扫描时将「概念属性矩阵」等既有属性结构视为已覆盖（避免与正文重复），故 01/02 层实际缺口为 21 页而非关键词初筛的 40+；余量由 03_advanced 核心页补足至 39 页。

| 层 | 页数 | 文件 |
|---|---|---|
| 01_foundation | 11 | `00_start/01_pl_prerequisites`、`00_start/04_effects_and_purity`、`00_start/06_keywords`、`01_ownership_borrow_lifetime/04_lifetimes_advanced`、`02_type_system/04_coercion_and_casting`、`02_type_system/05_data_abstraction_spectrum`、`03_values_and_references/01_reference_semantics`、`03_values_and_references/03_variable_model`、`04_control_flow/01_control_flow`、`07_modules_and_items/12_items`、`10_testing_basics/02_useful_development_tools` |
| 02_intermediate | 7 | `00_traits/07_generic_associated_types`、`01_generics/02_const_generics`、`02_memory_management/03_cow_and_borrowed`、`03_error_handling/02_error_handling_deep_dive`、`03_error_handling/04_exception_safety_rust_cpp`、`04_types_and_conversions/05_rtti_and_dynamic_typing`、`06_macros_and_metaprogramming/01_assert_matches` |
| 03_advanced | 21 | `00_concurrency/02_send_sync_auto_traits`、`00_concurrency/04_cross_platform_concurrency`、`00_concurrency/05_atomics_and_memory_ordering`、`01_async/02_async_advanced`、`01_async/03_async_patterns`、`01_async/05_async_cancellation_safety`、`01_async/07_async_closures`、`01_async/08_pin_unpin`、`01_async/09_stream_algebra_and_backpressure`、`01_async/12_waker_contract_deep_dive`、`01_async/13_async_trait_object_safety`、`02_unsafe/02_unsafe_boundary_panorama`、`02_unsafe/03_nll_and_polonius`、`02_unsafe/06_memory_model`、`02_unsafe/07_unsafe_reference`、`03_proc_macros/02_proc_macro`、`03_proc_macros/04_macro_debugging_and_diagnostics`、`03_proc_macros/09_macro_hygiene`、`04_ffi/02_ffi_advanced`、`06_low_level_patterns/03_type_erasure`、`06_low_level_patterns/05_stream_processing_semantics` |

- 跳过的候选：`02_unsafe/04_unsafe_rust_patterns.md` 实为重定向 stub（46 行，「已重定向」标记），不予补齐。
- 关系节链接全部指向既有 concept 页，经脚本逐条校验：**新增链接死链 0**。关系语义与 KG 的 instanceOf/dependsOn 边方向保持一致（上位=is-a、依赖=dependsOn）。

## 2. 任务 3：反例补齐 30 页（覆盖率 64.1% → 71.1%）

`check_mindmap_coverage.py` 复跑实测：

| 指标 | 补齐前（本轮基线） | 补齐后 |
|---|---|---|
| 反例存在页 | 275 / 429（64.1%） | **305 / 429（71.1%）** |
| 04_formal | 35（63.6%） | 49（89.1%） |
| 05_comparative | 18（90.0%） | 20（100.0%） |
| 06_ecosystem | 78（61.4%） | 92（72.4%） |

> 注：计划书基线记为 54.1%，系 07-09 口径；本轮起点实测已为 64.1%（W2-a 等中间轮次提升）。70% 目标已达成（+30 页，恰为计划量）。

**A 类：compile_fail 反例 14 页**（全部经 `rustc 1.97.0 --edition 2024` 实测复现，修正对照块经 `--emit=metadata` 实测通过）：

| 文件 | 错误码 | 主题 |
|---|---|---|
| `04_formal/00_type_theory/09_type_system_reference.md` | E0308 | 类型失配 |
| `04_formal/01_ownership_logic/05_tree_borrows_deep_dive.md` | E0502 | 别名×可变冲突 |
| `04_formal/01_ownership_logic/06_behavior_considered_undefined.md` | E0381 | 未初始化使用 |
| `04_formal/03_operational_semantics/07_constant_evaluation.md` | E0080 | const 越界求值 |
| `04_formal/05_rustc_internals/06_names_and_resolution.md` | E0425 | 名称解析失败 |
| `04_formal/05_rustc_internals/09_destructors.md` | E0509 | 移出 Drop 类型字段 |
| `04_formal/05_rustc_internals/10_lexical_structure.md` | literal out of range | 字面量越界 |
| `04_formal/05_rustc_internals/13_statements_and_expressions_reference.md` | E0308 | 尾表达式误加分号 |
| `04_formal/05_rustc_internals/14_patterns_reference.md` | E0005 | 可反驳模式用于 let |
| `04_formal/05_rustc_internals/15_generics_compiler_behavior.md` | E0282 | 推断信息不足 |
| `04_formal/05_rustc_internals/16_names_reference.md` | E0428 | 重复定义 |
| `06_ecosystem/11_domain_applications/09_data_structures_in_rust.md` | E0505 | 自引用结构体 |
| `05_comparative/00_paradigms/03_cpp_rust_surface_features.md` | E0502 | C++ 迭代器失效对照 |
| `06_ecosystem/09_testing_and_quality/04_benchmarking.md` | E0554 | stable 上用 `#[bench]` |

**B 类：文本/TOML/ignore 类陷阱 16 页**：`04_formal/02_separation_logic/04_borrow_sanitizer_in_formal`、`04_formal/03_operational_semantics/06_aeneas_symbolic_semantics`、`04_formal/04_model_checking/07_autoverus`、`05_comparative/00_paradigms/04_five_models_definition_matrix`、`06_ecosystem/00_toolchain/{05_compiler_infrastructure,07_rustdoc_196_changes,09_llvm_backend_and_codegen,13_compiler_testing}`、`06_ecosystem/01_cargo/{02_public_private_deps,03_resolver_v3_public_feature_unification,07_cargo_source_replacement,11_cargo_profiles_and_lints,14_cargo_workspaces,22_build_std}`、`06_ecosystem/05_systems_and_embedded/09_embedded_hal_1_0_migration`、`06_ecosystem/07_security_and_cryptography/03_cargo_vet_supply_chain`。

- 每页节长 ≤40 行，结构为「反例（含实测输出或配置片段）+ 修正对照 + 陷阱要点」。
- 实测勘误 1 处：`02_public_private_deps` 原拟用 E0446 compile_fail，rustc 1.97 实测该模式已转为 lint/可编译，遂改写为「编译器不再兜底」的行为陷阱（结论以实测为准）。

## 3. 任务 4：55 处父容器引导语 —— 已被并行工作清零

`python scripts/audit_content_completeness.py --json tmp/completeness_p1b.json` 复跑（2026-07-14 05:2x）：

- **空章节(父容器无引导语): 0 处 / 0 文件**（计划书基线为 55 处 / 21 文件）；
- JSON 明细 507 文件的 `empty_parent` 字段全部为空列表。

结论：该 55 处已由并行 P1-a 占位回填（或前序轮次）处理完毕，本任务无需重复施工。**如实登记：本项 0 改动。**

## 4. 验证汇总

| 检查 | 命令 | 结果 |
|---|---|---|
| 死链/跨层 | `python scripts/kb_auditor.py` | exit 0；死链 **0**、跨层问题 **0**、模板化 ⟹ 0 |
| 构建 | `mdbook build` | exit 0（仅既有 search index 体积 WARN） |
| 反例覆盖率 | `python scripts/check_mindmap_coverage.py` | 64.1% → **71.1%**（基线阈值 40% 远超） |
| 内容重叠（阻断门 8） | `python scripts/detect_content_overlap.py` | 1 对（迁移判定树 vs 速查表，**既有基线**，非本轮新增） |
| 新增链接 | 自写脚本逐条解析 39 页新节链接 | 死链 0 |
| compile_fail 真实性 | `rustc 1.97.0 --edition 2024` 逐块实测 | 14/14 复现预期错误码；5 个非平凡修正块 `--emit=metadata` 通过 |

## 5. 遗留与后续登记

1. **属性/关系剩余候选**：03_advanced 仍有 ~25 页（多为 `06_low_level_patterns`、`08_process_ipc` 的工程页）及 04–07 层 ~180 页缺属性/关系结构，登记为后续轮次候选（本轮按计划只覆盖 L1–L3 核心 ~40 页）。
2. **反例剩余**：06_ecosystem 35 页、07_future 28 页仍无反例节（多为主题索引/FAQ/版本跟踪页，反例适配性低），后续按页型筛选。
3. **TOC 未回填**：39 页新节未注册到各页「📑 目录」（避免与并行代理同改目录区冲突）；后续轮次可由目录生成器统一刷新。
4. **临时脚本**：`tmp/p1b_*.py`、`tmp/ce_test/` 为本轮施工脚手架（tmp/ 不入版本控制，按 AGENTS.md §6 红线保留于 tmp/）。
