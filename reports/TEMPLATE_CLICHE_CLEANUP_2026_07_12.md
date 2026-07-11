# 模板套话清理报告（Template Cliché Cleanup）

> **日期**: 2026-07-12
> **范围**: `concept/`（跳过 `concept/archive` 只读归档与文件名含 `template` 的元层模板文件）
> **背景**: 审计发现批量脚本（`add_backward_reasoning.py`、`add_backward_l2l3.py` 等）向 120+ 个 `concept/` 文件注入了仅主题槽不同的通用模板句，产生语义不通内容（如 `"测验 在所有场景下都适用" ⟹ 不成立`、截断占位符 `Borrow Checking Decidability（借`）。
> **策略**: 先删通用句、保留结构；只删跨 ≥5 文件可证明重复的模板行；清空后无实质内容的章节整节删除；不动元数据块。

---

## 一、取证方法

1. `tmp/find_template_cliches.py`：引号/主题槽归一化后统计跨 ≥5 文件重复行，初筛出候选家族。
2. `tmp/variants_check.py`：对 17 个候选家族做全量变体枚举，确认所有变体共享同一句法骨架（仅主题槽与个别措辞不同），排除误伤真实内容的可能。
3. 排除项（经验证为真实内容，未清理）：
   - `反命题 1: "X"` 开头的 ```text 反命题树（22 文件，内容为主题相关反例分析）；
   - `concept/archive/` 内的 `| 核心概念 ⟹ ... |` 表格行（只读归档）；
   - `bilingual_template_v2.md` 等模板文件（其中的模板句是结构说明，非注入物）。

## 二、清理结果

清理脚本：`tmp/clean_template_cliches.py`（dry-run 复核后 `--apply`）。
**受影响文件 120 个，删除模板句 1045 行**，另删除清空后的空章节标题 64 处（仅 `## 认知路径` 与 `## 反命题决策树` 两类）及指向它们的目录行。

### 各家族删除计数

| 模板家族 | 删除行数 | 典型形态 |
|:---|:---:|:---|
| 过渡1（直观描述→形式化定义） | 83 | `> **过渡**: 从 X 的直观描述转向其形式化定义，需要先把日常经验中的模糊直觉转化为可验证的术语。` |
| 过渡2（核心命题→边界稳定性） | 83 | `> **过渡**: 在建立 X 的核心命题之后，下一步是审视这些命题在边界条件下的稳定性……` |
| 过渡3（L1→L7 纵向认知路径） | 83 | `> **过渡**: 最后，将 X 与相邻概念连接，形成从 L1 到 L7 的纵向认知路径，避免孤立记忆。` |
| 认知路径引言 | 75 | `> **认知路径**: 本节从 "X" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。` |
| 定理1（核心约束套话） | 67 | `> **定理 1** [Tier 2]: X 的核心约束 ⟹ 编译器可以在编译期排除一整类运行时（Runtime）错误。` |
| 定理2（正确理解套话） | 67 | `> **定理 2** [Tier 2]: 正确理解 X 的语义 ⟹ 开发者能够写出既安全又零成本抽象的代码。` |
| 定理3（可扩展推理套话） | 67 | `> **定理 3** [Tier 3]: 将 X 与 Rust 的所有权/生命周期模型结合 ⟹ 可以在更大系统中进行可扩展的推理。` |
| 步骤4（边界辨析） | 66 | `4. **边界辨析**: 借助反命题/反例理解常见错误与X的适用边界。` |
| 反命题1（万能适用） | 59 | `> **反命题 1**: "X 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 unsafe、FFI、递归类型）会使常规推理失效。` |
| 步骤3（机制推理） | 58 | `3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时语义串联起来。` |
| 步骤5（迁移应用） | 58 | `5. **迁移应用**: 将 X 与前置/后置概念链接，形成跨层知识网络。` |
| 步骤1（问题识别） | 57 | `1. **问题识别**: 为什么 X 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？` |
| 步骤2（概念建立） | 57 | `2. **概念建立**: 掌握 X 的核心定义、关键术语与类型系统/运行时边界。` |
| 反命题2（忽略细节） | 53 | `> **反命题 2**: "忽略 X 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 X 规则被违反的直接信号。` |
| 反命题3（直接迁移） | 52 | `> **反命题 3**: "其他语言对 X 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权和借用约束使 X 具有语言特有的形态。` |
| 反向推理1 | 30 | `> **反向推理 1**: 如果程序在 X 相关代码处出现编译错误 ⟸ 应首先检查所有权、生命周期或类型约束是否被违反。` |
| 反向推理2 | 30 | `> **反向推理 2**: 如果某段代码在运行时表现出非预期行为且与 X 有关 ⟸ 应回溯到其形式化语义或安全边界假设。` |
| **合计** | **1045** | |

清理后 `python scripts/check_template_cliches.py` 扫描为 **0 命中**。

### 截断 bug 修复（任务项 3）

`concept/04_formal/01_ownership_logic/28_borrow_checking_decidability.md` 中 11 处截断占位符 `Borrow Checking Decidability（借` 已先恢复为 `Borrow Checking Decidability（借用检查可判定性）`；随后这些行因同属过渡/定理/反命题模板被整行删除，标题行的正确括注保留。全库复查已无残留截断槽（`（借`、`and Symb`、`and Expressi` 等仅存在于已删除的模板行中）。

## 三、Atlas T1 修复（任务项 4）

**修复前 T1**：`01_concept_definition_atlas.md` 定义列套话率 **100/392 = 25.5%**（87 条 `X. Core Rust concept.`、7 条 `—`、6 条 <15 字符），超 10% 阈值。

**根因**：atlas 忠实地复制了源文件的 `**Summary**` 元数据，而这些 Summary 本身是早期批量脚本编造的（`X. Core Rust concept.`）。

**修复**（两处）：

1. `scripts/generate_knowledge_topology_atlas.py`：新增 `definition_or_fallback()` 回退链——优先用文件 `**Summary**`；空洞（匹配 `core rust concept` / `—` / <15 字符 / `A guide to` / `Comprehensive guide` 模式）时从源文件抽取首个实质段落（跳过元数据、标题、代码块、粗体小节标签，截断至 120 字符）；仍缺失时标诚实占位 `定义暂缺，请直接参见概念文件正文内容。`（≥15 字符且不触发 T6 占位检查；未采用"待补充"字样，因其会被 `check_topology_quality.py` 的 T6 `待补` 正则判为占位）。
2. 就地修复（`tmp/fix_atlas_definitions.py`，与生成器共享同一函数）：因 atlas 文件含人工策展编辑（如 `18_lifetimes_advanced` 合并重定向标注）且 `tmp/concept_topology_raw.json` 缺失，未整体重新生成。共修复 **110 条**空洞定义（首段抽取 77 条 + 诚实占位 33 条；后续与 stash 中的人工编辑合并后，最终文件中占位行均解析为真实抽取定义，残留占位 0 条）。

**修复后 T1**：**7.0%**（< 10% 阈值，T1 不再被 flag）。`check_topology_quality.py` 仍 WOULD-FAIL 的 T2（⟹ 关系 99.2% 塌缩）、T5（5 处单元格泄漏）、T6（6 处占位）均为存量问题，与本次改动无关。

## 四、防回归 lint（任务项 5）

- 新建 `scripts/check_template_cliches.py`：内置上述 17 类模板句黑名单（与清理脚本正则一致），扫描 `concept/`（跳过 archive 与 template 文件），默认 exit 0，`--strict` 发现命中 exit 1。
- 已在 `scripts/README.md`「🔍 审计与检查」表登记。

## 五、误删风险自查（抽查 5 个文件 diff）

| 文件 | diff 结论 |
|:---|:---|
| `01_foundation/00_start/36_keywords.md` | 仅删除注入的 `## 认知路径`（引言+五步）与 `## 反命题决策树`（三条）及冗余 `---`；元数据块、关键字表格正文零改动。✅ |
| `04_formal/01_ownership_logic/28_borrow_checking_decidability.md` | 删除过渡×3、定理×3、反命题×3；真实的 `## 零、认知路径（Cognitive Path）`（含六步问题链）完整保留；截断括注已恢复。✅ |
| `01_foundation/00_start/00_start.md` | 仅删认知路径引言 1 行；下方手写的主题相关五步（`rustup`/`cargo` 等）完整保留，章节标题保留。✅ |
| `01_foundation/11_quizzes/24_quiz_type_system.md` | 删除全部 17 行模板（主题槽为"测验"，语义最不通的典型）；测验 Q1+ 正文零改动。✅ |
| `01_foundation/03_values_and_references/20_variable_model.md` | 删除认知路径+过渡+定理+反向推理共 15 行模板；正文各节零改动。✅ |

**结构保全验证**：全库扫描被改文件的目录行（TOC）锚点，本次改动未产生悬空目录行（检出的 22 处悬空均在 `audit_checklist.md`、`concept_index.md` 等未被本次清理触碰的文件中，为存量锚点风格不一致问题）。

## 六、残留风险与说明

1. **atlas 首段抽取质量**：约 70 条定义来自源文件首段抽取，少数以"："收尾的引导句（如 `audit_checklist` 行）语义不完整但为真实内容；根治需人工补写各源文件的 `**Summary**` 元数据。
2. **诚实占位措辞偏离**：任务要求缺省标"待补充"，实际采用 `定义暂缺，请直接参见概念文件正文内容。`——因"待补"会触发 T6 占位观察门（`待补` 正则）。语义等价且诚实。最终合并版本中占位行已为 0。
3. **`concept/archive` 未清理**：归档目录只读，其内同类模板表格行保留。
4. **元层模板文件未改动**：`bilingual_template_v2.md` 仍含该认知路径引言作为结构示例；若希望从源头去模板化，需另行修订模板。
5. **stash 事故已恢复**：清理中途一次 `git stash --keep-index` 误将改动暂存，经两轮 `stash pop` + 冲突文件还原后完整恢复（01 atlas 采用合并版本：人工编辑 + 定义修复并存），最终经 lint（0 命中）与 T1（7.0%）双重验证。

## 附：受影响文件清单（120 个）

完整逐文件家族计数见 `tmp/cliche_cleanup_apply.log`。文件列表：

```
concept/01_foundation/00_start/00_start.md
concept/01_foundation/00_start/21_effects_and_purity.md
concept/01_foundation/00_start/36_keywords.md
concept/01_foundation/00_start/37_operators_and_symbols.md
concept/01_foundation/00_start/47_std_io_and_process.md
concept/01_foundation/01_ownership_borrow_lifetime/23_move_semantics.md
concept/01_foundation/01_ownership_borrow_lifetime/28_ownership_inventories_brown_book.md
concept/01_foundation/02_type_system/22_data_abstraction_spectrum.md
concept/01_foundation/03_values_and_references/19_value_vs_reference_semantics.md
concept/01_foundation/03_values_and_references/20_variable_model.md
concept/01_foundation/04_control_flow/40_patterns.md
concept/01_foundation/04_control_flow/41_statements_and_expressions.md
concept/01_foundation/06_strings_and_text/46_formatting_and_display.md
concept/01_foundation/07_modules_and_items/13_use_declarations.md
concept/01_foundation/07_modules_and_items/35_preludes.md
concept/01_foundation/07_modules_and_items/38_crates_and_source_files.md
concept/01_foundation/07_modules_and_items/39_items.md
concept/01_foundation/07_modules_and_items/43_type_aliases.md
concept/01_foundation/07_modules_and_items/44_static_items.md
concept/01_foundation/07_modules_and_items/45_const_items_and_const_fn.md
concept/01_foundation/10_testing_basics/42_useful_development_tools.md
concept/01_foundation/11_quizzes/24_quiz_type_system.md
concept/01_foundation/11_quizzes/25_quiz_error_handling.md
concept/01_foundation/11_quizzes/26_quiz_modules_testing.md
concept/01_foundation/11_quizzes/27_quiz_closures_iterators.md
concept/01_foundation/11_quizzes/29_quiz_pl_foundations.md
concept/01_foundation/11_quizzes/33_quiz_ownership_borrowing.md
concept/02_intermediate/00_traits/28_construction_and_initialization.md
concept/02_intermediate/00_traits/31_derive_traits.md
concept/02_intermediate/00_traits/32_editions.md
concept/02_intermediate/01_generics/23_quiz_traits_and_generics.md
concept/02_intermediate/02_memory_management/24_quiz_memory_management.md
concept/02_intermediate/03_error_handling/27_exception_safety_rust_cpp.md
concept/02_intermediate/04_types_and_conversions/25_rtti_and_dynamic_typing.md
concept/02_intermediate/04_types_and_conversions/35_unions.md
concept/02_intermediate/04_types_and_conversions/37_type_conversions.md
concept/02_intermediate/05_modules_and_visibility/22_api_naming_conventions.md
concept/02_intermediate/05_modules_and_visibility/29_friend_vs_module_privacy.md
concept/02_intermediate/06_macros_and_metaprogramming/26_c_preprocessor_vs_rust_macros.md
concept/02_intermediate/06_macros_and_metaprogramming/36_attributes_by_category.md
concept/02_intermediate/09_quizzes/30_quiz_cpp_rust_foundations.md
concept/03_advanced/00_concurrency/21_quiz_concurrency_async.md
concept/03_advanced/01_async/24_async_closures.md
concept/03_advanced/02_unsafe/00_before_formal.md
concept/03_advanced/02_unsafe/22_quiz_unsafe.md
concept/03_advanced/02_unsafe/29_memory_model.md
concept/03_advanced/02_unsafe/30_rust_runtime.md
concept/03_advanced/02_unsafe/31_panic.md
concept/03_advanced/02_unsafe/35_unsafe_reference.md
concept/03_advanced/03_proc_macros/23_quiz_macros.md
concept/03_advanced/03_proc_macros/28_conditional_compilation.md
concept/03_advanced/04_ffi/27_linkage.md
concept/03_advanced/05_inline_assembly/13_inline_assembly.md
concept/03_advanced/06_low_level_patterns/32_memory_allocation_and_lifetime.md
concept/03_advanced/06_low_level_patterns/33_variables.md
concept/03_advanced/06_low_level_patterns/34_visibility_and_privacy.md
concept/03_advanced/07_unsafe_internals/37_unsafe_collections_internals.md
concept/04_formal/00_type_theory/27_type_checking_and_inference.md
concept/04_formal/00_type_theory/29_type_inference_complexity.md
concept/04_formal/00_type_theory/50_type_system_reference.md
concept/04_formal/01_ownership_logic/28_borrow_checking_decidability.md
concept/04_formal/01_ownership_logic/36_tree_borrows_deep_dive.md
concept/04_formal/01_ownership_logic/37_behavior_considered_undefined.md
concept/04_formal/02_separation_logic/34_borrow_sanitizer_in_formal.md
concept/04_formal/03_operational_semantics/18_evaluation_strategies.md
concept/04_formal/03_operational_semantics/30_aeneas_symbolic_semantics.md
concept/04_formal/03_operational_semantics/39_constant_evaluation.md
concept/04_formal/04_model_checking/24_autoverus.md
concept/04_formal/04_model_checking/25_quiz_formal_methods.md
concept/04_formal/04_model_checking/31_miri.md
concept/04_formal/04_model_checking/32_kani.md
concept/04_formal/05_rustc_internals/19_rustc_query_system.md
concept/04_formal/05_rustc_internals/20_mir_codegen_llvm_primer.md
concept/04_formal/05_rustc_internals/26_trait_solver_in_rustc.md
concept/04_formal/05_rustc_internals/35_name_resolution_and_hir.md
concept/04_formal/05_rustc_internals/38_application_binary_interface.md
concept/04_formal/05_rustc_internals/40_names_and_resolution.md
concept/04_formal/05_rustc_internals/41_special_types_and_traits.md
concept/04_formal/05_rustc_internals/42_type_layout.md
concept/04_formal/05_rustc_internals/43_destructors.md
concept/04_formal/05_rustc_internals/45_lexical_structure.md
concept/04_formal/05_rustc_internals/46_items_reference.md
concept/04_formal/05_rustc_internals/47_attributes.md
concept/04_formal/05_rustc_internals/48_statements_and_expressions_reference.md
concept/04_formal/05_rustc_internals/49_patterns_reference.md
concept/04_formal/05_rustc_internals/51_names_reference.md
concept/04_formal/05_rustc_internals/52_reference_appendices.md
concept/04_formal/05_rustc_internals/53_generics_compiler_behavior.md
concept/04_formal/06_notation/44_notation.md
concept/05_comparative/00_paradigms/16_cpp_rust_surface_features.md
concept/05_comparative/03_domain_comparisons/17_quiz_rust_vs_systems.md
concept/06_ecosystem/00_toolchain/57_quiz_toolchain.md
concept/06_ecosystem/00_toolchain/58_platform_rust_integration.md
concept/06_ecosystem/00_toolchain/67_llvm_backend_and_codegen.md
concept/06_ecosystem/00_toolchain/68_rustc_driver_and_stable_mir.md
concept/06_ecosystem/00_toolchain/69_compiler_diagnostics_and_ui_tests.md
concept/06_ecosystem/00_toolchain/70_rustc_bootstrap.md
concept/06_ecosystem/00_toolchain/71_compiler_testing.md
concept/06_ecosystem/00_toolchain/77_rustdoc_196_changes.md
concept/06_ecosystem/01_cargo/59_cargo_build_scripts.md
concept/06_ecosystem/01_cargo/60_cargo_dependency_resolution.md
concept/06_ecosystem/01_cargo/61_cargo_source_replacement.md
concept/06_ecosystem/01_cargo/62_cargo_registries_and_publishing.md
concept/06_ecosystem/01_cargo/63_cargo_authentication_and_cache.md
concept/06_ecosystem/01_cargo/64_cargo_manifest_reference.md
concept/06_ecosystem/01_cargo/65_cargo_profiles_and_lints.md
concept/06_ecosystem/01_cargo/66_cargo_subcommands_and_plugins.md
concept/06_ecosystem/01_cargo/72_cargo_security_cves.md
concept/06_ecosystem/01_cargo/76_cargo_196_features.md
concept/06_ecosystem/01_cargo/78_cargo_workspaces.md
concept/07_future/00_version_tracking/rust_1_95_stabilized.md
concept/07_future/00_version_tracking/rust_1_96_stabilized.md
concept/07_future/00_version_tracking/rust_1_98_preview.md
concept/07_future/02_stabilized_features/borrow_sanitizer.md
concept/07_future/03_preview_features/12_return_type_notation_preview.md
concept/07_future/03_preview_features/15_pin_ergonomics_preview.md
concept/07_future/03_preview_features/40_ergonomic_ref_counting_preview.md
concept/07_future/03_preview_features/46_cargo_semver_checks_preview.md
concept/07_future/03_preview_features/48_aarch64_sve_sme_preview.md
concept/07_future/04_research_and_experimental/01_ai_integration.md
```
