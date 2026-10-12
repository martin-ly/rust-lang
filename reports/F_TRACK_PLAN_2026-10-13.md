# F 轨道迁移计划（knowledge/ 目录治理）— 只读盘点版

> **日期**: 2026-10-13（中国标准时间）
> **范围**: `G:\_src\rust-lang` 的 `knowledge/` 迁移计划 + 全仓空目录治理计划
> **纪律**: 本阶段严格只读——未移动/修改/创建任何项目内文件，未 commit。本文件位于项目外 scratch 目录。
> **依据**: 根 `AGENTS.md` §2 Canonical 规则、§6 红线 7（stub 纯净度：≤25 行且 ≤2000 字节）、`scripts/check_stub_purity.py` 判定逻辑、`reports/HERMES_SESSION_CHECKPOINT_2026-10-12.md` §3-6/§5、`.kimi/NEXT_STEPS_PLAN_2026_07_16.md` T5。

---

## 0. 结论速览（先说最重要的）

1. **knowledge/ 当前实际状态：15 个 .md 文件，全部为合规 stub/索引，大型非 stub 文件 = 0。**
2. 检查点所称『82 个大型非 stub 文件』是 **2026-07-10 之前的历史基线**（`concept/00_meta/00_framework/todos.md` 2026-07-10 版记录『knowledge/ 大型非 stub 文件：82 个（P2 逐步迁移）』）。该迁移**已于 2026-07-19 完成**：commit `86e06ba37`（2026-07-19）删除 knowledge/ 143 个文件（0 插入），同日 `f3585bd9f` 删除 `archive/knowledge/` 26 个残留；大型正文此前已迁至 `content/safety_critical/`（55 文件）与 `content/ecosystem/deep_dives/`（2026-07-10 commit `5cb654956` 落位）。
3. 因此 **F 轨道的文件迁移部分已无待迁对象**；剩余工作是：①基线口径核对与勘误登记（§2）；②15 个现存文件的处置决定（全部保留，§3）；③空目录治理（38 个非构建空目录，§4）；④悬空引用修复清单（§5）。
4. **move_ledger.csv 实际不存在**（工作区与 git 历史均无此文件；任务上下文称『已存在则追加』与实况不符）——台账初始化本身是 F 轨道第一个待执行动作（§6）。

---

## 1. knowledge/ 盘点（2026-10-13 实测）

- 文件总数：**15**（全部 .md；git 跟踪 15，工作区与 git 一致，无未提交变更）
- 总字节：**7,464 B**；总行数（非空行）：**245**
- 最大文件：`knowledge/INDEX.md`（73 行 / 4,532 B，导航索引，属 `check_stub_purity.py` 的 `EXCLUDE_NAME_KEYWORDS` 豁免）
- 其余 14 个文件：10–12 行 / 412–689 B，**全部命中 stub 声明标记**（『本文件为学习入口 stub』『完整概念解释统一维护在』等），全部满足 AGENTS.md §6 红线 7（≤25 行且 ≤2000 B）
- `check_stub_purity.py` 口径复算：伪 stub=0、空壳页=0、高重复=0（与 `reports/STUB_PURITY_BASELINE_2026_07_15.json` 全绿一致）
- **大型非 stub 文件（>25 行且 >2000 B 且非声明 stub）：0 个**

| 文件 | 行数 | 字节 | 判定 |
|---|---:|---:|---|
| knowledge/INDEX.md | 73 | 4532 | 导航索引（豁免类） |
| knowledge/02_intermediate/01_collections.md | 10 | 462 | 合规 stub |
| knowledge/02_intermediate/05_strings.md | 10 | 470 | 合规 stub |
| knowledge/02_intermediate/06_traits.md | 10 | 431 | 合规 stub |
| knowledge/03_advanced/02_ffi.md | 10 | 412 | 合规 stub |
| knowledge/03_advanced/05_performance_optimization.md | 10 | 525 | 合规 stub |
| knowledge/03_advanced/unsafe/03_unsafe_rust.md | 12 | 689 | 合规 stub |
| knowledge/03_advanced/unsafe/README.md | 10 | 420 | 合规 stub |
| knowledge/04_expert/01_compiler_internals.md | 10 | 491 | 合规 stub |
| knowledge/04_expert/miri/01_tree_borrows.md | 11 | 588 | 合规 stub |
| knowledge/04_expert/miri/README.md | 11 | 412 | 合规 stub（含 1 处断链，见 §5） |
| knowledge/05_reference/03_std_library_cheatsheet.md | 10 | 473 | 合规 stub |
| knowledge/06_ecosystem/02_edition_2024.md | 11 | 588 | 合规 stub |
| knowledge/06_ecosystem/databases/02_sqlx_deep_dive.md | 10 | 469 | 合规 stub |
| knowledge/06_ecosystem/databases/README.md | 11 | 437 | 合规 stub |

---

## 2. 『82 个大型非 stub』基线核对（红线 §6：不采信未验证口径）

**基线出处**：`concept/00_meta/00_framework/todos.md` 于 commit `0a1dabf07`（2026-07-10）写入『`knowledge/` 大型非 stub 文件：82 个（P2 逐步迁移）』；`.kimi/NEXT_STEPS_PLAN_2026_07_16.md` T5 沿用『其余 82 个大型文件按用户指示暂不处理』；检查点 2026-10-12 §3-6 再次沿用。

**核对结果**：
- 在 2026-07-10 前后多个快照（`87f950572`、`e02c78637` 等，knowledge/ 均为 139 文件 / 119 内容页）上，用多种口径复算（>2000B 内容页=68、>1500B=72、>25 行内容页=74、含 README/INDEX 的 >2000B=85），**均无法精确复现 82**；该数字的原始生成脚本口径已不可考。→ 建议登记为『历史口径，不可复现』。
- **迁移实际完成时间线**（git 实证）：
  - 2026-07-10 `5cb654956`：大型专题正文迁入 `content/safety_critical/`、`content/ecosystem/deep_dives/`（AGENTS.md §2.1 允许 content/ 作为专题权威页；`reports/PHASE_G_H_J_COMPLETION_2026_07_10.md` 记录『原路径保留为重定向 stub』）。
  - 2026-07-19 `86e06ba37`：删除 knowledge/ 143 个文件（121 内容页 + 22 README/INDEX，0 插入）；同日 `f3585bd9f` 删除 `archive/knowledge/` 26 个残留副本。
  - 2026-07-15 `STUB_PURITY_BASELINE_2026_07_15`：伪 stub / 空壳 / 高重复 = 0。
- **结论**：F 轨道『82 文件迁移』在 2026-07-19 已实质完成；检查点将其列为未完成项属于**基线滞后**，建议勘误（见台账草案 L1）。

**基线 top-20 大型非 stub 文件 → 当前归宿**（基线快照 `e02c78637`，2026-07-10；按字节降序）：

| # | 基线路径 | 字节 | 当前归宿（实测） | 风险 |
|---|---|---:|---|---|
| 1 | knowledge/99_archive/04_exercises.md | 46440 | 已删除（86e06ba37）；git 历史可恢复 | 无（历史归档件） |
| 2 | knowledge/99_archive/03_case_studies.md | 45720 | 已删除（86e06ba37） | 无 |
| 3 | knowledge/04_expert/safety_critical/04_axiomatic_reasoning/02_rust_axiomatic_reasoning_trees.md | 34987 | 已迁 `content/safety_critical/04_axiomatic_reasoning/02_rust_axiomatic_reasoning_trees.md`（26284B） | 低：concept/ 无同主题页，content/ 为专题权威（§2.1 第 3 条），需在 concept/ 建索引链接 |
| 4 | knowledge/05_reference/03_std_library_cheatsheet.md | 29631 | 已 stub 化（现存 473B） | 无 |
| 5 | knowledge/04_expert/safety_critical/03_decision_trees/01_rust_decision_trees.md | 29075 | 已迁 `content/safety_critical/03_decision_trees/01_rust_decision_trees.md` | 低：决策树门（check_decision_trees.py）已覆盖 |
| 6 | knowledge/04_expert/safety_critical/09_reference/04_comprehensive_international_alignment_completion_report.md | 25951 | 已迁 `content/safety_critical/09_reference/` 同名件 | 低：报告类内容，建议归 reports/ 口径登记 |
| 7 | knowledge/04_expert/safety_critical/09_reference/12_quick_reference_card.md | 25212 | 已迁 `content/safety_critical/09_reference/12_quick_reference_card.md` | 低 |
| 8 | knowledge/04_expert/safety_critical/07_case_studies/05_case_study_05_railway_signaling.md | 24135 | 已迁 `content/safety_critical/07_case_studies/` 同名件 | 低 |
| 9 | knowledge/04_expert/safety_critical/09_reference/17_toolchain_setup_guide.md | 22508 | 已迁 `content/safety_critical/09_reference/` 同名件 | 低 |
| 10 | knowledge/06_ecosystem/deep_dives/02_tokio_deep_dive.md | 21695 | 已迁 `content/ecosystem/deep_dives/02_tokio_deep_dive.md` | 低 |
| 11 | knowledge/05_reference/01_keywords.md | 21342 | 已删除（86e06ba37）；无当前对应权威页 | **中**：关键词速查主题在 concept/ 无 canonical——若需恢复，建议新建 `concept/01_foundation/` 速查页并从 git 历史取正文 |
| 12 | knowledge/04_expert/safety_critical/08_training/02_certification_prep_guide.md | 21332 | 已迁 `content/safety_critical/08_training/02_certification_prep_guide.md` | 低 |
| 13 | knowledge/04_expert/safety_critical/07_case_studies/04_case_study_04_medical_devices.md | 20808 | 已迁 `content/safety_critical/07_case_studies/` 同名件 | 低 |
| 14 | knowledge/04_expert/safety_critical/09_reference/13_rust_safety_critical_coding_guidelines.md | 20645 | 已迁 `content/safety_critical/09_reference/` 同名件 | 低 |
| 15 | knowledge/04_expert/safety_critical/02_matrices/03_rust_ownership_memory_model_matrix.md | 20522 | 已迁 `content/safety_critical/02_matrices/` 同名件 | 低 |
| 16 | knowledge/06_ecosystem/deep_dives/01_axum_deep_dive.md | 20314 | 已迁 `content/ecosystem/deep_dives/01_axum_deep_dive.md` | 低 |
| 17 | knowledge/06_ecosystem/01_cargo_basics.md | 19718 | 已删除（86e06ba37）；concept/ 有 `06_ecosystem/01_cargo/` 系列（01_cargo_script 等 6 页）但无『cargo_basics』总览页 | **中**：Cargo 基础总览缺口——建议新建 `concept/06_ecosystem/01_cargo/00_cargo_basics_overview.md` 并从 git 历史取正文合并 |
| 18 | knowledge/04_expert/safety_critical/09_reference/18_tools_configuration_guide.md | 19716 | 已迁 `content/safety_critical/09_reference/` 同名件 | 低 |
| 19 | knowledge/04_expert/safety_critical/04_axiomatic_reasoning/01_formal_verification_practical_guide.md | 19391 | 已迁 `content/safety_critical/04_axiomatic_reasoning/` 同名件 | 低 |
| 20 | knowledge/06_ecosystem/deployment/01_kubernetes_deployment_guide.md | 19373 | 已删除（86e06ba37）；工作区存在 `k8s/` 目录可承接 | **中**：部署主题无 concept/ canonical——建议评估并入 `concept/06_ecosystem/` 或 content/ 生产实践套件 |

---

## 3. 现存 15 个文件的逐项处置建议（迁移表）

**总原则**：14 个 stub 均合规且其 canonical 目标页全部实测存在（11 个 INDEX.md 链接目标 0 缺失）→ **全部保留，不迁移、不新建**（canonical 唯一性规则：concept/ 已有同主题权威页，禁止新建重复页）。

| 源路径 | 建议 | 目标/理由 | 风险 |
|---|---|---|---|
| knowledge/INDEX.md | 保留 | 导航索引，AGENTS.md §4.0-8 要求与文件重命名同步维护；11 个 concept 链接全部有效 | 无 |
| knowledge/02_intermediate/01_collections.md | 保留 | canonical `concept/01_foundation/05_collections/01_collections.md`（36.9KB）存在 | 无 |
| knowledge/02_intermediate/05_strings.md | 保留 | canonical `concept/01_foundation/06_strings_and_text/01_strings_and_text.md`（39.9KB）存在 | 无 |
| knowledge/02_intermediate/06_traits.md | 保留 | canonical `concept/02_intermediate/00_traits/01_traits.md`（167.8KB）存在 | 无 |
| knowledge/03_advanced/02_ffi.md | 保留 | canonical `concept/03_advanced/04_ffi/01_rust_ffi.md`（47.9KB）存在 | 无 |
| knowledge/03_advanced/05_performance_optimization.md | 保留 | canonical `concept/06_ecosystem/10_performance/01_performance_optimization.md`（61.3KB）存在 | 无 |
| knowledge/03_advanced/unsafe/03_unsafe_rust.md | 保留 | canonical `concept/03_advanced/02_unsafe/01_unsafe.md`（194.6KB）存在 | 无 |
| knowledge/03_advanced/unsafe/README.md | 保留 | 同上 | 无 |
| knowledge/04_expert/01_compiler_internals.md | 保留 | canonical `concept/06_ecosystem/00_toolchain/04_compiler_internals.md`（46.2KB）存在 | 无 |
| knowledge/04_expert/miri/01_tree_borrows.md | 保留 | canonical `concept/04_formal/01_ownership_logic/05_tree_borrows_deep_dive.md`（16.0KB）存在 | 无 |
| knowledge/04_expert/miri/README.md | 保留 + 修链 | 其权威链接 `../../concept/04_formal/04_model_checking/08_miri.md` 断链（相对深度少一级，正确为 `../../../concept/...`；目标文件实测存在） | 低：单行链接修复，需 kb_auditor 复跑验证 |
| knowledge/05_reference/03_std_library_cheatsheet.md | 保留 | 指向 collections 等 canonical 组合 | 无 |
| knowledge/06_ecosystem/02_edition_2024.md | 保留 | canonical `concept/07_future/01_edition_roadmap/02_edition_guide.md`（49.6KB）存在 | 无 |
| knowledge/06_ecosystem/databases/02_sqlx_deep_dive.md | 保留 | canonical `concept/06_ecosystem/06_data_and_distributed/02_database_access.md`（39.3KB）存在 | 无 |
| knowledge/06_ecosystem/databases/README.md | 保留 | 同上 | 无 |

**若未来需要恢复已删除的速查主题**（§2 中 3 个『中风险』缺口），建议路径（均为『新建 canonical + 从 git 历史取正文』，非文件移动）：
- `concept/01_foundation/` 新增 keywords 速查页（源：git `e02c78637:knowledge/05_reference/01_keywords.md`）
- `concept/06_ecosystem/01_cargo/00_cargo_basics_overview.md`（源：git `e02c78637:knowledge/06_ecosystem/01_cargo_basics.md`）
- 部署主题并入 `concept/06_ecosystem/` 或 `content/` 生产实践（源：git `e02c78637:knowledge/06_ecosystem/deployment/01_kubernetes_deployment_guide.md`；工作区已有 `k8s/` 目录）

---

## 4. 空目录盘点与处置（全仓，排除 .git/ 与构建产物 target/）

**实测**：os.walk 全仓 0 文件目录共 598 个，其中 **560 个为构建产物**（`target/debug/.fingerprint/*`、`target/debug/build/*/out`、`examples/examples_check/target/*`——book/、target/ 本就不应入库，不属治理对象），**非构建空目录 38 个**，且 **38 个全部未被 git 跟踪**（git 不存储空目录；`git ls-files` 对下列目录返回 0 文件）。

| 组 | 空目录 | 处置建议（只移动不删除原则） |
|---|---|---|
| A. formal_rust（27 个） | `formal_rust/` 全树 0 文件（engineering-practices、language/17_iot…23_security_verification、refactor、software 等，含 `formal_rust/language` 子空目录 16 个） | **保留 + 登记**。全仓唯一引用是检查点文件本身；不在 Cargo.toml、不在 .gitignore、无任何脚本引用。git 视角已『不存在』。建议：在台账登记为 vestigial 骨架；若主代理决定清理，按『只移动』原则整体 `Move-Item formal_rust → archive/formal_rust_skeleton_2026-10/`（空目录移动不损失任何内容），但**不建议删除** |
| B. crates 残壳（11 个） | `crates/c11_frameworks/src/api/{auth,graphql,grpc,openapi,rest,sercurity}`（6）；`crates/c14_workflow/src/{benchmarks,tests,rust189/{async,concurrency,features}}`（5） | **保留 + 登记**。两 crate 均不在 workspace members（members 为 c11_macro_system_proc、c14_semantic_web），git 0 文件，无引用。注意 `api/sercurity` 为拼写错误目录。建议：登记为废弃骨架；如主代理要恢复这两个 crate，需先补 Cargo.toml 再迁移内容；否则可整体移入 `archive/`（移动而非删除） |
| C. book/ 构建骨架（2 个） | `book/05_comparative/06_quizzes`、`book/07_future/archive` | **保留不动**。book/ 是 mdbook 构建产物目录（AGENTS.md §2.1：除 README 外不应提交），空骨架随下次 `mdbook build` 再生成，无需治理 |

**登记方式**（符合『只移动不删除』）：38 个目录全部写入台账『保留登记』行；任何后续清理一律走『移动到 archive/』路径并逐条记台账，禁止 delete。

---

## 5. 附带发现：悬空引用（供主轨道修复，非移动操作）

1. `knowledge/04_expert/miri/README.md` → `../../concept/04_formal/04_model_checking/08_miri.md` 断链（应为 `../../../`；目标存在）。
2. 活跃目录中 **5 个文件共 24 处**指向已删除 knowledge/ 路径的引用（历史叙述性引用为主）：
   - `docs/11_project/04_hierarchy_mapping_master.md`（T-001/T-010/T-020 等映射行引用 `knowledge/01_fundamentals/ownership.md` 等 6 处）
   - `docs/00_meta/04_documentation_division_of_labor.md`（2 处）
   - `concept/00_meta/02_sources/01_authority_source_map.md`（Batch 1 行，1 处）
   - `docs/03_reference/quick_reference/19_rust_195_features_cheatsheet.md`（1 处）
   - `CHANGELOG.md`（历史条目，建议保留原文并加『已迁移』注记，不改写历史）
   建议：非 CHANGELOG 的 4 个文件改链至对应 concept/ canonical 或标注『已删除（86e06ba37）』；修复后跑 `scripts/kb_auditor.py` 验证死链=0。

---

## 6. move_ledger.csv 追加行草案（台账不存在，首行含表头初始化）

> 实测：项目根**无** move_ledger.csv（工作区与全部 git 历史均无）。以下为初始化草案；本阶段未写入项目。列建议：`date,action,source,target,reason,risk,verified_by`。

```csv
date,action,source,target,reason,risk,verified_by
2026-10-13,ledger_init,,move_ledger.csv,F 轨道启动：台账不存在，需初始化（本行为首条登记）,无,本计划 §0/§6
2026-10-13,勘误登记,reports/HERMES_SESSION_CHECKPOINT_2026-10-12.md §3-6,reports/F_TRACK_BASELINE_CORRECTION_2026-10-13.md,『82 个大型非 stub』为 2026-07-10 历史口径（todos.md@0a1dabf07）；迁移已于 2026-07-19 完成（86e06ba37 删 143 文件；正文迁 content/ 于 5cb654956）；当前 knowledge/ 大型非 stub=0,低,git ls-tree 86e06ba37~1 / e02c78637 复算 + STUB_PURITY_BASELINE_2026_07_15
2026-10-13,保留登记,knowledge/ 15 个 .md（14 stub + INDEX.md）,原地保留,全部满足 AGENTS.md §6 红线 7；canonical 目标页 11/11 实测存在；无迁移对象,无,check_stub_purity 口径复算（伪 stub=0）
2026-10-13,修链待办,knowledge/04_expert/miri/README.md,同文件（../../→../../../）,权威页链接相对深度错误致断链,低,kb_auditor 复跑验收
2026-10-13,保留登记,formal_rust/ 全树（27 个空目录 0 文件）,原地保留（可选：整体移动至 archive/formal_rust_skeleton_2026-10/）,vestigial 骨架；git 0 文件；无引用；只移动不删除原则下不得删除,低,os.walk + git ls-files 实测
2026-10-13,保留登记,crates/c11_frameworks/（6 个空目录）,原地保留（可选：整体移动至 archive/）,不在 workspace members；git 0 文件；含拼写错误目录 api/sercurity,低,同上
2026-10-13,保留登记,crates/c14_workflow/（5 个空目录）,原地保留（可选：整体移动至 archive/）,不在 workspace members；git 0 文件,低,同上
2026-10-13,保留登记,book/05_comparative/06_quizzes 与 book/07_future/archive,原地保留,mdbook 构建骨架，随构建再生成,无,AGENTS.md §2.1 book/ 定位
2026-10-13,修链待办,docs/11_project/04_hierarchy_mapping_master.md 等 4 文件（22 处）,改链至 concept/ canonical 或标注已删除,悬空 knowledge/ 引用（CHANGELOG 历史条目保留原文）,低,kb_auditor 复跑验收
```

---

## 7. 执行顺序建议（下一阶段可写操作时）

1. 初始化 move_ledger.csv（表头 + 上表登记行）。
2. 修 `knowledge/04_expert/miri/README.md` 断链（1 行）。
3. 修 4 个文件的悬空引用（CHANGELOG 除外）。
4. 跑 `python scripts/kb_auditor.py` + `python scripts/check_stub_purity.py --strict` 验收（红线 §6：完成声明须有门报告）。
5. 空目录：仅登记；如主代理决定清理，走『整体移动到 archive/』并逐条记台账。
6. 可选补缺口：keywords / cargo_basics / k8s 部署三个主题的 concept/ canonical 新建（从 git 历史取正文，走 canonical 唯一性审查 + overlap 门）。

*本文件为只读盘点产物，位于 scratch：`C:\Users\Administrator\AppData\Local\hermes\cache\scratch\F_TRACK_PLAN_2026-10-13.md`；未写入项目目录，未做任何 git 操作。*
