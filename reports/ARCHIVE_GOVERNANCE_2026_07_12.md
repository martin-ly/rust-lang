# 归档依赖治理报告（ARCHIVE_GOVERNANCE_2026_07_12）

> **日期**: 2026-07-12
> **范围**: 活跃目录（`concept/`、`knowledge/`、`docs/`、`content/`、`guides/`、`crates/`、`exercises/`）指向 `archive/` 的引用治理 + `concept/archive/` 外迁
> **依据**: AGENTS.md §2（archive/ 只读，活跃内容不得依赖归档；归档集中于顶层 `archive/`）

---

## 1. 盘点结果（治理前）

全量扫描活跃目录 Markdown 链接（含 `archive/` 的 URL）：

| 指标 | 数值 |
|---|---|
| 活跃目录 → archive/ 引用总数 | **503** |
| 被引 archive 目标（去重） | **143** |
| 引用带锚点（#anchor） | 3 |

### Top 20 热点（治理前）

| 引用数 | 被引归档文件 | 活跃等价物 |
|---:|---|---|
| 45 | `archive/research_notes_2026_06_25/type_theory/10_type_system_foundations.md` | ✅ |
| 34 | `archive/research_notes_2026_06_25/formal_methods/10_async_state_machine.md` | ✅ |
| 33 | `archive/research_notes_2026_06_25/formal_methods/10_send_sync_formalization.md` | ✅ |
| 26 | `archive/research_notes_2026_06_25/10_proof_index.md` | ✅ |
| 23 | `archive/research_notes_2026_06_25/formal_methods/README.md` | ✅ |
| 20 | `archive/research_notes_2026_06_25/type_theory/10_trait_system_formalization.md` | ✅ |
| 19 | `archive/research_notes_2026_06_25/10_tools_guide.md` | ✅ |
| 16 | `archive/research_notes_2026_06_25/formal_methods/10_pin_self_referential.md` | ✅ |
| 13 | `archive/deprecated/coq_skeleton/README.md` | 无（标注） |
| 12 | `archive/research_notes_2026_06_25/software_design_theory/03_execution_models/06_boundary_analysis.md` | ✅ |
| 10 | `archive/research_notes_2026_06_25/10_core_theorems_full_proofs.md` | ✅ |
| 10 | `archive/research_notes_2026_06_25/software_design_theory/01_design_patterns_formal/README.md` | ✅ |
| 9 | `archive/research_notes_2026_06_25/software_design_theory/04_compositional_engineering/README.md` | ✅ |
| 8 | `archive/research_notes_2026_06_25/type_theory/10_construction_capability.md` | ✅ |
| 8 | `archive/research_notes_2026_06_25/10_best_practices.md` | ✅ |
| 6 | `archive/research_notes_2026_06_25/experiments/10_performance_benchmarks.md` | ✅ |
| 6 | `archive/research_notes_2026_06_25/10_quality_checklist.md` | 无（迁移） |
| 6 | `archive/research_notes_2026_06_25/10_research_methodology.md` | ✅ |
| 5 | `archive/cargo_package_management_from_c02/00_INDEX.md` | 无（标注） |
| 5 | `archive/research_notes_2026_06_25/10_formal_proof_system_guide.md` | ✅ |

## 2. 分类统计与处置

| 类别 | 目标数 | 引用数 | 处置 |
|---|---:|---:|---|
| A 有活跃等价物（`archive/research_notes_2026_06_25/` ↔ `docs/research_notes/` 同名同路径） | 62 | 378 | 链接改指活跃版本 |
| B 无活跃等价物但内容有价值 | 7 | 14 | 迁移归档文件为活跃文件 + 链接改指 |
| C `concept/archive/` 嵌入权威层 | 35 个文件 | 1 个活跃链接 + 1 处行内路径 | 整体外迁顶层归档 + 更新引用 |
| D 纯历史引用（Coq 骨架、历史审计报告、归档知识库、历史版本材料） | 74 | 105 | 保留 + 显式"归档只读"标注 |
| E knowledge 内部归档区（`knowledge/99_archive/`，非顶层 archive/） | 3 | 6 | 不属本次范围，保持不变 |

### 2.1 A 类：链接改指活跃版本（378 处）

- 机械重写规则：URL 中 `archive/research_notes_2026_06_25/X` → 从源文件到 `docs/research_notes/X` 的相对路径（保留锚点与链接文本）。
- 实际重写 **392 处 / 68 个文件**（含 B 类 14 处）。
- 重写量最大的文件：`docs/07_project/07_documentation_cross_reference_guide.md`（71）、`docs/01_learning/01_learning_path_planning.md`（19）、`docs/04_thinking/04_applications_analysis_view.md`（15）、`docs/rust-formal-engineering-system/09_research_agenda/04_research_methods/README.md`（14）等。

**内容覆盖验证**：

- 3 处带锚点引用（`10_construction_capability.md#类型构造决策树`、`06_boundary_analysis.md#确定性判定决策树`、`#决策树选择执行模型`）——活跃版本均存在对应标题/显式锚点，**全部覆盖**。
- 对引用数 ≥4 的 25 个热点目标做标题集对比：活跃版本标题数全部 ≥ 归档版本；归档版独有标题共 44 个，其中绝大多数为 emoji slug 差异（⚠️ 等）与"Rust 1.94 更新内容"小节——后者在活跃版中已被"Rust 1.97.0 更新内容"小节替代（如 `10_type_system_foundations.md`、`10_tools_guide.md`、`10_best_practices.md`、`10_research_methodology.md`）。**无需回迁内容**。

### 2.2 B 类：迁移归档文件为活跃文件（7 个文件，14 处引用）

迁移到 `docs/research_notes/` 同名位置，内容不改，仅在 H1 后加一行"迁移说明"：

| 新位置（活跃） | 来源 |
|---|---|
| `docs/research_notes/10_quality_checklist.md` | `archive/research_notes_2026_06_25/10_quality_checklist.md`（583 行） |
| `docs/research_notes/10_formal_verification_guide.md` | 同上前缀（790 行） |
| `docs/research_notes/10_coq_of_rust_integration_plan.md` | 同上（121 行） |
| `docs/research_notes/10_aeneas_integration_plan.md` | 同上（640 行） |
| `docs/research_notes/formal_methods/10_macro_system_mindmap.md` | 同上（665 行） |
| `docs/research_notes/10_rust_193_language_features_comprehensive_analysis.md` | 同上（11 行，本身为重定向 stub；同时修复了其内部指向 `archive/research_notes/` 与错误相对路径的链接） |
| `docs/research_notes/10_rust_194_research_update.md` | 同上（10 行，本身为指向 `concept/07_future/` 的重定向 stub） |

> 附带收益：这 7 个文件此前在活跃文档中还有大量**相对链接形式**的死链（如 `[QUALITY_CHECKLIST](10_quality_checklist.md)`），迁移后一并复活（如 `10_aeneas_integration_plan.md` 被 8+ 活跃文件以相对链接引用）。

### 2.3 C 类：`concept/archive/` 外迁（35 个文件）

- 整体移动：`concept/archive/` → **`archive/2026/concept_archive/`**（35 个文件，符合"归档集中顶层"）。
- 更新的活跃引用：
  - `concept/README.md` L128：`archive/PLAN_concept_knowledge_system_v2.md` → `../archive/2026/concept_archive/PLAN_concept_knowledge_system_v2.md`（加"归档只读"说明）；
  - `concept/00_meta/knowledge_topology/kg_ontology_v2.md` L39：行内路径 `archive/kg_ontology_v1_archived.md` → `archive/2026/concept_archive/kg_ontology_v1_archived.md`；
  - `scripts/README.md` 归档目录示例更新。
- `concept/SUMMARY.md` 检查：无任何 archive 相关条目，无需清理。
- 保持不动的历史叙述（行内代码/变更日志 prose，非链接）：`concept/07_future/00_version_tracking/05_rust_version_tracking.md`、`concept/07_future/04_research_and_experimental/03_evolution.md`、根 `CHANGELOG.md` 中对 `concept/archive/` 的历史描述。
- **已知代价（归档只读，未修改归档内容）**：`archive/2026/concept_archive/` 内文件原有 **414 个 `../` 相对链接**指向 `concept/` 活跃页，迁移后这些相对链接失效；`ARCHIVE_INDEX.md` 内自述路径亦为旧路径。归档只读约束下不予修改，如需恢复可整体加一层 `../../concept/` 路径修正（需放宽只读限制）。

### 2.4 D 类：纯历史引用显式标注（105 处 → 全部带"归档只读"上下文）

- 本次新增标注 **74 行 / 36 个文件**（在归档链接后追加 `（归档只读）`）；其余 31 处原已含"已归档/归档说明/历史版本存档"等上下文（如 `docs/02_reference/quick_reference/02_cargo_cheatsheet.md`、`knowledge/03_advanced/macros/*` stub、`docs/06_toolchain/06_0x_*` stub）。
- 主要目标群：
  - `archive/deprecated/coq_skeleton/`（Coq 形式化骨架 .v 文件与 README，21 处）——分布在 `docs/research_notes/10_formal_methods_master_index.md`、`10_system_summary.md`、`10_rustbelt_alignment.md` 等；
  - `archive/rust-ownership-decidability/`（归档子项目，25 处）——集中于 `docs/00_meta/00_formal_content_master_index.md`（18 处已标注）；
  - `archive/reports/2026_07/`（历史审计/基线报告，12 处）——`concept/00_meta/04_navigation/navigation.md` 等；
  - `archive/cargo_package_management_from_c02/`（6 处，原已标注"已归档"）；
  - `archive/docs/06_toolchain/06_0x_*`（4 处，活跃 stub 的"历史版本存档"指向，原已标注）。

## 3. 治理后验证

| 指标 | 治理前 | 治理后 |
|---|---:|---:|
| 活跃目录 → archive/ 引用总数 | 503 | 105 |
| 其中无"归档只读"上下文标注 | ~470+ | **0** |
| 死链（指向 archive 的引用） | 0 | 0 |
| `concept/archive/` 内嵌归档文件 | 35 | 0（已迁 `archive/2026/concept_archive/`） |

- `python scripts/kb_auditor.py --link-check`：**死链 1**——`concept/03_advanced/01_async/38_async_boundary_panorama.md` → `../02_unsafe/32_unsafe_boundary_panorama.md`（目标文件全库不存在）。该文件为**未提交的新增文件（untracked），死链为既有问题，与本次归档治理无关**，未在本次范围内处置。
- 重写时每个新链接均做 `os.path.exists` 校验，0 个 WARN。

## 4. 迁移/改动清单汇总

- 重写链接：68 个活跃文件，392 处链接。
- 新增活跃文件（归档迁入）：7 个（见 §2.2）。
- 新增标注：36 个活跃文件，74 行。
- 移动：`concept/archive/`（35 文件）→ `archive/2026/concept_archive/`。
- 其他编辑：`concept/README.md`、`concept/00_meta/knowledge_topology/kg_ontology_v2.md`、`scripts/README.md`、`docs/research_notes/10_rust_193_language_features_comprehensive_analysis.md`（修复 stub 内部链接）。
- git 状态：236 modified / 35 deleted / 11 untracked（未 commit）。

## 5. 剩余显式历史引用清单（105 处，均已标注，按目标聚合）

详见 §2.4；Top 目标：`archive/deprecated/coq_skeleton/README.md`（13）、`archive/cargo_package_management_from_c02/00_INDEX.md`（5）、`archive/deprecated/README.md`（5）、`archive/reports/2026_07/SEMANTIC_SPACE_CRITICAL_AUDIT_2026_05_24.md`（4）、`archive/deprecated/coq_skeleton/OWNERSHIP_UNIQUENESS.v`（4）、`archive/rust-ownership-decidability/actor-specialty/ACTOR_MODEL_DEEP_DIVE.md`（3）、`archive/docs/2026_03_reorganization/VERSION_INDEX.md`（3）等共 68 个目标。

另有 `knowledge/99_archive/` 6 处引用（`knowledge/INDEX.md` → `02_version_tracking.md`/`03_case_studies.md`/`04_exercises.md`）——属于 knowledge 目录内部归档区，非顶层 `archive/` 依赖，未处理。

## 6. 后续建议（本次未做）

1. `docs/research_notes/` 中存在与本次无关的既有死链目标：`10_contributing.md`、`10_maintenance_guide.md`、`10_statistics.md`、`10_writing_guide.md`、`10_feature_template.md`、`10_example.md`、`10_template.md` 仅存在于 `archive/research_notes_2026_06_25/`，被活跃文档以相对链接引用——建议按 B 类同样方式迁回。
2. 修复既有死链 `38_async_boundary_panorama.md` → `32_unsafe_boundary_panorama.md`（或创建该 unsafe 域边界全景页）。
3. 若允许修改归档文件，可批量修正 `archive/2026/concept_archive/` 内 414 个 `../` 链接为 `../../concept/` 前缀，并更新 `ARCHIVE_INDEX.md` 自述路径。
4. `knowledge/99_archive/` 是否应并入顶层 `archive/`（AGENTS.md "归档集中顶层"），建议单独决策。
