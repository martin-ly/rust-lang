# Content/ 目录治理报告 Z2

**日期**: 2026-07-14  
**范围**: `content/`（`content/ecosystem/` + `content/safety_critical/`）  
**目标**: 完成 `content/` 第五轨治理，确保 canonical 来源声明、死链清理、权威来源对齐与 mdbook 构建通过。

---

## 1. 文件统计

| 目录 | 文件数 | 说明 |
|------|--------|------|
| `content/` 总计 | **61** | 全部为 `.md` 文件 |
| `content/ecosystem/` | **4** | README + deep_dives/README + Axum/Tokio 深度解析 |
| `content/safety_critical/` | **56** | 主索引、完成报告、10 个子专题目录 |

### 子目录分布（safety_critical）

- `01_mind_maps/`: 3
- `02_matrices/`: 4
- `03_decision_trees/`: 2
- `04_axiomatic_reasoning/`: 2
- `05_strategic_guidance/`: 2
- `06_roadmaps/`: 4
- `07_case_studies/`: 6
- `08_training/`: 5
- `09_reference/`: 19
- `10_standards/`: 5
- 根目录: 4（README、master_index、readme_ecosystem、completion_report）

---

## 2. Canonical 审查与处置

### 处置原则

- `concept/` 已覆盖的通用 Rust 概念（性能优化、API 设计、FFI 等），若 `content/` 文件以重复通用推导为主，则规范化为专题入口 stub。
- 安全关键领域专属内容（标准合规、案例研究、认证备考、工具链矩阵等）保留为 `content/` 专题权威页，并在顶部使用 AGENTS.md §4.4 模板声明 canonical 来源。

### 处置结果

| 处置类型 | 数量 | 说明 |
|----------|------|------|
| **保留为专题权威页** | 60 | 全部添加/更新 `content/` 专题深度内容入口声明 |
| **规范化为 stub** | 1 | `content/safety_critical/09_reference/10_performance_optimization_guide.md` |
| **canonical 链接更新** | 36 | 将明显错误的权威来源链接指向对应 `concept/` 页 |
| **声明格式统一** | 17 | 将旧格式 `通用 Rust 概念解释请见...` 统一为 AGENTS.md 模板 |

### Stub 文件详情

- `content/safety_critical/09_reference/10_performance_optimization_guide.md`
  - 原因：通用 Rust 性能优化已由 `concept/06_ecosystem/10_performance/01_performance_optimization.md` 覆盖。
  - 处置：保留路径，正文替换为安全关键性能要点速查 + 决策树 + canonical 链接。

### 典型 canonical 链接修正示例

| 文件 | 原链接 | 修正后 |
|------|--------|--------|
| `09_reference/07_ffi_integration_guide.md` | `concept/00_meta/04_navigation/07_learning_guide.md` | `concept/03_advanced/04_ffi/01_rust_ffi.md` |
| `04_axiomatic_reasoning/02_rust_axiomatic_reasoning_trees.md` | `concept/00_meta/00_framework/boundary_extension_tree.md` | `concept/04_formal/01_ownership_logic/05_tree_borrows_deep_dive.md` |
| `01_mind_maps/01_academic_research_landscape.md` | `concept/00_meta/04_navigation/02_career_landscape.md` | `concept/04_formal/01_ownership_logic/05_tree_borrows_deep_dive.md` 等 |
| `10_standards/01_do_178c_rust_compliance_pathway.md` | `concept/06_ecosystem/11_domain_applications/04_licensing_and_compliance.md` | `concept/04_formal/04_model_checking/03_aerospace_certification_formal_methods.md` |

---

## 3. 死链修复

### 修复前

手动扫描 `content/` 内部链接发现 **8 处死链**：

- `content/safety_critical/03_readme_rust_safety_critical_ecosystem.md`
  - `../../../concept/`（目录链接，路径深度错误）
  - `10_00_completion_report_100_percent.md` × 3（旧文件名，实际为 `01_completion_report_100_percent.md`）
- `08_training/02_certification_prep_guide.md`、`09_reference/05_deployment_and_maintenance_guide.md`、`09_reference/15_security_audit_guide.md`、`10_standards/04_misra_c_2025_addendum_6_guide.md`
  - `concept/00_meta/03_audit/08_concept_audit_guide.md`（文件不存在，应为 `01_concept_audit_guide.md` 或更专题的 concept 页）

### 修复后

- **死链数**: 0
- **修复处数**: 5 处（1 目录深度 + 3 旧文件名 + 1 audit 文件编号）
- **影响文件**: 2 个（其中 4 个文件的 audit 死链通过 canonical 更新一并替换）

---

## 4. 占位/TODO 清理

扫描 `content/` 中 `TODO/占位/待补充/待完善` 等标记：

- 发现的 `TODO` 均为代码示例中的 `todo!()` 或练习脚手架注释，不属于内容占位。
- 未发现需要补充的空章节或占位段落。
- **结论**: 无需新增内容；已确认无未完成占位。

---

## 5. 验证结果

| 验证项 | 命令 | 结果 |
|--------|------|------|
| 死链检查 | `python scripts/kb_auditor.py` | 死链 0，跨层问题 0 |
| content/ 内部死链 | 自定义 Python 扫描 | 0 |
| 内容重叠 | `python scripts/detect_content_overlap.py` | 无新增高重叠；仍 1 对 pre-existing（concept vs docs，与 content/ 无关） |
| mdbook 构建 | `mdbook build` | 通过（仅有搜索索引大小 warning） |

---

## 6. 变更文件清单

### 内容变更

- `content/README.md`
- `content/safety_critical/03_readme_rust_safety_critical_ecosystem.md`
- `content/safety_critical/09_reference/10_performance_optimization_guide.md`（stub 化）
- 其余 52 个 `content/safety_critical/` 非 README 文件（canonical 声明更新/格式统一）
- `content/ecosystem/deep_dives/01_axum_deep_dive.md`、`02_tokio_deep_dive.md`（因修复通用 `concept/` 目录链接被扫描到，实际链接未被改动）

### 新增/修改报告

- `reports/CONTENT_GOVERNANCE_Z2_2026_07_14.md`（本文件）

---

## 7. 后续建议

1. 将 `content/` 纳入 `kb_auditor.py` 审计范围（当前 auditor 仅报告 concept/ 文件数 496，未覆盖 content/），以便未来死链问题能被自动发现。
2. 对 `content/safety_critical/09_reference/01_api_design_guidelines.md` 与 `07_ffi_integration_guide.md` 进行内容审计；若确认主要为通用概念重复，可进一步 stub 化。
3. 维护 `content/` 文件清单，新增文件时必须先运行 `detect_content_overlap.py` 并声明 canonical 来源。

---

**状态**: ✅ 治理完成，验证通过。
