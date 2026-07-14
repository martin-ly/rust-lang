# Crates 非 docs/ Markdown 治理报告 X1A

**Date**: 2026-07-14
**Scope**: `crates/c01_*` 至 `crates/c05_*` 中所有非 `docs/` 目录的 `.md` 文件
**Target Archive**: `archive/2026/crates_reports/`
**Status**: ✅ 完成

---

## 执行摘要

本轮治理对前 5 个 crate（`c01_ownership_borrow_scope`、`c02_type_system`、`c03_control_fn`、`c04_generic`、`c05_threads`）中 79 个非 `docs/` Markdown 文件进行了分类处置：

| 处置类型 | 数量 | 说明 |
| :--- | :--- | :--- |
| 归档（Archive） | 42 | 历史 AI 生成报告、完成总结、版本追踪草稿等，统一移动到 `archive/2026/crates_reports/` |
| 改 stub | 7 | 与 `concept/` 权威页重复的通用概念文档，改写为权威来源 stub（含治理前已是 stub 的 3 个文件） |
| 保留加权威注记 | 3 | `c04_generic` crate 特定项目文档，保留并加注 canonical 来源 |
| 标准文件保留 | 27 | `README.md` / `CHANGELOG.md` / `CONTRIBUTING.md` / `examples/README.md` / `tests/README.md` / `src/README.md` / `src/archive/README.md` |

处置后剩余 37 个非 `docs/` Markdown 文件，全部为标准文件、已处置 stub 或已加注 crate 特定文档。

---

## 验证结果

| 验证项 | 命令 | 结果 |
| :--- | :--- | :--- |
| 知识体系审计 | `python scripts/kb_auditor.py` | ✅ 死链 0，跨层问题 0 |
| mdbook 构建 | `mdbook build` | ✅ 构建成功（仅搜索索引体积 WARN） |
| 命名规范 | `python scripts/check_naming_convention.py --strict` | ✅ ERROR=0（WARN=79，均为已登记的专题系列/版本目录白名单） |

---

## 归档清单（42 个文件）

### `c01_ownership_borrow_scope/` → `archive/2026/crates_reports/c01_ownership_borrow_scope/`

- `RUST_189_FEATURES_ANALYSIS.md`
- `RUST_190_COMPREHENSIVE_PROGRESS_REPORT.md`
- `RUST_190_ENHANCEMENT_COMPLETION_REPORT.md`
- `RUST_190_LATEST_FEATURES_ENHANCEMENT_REPORT.md`
- `VISUALIZATION_ENHANCEMENT_SUMMARY.md`

### `c02_type_system/` → `archive/2026/crates_reports/c02_type_system/`

- `dispatch_mechanisms_supplement_2025_10_19.md`
- `final_delivery_report_2025_10_22.md`
- `project_completion_summary_2025_10_22.md`
- `project_status_2025_10_22.md`
- `readme_rust_189.md`
- `rust_190_feature_inventory_report.md`
- `rust_192_completion_report.md`
- `reports/C02_COMPREHENSIVE_ENHANCEMENT_REPORT_2025_10_20.md`
- `reports/C02_EXTENSION_ENHANCEMENT_REPORT_2025_10_20.md`
- `reports/CARGO_DOCUMENTATION_SYSTEM_REPORT.md`
- `reports/CARGO_SUPPLEMENT_REPORT.md`
- `reports/ENHANCEMENT_COMPLETION_REPORT.md`
- `reports/FINAL_COMPLETION_REPORT.md`
- `reports/MULTI_TASK_PROGRESSION_REPORT.md`
- `reports/PROJECT_COMPLETION_SUMMARY.md`
- `reports/REPAIR_SUMMARY.md`
- `reports/RUST_190_ENHANCEMENT_COMPLETION_REPORT.md`
- `reports/RUST_FEATURES_DOCUMENTATION_ORGANIZATION_REPORT.md`

### `c03_control_fn/` → `archive/2026/crates_reports/c03_control_fn/`

- `rust_192_completion_summary.md`
- `reports/BASIC_SYNTAX_ENHANCEMENT_SUMMARY.md`
- `reports/C03_COMPREHENSIVE_ENHANCEMENT_REPORT_2025_10_20.md`
- `reports/FINAL_PROJECT_COMPLETION_SUMMARY.md`
- `reports/PROJECT_COMPLETION_REPORT.md`
- `reports/RUST_190_COMPLETE_FEATURES_REPORT.md`
- `reports/RUST_190_COMPREHENSIVE_ADVANCEMENT_REPORT.md`
- `reports/RUST_190_ENHANCEMENT_COMPLETION_REPORT.md`
- `reports/RUST_190_FINAL_PROJECT_COMPLETION_SUMMARY.md`

### `c04_generic/` → `archive/2026/crates_reports/c04_generic/`

- `reports/C04_COMPREHENSIVE_ENHANCEMENT_REPORT_2025_10_20.md`
- `reports/DOCUMENTATION_ORGANIZATION_REPORT.md`
- `reports/FINAL_ENHANCEMENT_SUMMARY.md`
- `reports/FINAL_PROJECT_REPORT.md`
- `reports/KNOWLEDGE_SYSTEM_COMPLETION_REPORT_2025_10_19.md`
- `reports/PROJECT_ACHIEVEMENT_SUMMARY.md`
- `reports/PROJECT_COMPLETION_REPORT.md`
- `reports/PROJECT_SUMMARY.md`

### `c05_threads/` → `archive/2026/crates_reports/c05_threads/`

- `reports/C05_COMPREHENSIVE_ENHANCEMENT_REPORT_2025_10_20.md`
- `reports/RUST_190_FEATURES_SUMMARY.md`

---

## 改写为 Stub 的文件（7 个）

| 文件 | 权威来源指向 |
| :--- | :--- |
| `crates/c02_type_system/api_documentation.md` | `concept/01_foundation/02_type_system/01_type_system.md` |
| `crates/c02_type_system/best_practices_guide.md` | `concept/01_foundation/02_type_system/01_type_system.md` 等 |
| `crates/c02_type_system/cargo_package_management_guide.md` | `concept/01_foundation/07_modules_and_items/11_crates_and_source_files.md` |
| `crates/c02_type_system/examples_and_use_cases.md` | `concept/01_foundation/02_type_system/01_type_system.md` |
| `crates/c02_type_system/readme_rust_190.md` | `concept/01_foundation/02_type_system/01_type_system.md`、`concept/07_future/00_version_tracking/rust_1_90_stabilized.md` |
| `crates/c02_type_system/tutorial_guide.md` | `concept/01_foundation/02_type_system/01_type_system.md` 等 |
| `crates/c05_threads/exercises/01_thread_communication.md` | `concept/03_advanced/00_concurrency/01_concurrency.md` |

> 注：`crates/c02_type_system/examples_and_use_cases.md`、`readme_rust_190.md`、`tutorial_guide.md` 在治理前已是 stub；本轮新增 stub 为前 4 个文件。

---

## 保留并加注权威来源的文件（3 个）

| 文件 | 说明 |
| :--- | :--- |
| `crates/c04_generic/badges.md` | crate 项目状态页，加注指向泛型/Trait 权威页 |
| `crates/c04_generic/config.md` | crate 配置文件说明，加注指向泛型/Trait 权威页 |
| `crates/c04_generic/demo_script.md` | crate 演示脚本索引，加注指向泛型/Trait 权威页 |

---

## 标准文件保留（27 个）

以下文件属于 crate 标准入口/元数据，未做内容改动：

- `crates/c01_ownership_borrow_scope/README.md`
- `crates/c01_ownership_borrow_scope/CHANGELOG.md`
- `crates/c01_ownership_borrow_scope/CONTRIBUTING.md`
- `crates/c01_ownership_borrow_scope/examples/README.md`
- `crates/c01_ownership_borrow_scope/tests/README.md`
- `crates/c01_ownership_borrow_scope/src/archive/README.md`
- `crates/c02_type_system/README.md`
- `crates/c02_type_system/CHANGELOG.md`
- `crates/c02_type_system/CONTRIBUTING.md`
- `crates/c02_type_system/examples/README.md`
- `crates/c02_type_system/src/README.md`
- `crates/c02_type_system/src/archive/README.md`
- `crates/c02_type_system/tests/README.md`
- `crates/c03_control_fn/README.md`
- `crates/c03_control_fn/examples/README.md`
- `crates/c03_control_fn/tests/README.md`
- `crates/c03_control_fn/src/archive/README.md`
- `crates/c04_generic/README.md`
- `crates/c04_generic/CHANGELOG.md`
- `crates/c04_generic/CONTRIBUTING.md`
- `crates/c04_generic/examples/README.md`
- `crates/c04_generic/src/archive/README.md`
- `crates/c04_generic/tests/README.md`
- `crates/c05_threads/README.md`
- `crates/c05_threads/examples/README.md`
- `crates/c05_threads/tests/README.md`
- `crates/c05_threads/src/archive/README.md`

---

## 外链修复

`docs/12_research_notes/01_alignment_matrices/32_rust_book_alignment.md` 中指向 `crates/c02_type_system/cargo_package_management_guide.md` 的两处链接已修复为：

```markdown
[concept/01_foundation/07_modules_and_items/11_crates_and_source_files.md](../../../concept/01_foundation/07_modules_and_items/11_crates_and_source_files.md)
```

确保对齐矩阵中 TRPL Ch7 / Ch14 的 package/crate/Cargo 主题指向 `concept/` 权威页。

---

## 后续建议

1. **c06–c10 已归档范围**：确认 `archive/2026/crates_reports/c06_async/` 等目录与本轮归档风格一致（按 crate 名归集）。
2. **docs/ 内剩余引用**：建议后续轮次扫描 `docs/` 中仍指向 `crates/*/reports/` 或历史完成报告类文件的链接，逐步替换为 `concept/` 权威页或移除。
3. **CI 挂载**：本轮变更仅涉及 Markdown 与归档，不影响 `cargo check/test`；若后续扩展归档动作，建议在 CI 中加入 `find archive/2026/crates_reports -type f | wc -l` 类基线断言。

---

*报告生成时间*: 2026-07-14 17:30 CST
