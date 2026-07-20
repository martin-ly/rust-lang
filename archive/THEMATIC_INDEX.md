# Archive 主题索引

> 本文件按“内容主题”对 `archive/` 进行索引，按 8 大主题 + 1 独立专题集合组织。
> 生成时间：2026-07-20（重组后）
> 适用范围：`archive/` 全部只读历史内容。

---

## 使用说明

- 本索引不移动任何文件，只提供导航。
- 路径均为相对 `archive/` 的 Unix 风格路径（`/`）。
- 如需引用 archive 中的资料，请在链接文本中标注“（历史归档）”，见 `archive_policy.md` §6。
- 每个主题下的“活跃对应页”指向当前项目中的权威来源，不应将 archive 作为学习路径默认入口。

---

## 主题总览

| 主题 | 子主题数 | 核心目录 | 说明 |
|------|---------|----------|------|
| [1. 治理与元数据](#1-治理与元数据) | 4 | `01_governance/` | 归档政策、项目计划、顶层审计、元数据脚本 |
| [2. Rust 版本与权威来源对齐](#2-rust-版本与权威来源对齐) | 4 | `02_version_alignment/` | 版本跟踪、验证报告、权威来源对比、检查清单 |
| [3. 概念页历史与迁移](#3-概念页历史与迁移) | 4 | `03_concept_history/` | 旧版概念页、知识卡片、指南、AI 辅助编程 |
| [4. Crate 完成与增强报告](#4-crate-完成与增强报告) | 11 | `04_crate_reports/` | 按 crate 组织的完成报告、Cargo 包管理旧版 |
| [5. 形式化方法与所有权可判定性](#5-形式化方法与所有权可判定性) | 6 | `05_formal_methods/` | 形式化、学术工具、所有权可判定性、废弃方案 |
| [6. 生态深度内容](#6-生态深度内容) | 10 | `06_ecosystem/` | 异步、数据库、序列化、场景、生产实践、前沿特性 |
| [7. 研究笔记与实验](#7-研究笔记与实验) | 6 | `07_research_notes/` | 版本研究、研究快照、设计理论、类型理论、实验 |
| [8. 质量审计、链路检查与临时文件](#8-质量审计链路检查与临时文件) | 8 | `08_quality_audits/` | 审计报告、链路检查、备份入口、临时参考 |
| [9. 独立专题集合](#9-独立专题集合) | 2 | `09_special_collections/` | 超大独立集合：所有权可判定性、docs 大备份 |

---

## 1. 治理与元数据

### 1.1 归档政策与目录说明

- [`README.md`](README.md) — `archive/` 目录说明与使用规则
- [`ARCHIVE_REORG_LOG_2026_07_20.md`](ARCHIVE_REORG_LOG_2026_07_20.md) — 本次重组迁移记录
- [`01_governance/01_archive_policy/ARCHIVE_INDEX.md`](01_governance/01_archive_policy/ARCHIVE_INDEX.md) — 历史归档索引
- [`../archive_policy.md`](../archive_policy.md) — 归档政策全文
- 活跃对应页：无（治理文件本身）

### 1.2 项目级计划与跟进报告

- [`01_governance/CRITICAL_AUDIT_REPORT_2026.md`](01_governance/CRITICAL_AUDIT_REPORT_2026.md) — 2026 年批判性审计
- [`01_governance/PROJECT_FOLLOW_UP_PLAN.md`](01_governance/PROJECT_FOLLOW_UP_PLAN.md)、[`01_governance/PROJECT_NEXT_PHASE_PLAN.md`](01_governance/PROJECT_NEXT_PHASE_PLAN.md)、[`01_governance/PHASE1_COMPLETION_REPORT.md`](01_governance/PHASE1_COMPLETION_REPORT.md) 等
- [`01_governance/02_project_plans/`](01_governance/02_project_plans/) — 2026 年 3 月重组计划、语义空间 Wave 计划等
- 活跃对应页：[`concept/07_future/`](../concept/07_future/)

### 1.3 项目报告

- [`01_governance/03_project_reports/`](01_governance/03_project_reports/) — Rust 1.94 特性清单、crates 更新报告
- 活跃对应页：[`concept/`](../concept/)

### 1.4 根级元数据与脚本

- [`01_governance/04_root_meta/concept_kb.json`](01_governance/04_root_meta/concept_kb.json) — 元知识库索引
- [`01_governance/04_root_meta/concept_index_retired_2026-05-21.json`](01_governance/04_root_meta/concept_index_retired_2026-05-21.json) — 已退役 concept 索引
- [`01_governance/04_root_meta/kg_data_v1_retired_2026-05-23.json`](01_governance/04_root_meta/kg_data_v1_retired_2026-05-23.json) — 知识图谱 v1 退役数据
- [`01_governance/04_root_meta/kg_data_v2_retired_2026-07-12.json`](01_governance/04_root_meta/kg_data_v2_retired_2026-07-12.json) — 知识图谱 v2 退役数据
- 活跃对应页：[`concept/`](../concept/)、[`tools/`](../tools/)

---

## 2. Rust 版本与权威来源对齐

### 2.1 版本跟踪与特性对齐

- [`02_version_alignment/RUST_196_FEATURE_ALIGNMENT_AUDIT.md`](02_version_alignment/RUST_196_FEATURE_ALIGNMENT_AUDIT.md) — 1.96 特性对齐审计
- [`02_version_alignment/RUST_1.96_MIGRATION_PLAN.md`](02_version_alignment/RUST_1.96_MIGRATION_PLAN.md)、[`02_version_alignment/RUST_1.96_MIGRATION_COMPLETE.md`](02_version_alignment/RUST_1.96_MIGRATION_COMPLETE.md)
- [`02_version_alignment/01_rust_version_tracking/`](02_version_alignment/01_rust_version_tracking/) — 工具链、历史版本文档、版本报告
- 活跃对应页：[`concept/07_future/00_version_tracking/`](../concept/07_future/00_version_tracking/)

### 2.2 验证报告

- [`02_version_alignment/02_verification_reports/`](02_version_alignment/02_verification_reports/) — Rust 1.94 验证报告族
- 活跃对应页：[`concept/07_future/00_version_tracking/`](../concept/07_future/00_version_tracking/)

### 2.3 对称差分析与国际权威对比

- [`02_version_alignment/RUST_SYMMETRIC_DIFFERENCE_ANALYSIS_2026_05_01.md`](02_version_alignment/RUST_SYMMETRIC_DIFFERENCE_ANALYSIS_2026_05_01.md) — 国际权威来源对称差分析
- [`02_version_alignment/RUST_REFERENCE_GAP_ANALYSIS_REPORT.md`](02_version_alignment/RUST_REFERENCE_GAP_ANALYSIS_REPORT.md) — Rust Reference 缺口分析
- 活跃对应页：[`concept/07_future/`](../concept/07_future/)

### 2.4 2026 检查清单

- [`02_version_alignment/04_2026_checklists/`](02_version_alignment/04_2026_checklists/) — 2026 H1 版本对齐检查清单、2026 Q2 季度同步检查清单
- 活跃对应页：无（审计产物）

---

## 3. 概念页历史与迁移

### 3.1 旧版概念页

- [`03_concept_history/01_legacy_concept_pages/`](03_concept_history/01_legacy_concept_pages/) — 从 `concept/` 各层级迁移出来的旧版概念页（35+ 份）
- 活跃对应页：[`concept/`](../concept/) 各层级权威页

### 3.2 知识卡片旧版

- [`03_concept_history/02_knowledge_cards/`](03_concept_history/02_knowledge_cards/) — 旧版知识卡片（基础、中级、高级、专家）
- 活跃对应页：[`concept/`](../concept/)

### 3.3 指南旧版

- [`03_concept_history/03_guides/`](03_concept_history/03_guides/) — 旧版指南
- 活跃对应页：[`docs/04_guides/`](../docs/04_guides/)

### 3.4 AI 辅助编程

- [`03_concept_history/03_guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2026.md`](03_concept_history/03_guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2026.md)
- [`03_concept_history/03_guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2025.md`](03_concept_history/03_guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2025.md)
- 活跃对应页：[`docs/04_guides/`](../docs/04_guides/)

---

## 4. Crate 完成与增强报告

### 4.1–4.10 按 Crate 组织

- [`04_crate_reports/01_c01_ownership_borrow_scope/`](04_crate_reports/01_c01_ownership_borrow_scope/) — 所有权/借用/作用域；Rust 1.89/1.90 特性分析
- [`04_crate_reports/02_c02_type_system/`](04_crate_reports/02_c02_type_system/) — 类型系统、Cargo 文档、dispatch 机制
- [`04_crate_reports/03_c03_control_fn/`](04_crate_reports/03_c03_control_fn/) — 控制流与函数
- [`04_crate_reports/04_c04_generic/`](04_crate_reports/04_c04_generic/) — 泛型
- [`04_crate_reports/05_c05_threads/`](04_crate_reports/05_c05_threads/) — 线程
- [`04_crate_reports/06_c06_async/`](04_crate_reports/06_c06_async/) — 异步生态（最大报告族）
- [`04_crate_reports/07_c07_process/`](04_crate_reports/07_c07_process/) — 进程/错误处理/同步原语
- [`04_crate_reports/08_c08_algorithms/`](04_crate_reports/08_c08_algorithms/) — 算法 crate
- [`04_crate_reports/09_c09_design_pattern/`](04_crate_reports/09_c09_design_pattern/) — 设计模式
- [`04_crate_reports/10_c10_networks/`](04_crate_reports/10_c10_networks/) — 网络 crate
- 活跃对应页：[`crates/`](../crates/)

### 4.11 Cargo 包管理旧版

- [`04_crate_reports/11_cargo_package_management/`](04_crate_reports/11_cargo_package_management/) — 17 份文档 + diagrams + examples
- 活跃对应页：[`concept/06_ecosystem/cargo/`](../concept/06_ecosystem/)、[`crates/c02_type_system/`](../crates/c02_type_system/)

### 4.12 C08 算法 Crate 旧版文档

- [`04_crate_reports/08_c08_algorithms_docs_archive_2025/`](04_crate_reports/08_c08_algorithms_docs_archive_2025/) — 旧版算法 crate 文档归档
- 活跃对应页：[`crates/c08_algorithms/`](../crates/c08_algorithms/)

---

## 5. 形式化方法与所有权可判定性

### 5.1 所有权可判定性专题入口

- [`05_formal_methods/01_ownership_decidability_collection/README.md`](05_formal_methods/01_ownership_decidability_collection/README.md) — 专题入口
- 完整集合：[`09_special_collections/rust_ownership_decidability/`](09_special_collections/rust_ownership_decidability/)
- 活跃对应页：[`concept/04_formal/`](../concept/04_formal/)

### 5.2 学术工具

- [`05_formal_methods/02_academic_tools/`](05_formal_methods/02_academic_tools/) — RustBelt、Tree Borrows、Polonius、Kani、Prusti、Creusot、Aeneas
- 活跃对应页：[`concept/04_formal/02_separation_logic/`](../concept/04_formal/02_separation_logic/)

### 5.3 形式化工程系统

- [`05_formal_methods/03_formal_engineering_system/`](05_formal_methods/03_formal_engineering_system/) — 形式化工程系统资料
- 活跃对应页：[`concept/04_formal/`](../concept/04_formal/)

### 5.4 废弃方案

- [`05_formal_methods/04_coq_aeneas_deprecated/`](05_formal_methods/04_coq_aeneas_deprecated/) — Aeneas、Coq/Isabelle 证明脚手架、Coq-of-Rust 计划
- 活跃对应页：[`content/safety_critical/`](../content/safety_critical/)

### 5.5 研究笔记-形式化

- [`05_formal_methods/05_research_notes_formal/`](05_formal_methods/05_research_notes_formal/) — 形式化方法研究笔记
- 活跃对应页：[`concept/04_formal/`](../concept/04_formal/)

### 5.6 中文所有权教程

- [`05_formal_methods/06_chinese_ownership_tutorial/`](05_formal_methods/06_chinese_ownership_tutorial/) — 中文所有权与可判定性教程旧版
- 活跃对应页：[`concept/04_formal/`](../concept/04_formal/)

---

## 6. 生态深度内容

### 6.1 异步运行时

- [`06_ecosystem/01_async_runtimes/`](06_ecosystem/01_async_runtimes/) — Tokio 等异步运行时
- 活跃对应页：[`concept/03_advanced/01_async/`](../concept/03_advanced/01_async/)

### 6.2 数据库与 ORM

- [`06_ecosystem/02_databases_orm/`](06_ecosystem/02_databases_orm/) — SQLx、Sea-ORM
- 活跃对应页：[`concept/06_ecosystem/databases/`](../concept/06_ecosystem/)

### 6.3 序列化与数据格式

- [`06_ecosystem/03_serialization/`](06_ecosystem/03_serialization/) — Serde 最佳实践
- 活跃对应页：[`concept/06_ecosystem/`](../concept/06_ecosystem/)

### 6.4 场景化应用

- [`06_ecosystem/04_scenarios/`](06_ecosystem/04_scenarios/) — CLI、Web、数据工程/ML、嵌入式、游戏
- 活跃对应页：[`content/ecosystem/`](../content/ecosystem/)、[`docs/05_practice/`](../docs/05_practice/)

### 6.5 生产实践

- [`06_ecosystem/05_production_practices/`](06_ecosystem/05_production_practices/) — K8s、serverless、CI/CD、可观测性、性能调优
- 活跃对应页：[`content/safety_critical/`](../content/safety_critical/)、[`docs/05_practice/`](../docs/05_practice/)

### 6.6 前沿特性跟踪

- [`06_ecosystem/06_emerging_features/`](06_ecosystem/06_emerging_features/) — async closures、TAIT、generic const exprs、WASM、gen blocks
- 活跃对应页：[`concept/07_future/`](../concept/07_future/)

### 6.7 知识表征矩阵

- [`06_ecosystem/07_representations/`](06_ecosystem/07_representations/) — Bloom × Krathwohl 矩阵、知识表征映射
- 活跃对应页：[`concept/00_meta/`](../concept/00_meta/)

### 6.8 Crate 案例研究入口

- [`06_ecosystem/08_crate_case_studies/README.md`](06_ecosystem/08_crate_case_studies/README.md) — 专题入口
- 完整集合：[`09_special_collections/rust_ownership_decidability/case-studies/`](09_special_collections/rust_ownership_decidability/case-studies/)
- 活跃对应页：[`crates/`](../crates/)、[`concept/06_ecosystem/`](../concept/06_ecosystem/)

### 6.9 错误处理

- [`06_ecosystem/09_error_handling/`](06_ecosystem/09_error_handling/) — 错误处理生态深度
- 活跃对应页：[`concept/06_ecosystem/`](../concept/06_ecosystem/)

### 6.10 Web 框架

- [`06_ecosystem/10_web_frameworks/`](06_ecosystem/10_web_frameworks/) — Axum、Actix-web、Rocket 等
- 活跃对应页：[`concept/06_ecosystem/networks/`](../concept/06_ecosystem/)

---

## 7. 研究笔记与实验

### 7.1 版本特性研究笔记

- [`07_research_notes/01_version_research/`](07_research_notes/01_version_research/) — Rust 1.91–1.94 特性研究笔记
- 活跃对应页：[`concept/07_future/00_version_tracking/`](../concept/07_future/00_version_tracking/)

### 7.2 研究笔记快照（2026-06-25）

- [`07_research_notes/02_snapshot_2026_06_25/`](07_research_notes/02_snapshot_2026_06_25/) — 根文件快照（项目报告、索引、教程、cheatsheet 等）
- 活跃对应页：[`concept/`](../concept/)

### 7.3 设计理论

- [`07_research_notes/03_software_design_theory/`](07_research_notes/03_software_design_theory/) — 设计模式、工作流、执行模型、分布式模式
- 活跃对应页：[`concept/06_ecosystem/03_design_patterns/`](../concept/06_ecosystem/03_design_patterns/)

### 7.4 类型理论

- [`07_research_notes/04_type_theory/`](07_research_notes/04_type_theory/) — 类型系统基础、trait 形式化、const 求值
- 活跃对应页：[`concept/04_formal/`](../concept/04_formal/)

### 7.5 实验

- [`07_research_notes/05_experiments/`](07_research_notes/05_experiments/) — 性能/编译器实验笔记
- 活跃对应页：[`examples/`](../examples/)

### 7.6 形式化统一模型

- [`07_research_notes/06_formal_unified_models/`](07_research_notes/06_formal_unified_models/) — LSIP、PostgreSQL 形式化、Rust 核心 crate 形式化塔
- 活跃对应页：[`concept/04_formal/`](../concept/04_formal/)

---

## 8. 质量审计、链路检查与临时文件

### 8.1 链路健康与死链报告

- [`08_quality_audits/LINK_CHECK_REPORT_FULL.md`](08_quality_audits/LINK_CHECK_REPORT_FULL.md) — 全库链路健康报告
- 活跃对应页：无（审计产物）

### 8.2 内容重叠与去重报告

- [`08_quality_audits/02_content_overlap/`](08_quality_audits/02_content_overlap/) — 内容重叠检测报告、重复内容审计
- 活跃对应页：无（审计产物）

### 8.3 内容完整性与 i18n 审计

- [`08_quality_audits/CONTENT_COMPLETENESS_UNIFICATION_SUMMARY.md`](08_quality_audits/CONTENT_COMPLETENESS_UNIFICATION_SUMMARY.md)
- 活跃对应页：无（审计产物）

### 8.4 安全/供应链审计

- [`08_quality_audits/MIRI_TESTS_FIX_REPORT.md`](08_quality_audits/MIRI_TESTS_FIX_REPORT.md)
- 活跃对应页：[`supply-chain/`](../supply-chain/)

### 8.5 临时文件与快速参考

- [`08_quality_audits/05_temp_quick_reference/`](08_quality_audits/05_temp_quick_reference/) — 历史临时文件、快速参考
- 活跃对应页：[`docs/03_reference/quick_reference/`](../docs/03_reference/quick_reference/)

### 8.6 已废弃方案

- [`05_formal_methods/04_coq_aeneas_deprecated/`](05_formal_methods/04_coq_aeneas_deprecated/) — 已废弃方案（迁移后位置）
- 活跃对应页：[`content/safety_critical/`](../content/safety_critical/)

### 8.7 docs 大备份入口

- [`08_quality_audits/07_backup_from_docs_entry/README.md`](08_quality_audits/07_backup_from_docs_entry/README.md) — 专题入口
- 完整集合：[`09_special_collections/backup_from_docs/`](09_special_collections/backup_from_docs/)
- 活跃对应页：[`docs/`](../docs/)

### 8.8 按时间归档报告

- [`08_quality_audits/08_reports_by_time/`](08_quality_audits/08_reports_by_time/) — 2025-12、2026 Q1、2026_07 等历史报告
- 活跃对应页：无（审计产物）

### 8.9 C-class 审计包

- [`08_quality_audits/09_c_class_audit_2026_06_08/`](08_quality_audits/09_c_class_audit_2026_06_08/) — 2026-06-08 C-class 审计完整包
- 活跃对应页：无（审计产物）

---

## 9. 独立专题集合

### 9.1 所有权可判定性

- [`09_special_collections/rust_ownership_decidability/`](09_special_collections/rust_ownership_decidability/) — 450+ 文件，核心教学资料
- 专题入口：[`05_formal_methods/01_ownership_decidability_collection/README.md`](05_formal_methods/01_ownership_decidability_collection/README.md)
- 活跃对应页：[`concept/04_formal/`](../concept/04_formal/)

### 9.2 docs 大备份

- [`09_special_collections/backup_from_docs/`](09_special_collections/backup_from_docs/) — 2025 年 `docs/` 大重组完整备份（~11,755 文件）
- 专题入口：[`08_quality_audits/07_backup_from_docs_entry/README.md`](08_quality_audits/07_backup_from_docs_entry/README.md)
- 活跃对应页：[`docs/`](../docs/)、[`concept/`](../concept/)

---

## 附录 A：关键统计数据（重组后）

| 指标 | 数值 |
|------|------|
| 8 大主题目录下文件总数 | 约 1,108 |
| 独立专题集合文件总数 | 约 12,320 |
| 合计 | 约 13,428 |
| 历史未主题化目录 | 0 |

> 注：独立专题集合 `rust_ownership_decidability/` 与 `backup_from_docs/` 内部结构保留，不拆散。

---

## 附录 B：相关文件

- [`RELATIONSHIP_MAP.md`](RELATIONSHIP_MAP.md) — 文件关联组与相关度分析
- [`ARCHIVE_REORG_LOG_2026_07_20.md`](ARCHIVE_REORG_LOG_2026_07_20.md) — 重组迁移记录
- [`tmp/archive_overlap_scan_before_reorg_2026_07_20.md`](../tmp/archive_overlap_scan_before_reorg_2026_07_20.md) — 重组前重叠检测报告
- [`../archive_policy.md`](../archive_policy.md) — 归档政策
