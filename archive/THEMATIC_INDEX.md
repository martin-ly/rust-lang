# Archive 主题索引

> 本文件按“内容主题”对 `archive/` 进行索引，弥补原有“来源/时间”目录组织的可发现性不足。
> 生成时间：2026-07-19
> 适用范围：`archive/` 全部只读历史内容。

---

## 使用说明

- 本索引不移动任何文件，只提供导航。
- 路径均为相对 `archive/` 的 Unix 风格路径（`/`）。
- 如需引用 archive 中的资料，请在链接文本中标注“（历史归档）”，见 `archive_policy.md` §6。
- 每个主题下的“活跃对应页”指向当前项目中的权威来源，不应将 archive 作为学习路径默认入口。

---

## 主题总览

| 主题 | 子主题数 | 核心目录/文件 | 说明 |
|------|---------|--------------|------|
| [1. 治理与元数据](#1-治理与元数据) | 3 | 根报告、README、root_meta | 归档政策、项目计划、顶层审计、元数据脚本 |
| [2. Rust 版本与权威来源对齐](#2-rust-版本与权威来源对齐) | 3 | 顶层 `RUST_*` 报告、verification_reports | 版本跟踪、特性验证、权威来源对比 |
| [3. 概念页历史与迁移](#3-概念页历史与迁移) | 3 | 2026/concept_archive、knowledge、guides | 旧版概念页、知识卡片、指南旧版 |
| [4. Crate 完成与增强报告](#4-crate-完成与增强报告) | 3 | 2026/crates_reports、crates_c08_...、cargo_package_management_from_c02 | Crate 完成报告、旧版文档、Cargo 包管理 |
| [5. 形式化方法与所有权可判定性](#5-形式化方法与所有权可判定性) | 5 | rust-ownership-decidability、content/academic | 形式化、可判定性、验证工具、案例研究 |
| [6. 生态深度内容](#6-生态深度内容) | 7 | content/ecosystem、content/scenarios、content/production | 异步、数据库、场景、生产实践、前沿特性 |
| [7. 研究笔记与实验](#7-研究笔记与实验) | 3 | research_notes、research_notes_2026_06_25 | 版本研究、形式化、设计理论 |
| [8. 质量审计、链路检查与临时文件](#8-质量审计链路检查与临时文件) | 7 | reports、temp、backup_from_docs、deprecated | 审计报告、链路检查、备份、废弃方案 |

---

## 1. 治理与元数据

### 1.1 归档政策与目录说明

- [`README.md`](README.md) — `archive/` 目录说明与使用规则
- [`../archive_policy.md`](../archive_policy.md) — 归档政策全文
- 活跃对应页：无（治理文件本身）

### 1.2 项目级计划与跟进报告

- [`CRITICAL_AUDIT_REPORT_2026.md`](CRITICAL_AUDIT_REPORT_2026.md) — 2026 年批判性审计
- [`RUST_SYMMETRIC_DIFFERENCE_ANALYSIS_2026_05_01.md`](RUST_SYMMETRIC_DIFFERENCE_ANALYSIS_2026_05_01.md) — 国际权威来源对称差分析
- [`RUST_196_FEATURE_ALIGNMENT_AUDIT.md`](RUST_196_FEATURE_ALIGNMENT_AUDIT.md) — 1.96 特性对齐审计
- [`RUST_REFERENCE_GAP_ANALYSIS_REPORT.md`](RUST_REFERENCE_GAP_ANALYSIS_REPORT.md) — Rust Reference 缺口分析
- [`PROJECT_FOLLOW_UP_PLAN.md`](PROJECT_FOLLOW_UP_PLAN.md)、[`PROJECT_NEXT_PHASE_PLAN.md`](PROJECT_NEXT_PHASE_PLAN.md)、[`PHASE1_COMPLETION_REPORT.md`](PHASE1_COMPLETION_REPORT.md) 等
- 活跃对应页：[`concept/07_future/00_version_tracking/`](../concept/07_future/00_version_tracking/)

### 1.3 根级元数据与脚本

- [`root_meta/concept_kb.json`](root_meta/concept_kb.json) — 元知识库索引（48k+ 行）
- [`root_meta/`](root_meta/) 内缓存、Docker Compose、Python 脚本
- 活跃对应页：[`concept/`](../concept/)、[`tools/`](../tools/)

---

## 2. Rust 版本与权威来源对齐

### 2.1 版本跟踪与特性对齐

- 顶层 `RUST_189_*` 至 `RUST_197_*` 系列报告
- [`2026/concept_archive/`](2026/concept_archive/) — 旧版概念页按版本归档
- 活跃对应页：[`concept/07_future/00_version_tracking/`](../concept/07_future/00_version_tracking/)

### 2.2 验证报告

- [`verification_reports/`](verification_reports/) — Rust 1.94 等版本验证报告
- 活跃对应页：[`concept/07_future/00_version_tracking/`](../concept/07_future/00_version_tracking/)

### 2.3 对称差分析与国际权威对比

- [`RUST_SYMMETRIC_DIFFERENCE_ANALYSIS_2026_05_01.md`](RUST_SYMMETRIC_DIFFERENCE_ANALYSIS_2026_05_01.md)
- 活跃对应页：[`concept/07_future/`](../concept/07_future/)

---

## 3. 概念页历史与迁移

### 3.1 旧版概念页

- [`2026/concept_archive/`](2026/concept_archive/) — 35+ 份旧版概念页（所有权、生命周期、异步、泛型等）
- 活跃对应页：[`concept/`](../concept/) 各层级权威页

### 3.2 知识卡片旧版

- [`knowledge/01_fundamentals/01_borrowing.md`](knowledge/01_fundamentals/01_borrowing.md)
- [`knowledge/01_fundamentals/03_lifetimes.md`](knowledge/01_fundamentals/03_lifetimes.md)
- [`knowledge/01_fundamentals/04_ownership.md`](knowledge/01_fundamentals/04_ownership.md)
- [`knowledge/02_intermediate/`](knowledge/02_intermediate/)、[`knowledge/03_advanced/`](knowledge/03_advanced/)
- 活跃对应页：[`concept/`](../concept/)

### 3.3 指南旧版

- [`guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2026.md`](guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2026.md)
- [`guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2025.md`](guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2025.md)
- 活跃对应页：[`docs/04_guides/`](../docs/04_guides/)

---

## 4. Crate 完成与增强报告

### 4.1 按 Crate 组织的完成报告

- [`2026/crates_reports/c01_ownership_borrow_scope/`](2026/crates_reports/c01_ownership_borrow_scope/)
- [`2026/crates_reports/c02_type_system/`](2026/crates_reports/c02_type_system/)
- [`2026/crates_reports/c04_generic/`](2026/crates_reports/c04_generic/)
- [`2026/crates_reports/c06_async/`](2026/crates_reports/c06_async/)
- [`2026/crates_reports/c07_process/`](2026/crates_reports/c07_process/)
- [`2026/crates_reports/c08_algorithms/`](2026/crates_reports/c08_algorithms/)
- [`2026/crates_reports/c09_design_pattern/`](2026/crates_reports/c09_design_pattern/)
- [`2026/crates_reports/c10_networks/`](2026/crates_reports/c10_networks/)
- 注：各目录内含大量 FINAL/COMPLETION/ENHANCEMENT/UPGRADE 报告，存在主题重叠。
- 活跃对应页：[`crates/`](../crates/)

### 4.2 Crate 文档旧版

- [`2026/crates_c08_algorithms_docs_archive_2025/`](2026/crates_c08_algorithms_docs_archive_2025/)
- 活跃对应页：[`crates/c08_algorithms/`](../crates/c08_algorithms/)

### 4.3 Cargo 包管理体系旧版

- [`cargo_package_management_from_c02/`](cargo_package_management_from_c02/) — 17 份文档 + `diagrams/` + `examples/`
- 活跃对应页：[`concept/06_ecosystem/cargo/`](../concept/06_ecosystem/)、[`crates/c02_type_system/`](../crates/c02_type_system/)

---

## 5. 形式化方法与所有权可判定性

### 5.1 核心教程与可判定性分析

- [`rust-ownership-decidability/00-foundations/`](rust-ownership-decidability/00-foundations/)
- [`rust-ownership-decidability/01-core-concepts/`](rust-ownership-decidability/01-core-concepts/)
- [`rust-ownership-decidability/04-decidability-analysis/`](rust-ownership-decidability/04-decidability-analysis/)
- [`docs/rust-ownership-chinese/`](docs/rust-ownership-chinese/) — 中文所有权与可判定性教程旧版
- 活跃对应页：[`concept/04_formal/`](../concept/04_formal/)

### 5.2 验证工具

- [`rust-ownership-decidability/03-verification-tools/`](rust-ownership-decidability/03-verification-tools/)
- [`content/academic/`](content/academic/) — RustBelt、Tree Borrows、Polonius、Kani、Prusti、Creusot、Aeneas、Coq
- 活跃对应页：[`concept/04_formal/02_separation_logic/`](../concept/04_formal/02_separation_logic/)

### 5.3 案例研究

- [`rust-ownership-decidability/case-studies/`](rust-ownership-decidability/case-studies/) — 按领域组织（wasm, security, ml-ai, media, gamedev, embedded, database, cloud, cli, blockchain）
- 活跃对应页：[`concept/06_ecosystem/`](../concept/06_ecosystem/)、[`content/`](../content/)

### 5.4 并发/异步/分布式专题

- [`rust-ownership-decidability/12-concurrency-patterns/`](rust-ownership-decidability/12-concurrency-patterns/)
- [`rust-ownership-decidability/async-specialty/`](rust-ownership-decidability/async-specialty/)
- [`rust-ownership-decidability/16-program-semantics/distributed-patterns/`](rust-ownership-decidability/16-program-semantics/distributed-patterns/)
- 活跃对应页：[`concept/03_advanced/01_async/`](../concept/03_advanced/01_async/)、[`concept/05_comparative/`](../concept/05_comparative/)

### 5.5 形式化工程系统旧版

- [`docs/c_class_audit_2026_06_08/rust-formal-engineering-system/`](docs/c_class_audit_2026_06_08/rust-formal-engineering-system/)
- 活跃对应页：[`concept/04_formal/`](../concept/04_formal/)

---

## 6. 生态深度内容

### 6.1 异步运行时与网络

- [`content/ecosystem/async_runtimes/`](content/ecosystem/async_runtimes/)
- [`content/ecosystem/error_handling/`](content/ecosystem/error_handling/)
- 活跃对应页：[`concept/03_advanced/01_async/`](../concept/03_advanced/01_async/)、[`concept/06_ecosystem/networks/`](../concept/06_ecosystem/)

### 6.2 数据库与 ORM

- [`content/ecosystem/`](content/ecosystem/) 中 SQLx、SeaORM 相关材料
- 活跃对应页：[`concept/06_ecosystem/databases/`](../concept/06_ecosystem/)

### 6.3 序列化与数据格式

- [`content/ecosystem/serialization/`](content/ecosystem/serialization/)
- 活跃对应页：[`concept/06_ecosystem/`](../concept/06_ecosystem/)

### 6.4 场景化应用

- [`content/scenarios/`](content/scenarios/) — CLI、Web、嵌入式、游戏、数据工程、系统基础设施
- 活跃对应页：[`content/ecosystem/`](../content/ecosystem/)（若已迁移）、[`docs/05_practice/`](../docs/05_practice/)

### 6.5 生产实践

- [`content/production/`](content/production/) — K8s、serverless、CI/CD、可观测性、性能调优
- 活跃对应页：[`content/safety_critical/`](../content/safety_critical/)、[`docs/05_practice/`](../docs/05_practice/)

### 6.6 前沿特性跟踪

- [`content/emerging/`](content/emerging/) — async closures、TAIT、generic const exprs、WASM、gen blocks
- 活跃对应页：[`concept/07_future/`](../concept/07_future/)

### 6.7 知识表征矩阵

- [`content/representations/`](content/representations/)
- 活跃对应页：[`concept/00_meta/`](../concept/00_meta/)

---

## 7. 研究笔记与实验

### 7.1 版本特性研究笔记

- [`research_notes/`](research_notes/) — Rust 1.91–1.94 特性、语义框架、工具矩阵
- 活跃对应页：[`concept/07_future/00_version_tracking/`](../concept/07_future/00_version_tracking/)

### 7.2 研究笔记快照（2026-06-25）

- [`research_notes_2026_06_25/`](research_notes_2026_06_25/)
- 子目录：`experiments/`、`formal_methods/`、`formal_modules/`、`software_design_theory/`、`type_theory/`
- 活跃对应页：[`concept/04_formal/`](../concept/04_formal/)

### 7.3 设计理论

- [`research_notes_2026_06_25/software_design_theory/`](research_notes_2026_06_25/software_design_theory/)
- 活跃对应页：[`concept/06_ecosystem/03_design_patterns/`](../concept/06_ecosystem/03_design_patterns/)

---

## 8. 质量审计、链路检查与临时文件

### 8.1 链路健康与死链报告

- [`LINK_CHECK_REPORT_FULL.md`](LINK_CHECK_REPORT_FULL.md)
- [`reports/2026_07/`](reports/2026_07/) 中 `LINK_CHECK_*.md` 系列
- 活跃对应页：无（审计产物）

### 8.2 内容重叠与去重报告

- [`reports/2026_07/CONTENT_OVERLAP_DETECTION_*.md`](reports/2026_07/)
- 活跃对应页：无（审计产物）

### 8.3 内容完整性与 i18n 审计

- [`reports/2026_07/CONTENT_COMPLETENESS_*.md`](reports/2026_07/)
- [`reports/2026_07/I18N_*.md`](reports/2026_07/)
- 活跃对应页：无（审计产物）

### 8.4 安全/供应链审计

- [`reports/2026_07/`](reports/2026_07/) 中安全相关报告
- 活跃对应页：[`supply-chain/`](../supply-chain/)

### 8.5 临时文件与快速参考

- [`temp/`](temp/)
- [`docs/temp/`](docs/temp/)
- [`docs/version_reports/`](docs/version_reports/)
- 活跃对应页：[`docs/03_reference/quick_reference/`](../docs/03_reference/quick_reference/)

### 8.6 备份与重组历史

- [`backup_from_docs/`](backup_from_docs/) — 2025 年 `docs/` 大重组备份
- [`docs/2026_03_reorganization/`](docs/2026_03_reorganization/) — 2026 年 3 月重组记录
- 活跃对应页：[`docs/`](../docs/)

### 8.7 已废弃方案

- [`deprecated/RUST_SAFETY_CRITICAL_ECOSYSTEM/`](deprecated/RUST_SAFETY_CRITICAL_ECOSYSTEM/)
- [`deprecated/coq_skeleton/`](deprecated/coq_skeleton/)
- 活跃对应页：[`content/safety_critical/`](../content/safety_critical/)

---

## 附录 A：关键统计数据

| 指标 | 数值 |
|------|------|
| Markdown 文件总数 | 12,361 |
| 重复标题组 | 1,354 组 |
| MD5 完全相同文件组 | 1,211 组 |
| 顶层全局报告 | 21 份 |
| 空标题文件（未匹配到 `#` 一级标题） | 4,467 份 |

> 注：空标题文件多集中在 `backup_from_docs/backup_from_docs/`、旧版报告和 README 中，标题提取规则仅匹配 `# 标题`，部分文件使用 `#标题` 或 front matter 形式导致未命中。建议后续完善标题元数据。

---

## 附录 B：相关文件

- [`RELATIONSHIP_MAP.md`](RELATIONSHIP_MAP.md) — 文件关联组与相关度分析
- [`tmp/archive_overlap_scan_2026_07_19.md`](../tmp/archive_overlap_scan_2026_07_19.md) — 完整重叠检测报告
- [`tmp/archive_inventory_before_2026_07_19.txt`](../tmp/archive_inventory_before_2026_07_19.txt) — 目录结构备份清单
