# Archive 文件关联度映射（重组后）

> 本文件梳理 `archive/` 内部高相关度文件组，便于检索、合并与清理决策。
> 生成时间：2026-07-20
> 配套文件：[`THEMATIC_INDEX.md`](THEMATIC_INDEX.md)

---

## 关联度评级

| 评级 | 含义 | 建议动作 |
|------|------|----------|
| 🔴 极高 | 同一事件/主题的多个版本，内容高度重叠或完全相同 | 已合并或标记主报告，其余改为 stub |
| 🟠 高 | 同一主题的不同角度或前后版本 | 建立版本映射，保留差异较大的版本 |
| 🟡 中 | 主题相关但领域不同 | 保留，在索引中交叉引用 |
| 🟢 低 | 仅在高层主题相关 | 无需特别处理 |

---

## 组 A：版本特性对齐族 🔴 极高

**主题**：项目与国际/官方权威来源的版本对齐与验证。

| 文件/目录 | 说明 |
|-----------|------|
| `02_version_alignment/RUST_196_FEATURE_ALIGNMENT_AUDIT.md` | 1.96 特性对齐审计 |
| `02_version_alignment/RUST_REFERENCE_GAP_ANALYSIS_REPORT.md` | Rust Reference 缺口分析 |
| `02_version_alignment/RUST_SYMMETRIC_DIFFERENCE_ANALYSIS_2026_05_01.md` | 国际权威来源对称差分析 |
| `02_version_alignment/02_verification_reports/` | Rust 1.94 等版本验证报告 |
| `02_version_alignment/01_rust_version_tracking/` | 工具链、历史版本文档、版本报告 |
| `07_research_notes/01_version_research/` | 版本特性研究笔记 |
| `04_crate_reports/*/RUST_189_*`、`04_crate_reports/*/RUST_190_*` | 各 crate 版本特性报告 |

**相关度**: 高（同一主题：版本权威来源对齐）
**建议动作**: 已集中到 `02_version_alignment/` 各子目录；在 `THEMATIC_INDEX.md` 中统一交叉引用。

---

## 组 B：Crate 完成报告族 🔴 极高

**主题**：各 crate 的“完成/增强/升级”报告，存在大量重复和近克隆。

| 目录 | 说明 |
|------|------|
| `04_crate_reports/01_c01_ownership_borrow_scope/` | 所有权/借用/作用域 crate 报告 |
| `04_crate_reports/02_c02_type_system/` | 类型系统 crate 报告 |
| `04_crate_reports/06_c06_async/` | 异步 crate 报告（最大报告族） |
| `04_crate_reports/08_c08_algorithms/` | 算法 crate 报告 |
| `04_crate_reports/10_c10_networks/` | 网络 crate 报告 |
| `04_crate_reports/08_c08_algorithms_docs_archive_2025/` | 旧版算法 crate 文档 |
| `04_crate_reports/11_cargo_package_management/` | Cargo 包管理旧版教程 |

**重叠检测数据**: 聚焦扫描发现多对高相似度（Jaccard ≥ 0.6）crate 报告。
**建议动作**: 已按 crate 集中；未来可进一步每个 crate 选主报告，其余 stub 化；MD5 完全相同文件可删除。

---

## 组 C：Cargo 包管理旧版族 🟠 高

**主题**：Cargo 包管理体系旧版（2025-10）。

| 文件/目录 | 说明 |
|-----------|------|
| `04_crate_reports/11_cargo_package_management/` | 17 份文档 + diagrams + examples |
| 当前活跃 `concept/06_ecosystem/cargo/` | 新版权威来源 |

**相关度**: 高（同一主题旧版与新版迁移关系）
**建议动作**: 保留为历史参考；在 `THEMATIC_INDEX.md` 中明确标注活跃对应页；无需物理合并。

---

## 组 D：形式化/所有权/可判定性族 🔴 极高

**主题**：Rust 所有权、借用、可判定性、形式化验证的教学与研究资料。

| 目录/文件 | 说明 |
|-----------|------|
| `09_special_collections/rust_ownership_decidability/` | 全部 450+ 文件，核心教学资料 |
| `05_formal_methods/06_chinese_ownership_tutorial/` | 中文所有权与可判定性教程旧版 |
| `05_formal_methods/02_academic_tools/` | RustBelt、Tree Borrows、Polonius、Kani、Prusti、Creusot、Aeneas |
| `05_formal_methods/05_research_notes_formal/` | 形式化方法研究笔记 |
| `07_research_notes/06_formal_unified_models/` | LSIP、PostgreSQL 形式化、Rust 核心 crate 形式化塔 |
| `03_concept_history/02_knowledge_cards/04_expert/academic/` | 专家级学术知识卡片 |

**相关度**: 极高（同一学术/教学主题，多版本、多格式）
**建议动作**: 已保留 `09_special_collections/rust_ownership_decidability/` 作为主历史归档；在 `THEMATIC_INDEX.md` 中建立清晰的专题入口；`05_formal_methods/` 收纳学术工具与研究笔记。

---

## 组 E：生态深度族 🟡 中-高

**主题**：Rust 生态深度内容（异步、数据库、序列化、场景、生产实践、前沿特性）。

| 目录 | 说明 |
|------|------|
| `06_ecosystem/01_async_runtimes/` | 异步运行时 |
| `06_ecosystem/02_databases_orm/` | 数据库与 ORM |
| `06_ecosystem/03_serialization/` | 序列化 |
| `06_ecosystem/04_scenarios/` | 场景化应用 |
| `06_ecosystem/05_production_practices/` | 生产实践 |
| `06_ecosystem/06_emerging_features/` | 前沿特性 |
| `06_ecosystem/07_representations/` | 知识表征 |
| `06_ecosystem/08_crate_case_studies/` | Crate 案例研究入口（指向 `rust_ownership_decidability/case-studies/`） |
| `07_research_notes/03_software_design_theory/` | 设计理论研究 |

**相关度**: 中-高（主题接近，但领域不同）
**建议动作**: 已按主题拆分；在 `THEMATIC_INDEX.md` 中按主题交叉引用。

---

## 组 F：审计报告族 🟠 高

**主题**：质量门历史报告（链路检查、内容重叠、内容完整性、i18n、安全审计）。

| 文件/目录 | 说明 |
|-----------|------|
| `08_quality_audits/LINK_CHECK_REPORT_FULL.md` | 全库链路健康报告 |
| `08_quality_audits/02_content_overlap/` | 内容重叠检测报告 |
| `08_quality_audits/08_reports_by_time/2026_07/` | 2026 年 7 月质量门报告 |
| `08_quality_audits/08_reports_by_time/2026_Q1/` | 2026 Q1 质量门报告 |
| `08_quality_audits/09_c_class_audit_2026_06_08/` | C-class 审计包 |
| `01_governance/CRITICAL_AUDIT_REPORT_2026.md` | 批判性审计 |

**相关度**: 高（同一主题：质量门历史报告）
**建议动作**: 已按审计类型和时间归并；在 `THEMATIC_INDEX.md` 中提供快速入口。

---

## 组 G：备份与独立专题集合 🟡 中

**主题**：超大历史备份与专题独立集合。

| 目录 | 说明 |
|------|------|
| `09_special_collections/backup_from_docs/` | 2025 年 `docs/` 大重组完整备份 |
| `09_special_collections/rust_ownership_decidability/` | 所有权可判定性研究历史资料 |
| `08_quality_audits/07_backup_from_docs_entry/` | docs 大备份入口 stub |
| `05_formal_methods/01_ownership_decidability_collection/` | 所有权可判定性专题入口 stub |

**相关度**: 中（均为历史资料，但来源不同）
**建议动作**: 保留为独立集合，不拆散；在主题目录中创建入口 stub；在 `THEMATIC_INDEX.md` 中标注专题入口。

---

## 组 H：顶层全局报告族 🟡 中

**主题**：项目全局层面的计划、审计、对齐报告。

| 文件 | 说明 |
|------|------|
| `01_governance/PHASE1_COMPLETION_REPORT.md` | 阶段 1 完成报告 |
| `01_governance/PROJECT_FOLLOW_UP_PLAN.md` | 项目后续计划 |
| `01_governance/PROJECT_NEXT_PHASE_PLAN.md` | 下阶段计划 |
| `01_governance/CRITICAL_AUDIT_REPORT_2026.md` | 批判性审计 |
| `02_version_alignment/RUST_SYMMETRIC_DIFFERENCE_ANALYSIS_2026_05_01.md` | 对称差分析 |
| `02_version_alignment/RUST_196_FEATURE_ALIGNMENT_AUDIT.md` | 1.96 对齐审计 |
| `02_version_alignment/RUST_REFERENCE_GAP_ANALYSIS_REPORT.md` | Reference 缺口 |
| `08_quality_audits/LINK_CHECK_REPORT_FULL.md` | 全库链路报告 |

**相关度**: 中（均为项目级文件，但主题不同）
**建议动作**: 保留在主题根目录；在 `THEMATIC_INDEX.md` 中按主题分类引用。

---

## 跨集合相关度（新增/合并后）

| 来源 A | 来源 B | 关系 | 处理状态 |
|---|---|---|---|
| `archive/docs/content/` | `archive/content/`（已迁移至 `06_ecosystem/` 等） | 镜像副本 | 已合并/去重，docs/content 已移除 |
| `docs/deprecated/` | `08_quality_audits/deprecated/` | 重复目录 | 已合并到 `05_formal_methods/04_coq_aeneas_deprecated/` |
| `docs/temp/` | `08_quality_audits/temp/` | 重复目录 | 已合并到 `08_quality_audits/05_temp_quick_reference/` |
| `2026/crates_c08_algorithms_docs_archive_2025/` | `2026/crates_reports/c08_algorithms/` | 同一 crate 报告历史 | 已合并到 `04_crate_reports/08_c08_algorithms/` 与 `08_c08_algorithms_docs_archive_2025/` |
| `research_notes/` 与 `research_notes_2026_06_25/` | `rust-ownership-decidability/10-research-frontiers/` | 版本研究重叠 | 已集中并通过索引交叉引用 |
| `backup_from_docs/formal_rust/` | `rust-ownership-decidability/` | 主题重叠 | 不拆散，在 `05_formal_methods/` 中建立专题入口 |
| `backup_from_docs/language/` | `2026/concept_archive/`、`03_concept_history/` | 旧版概念页来源 | 不拆散，在 `03_concept_history/` 中建立旧版概念入口 |

---

## 后续清理建议

| 优先级 | 关联组 | 动作 | 说明 |
|--------|--------|------|------|
| P0 | 组 B | 继续去重 crate 完成报告 | 每个 crate 选主报告，其余 stub 化 |
| P1 | 组 D | 完善 `rust_ownership_decidability/` 子索引 | 按主题生成子索引 |
| P2 | 组 A | 统一版本对齐报告引用 | 避免权威来源引用混乱 |
| P3 | 组 F | 保留按时间序列审计报告 | 已归并到 `08_quality_audits/08_reports_by_time/` |
| P4 | 组 G | 完善 `backup_from_docs/` 主题子索引 | 提升 11K 文件的可发现性 |
| P5 | 跨集合 | 监控新增重复 | 每月运行 `scripts/archive_index_sync.py` |

---

## 相关文件

- [`THEMATIC_INDEX.md`](THEMATIC_INDEX.md) — 主题索引
- [`ARCHIVE_REORG_LOG_2026_07_20.md`](ARCHIVE_REORG_LOG_2026_07_20.md) — 重组迁移记录
- [`tmp/archive_overlap_scan_before_reorg_2026_07_20.md`](../tmp/archive_overlap_scan_before_reorg_2026_07_20.md) — 重组前重叠检测报告
- [`../archive_policy.md`](../archive_policy.md) — 归档政策
