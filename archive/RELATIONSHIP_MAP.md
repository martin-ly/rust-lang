# Archive 文件关联度映射

> 本文件梳理 `archive/` 内部高相关度文件组，便于检索、合并与清理决策。
> 生成时间：2026-07-19
> 配套文件：[`THEMATIC_INDEX.md`](THEMATIC_INDEX.md)

---

## 关联度评级

| 评级 | 含义 | 建议动作 |
|------|------|----------|
| 🔴 极高 | 同一事件/主题的多个版本，内容高度重叠或完全相同 | 合并或标记主报告，其余改为 stub |
| 🟠 高 | 同一主题的不同角度或前后版本 | 建立版本映射，保留差异较大的版本 |
| 🟡 中 | 主题相关但领域不同 | 保留，在索引中交叉引用 |
| 🟢 低 | 仅在高层主题相关 | 无需特别处理 |

---

## 组 A：版本特性对齐族 🔴 极高

**主题**：项目与国际/官方权威来源的版本对齐与验证。

| 文件 | 说明 |
|------|------|
| `RUST_196_FEATURE_ALIGNMENT_AUDIT.md` | 1.96 特性对齐审计 |
| `RUST_REFERENCE_GAP_ANALYSIS_REPORT.md` | Rust Reference 缺口分析 |
| `RUST_SYMMETRIC_DIFFERENCE_ANALYSIS_2026_05_01.md` | 国际权威来源对称差分析 |
| `verification_reports/RUST_194_VERIFICATION_REPORT.md` | 1.94 编译器验证报告 |
| `research_notes/10_rust_194_core_notes_index.md` | 1.94 研究笔记索引 |
| `2026/concept_archive/` 中各版本对应旧版概念页 | 旧版概念页按版本归档 |

**相关度**: 高（同一主题：版本权威来源对齐）
**建议动作**: 在 `THEMATIC_INDEX.md` 中统一交叉引用；如未来物理重组，可合并到 `archive/02_version_alignment/`。

---

## 组 B：Crate 完成报告族 🔴 极高

**主题**：各 crate 的“完成/增强/升级”报告，存在大量重复和近克隆。

| 目录 | 说明 |
|------|------|
| `2026/crates_reports/c08_algorithms/` | 20+ 份 FINAL/COMPLETION/ENHANCEMENT/UPGRADE 报告 |
| `2026/crates_reports/c10_networks/` | 同类完成报告 |
| `2026/crates_reports/c06_async/` | 多任务完成报告族 |
| `2026/crates_reports/c01_ownership_borrow_scope/` | RUST_189/190 特性分析报告 |
| `2026/crates_c08_algorithms_docs_archive_2025/` | 旧版算法 crate 文档 |

**重叠检测数据**:

- 聚焦扫描发现 10 对高相似度（Jaccard ≥ 0.6）crate 报告对。
- 顶层存在大量同名/空标题报告（如 `FINAL_COMPLETION_REPORT.md`、`PROJECT_COMPLETION_REPORT.md`）。

**相关度**: 极高（同一事件多份报告，内容高度重叠）
**建议动作**:

1. 每个 crate 挑选一份最完整的“主报告”保留。
2. 其余报告改为重定向 stub，指向主报告。
3. 对完全相同的文件（MD5 相同）可安全删除冗余副本。

---

## 组 C：Cargo 包管理旧版族 🟠 高

**主题**：Cargo 包管理体系旧版（2025-10）。

| 文件/目录 | 说明 |
|-----------|------|
| `cargo_package_management_from_c02/` | 17 份文档 + diagrams + examples |
| `cargo_package_management_from_c02/README.md` | 旧版导航 |
| 当前活跃 `concept/06_ecosystem/cargo/` | 新版权威来源 |

**相关度**: 高（同一主题旧版与新版迁移关系）
**建议动作**: 保留为历史参考；在 `THEMATIC_INDEX.md` 中明确标注活跃对应页；无需物理合并。

---

## 组 D：形式化/所有权/可判定性族 🔴 极高

**主题**：Rust 所有权、借用、可判定性、形式化验证的教学与研究资料。

| 目录/文件 | 说明 |
|-----------|------|
| `rust-ownership-decidability/` | 全部 450+ 文件，核心教学资料 |
| `docs/c_class_audit_2026_06_08/rust-ownership-decidability/` | C 类审计中的旧版副本 |
| `docs/rust-ownership-chinese/` | 中文所有权与可判定性教程旧版 |
| `content/academic/` | RustBelt、Tree Borrows、Polonius、Kani、Prusti、Creusot、Aeneas、Coq |
| `research_notes_2026_06_25/formal_methods/` | 形式化方法研究笔记 |

**重叠检测数据**:

- 研究笔记双版本聚焦扫描发现 1 对高相似度。
- `content/academic/` 中 `tree_borrows_guide.md` 与 `tree_borrows_authoritative_guide.md` 疑似同一主题双版本。
- `docs/rust-ownership-chinese/` 与 `rust-ownership-decidability/` 内容存在大量主题重叠。

**相关度**: 极高（同一学术/教学主题，多版本、多格式）
**建议动作**:

1. 保留 `rust-ownership-decidability/` 作为主历史归档。
2. 在 `THEMATIC_INDEX.md` 中建立清晰的版本映射表。
3. 对 `content/academic/` 中疑似双版本文件进行人工复核，决定是否合并。
4. `docs/c_class_audit_2026_06_08/` 作为重组历史备份，建议整体保留，不单独处理。

---

## 组 E：生态深度族 🟡 中-高

**主题**：Rust 生态深度内容（异步、数据库、序列化、场景、生产实践、前沿特性）。

| 目录 | 说明 |
|------|------|
| `content/ecosystem/` | 异步运行时、数据库、序列化、错误处理 |
| `content/scenarios/` | 按应用场景（CLI、Web、嵌入式、游戏等） |
| `content/production/` | K8s、serverless、CI/CD、可观测性、性能调优 |
| `content/emerging/` | 前沿特性跟踪 |
| `research_notes/` 中生态相关笔记 | 版本特性与生态工具 |

**相关度**: 中-高（主题接近，但领域不同）
**建议动作**: 保留现有目录结构；在 `THEMATIC_INDEX.md` 中按主题交叉引用；未来如物理重组，可集中为 `archive/06_ecosystem/`。

---

## 组 F：审计报告族 🟠 高

**主题**：质量门历史报告（链路检查、内容重叠、内容完整性、i18n、安全审计）。

| 文件/目录 | 说明 |
|-----------|------|
| `LINK_CHECK_REPORT_FULL.md` | 全库链路健康报告（906 KB） |
| `reports/2026_07/CONTENT_OVERLAP_DETECTION_*.md` | 逐日重叠检测报告 |
| `reports/2026_07/LINK_CHECK_*.md` | 逐日链路检测报告 |
| `reports/2026_07/CONTENT_COMPLETENESS_*.md` | 内容完整性审计 |
| `reports/2026_07/I18N_*.md` | 国际化审计 |
| `CRITICAL_AUDIT_REPORT_2026.md` | 批判性审计 |

**相关度**: 高（同一主题：质量门历史报告）
**建议动作**: 按时间序列保留；在 `THEMATIC_INDEX.md` 中提供快速入口。如空间有限，可仅保留最新版本与关键版本，其余压缩或 stub 化。

---

## 组 G：备份与重组历史族 🟡 中

**主题**：迁移/备份历史，非当前权威来源。

| 目录 | 说明 |
|------|------|
| `backup_from_docs/` | 2025 年 `docs/` 大重组完整备份 |
| `docs/2026_03_reorganization/` | 2026 年 3 月重组记录 |
| `docs/rust-ownership-chinese/` | 中文所有权教程旧版（含 Rust 项目） |
| `temp/` | 历史临时文件 |

**相关度**: 中（均为迁移/备份历史，但来源不同）
**建议动作**:

1. `backup_from_docs/` 作为整体历史备份，建议保留，不单独处理。
2. 对 `temp/` 中明显无价值的临时文件（如空文件、缓存）可清理，需用户确认。
3. 在 `THEMATIC_INDEX.md` 中标注“备份来源”与“活跃对应页”。

---

## 组 H：顶层全局报告族 🟡 中

**主题**：项目全局层面的计划、审计、对齐报告。

| 文件 | 说明 |
|------|------|
| `PHASE1_COMPLETION_REPORT.md` | 阶段 1 完成报告 |
| `PROJECT_FOLLOW_UP_PLAN.md` | 项目后续计划 |
| `PROJECT_NEXT_PHASE_PLAN.md` | 下阶段计划 |
| `CRITICAL_AUDIT_REPORT_2026.md` | 批判性审计 |
| `RUST_SYMMETRIC_DIFFERENCE_ANALYSIS_2026_05_01.md` | 对称差分析 |
| `RUST_196_FEATURE_ALIGNMENT_AUDIT.md` | 1.96 对齐审计 |
| `RUST_REFERENCE_GAP_ANALYSIS_REPORT.md` | Reference 缺口 |
| `LINK_CHECK_REPORT_FULL.md` | 全库链路报告 |

**相关度**: 中（均为项目级文件，但主题不同）
**建议动作**: 保留在根目录；在 `THEMATIC_INDEX.md` 中按主题分类引用即可。

---

## 建议的后续清理优先级

| 优先级 | 关联组 | 动作 | 预估收益 |
|--------|--------|------|----------|
| P0 | 组 B | 合并/去重 crate 完成报告 | 减少大量重复文件，提升可发现性 |
| P1 | 组 D | 建立形式化/所有权资料版本映射 | 理清 450+ 文件关系 |
| P2 | 组 A | 统一版本对齐报告引用 | 避免权威来源引用混乱 |
| P3 | 组 F | 按时间序列归档审计报告 | 减少重复审计报告堆积 |
| P4 | 组 G | 清理 `temp/` 与 `backup_from_docs/` 中无效文件 | 释放空间 |
| P5 | 组 E、H | 保持索引化，按需处理 | 维持现状 |

---

## 相关文件

- [`THEMATIC_INDEX.md`](THEMATIC_INDEX.md) — 主题索引
- [`tmp/archive_overlap_scan_2026_07_19.md`](../tmp/archive_overlap_scan_2026_07_19.md) — 完整重叠检测报告
- [`tmp/archive_inventory_before_2026_07_19.txt`](../tmp/archive_inventory_before_2026_07_19.txt) — 目录结构备份清单
- [`../archive_policy.md`](../archive_policy.md) — 归档政策
