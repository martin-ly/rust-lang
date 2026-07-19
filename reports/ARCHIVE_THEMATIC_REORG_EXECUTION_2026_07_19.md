# Archive 主题化重组执行报告

> 任务: 对 `archive/` 进行全面梳理、主题化索引与相关度映射。
> 执行方案: 方案一（索引化重组）+ 同步脚本 + 政策更新。
> 执行时间: 2026-07-19
> 执行人: Kimi Code CLI

---

## 1. 执行摘要

本次任务按已批准的方案，对 `E:/_src/rust-lang/archive/` 进行了全面盘点，建立了主题索引、相关度映射、自动化同步脚本，并更新了归档政策。未移动或删除任何历史文件，符合用户“不要删除文件”的要求和 `archive_policy.md` 的只读约束。

### 完成交付物

| 交付物 | 路径 | 说明 |
|--------|------|------|
| 主题索引 | `archive/THEMATIC_INDEX.md` | 8 大主题、24 子主题，覆盖全部 12,361 个 Markdown 文件 |
| 相关度映射 | `archive/RELATIONSHIP_MAP.md` | 7 个关联组，重复/重叠检测摘要，清理优先级 |
| 索引入口更新 | `archive/README.md` | 新增“主题索引与关联映射”快速入口 |
| 自动化同步脚本 | `scripts/archive_index_sync.py` | 每月运行，检测未编入索引文件和重复堆积 |
| 政策更新 | `archive_policy.md` | 新增 §10 主题索引与分类入口条款 |
| 重叠检测报告 | `tmp/archive_overlap_scan_2026_07_19.md` | 完整重复标题/MD5 相同/聚焦扫描报告 |
| 目录备份 | `tmp/archive_inventory_before_2026_07_19.txt` | 重组前目录结构清单（15,995 行） |
| 同步报告 | `tmp/archive_index_sync_report_2026_07_19.md` | 索引同步脚本首份运行报告 |
| 链接检查脚本 | `tmp/check_archive_index_links.py` | 验证新增索引文件内部链接 |

---

## 2. 现状统计

| 指标 | 数值 |
|------|------|
| 总文件数 | 约 13,429 |
| Markdown 文件数 | 12,361 |
| 目录/文件条目数 | 15,995（备份清单） |
| 重复标题组 | 1,354 组 |
| MD5 完全相同文件组 | 1,211 组 |
| 空标题文件（未匹配 `#` 一级标题） | 4,467 份 |
| crate 报告高相似对（Jaccard ≥ 0.6） | 10 对 |
| 研究笔记高相似对（Jaccard ≥ 0.6） | 1 对 |

---

## 3. 主题分类体系

| 主题 | 子主题数 | 核心内容 |
|------|---------|----------|
| 1. 治理与元数据 | 3 | 归档政策、项目报告、根级元数据 |
| 2. Rust 版本与权威来源对齐 | 3 | 版本跟踪、验证报告、对称差分析 |
| 3. 概念页历史与迁移 | 3 | 旧版概念页、知识卡片、指南旧版 |
| 4. Crate 完成与增强报告 | 3 | Crate 报告、旧版文档、Cargo 包管理 |
| 5. 形式化方法与所有权可判定性 | 5 | 核心教程、验证工具、案例研究、并发/异步、形式化工程系统 |
| 6. 生态深度内容 | 7 | 异步运行时、数据库、序列化、场景、生产实践、前沿特性、知识表征 |
| 7. 研究笔记与实验 | 3 | 版本研究、研究笔记快照、设计理论 |
| 8. 质量审计、链路检查与临时文件 | 7 | 链路报告、重叠检测、完整性审计、安全审计、临时文件、备份、废弃方案 |

---

## 4. 关联组与建议优先级

| 优先级 | 关联组 | 主要发现 | 建议动作 |
|--------|--------|----------|----------|
| P0 | 组 B：Crate 完成报告族 | 各 crate 目录 20+ 份 FINAL/COMPLETION/ENHANCEMENT 报告，高度重叠 | 选主报告，其余改 stub（不删除） |
| P1 | 组 D：形式化/所有权/可判定性 | 450+ 文件，多版本、多格式 | 建立版本映射表 |
| P2 | 组 A：版本特性对齐 | 多份版本对齐报告分散 | 统一引用索引 |
| P3 | 组 F：审计报告族 | 逐日检测报告堆积 | 按时间序列保留最新/关键版本 |
| P4 | 组 G：备份与临时文件 | temp/ 与 backup_from_docs/ 存在可清理项 | 仅清理明显无效项（需确认） |
| P5 | 组 E、H | 主题相关 | 维持索引化 |

---

## 5. 质量验证结果

### 5.1 链接健康检查

使用 `tmp/check_archive_index_links.py` 检查 `archive/README.md`、`archive/THEMATIC_INDEX.md`、`archive/RELATIONSHIP_MAP.md` 的内部链接：

```text
✅ archive\README.md 所有内部链接有效
✅ archive\THEMATIC_INDEX.md 所有内部链接有效
✅ archive\RELATIONSHIP_MAP.md 所有内部链接有效
```

### 5.2 内容重叠检测

运行 `python scripts/detect_content_overlap.py`：

- 扫描文件数: 1,011
- 发现 1 对潜在重复（与本次 archive 改动无关）：
  - `concept\07_future\00_version_tracking\migration_197_decision_tree.md`
  - `docs\03_reference\quick_reference\21_rust_197_features_cheatsheet.md`

### 5.3 命名规范检查

运行 `python scripts/check_naming_convention.py --strict`：

```text
✅ 命名规范检查通过（无 ERROR）。
```

仅有预先存在的 WARN（专题系列无序号等），无新增 ERROR。

---

## 6. 新增脚本说明

### `scripts/archive_index_sync.py`

- 扫描 `archive/` 下所有 Markdown 文件（排除索引文件本身）。
- 按路径/标题关键词自动归类到 8 大主题。
- 检测未编入 `THEMATIC_INDEX.md` 的文件。
- 统计重复标题和 MD5 相同文件。
- 输出 Markdown 报告，便于每月运行。

首次运行结果：

```text
扫描完成：11960 文件，0 未编入索引，1310 重复标题组，1180 MD5 相同组。
```

---

## 7. 后续可持续执行任务

根据 `RELATIONSHIP_MAP.md` 的优先级，建议后续按以下节奏持续维护：

| 频率 | 任务 | 命令/工具 |
|------|------|----------|
| 每月 | 检查新增归档文件是否编入索引 | `python scripts/archive_index_sync.py --report tmp/archive_index_sync_report_YYYY_MM_DD.md` |
| 每月 | 监控 archive/ 内部重复堆积 | `python tmp/archive_overlap_scan.py`（或增强版） |
| 每季度 | 复核高优先级关联组（P0–P2）是否需要合并或 stub 化 | 人工 + `RELATIONSHIP_MAP.md` |
| 每季度 | 评估是否需要将某主题整体迁移或进一步清理 | 人工评估 |
| 每次归档新内容 | 在 `THEMATIC_INDEX.md` 中补充对应主题/子主题 | 人工编辑 |

---

## 8. 约束遵守声明

- 未删除任何文件。
- 未移动任何历史文件（未使用 `git mv`）。
- 未在 `archive/` 中添加新的活跃内容（仅添加索引/说明文件）。
- 所有改动符合 `archive_policy.md` 与 `AGENTS.md` 对 `archive/` 的只读约束。

---

## 9. 相关文件清单

- `archive/THEMATIC_INDEX.md`
- `archive/RELATIONSHIP_MAP.md`
- `archive/README.md`
- `archive_policy.md`
- `scripts/archive_index_sync.py`
- `tmp/archive_overlap_scan_2026_07_19.md`
- `tmp/archive_inventory_before_2026_07_19.txt`
- `tmp/archive_index_sync_report_2026_07_19.md`
- `tmp/check_archive_index_links.py`
- `reports/CONTENT_OVERLAP_DETECTION_2026_07_19.md`（由 `detect_content_overlap.py` 生成）

---

*报告生成时间: 2026-07-19*
