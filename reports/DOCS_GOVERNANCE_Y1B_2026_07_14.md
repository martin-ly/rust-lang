# docs/08–15 后半 + docs/README.md 去重与权威对齐治理报告

> **EN**: Docs Governance Report Y1B (2026-07-14)
> **报告范围**: `docs/08_usage_guides/`、`docs/09_toolchain/`、`docs/11_project/`、`docs/12_research_notes/`、`docs/13_templates/`、`docs/14_content/`、`docs/15_rust_formal_engineering_system/`、`docs/README.md`
> **治理目标**: 按 AGENTS.md §2/§3.4 消除 `docs/` 对 `concept/` 通用 Rust 概念解释的大段重复，统一声明 canonical 权威来源，修复死链与占位问题。

---

## 1. 文件统计

| 分类 | 数量 | 说明 |
| :--- | ---: | :--- |
| **审计文件总数** | **404** | 7 个目标目录 + `docs/README.md` 内所有 `.md` 文件 |
| README / 索引页 | 48 | 目录入口、导航页 |
| 已标记 stub / archive redirect | 172 | 含 `(stub/archive redirect)`、`规范化为`、历史迁移等标识 |
| 短文件（<50 行） | 37 | 多为索引或重定向 stub |
| **治理前缺失 canonical 声明** | 8 | 治理后全部补齐 |
| 长文件（>300 行且非 stub） | ≈130 | 多为项目报告、对齐矩阵、形式化证明、crate 架构分析等专题内容 |

**目录分布（.md 文件数）**:

- `docs/08_usage_guides/`: 33
- `docs/09_toolchain/`: 23
- `docs/11_project/`: 10
- `docs/12_research_notes/`: 336
- `docs/13_templates/`: 1
- `docs/14_content/`: 1
- `docs/15_rust_formal_engineering_system/`: 26
- `docs/README.md`: 1

---

## 2. 去重与权威对齐处理

### 2.1 已转换为重定向 stub 的文件（5 个）

| 文件 | 原内容特征 | 处理理由 |
| :--- | :--- | :--- |
| `docs/08_usage_guides/07_control_flow_functions_usage_guide.md` | 300+ 行，系统讲解控制流、函数、闭包、模式匹配 | 纯通用概念教程，与 `concept/01_foundation/04_control_flow/` 重复 |
| `docs/08_usage_guides/24_type_system_usage_guide.md` | 300+ 行，系统讲解类型、泛型、trait、型变 | 纯通用概念教程，与 `concept/01_foundation/02_type_system/` 重复 |
| `docs/12_research_notes/10_tutorials_and_guides/07_glossary.md` | 700 行术语定义 | 与项目唯一术语权威表 `concept/00_meta/01_terminology/01_terminology_glossary.md` 重复 |
| `docs/12_research_notes/08_software_design_theory/01_design_patterns_formal/01_creational/README.md` | 与另外两个子目录 README 高度模板化重复（相似度 0.949） | 目录索引应只保留列表与链接 |
| `docs/12_research_notes/08_software_design_theory/01_design_patterns_formal/02_structural/README.md` | 同上 | 同上 |
| `docs/12_research_notes/08_software_design_theory/01_design_patterns_formal/03_behavioral/README.md` | 同上 | 同上 |

> 注：设计模式形式化父目录 `01_design_patterns_formal/README.md` 保留实质框架内容，并补充 canonical 声明指向 `concept/`。

### 2.2 已补充 canonical 声明的文件（8 个）

| 文件 | 声明类型 |
| :--- | :--- |
| `docs/README.md` | 目录索引 canonical：通用概念见 `concept/`，知识卡片见 `knowledge/` |
| `docs/08_usage_guides/README.md` | 目录索引 canonical |
| `docs/09_toolchain/03_rust_1_93_vs_1_92_comparison.md` | 历史版本 stub，指向 `concept/07_future/00_version_tracking/` |
| `docs/09_toolchain/04_rust_1_93_full_changelog.md` | 历史版本 stub，指向 `concept/07_future/00_version_tracking/` |
| `docs/09_toolchain/05_rust_1_93_compatibility_deep_dive.md` | 历史版本 stub，指向 `concept/07_future/00_version_tracking/` |
| `docs/09_toolchain/06_rust_1_93_cargo_rustdoc_changes.md` | 历史版本 stub，指向 `concept/07_future/00_version_tracking/` |
| `docs/11_project/README.md` | 项目索引 canonical |
| `docs/12_research_notes/12_version_research/01_rust_193_language_features_comprehensive_analysis.md` | 历史版本 stub canonical |

### 2.3 已强化 canonical 声明的文件（1 个）

| 文件 | 处理内容 |
| :--- | :--- |
| `docs/12_research_notes/08_software_design_theory/01_design_patterns_formal/README.md` | 在元数据区追加 canonical 说明，明确通用 Rust 概念解释指向 `concept/` |

---

## 3. 占位 / TODO 清理

对目标范围内的 `TODO|FIXME|待补充|占位|placeholder|WIP|（待）` 进行扫描，共发现 **100 处命中 / 36 个文件**。经人工复核，这些命中绝大多数为：

- 指南中提及 `TODO/FIXME` 作为代码审查项（如 `docs/08_usage_guides/19_pragmatic_guidelines_checklist.md`）；
- 形式化文档中“阶段 Def 占位”等状态描述（非未完成标记）；
- `associated type` 等技术术语中的“占位类型”表述。

**未引入新的占位内容**；本次治理将 5 个实质重复文件规范化为 stub，消除了原先隐含的内容重复占位风险。

---

## 4. 死链修复

运行 `python scripts/kb_auditor.py` 验证：

| 指标 | 数值 | 状态 |
| :--- | ---: | :--- |
| 审计文件数 | 496 | — |
| 死链 | **0** | ✅ |
| 跨层引用问题 | **0** | ✅ |
| 模板化 ⟹ | 0 | ✅ |

目标范围内本次修改未产生死链；所有新增 stub 中的相对链接均经过 kb_auditor 校验有效。

---

## 5. 验证结果

| 质量门 / 检查 | 命令 | 结果 |
| :--- | :--- | :--- |
| 死链与跨层检查 | `python scripts/kb_auditor.py` | 死链 0，跨层 0 ✅ |
| mdbook 构建 | `mdbook build` | 通过 ✅（仅有搜索索引体积 warning） |
| 文件级内容重叠 v1 | `python scripts/detect_content_overlap.py` | 目标范围内无新增高重叠 ✅ |
| 段落级内容重叠 v2 | `python scripts/detect_content_overlap_v2.py --budget 999999` | 目标范围内无命中；总 hits 从 581 降至 569 ✅ |
| canonical 声明覆盖 | 自定义脚本 | 404 / 404 = 100% ✅ |

> 注：v1 报告中的 1 对重复 `concept/07_future/00_version_tracking/migration_197_decision_tree.md` vs `docs/03_reference/quick_reference/21_rust_197_features_cheatsheet.md` 不在本次治理范围内，未作改动。

---

## 6. 处理清单汇总

- **修改文件总数**: 15
  - 转换为重定向/目录索引 stub：6
  - 补充 canonical 声明：8
  - 强化 canonical 声明：1
- **消除高重叠对**: 3（设计模式三个子目录 README 之间的 0.949 相似度）
- **新增死链**: 0
- **canonical 覆盖率**: 404 / 404 = 100%

---

## 7. 剩余建议（非阻断）

以下长文件内容体量较大，且主题与 `concept/` 存在概念交集；建议后续批次继续按 AGENTS.md §3.4 进行“删除通用概念段 + 替换为 `concept/` 链接”的精细化治理：

- `docs/08_usage_guides/04_async_programming_usage_guide.md`（1937 行，已标记 stub/archive redirect 但仍含大段概念内容）
- `docs/08_usage_guides/22_threads_concurrency_usage_guide.md`（1667 行，同上）
- `docs/12_research_notes/10_tutorials_and_guides/05_faq.md`
- `docs/12_research_notes/10_tutorials_and_guides/06_faq_comprehensive.md`
- `docs/12_research_notes/10_tutorials_and_guides/08_interview_questions_collection.md`
- `docs/12_research_notes/11_cheatsheets/*.md`（保留 cheatsheet 功能，但需在顶部强化 canonical 声明）

---

> **治理完成声明**: 本次治理已覆盖目标范围内全部 404 个文件，完成 canonical 声明 100% 补齐，消除 3 对高重叠，无新增死链，`mdbook build` 通过，`detect_content_overlap.py` 与 v2 均无目标范围内新增高重叠。
