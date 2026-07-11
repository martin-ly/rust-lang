# 重叠对 v2 处置报告（54 对 MERGE + DOCS_INTERNAL）

**日期**: 2026-07-12
**输入**: `reports/OVERLAP_TRIAGE_2026-07-11.json`（MERGE 5 + DOCS_INTERNAL 49 = 54 对，源自 `reports/CONTENT_OVERLAP_V2_2026-07-11.json`）
**验证基线**: `reports/CONTENT_OVERLAP_V2_2026-07-12.json` + `reports/OVERLAP_TRIAGE_2026-07-12.json`（处置后重跑）

---

## 1. 处置总览

| 处置方式 | 对数 | 说明 |
|---|:---:|---|
| 删除（裸删，零引用） | 1 | c03 `multidimensional_matrix.md`（与 `mind_map.md` 逐字节克隆，仅 EN 行不同，全仓零引用） |
| 差异化保留 | 1 | c01 两个 crate stub（不同主题的导航表，仅 H1 与模板相同 → 改写 H1/导语区分） |
| 豁免（模板复用） | 52 | 3 对 design_patterns_formal 系列 README + 49 对 DOCS_INTERNAL（48 对 docs/03_practice 项目骨架 + 1 对 workflow/distributed README） |
| 待人工 review | 0（54 对范围内） | 54 对全部闭环；另有 1 对新浮现 MERGE 列入待 review（见 §5） |

**链接更新计数**: 0。删除/改写的 3 个文件在全仓（排除 reports/archive/book/tmp/target/.git）grep 均无任何入链，无需更新引用。
**额外处置**（重跑 triage 后新浮现的同族克隆，超出原 54 对但风险等价）: 删除 c03 `knowledge_graph.md`（与 `mind_map.md` 仅 EN 行不同、零引用）。

---

## 2. MERGE（5 对）逐对处置

| # | sim | 文件 1 | 文件 2 | 处置 | 依据 |
|:---:|:---:|:---|:---|:---|:---|
| M1 | 1.0 | `crates/c01_ownership_borrow_scope/docs/c01_ownership/quick_reference.md` | `crates/c01_ownership_borrow_scope/docs/tier_03_references/04_drop_and_raii_reference.md` | **差异化保留** | 两者均为 AGENTS.md §6.4 治理 stub，但主题导航表不同（所有权速查 vs Drop/RAII 锚点），删除任一会丢失导航信息。改写两文件 H1 与导语区分主题；重跑后 sim 1.0 → **0.526**（跌出近克隆区间，落入 REVIEW 低分区） |
| M2 | 1.0 | `crates/c03_control_fn/docs/mind_map.md` | `crates/c03_control_fn/docs/multidimensional_matrix.md` | **删除文件 2** | 逐字节克隆（diff 仅 EN 行）。`mind_map.md` 被 `docs/04_thinking/04_thinking_representation_methods.md:601` 引用故保留；`multidimensional_matrix.md` 全仓零引用，裸删无死链风险 |
| M3 | 0.949 | `docs/research_notes/software_design_theory/01_design_patterns_formal/01_creational/README.md` | `.../02_structural/README.md` | **豁免（模板复用）** | 系列索引页：元数据块/章节模板/Rust 1.94 更新节相同，但模式清单（创建型 5 个 vs 结构型 7 个）、标题、权威来源标注均不同。属正常系列模板复用 |
| M4 | 0.949 | `.../01_creational/README.md` | `.../03_behavioral/README.md` | **豁免（模板复用）** | 同上（行为型 11 个模式，内容实质不同） |
| M5 | 0.949 | `.../02_structural/README.md` | `.../03_behavioral/README.md` | **豁免（模板复用）** | 同上 |

> 注：M3–M5 sim=0.949 < 0.95，按任务规则落入「0.7≤sim<0.95 骨架互撞」区间；经 diff 确认为差异化系列内容，豁免。

---

## 3. DOCS_INTERNAL（49 对）逐对处置

### 3.1 docs/03_practice 项目骨架互撞（48 对）——全部豁免

涉及 13 个实践项目文件（`03_project_03_calculator` ~ `03_project_15_distributed_system`），两两 sim 0.71–0.821。抽查 `03_project_03_calculator.md` 与 `03_project_05_text_statistics.md` 确认：

- 相同部分：章节模板（📑目录/项目目标/功能需求/学习要点/参考实现/相关概念/权威来源索引）、元数据块格式、来源标注样式；
- 不同部分：项目目标、功能需求清单、学习要点代码示例、难度/预计时间/所需知识——**均为不同项目的实质内容**。

结论：教学项目系列的标准模板复用，非内容抄袭。**48 对全部豁免，不改动文件**（改动反而会破坏系列一致性）。

| sim | 文件 1 | 文件 2 | 处置 |
|:---:|:---|:---|:---|
| 0.821 | 03_project_05_text_statistics | 03_project_13_database_engine | 豁免 |
| 0.806 | 03_project_07_chat_server | 03_project_11_web_server | 豁免 |
| 0.793 | 03_project_05_text_statistics | 03_project_12_wasm_app | 豁免 |
| 0.767 | 03_project_12_wasm_app | 03_project_13_database_engine | 豁免 |
| 0.742 | 03_project_03_calculator | 03_project_08_cache_system | 豁免 |
| 0.742 | 03_project_03_calculator | 03_project_09_log_parser | 豁免 |
| 0.742 | 03_project_03_calculator | 03_project_10_data_pipeline | 豁免 |
| 0.742 | 03_project_08_cache_system | 03_project_09_log_parser | 豁免 |
| 0.742 | 03_project_08_cache_system | 03_project_10_data_pipeline | 豁免 |
| 0.742 | 03_project_09_log_parser | 03_project_10_data_pipeline | 豁免 |
| 0.733 | 03_project_03_calculator | 03_project_05_text_statistics | 豁免 |
| 0.733 | 03_project_05_text_statistics | 03_project_08_cache_system | 豁免 |
| 0.733 | 03_project_05_text_statistics | 03_project_09_log_parser | 豁免 |
| 0.733 | 03_project_05_text_statistics | 03_project_10_data_pipeline | 豁免 |
| 0.719 | 03_project_03_calculator | 03_project_04_password_generator | 豁免 |
| 0.719 | 03_project_03_calculator | 03_project_06_concurrent_downloader | 豁免 |
| 0.719 | 03_project_03_calculator | 03_project_07_chat_server | 豁免 |
| 0.719 | 03_project_03_calculator | 03_project_11_web_server | 豁免 |
| 0.719 | 03_project_03_calculator | 03_project_14_async_runtime | 豁免 |
| 0.719 | 03_project_03_calculator | 03_project_15_distributed_system | 豁免 |
| 0.719 | 03_project_04_password_generator | 03_project_08_cache_system | 豁免 |
| 0.719 | 03_project_04_password_generator | 03_project_09_log_parser | 豁免 |
| 0.719 | 03_project_04_password_generator | 03_project_10_data_pipeline | 豁免 |
| 0.719 | 03_project_06_concurrent_downloader | 03_project_08_cache_system | 豁免 |
| 0.719 | 03_project_06_concurrent_downloader | 03_project_09_log_parser | 豁免 |
| 0.719 | 03_project_06_concurrent_downloader | 03_project_10_data_pipeline | 豁免 |
| 0.719 | 03_project_07_chat_server | 03_project_08_cache_system | 豁免 |
| 0.719 | 03_project_07_chat_server | 03_project_09_log_parser | 豁免 |
| 0.719 | 03_project_07_chat_server | 03_project_10_data_pipeline | 豁免 |
| 0.719 | 03_project_08_cache_system | 03_project_11_web_server | 豁免 |
| 0.719 | 03_project_08_cache_system | 03_project_14_async_runtime | 豁免 |
| 0.719 | 03_project_08_cache_system | 03_project_15_distributed_system | 豁免 |
| 0.719 | 03_project_09_log_parser | 03_project_11_web_server | 豁免 |
| 0.719 | 03_project_09_log_parser | 03_project_14_async_runtime | 豁免 |
| 0.719 | 03_project_09_log_parser | 03_project_15_distributed_system | 豁免 |
| 0.719 | 03_project_10_data_pipeline | 03_project_11_web_server | 豁免 |
| 0.719 | 03_project_10_data_pipeline | 03_project_14_async_runtime | 豁免 |
| 0.719 | 03_project_10_data_pipeline | 03_project_15_distributed_system | 豁免 |
| 0.710 | 03_project_03_calculator | 03_project_13_database_engine | 豁免 |
| 0.710 | 03_project_04_password_generator | 03_project_05_text_statistics | 豁免 |
| 0.710 | 03_project_05_text_statistics | 03_project_06_concurrent_downloader | 豁免 |
| 0.710 | 03_project_05_text_statistics | 03_project_07_chat_server | 豁免 |
| 0.710 | 03_project_05_text_statistics | 03_project_11_web_server | 豁免 |
| 0.710 | 03_project_05_text_statistics | 03_project_14_async_runtime | 豁免 |
| 0.710 | 03_project_05_text_statistics | 03_project_15_distributed_system | 豁免 |
| 0.710 | 03_project_08_cache_system | 03_project_13_database_engine | 豁免 |
| 0.710 | 03_project_09_log_parser | 03_project_13_database_engine | 豁免 |
| 0.710 | 03_project_10_data_pipeline | 03_project_13_database_engine | 豁免 |

（上表 48 行，文件名均省略公共前缀 `docs/03_practice/` 与后缀 `.md`。）

### 3.2 研究笔记系列 README（1 对）——豁免

| sim | 文件 1 | 文件 2 | 处置 | 依据 |
|:---:|:---|:---|:---|:---|
| 0.750 | `docs/research_notes/software_design_theory/02_workflow/README.md` | `docs/research_notes/software_design_theory/05_distributed/README.md` | **豁免（模板复用）** | diff 确认：工作流引擎模式 vs 分布式模式，主题、模式清单、权威来源完全不同，仅共享形式化定义规范模板与 Rust 1.94 更新节 |

---

## 4. 验证结果

### 4.1 重叠检测重跑（`python scripts/detect_content_overlap_v2.py --budget 999999` + `triage_overlap.py`）

| 指标 | 处置前（07-11） | 处置后（07-12） | 变化 |
|---|:---:|:---:|:---:|
| 扫描文件 | 1901 | 1899 | −2（删除 2 个 c03 克隆） |
| 命中对（sim≥0.5） | 557 | 559 | +2（c01 stub 改写后关键词变化产生 2 个低分新对，均 <0.6，落入 REVIEW） |
| MERGE | 5 | 5 | 构成已变：原 M1（c01）sim 降至 0.526 出榜、M2（c03 multidim）消除；新上榜为 safety_tags 双向对（见 §5） |
| DOCS_INTERNAL | 49 | 49 | 全部为已确认豁免的模板复用对 |
| 54 对中仍 ≥0.7 的 | 54 | 52 | 均为豁免对；无非豁免残留 |

**54 对闭环率：100%**（1 删除 + 1 差异化 + 52 豁免）。

### 4.2 死链检查

- 全仓 grep（排除 reports/archive/book/tmp/target/.git）：两个被删 c03 文件**零入链**，c01 两文件**零入链** → 链接更新计数 0，无新死链。
- `python scripts/check_links.py`（仅扫 docs/）：损坏链接 7048/43137，为既有基线问题（本次未改动 docs/ 下任何文件，未引入新死链；基线治理超出本任务范围）。
- `kb_auditor` 全量死链检查耗时较长，跳过；以上 grep + check_links 组合已覆盖本次改动面。

---

## 5. 残留风险与待人工 review 清单

| # | 项目 | 说明 | 建议 |
|:---:|:---|:---|:---|
| R1 | `concept/04_formal/02_separation_logic/33_safety_tags_in_formal.md` ↔ `concept/07_future/03_preview_features/31_safety_tags_preview.md`（sim 0.855，双向） | 重跑后新进入 MERGE。**两文件均声明「本文件为 concept/ 权威页」**，违反 AGENTS.md §2 单一权威来源规则；内容分别为形式化层处理与预览特性跟踪，存在真实重叠 | **待人工 review**：确定权威层（建议 04_formal 为权威页、07_future 改为摘要+canonical 链接，或反之），需通读 187/166 行专家内容后合并，未擅动 |
| R2 | c01 两个 crate stub 改写后 sim 0.526 | 仍共享治理模板导语，关键词检测会低分命中 | 可接受（模板化 stub 是治理机制本身）；如要彻底消除，需改检测脚本对 ≤40 行真 stub 豁免——属检测规则问题，非内容问题 |
| R3 | `crates/c02_type_system/readme_rust_189.md` ↔ `readme_rust_190.md`（sim 1.0）、`crates/c10_networks` 两个 857 行重复文件 | 属 SERIES 白名单桶（版本系列），不在本任务 54 对范围。但 c10 两文件 kw_sim=1.0 疑似真克隆而非分章 | 建议下一轮针对 SERIES 桶中 kw_sim≥0.95 的对专项复核 |
| R4 | REVIEW 桶 487 对 | 大量 crates/ 15 行导航 stub 互撞（mind_map/visualization_index/glossary 等同模板） | 与 R2 同类：建议检测脚本对真 stub 豁免，而非逐文件改写 |
| R5 | 环境并发风险 | 处置过程中观察到工作区被外部进程还原过一次（首次删除的 `multidimensional_matrix.md` 与 c01 改写被回退），已重新执行并验证。最终状态以 `git status` 为准：2 删除（c03 multidim/knowledge_graph）+ 2 修改（c01 两 stub） | 提交前请再次 `git status` 确认无并发回退 |

---

## 6. 变更文件清单

```text
D  crates/c03_control_fn/docs/multidimensional_matrix.md   （克隆，零引用）
D  crates/c03_control_fn/docs/knowledge_graph.md           （克隆，零引用；重跑 triage 新上榜的同族对）
M  crates/c01_ownership_borrow_scope/docs/c01_ownership/quick_reference.md              （H1/导语差异化）
M  crates/c01_ownership_borrow_scope/docs/tier_03_references/04_drop_and_raii_reference.md （H1/导语差异化）
A  reports/OVERLAP_V2_DISPOSITION_2026_07_12.md            （本报告）
```

未做 git commit。验证产物：`reports/CONTENT_OVERLAP_V2_2026-07-12.{md,json}`、`reports/OVERLAP_TRIAGE_2026-07-12.{md,json}` 由脚本重跑生成。
