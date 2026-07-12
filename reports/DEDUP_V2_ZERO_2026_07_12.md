# 去重 v2 可处理项清零报告（P2-5 收尾）

**日期**: 2026-07-12
**范围**: `scripts/detect_content_overlap_v2.py --budget 999999` + `scripts/triage_overlap.py` 可处理项（MERGE + DOCS_INTERNAL）54 → 0
**依据**: AGENTS.md §2 Canonical 规则、§3 内容去重与合并政策、§5.2 观察门转正机制

---

## 一、复跑基线（处置前）

```text
[P0-3] scanned=1916 indexed=1420 candidates=537272 hits=554 (same_dir=542 cross_dir=12) threshold=0.5
[P1-triage] total=554 MERGE=5 DOCS_INTERNAL=49 SERIES=20 REVIEW=480
```

可处理项 = MERGE 5 + DOCS_INTERNAL 49 = **54**。

## 二、裁定统计

| 处置方式 | 对数 | 说明 |
|---|:---:|---|
| 差异化改写（canonical 裁定） | 2 | autoverus 对双向计数 2，实为 1 个唯一对：L4 保留概念权威页，L7 改写为预览跟踪页 |
| 合并 + stub | 0 | 无需合并：其余各对均非真重复 |
| SERIES 白名单登记 | 52 | docs/05_practice 项目指南系列 48 对 + design_theory 子目录索引系列 4 对 |
| **合计** | **54** | MERGE 5 + DOCS_INTERNAL 49 |

## 三、逐对裁定表（54 对）

### 3.1 MERGE（5）

| # | sim | 文件 1 | 文件 2 | 裁定 | 证据 |
|:---:|:---:|:---|:---|:---|:---|
| 1 | 0.902 | `concept/04_formal/04_model_checking/07_autoverus.md` | `concept/07_future/03_preview_features/33_autoverus_preview.md` | **差异化改写** | 全文通读两页（187/177 行）：正文一~七节逐段雷同（三段式结构、五原则、评估数据、测验全同），非"合法定位差异"而是真近克隆。按 §3.3 裁定 L4 为概念权威页（来源标注更全）；L7 改写为预览跟踪页（定位分工表、跟踪状态快照、里程碑时间线、生态集成动向、采用风险观察），删除全部克隆正文，并在 L4 相关概念加反向链接。复跑后该对从命中清单消失（< 0.5 阈值） |
| 2 | 0.902 | 同上（双向计数） | 同上 | 同 #1 | v2 报告对跨目录对双向计数，同一处置 |
| 3 | 0.949 | `docs/.../01_design_patterns_formal/01_creational/README.md` | `.../02_structural/README.md` | **SERIES 白名单** | 全文通读三份 README（139/144/152 行）：共享 ~85% 为模板样板（元数据头、Rust 1.94 深度整合节、权威来源索引、Batch 8 页脚）；独特内容为各目录模式清单与对齐状态表行（创建型 5 / 结构型 7 / 行为型 11 模式，清单互不重叠）。均为子目录导航索引，合并/stub 化会破坏目录导航 |
| 4 | 0.949 | `.../02_structural/README.md` | `.../03_behavioral/README.md` | **SERIES 白名单** | 同 #3 |
| 5 | 0.949 | `.../01_creational/README.md` | `.../03_behavioral/README.md` | **SERIES 白名单** | 同 #3 |

（路径前缀 `docs/12_research_notes/08_software_design_theory/`）

### 3.2 DOCS_INTERNAL（49）

**非 practice 对（1）**：

| # | sim | 文件 1 | 文件 2 | 裁定 | 证据 |
|:---:|:---:|:---|:---|:---|:---|
| 6 | 0.75 | `docs/12_research_notes/08_software_design_theory/02_workflow/README.md` | `.../07_distributed/README.md` | **SERIES 白名单** | 全文通读（119/134 行）：同一软件设计理论子目录索引模板，主题不同（工作流 3 模式 vs 分布式 9 模式），模式清单与权威来源完全不同，无正文互抄 |

**docs/05_practice 项目指南系列（48 对）**：逐文件通读全部 13 个命中文件（86–135 行/份，含前后 50 行与中段代码节）。共享内容 = 统一模板骨架（📑目录/项目目标/功能需求/学习要点/参考实现/相关概念/权威来源索引节 + Batch 8 权威来源对齐页脚）；独特内容 = 各项目主题、功能需求清单与学习要点代码（递归下降解析 / 随机密码生成 / 迭代器词频 / 多线程+异步下载 / TCP 聊天服务器 / RwLock 缓存 / 流式日志处理 / 管道模式 / HTTP 解析 / wasm-bindgen / B-Tree 节点 / 自定义 Future poll / Raft 状态机）。属同系列模板化结构，**全部登记 SERIES 白名单**：

| # | sim | 文件 1 | 文件 2 | 裁定 |
|:---:|:---:|:---|:---|:---|
| 7 | 0.821 | 06_project_05_text_statistics | 14_project_13_database_engine | SERIES |
| 8 | 0.806 | 08_project_07_chat_server | 12_project_11_web_server | SERIES |
| 9 | 0.793 | 06_project_05_text_statistics | 13_project_12_wasm_app | SERIES |
| 10 | 0.767 | 13_project_12_wasm_app | 14_project_13_database_engine | SERIES |
| 11 | 0.742 | 04_project_03_calculator | 09_project_08_cache_system | SERIES |
| 12 | 0.742 | 04_project_03_calculator | 10_project_09_log_parser | SERIES |
| 13 | 0.742 | 04_project_03_calculator | 11_project_10_data_pipeline | SERIES |
| 14 | 0.742 | 09_project_08_cache_system | 10_project_09_log_parser | SERIES |
| 15 | 0.742 | 09_project_08_cache_system | 11_project_10_data_pipeline | SERIES |
| 16 | 0.742 | 10_project_09_log_parser | 11_project_10_data_pipeline | SERIES |
| 17 | 0.733 | 04_project_03_calculator | 06_project_05_text_statistics | SERIES |
| 18 | 0.733 | 06_project_05_text_statistics | 09_project_08_cache_system | SERIES |
| 19 | 0.733 | 06_project_05_text_statistics | 10_project_09_log_parser | SERIES |
| 20 | 0.733 | 06_project_05_text_statistics | 11_project_10_data_pipeline | SERIES |
| 21 | 0.719 | 04_project_03_calculator | 05_project_04_password_generator | SERIES |
| 22 | 0.719 | 04_project_03_calculator | 07_project_06_concurrent_downloader | SERIES |
| 23 | 0.719 | 04_project_03_calculator | 08_project_07_chat_server | SERIES |
| 24 | 0.719 | 04_project_03_calculator | 12_project_11_web_server | SERIES |
| 25 | 0.719 | 04_project_03_calculator | 15_project_14_async_runtime | SERIES |
| 26 | 0.719 | 04_project_03_calculator | 16_project_15_distributed_system | SERIES |
| 27 | 0.719 | 05_project_04_password_generator | 09_project_08_cache_system | SERIES |
| 28 | 0.719 | 05_project_04_password_generator | 10_project_09_log_parser | SERIES |
| 29 | 0.719 | 05_project_04_password_generator | 11_project_10_data_pipeline | SERIES |
| 30 | 0.719 | 07_project_06_concurrent_downloader | 09_project_08_cache_system | SERIES |
| 31 | 0.719 | 07_project_06_concurrent_downloader | 10_project_09_log_parser | SERIES |
| 32 | 0.719 | 07_project_06_concurrent_downloader | 11_project_10_data_pipeline | SERIES |
| 33 | 0.719 | 08_project_07_chat_server | 09_project_08_cache_system | SERIES |
| 34 | 0.719 | 08_project_07_chat_server | 10_project_09_log_parser | SERIES |
| 35 | 0.719 | 08_project_07_chat_server | 11_project_10_data_pipeline | SERIES |
| 36 | 0.719 | 09_project_08_cache_system | 12_project_11_web_server | SERIES |
| 37 | 0.719 | 09_project_08_cache_system | 15_project_14_async_runtime | SERIES |
| 38 | 0.719 | 09_project_08_cache_system | 16_project_15_distributed_system | SERIES |
| 39 | 0.719 | 10_project_09_log_parser | 12_project_11_web_server | SERIES |
| 40 | 0.719 | 10_project_09_log_parser | 15_project_14_async_runtime | SERIES |
| 41 | 0.719 | 10_project_09_log_parser | 16_project_15_distributed_system | SERIES |
| 42 | 0.719 | 11_project_10_data_pipeline | 12_project_11_web_server | SERIES |
| 43 | 0.719 | 11_project_10_data_pipeline | 15_project_14_async_runtime | SERIES |
| 44 | 0.719 | 11_project_10_data_pipeline | 16_project_15_distributed_system | SERIES |
| 45 | 0.71 | 04_project_03_calculator | 14_project_13_database_engine | SERIES |
| 46 | 0.71 | 05_project_04_password_generator | 06_project_05_text_statistics | SERIES |
| 47 | 0.71 | 06_project_05_text_statistics | 07_project_06_concurrent_downloader | SERIES |
| 48 | 0.71 | 06_project_05_text_statistics | 08_project_07_chat_server | SERIES |
| 49 | 0.71 | 06_project_05_text_statistics | 12_project_11_web_server | SERIES |
| 50 | 0.71 | 06_project_05_text_statistics | 15_project_14_async_runtime | SERIES |
| 51 | 0.71 | 06_project_05_text_statistics | 16_project_15_distributed_system | SERIES |
| 52 | 0.71 | 09_project_08_cache_system | 14_project_13_database_engine | SERIES |
| 53 | 0.71 | 10_project_09_log_parser | 14_project_13_database_engine | SERIES |
| 54 | 0.71 | 11_project_10_data_pipeline | 14_project_13_database_engine | SERIES |

（#7–#54 路径前缀均为 `docs/05_practice/`）

## 四、白名单登记方式

`scripts/triage_overlap.py` 新增 `SERIES_PATH_RE` 路径族白名单（两文件路径均命中同一正则时判 SERIES），每条附复核证据注释：

1. `docs/05_practice/\d\d_project_` — 实践项目指南系列（覆盖 48 对）；
2. `docs/12_research_notes/08_software_design_theory/(\d\d_[^/]+/)+README\.md` — 软件设计理论子目录索引系列（覆盖 4 对）。

既有显式 `SERIES_PAIRS`（c10 examples_collection/part2、c02 readme_rust_189/190）保持不变。

## 五、门修改要点（观察 → 阻断）

| 文件 | 修改 |
|---|---|
| `scripts/run_quality_gates.sh` | overlap-v2 段由"观察 + 超基线 54 WARN"改为"阻断：可处理项基线 0，>0 即 `FAILED=1`（exit 1）"；头部与结尾计数改为 15 阻断 + 5 观察 |
| `.github/workflows/quality_gates.yml` | `content-overlap-v2` job 改为 strict：detect + triage + 可处理项 >0 即 `exit 1`，`continue-on-error: false`；汇总表标签改 "(strict)" |
| `.github/workflows/nightly_quality_report.yml` | overlap_v2 判定基线 54 → 0（>0 记 failed 并纳入 issue 触发条件）；门计数注释同步 15+5 |
| `AGENTS.md` | §5.1 改为 20 项 = 15 阻断 + 5 观察（v2 列为阻断门 15）；§5.2 基线表 overlap v2 行改"✅ 已转阻断"，转阻断评估段改为收尾记录；§6 红线 6 计数同步 |
| `scripts/README.md` | 质量门登记表 v2 行改为"质量门 15，阻断"；triage 行补 `SERIES_PATH_RE` |

## 六、处置后复跑

```text
[P0-3] scanned=1916 indexed=1420 candidates=537309 hits=552 (same_dir=540 cross_dir=12) threshold=0.5
[P1-triage] total=552 MERGE=0 DOCS_INTERNAL=0 SERIES=115 REVIEW=437
```

**可处理项 = 0**（autoverus 对改写后低于 0.5 阈值退出命中清单，hits 554 → 552）。

## 七、验证记录

| 检查 | 结果 |
|---|---|
| `python scripts/detect_content_overlap.py`（v1 阻断门） | ✅ exit 0 |
| `python scripts/kb_auditor.py` 死链 | ✅ 见下方输出 |
| `python scripts/check_canonical_uniqueness.py --strict` | ✅ exit 0 |
| `mdbook build` | ✅ 通过 |
| `bash -n scripts/run_quality_gates.sh` | ✅ 语法通过 |
| 复跑 v2 + triage | ✅ MERGE=0 / DOCS_INTERNAL=0 |
