# 全面质量审计与改进计划（2026-07-09）

> **触发原因**：用户反馈当前内容存在大量不完整、不完善之处，需全面递归梳理。
> **审计范围**：`concept/`、`crates/`、`knowledge/`、`docs/`、`reports/`、`.kimi/` 计划文件
> **状态**：已完成初轮量化扫描，待用户确认后分阶段治理

---

## 一、量化发现

### 1.1 概念页（concept/）质量缺口

| 指标 | 数量 | 说明 |
|---|---|---|
| `concept/` 文件总数 | ~508 | 含 archive |
| 行数 < 100 的页面 | **78** | 其中大量为本次 crates/docs 整治或 P2-Q3 新建/迁移的薄页 |
| 行数 < 50 的页面 | **16** | 多为占位/索引/重定向页，需补全或归档 |
| 含 `待补充` 标记 | **~70** | 多数为文件末尾 TODO 列表，部分为真实内容缺口 |
| 含 `未完成` 标记 | **~20** | 需优先补全 |
| 含 `WIP` 标记 | **4** | 异步闭包、eBPF、Cranelift、Rust Effect System 等 |
| 缺失 EN/Summary | **1** | `concept/00_meta/trpl_3rd_ed_mapping.md` |
| EN 标题含中文 | **1** | `concept/archive/rust_vs_cpp_formal_system_vs_mechanism_engineering_core_arguments_index.md` |
| 真实 `LINK_PLACEHOLDER` | **0** | 历史问题已基本解决（仅报告/检查清单中保留文字说明） |

### 1.2 重点关注薄页（本次新增/迁移）

以下页面在 crates/docs 整治或 P2-Q3 中创建/迁移，但内容较薄，需二次 enrich：

- **进程 IPC 系列**（`concept/03_advanced/02_process_ipc/`）：06~10 号页均 <100 行
- **Cargo 系列**（`concept/06_ecosystem/01_cargo/`）：80~86 号页均 <100 行
- **设计模式系列**：`82_engineering_and_production_patterns.md`、`84_design_patterns_glossary.md`
- **算法系列**：`79_cutting_edge_algorithms.md`、`80_formal_algorithm_theory.md`
- **元层索引**：`knowledge_topology/` 下多个 24 行图谱页
- **形式化/并发**：`22_cross_platform_concurrency.md`、`53_generics_compiler_behavior.md`

### 1.3 标记为“未完成”的核心文件

| 文件 | 主题 |
|---|---|
| `concept/01_foundation/11_quizzes/26_quiz_modules_testing.md` | 测试模块测验 |
| `concept/02_intermediate/06_macros_and_metaprogramming/13_dsl_and_embedding.md` | DSL 与嵌入 |
| `concept/03_advanced/00_concurrency/16_lock_free.md` | 无锁编程 |
| `concept/03_advanced/00_concurrency/21_quiz_concurrency_async.md` | 并发异步测验 |
| `concept/03_advanced/01_async/24_async_closures.md` | 异步闭包 |
| `concept/03_advanced/01_async/26_async_patterns.md` | 异步模式 |
| `concept/03_advanced/01_async/39_future_and_executor_mechanisms.md` | Future/Executor 机制 |
| `concept/04_formal/03_operational_semantics/15_hoare_logic.md` | Hoare 逻辑 |
| `concept/06_ecosystem/03_design_patterns/34_idioms_spectrum.md` | 惯用法谱系 |
| `concept/06_ecosystem/03_design_patterns/84_design_patterns_glossary.md` | 设计模式术语表 |
| `concept/07_future/03_preview_features/20_borrowsanitizer_preview.md` | BorrowSanitizer |
| `concept/07_future/03_preview_features/38_cranelift_backend_preview.md` | Cranelift Backend |
| `concept/07_future/04_research_and_experimental/03_evolution.md` | Rust 演进 |
| `concept/07_future/04_research_and_experimental/29_ebpf_rust.md` | eBPF |
| `concept/07_future/05_roadmaps/24_roadmap.md` | Roadmap |

### 1.4 未完成的计划/任务

| 来源 | 未完成任务 | 优先级 |
|---|---|---|
| `.kimi/FOLLOW_UP_PLAN_2026_07_09.md` | 阶段 C1 i18n 工具落地 | 高 |
| `.kimi/FOLLOW_UP_PLAN_2026_07_09.md` | 阶段 C2 外部失效链接修复 | 高 |
| `.kimi/FOLLOW_UP_PLAN_2026_07_09.md` | 阶段 C3 Brown inventory i18n | 中 |
| `.kimi/SUSTAINABLE_IMPROVEMENT_PLAN_2026_06_28_CONFIRMED.md` | 第四阶段 I3：治理 506 条外部失效链接 | 高 |
| `.kimi/SUSTAINABLE_IMPROVEMENT_PLAN_2026_06_28_CONFIRMED.md` | 第四阶段 I4：cargo-vet 持续审计 | 中 |
| `.kimi/SUSTAINABLE_IMPROVEMENT_PLAN_2026_06_28_CONFIRMED.md` | 第四阶段 I5：自动化版本管理仪表盘 | 低 |
| `.kimi/Q4_EXTERNAL_LINK_FIX_PLAN_2026_07_09.md` | 外部链接修复专项行动 | 高 |

### 1.5 代码/可验证示例缺口

- `crates/c03_control_fn/src/kani_examples.rs` 与 `crates/c04_generic/src/kani_examples.rs`：已通过编译检查，但本地无 Kani 环境，未实际运行证明。
- `crates/c17_resolver_v3_public_demo/`：`public = true` 在 stable 上仅解析语法、忽略语义，完整语义验证需 nightly。
- 多处 `#[cfg(kani)]` / `cfg(nightly)` 示例未在 CI 中实际执行。

---

## 二、改进策略

### 2.1 原则

1. **先元数据、再内容**：先解决 EN/Summary、标题、占位符问题，再补正文。
2. **先权威页、再周边**：优先 enrich `concept/` 权威页，再处理 `knowledge/` / `docs/` 摘要。
3. **先薄页、再未完成**：先给薄页增加结构化内容（定义、对比、示例、反例），再处理明确标记“未完成”的页面。
4. **质量门禁不变**：每项修改后跑通 `kb_auditor.py`、`detect_content_overlap.py`、`cargo check/test/clippy`。

### 2.2 阶段划分

#### 阶段 Q1：元数据急救（1~2 天）

| 编号 | 任务 | 产出 |
|---|---|---|
| Q1-1 | 修复所有缺失/不合格的 EN/Summary | 0 缺失 |
| Q1-2 | 标准化中文 EN 标题 | 0 中文 EN 标题 |
| Q1-3 | 清理或归档 concept/ 中无实质内容的 stub/重定向页 | 决策清单 |
| Q1-4 | 统一检查 `concept/SUMMARY.md` 中所有链接有效性 | 0 死链 |

#### 阶段 Q2：薄页 enrichment（1~2 周）

| 编号 | 任务 | 目标 |
|---|---|---|
| Q2-1 | 进程 IPC 系列 5 个薄页补全 | 每个 ≥200 行，含定义、对比表、示例、最佳实践 |
| Q2-2 | Cargo 系列 7 个薄页补全 | 每个 ≥150 行，含命令示例、配置说明 |
| Q2-3 | 设计模式/算法/形式化/并发薄页补全 | 每个 ≥150 行 |
| Q2-4 | 元层 `knowledge_topology/` 24 行图谱页补全或合并 | 形成可读的拓扑说明 |

#### 阶段 Q3：明确“未完成”页面补全（1~2 周）

按优先级处理 §1.3 中 15 个标记“未完成”的核心文件。

#### 阶段 Q4：外部链接与 i18n（2~4 周）

| 编号 | 任务 | 来源 |
|---|---|---|
| Q4-1 | 外部失效链接修复 | `Q4_EXTERNAL_LINK_FIX_PLAN_2026_07_09.md` |
| Q4-2 | Brown inventory i18n 补全 | `FOLLOW_UP_PLAN_2026_07_09.md` C3 |
| Q4-3 | i18n 自动化工具落地 | `FOLLOW_UP_PLAN_2026_07_09.md` C1 |

#### 阶段 Q5：可验证示例与 CI（持续）

| 编号 | 任务 | 说明 |
|---|---|---|
| Q5-1 | 在 CI  nightly 矩阵中运行 Kani 示例 | 需安装 Kani |
| Q5-2 | resolver v3 `public=true` 完整语义验证 | 需 nightly `-Zpublic-dependency` |
| Q5-3 | 建立每周自动质量报告 | 基于 `kb_auditor.py` + `detect_content_overlap.py` |

---

## 三、待确认问题

1. **是否同意上述阶段划分与优先级？**
2. **是否立即启动阶段 Q1（元数据急救）？**
3. **阶段 Q2 中优先补全哪个系列？** 候选：A. 进程 IPC；B. Cargo；C. 设计模式/算法；D. 全部并行推进
4. **外部链接修复（Q4-1）是否提前到 Q2 之前？** 506 条失效链接是显式技术债，可能优先级更高。

---

*确认后，我将按阶段推进并持续汇报。*
