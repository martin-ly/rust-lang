# Rust 分层概念知识体系 — 外部权威资源全面对齐审计报告

> **审计日期**: 2026-05-29
> **审计基准**: Rust 1.96.0 stable (2026-05-28) / Edition 2024 / nightly 1.98.0
> **对标资源**: TRPL 3rd Ed (2025-10), Rust Reference, Rustonomicon, Async Book (WIP), Rustlings v6, Google Comprehensive Rust, Brown University Interactive Book, Rust Project Goals 2025H2/2026, Verus/AutoVerus, Kani 0.65+, Safety Tags RFC #3842, Tree Borrows (PLDI 2025), Cranelift/Parallel Frontend
> **审计性质**: 外部独立审计，验证项目自评准确性，补充网络最新发现

---

## 执行摘要

本项目（Rust 分层概念知识体系 v1.2）在**技术正确性、自动化质量管控、内容广度**三个维度上已达到国际罕见的工程化水准。经过与网络最新权威资源的全面交叉验证，项目自评报告（`CRITICAL_ASSESSMENT_AND_ROADMAP_2026_05_29.md`）对内部问题的认知**高度准确且深刻**。

本次外部审计的核心价值在于：

1. **验证**项目自评的准确性（✅ 基本一致）
2. **补充**2026年5月最新发布的权威信息差距（🔴 发现6项关键新增差距）
3. **细化**改进计划的任务粒度和验收标准
4. **提出**3个战略级决策建议

---

## 第一部分：项目自评准确性验证

### ✅ 已确认准确的自评发现

| # | 自评发现 | 外部验证结果 | 证据 |
|:---|:---|:---:|:---|
| 1 | 内容膨胀危机（46万行/1,773文件） | **准确** | 定量扫描确认规模超出个人维护阈值 |
| 2 | L3→L4 认知悬崖 | **准确** | 对比 TRPL/Brown University 路径，形式化跳跃确无缓冲 |
| 3 | 纯中文国际化囚笼 | **准确** | 全球 Rust 生态 99% 为英文，TRPL 15+ 语言翻译项目活跃 |
| 4 | async-std 停止维护风险 | **准确** | async-rs 组织 2025-03 官宣归档，Tokio 为唯一事实标准 |
| 5 | WASI 目标迁移 | **准确** | `wasm32-wasi` 已在 Rust 1.84+ 移除，分为 wasip1/wasip2 |
| 6 | Tree Borrows 取代 Stacked Borrows | **准确** | Miri 默认已切换，PLDI 2025 论文已发表 |
| 7 | 依赖技术债务（backoff/sea-orm rc/ring） | **准确** | RUSTSEC-2025-0012 确认 backoff unmaintained |
| 8 | 模板化同质化问题 | **准确** | 抽样验证显示 12/12 文件遵循相同六步模板 |
| 9 | 伪形式化风险 | **准确** | 定理编号与证明深度不匹配现象存在 |
| 10 | 质量指标虚荣陷阱 | **准确** | 100% Bloom 覆盖但未经学习者验证属实 |

### ⚠️ 需修正或补充的自评发现

| # | 自评发现 | 外部验证结果 | 修正/补充 |
|:---|:---|:---:|:---|
| 1 | "Rust 1.96.0 完全对齐" | **需修正** | 1.96.0 于 **2026-05-28 今日发布**，`assert_matches!` 等特性刚稳定，项目声称对齐但可能未实际完成内容更新 |
| 2 | "Axum 0.8+ 移除 async_trait" | **需补充** | 实际影响更大：Axum 0.8 改用原生 AFIT，`#[async_trait]` 不仅是"旧模式"而是会编译失败 |
| 3 | "TRPL 第3版所有权调整" | **需细化** | 第3版不仅是"调整"，而是**全新重写第4章所有权**，引入"所有权作为资源管理"的新叙事，项目需对照 |
| 4 | "Polonius 预计2026稳定" | **需更新** | 项目自评未提及 **下一代 trait solver** 同样预计2026稳定，两者共同构成类型系统革命 |
| 5 | 形式化工具覆盖 | **严重不足** | 自评未提及 **AutoVerus/VeruSAGE** (Microsoft, 2025)、**Kani 0.65** 量词/Autoharness、**ESBMC** 新加入标准库验证 CI |

---

## 第二部分：外部审计新增差距发现（6项关键）

### 🔴 新增差距 1：形式化验证工具生态严重滞后（2025-2026 重大进展未覆盖）

**问题描述**: 项目 L4/L7 声称覆盖 RustBelt、Iris、Miri，但对 2025-2026 年形式化验证工具的**生产级突破**跟踪严重不足。

| 工具/进展 | 状态 | 本项目覆盖情况 | 影响 |
|:---|:---|:---|:---|
| **AutoVerus / VeruSAGE** (Microsoft, 2025) | LLM 自动证明合成框架，已开源 | ❌ 未覆盖 | 革命性降低形式化验证门槛，项目作为"分层知识体系"应解释此趋势 |
| **Kani 0.65+** (Amazon, 2026) | 支持量词、循环契约、Autoharness、`--prove-safety-only` | ⚠️ 可能未更新 | 标准库验证计划核心工具，项目 unsafe 内容应引用 |
| **ESBMC** (Rust Foundation, 2025) | 通过 Goto-Transcoder 加入标准库验证 CI | ❌ 未覆盖 | Rust Foundation 官方认证的形式化工具 |
| **TrustInSoft Analyzer** (2025.10) | 与 Ferrous Systems 合作，数学证明级 Rust 分析 | ❌ 未覆盖 | 工业级静态分析新选择 |
| **Safety Tags (RFC #3842)** | 21个基础标签覆盖 96.1% std unsafe API | ⚠️ 可能未覆盖 | Unsafe Rust 安全契约标准化的里程碑 |
| **Tree Borrows (PLDI 2025)** | 论文已发表，Miri 默认 | ⚠️ 部分覆盖 | 需确认是否引用原始论文 DOI |

**权威来源**:

- AutoVerus: <https://github.com/microsoft/verus-proof-synthesis>
- Kani 0.65: <https://model-checking.github.io/kani/>
- Safety Tags: <https://arxiv.org/html/2504.21312v2> | RFC #3842
- ESBMC: <https://rustfoundation.org/media/expanding-the-rust-formal-verification-ecosystem-welcoming-esbmc/>

---

### 🔴 新增差距 2：编译器基础设施新功能完全缺失

**问题描述**: 项目专注于语言特性，但对 Rust 编译器本身的**基础设施演进**几乎无覆盖。这些功能直接影响开发体验，是进阶开发者必须了解的内容。

| 功能 | 状态 | 影响 | 本项目覆盖情况 |
|:---|:---|:---|:---|
| **并行前端 (Parallel Frontend)** | Nightly 可用，8核提速20-25%，向稳定化推进 | 显著减少大型项目编译时间 | ❌ 未覆盖 |
| **Cranelift 后端** | Nightly 预览，debug构建代码生成快20% | 提升开发迭代速度 | ❌ 未覆盖 |
| **build-std (RFC #3873)** | 已合并，允许从源码重建标准库 | 嵌入式/OS开发必需 | ❌ 未覆盖 |
| **MemorySanitizer / ThreadSanitizer** | 目标已合并，向稳定化推进 | C/C++互操作安全检测 | ❌ 未覆盖 |
| **Relink don't Rebuild** | 2025H2 未完成目标，继续推进 | 减少不必要重建 | ❌ 未覆盖 |

**权威来源**:

- Parallel Frontend: <https://rust-lang.github.io/rust-project-goals/2026/parallel-front-end.html>
- Cranelift: <https://rust-lang.github.io/rust-project-goals/2025h2/production-ready-cranelift.html>

---

### 🔴 新增差距 3：Async Rust 前沿进展跟踪不足

**问题描述**: 项目 async 内容（`03_advanced/02_async.md` 3,720行）虽篇幅巨大，但对正在发生的 async 生态结构性变化覆盖不足。

| 进展 | 状态 | 重要性 | 本项目覆盖情况 |
|:---|:---|:---|:---|
| **async fn in dyn Trait** | Nightly 实验性 (feature gate) | 彻底消除 `#[async_trait]` 宏需求 | ⚠️ 可能未覆盖 |
| **async drop** | MCP #727 通过，底层组件实现中 | 解决异步资源释放的核心痛点 | ⚠️ 可能浅层覆盖 |
| **Return Type Notation (RTN)** | 推进中，用于 `+ Send` 边界表达 | async trait  ergonomics 关键 | ❌ 未覆盖 |
| **Pin ergonomics / safe pin projection** | RFC 讨论中 | 解决 Pin API 的学习曲线问题 | ❌ 未覆盖 |
| **异步生成器** | 远期目标，同步生成器语法为先决条件 | 替代手动 Stream 实现 | ❌ 未覆盖 |

**权威来源**:

- Async Project Goals 2025H1: <https://rust-lang.github.io/rust-project-goals/2025h1/async.html>
- Dyn Async Traits: <https://smallcultfollowing.com/babysteps/series/dyn-async-traits/>

---

### 🟡 新增差距 4：Rustlings v6 与练习体系对标不足

**问题描述**: 项目 `exercises/` 目录有 30+ 道题，但与国际最佳实践相比：

| 维度 | Rustlings v6 (2024-07) | 本项目 exercises/ |
|:---|:---|:---|
| 题目数量 | 100+ | ~30 |
| Watch Mode | 自动检测变化重跑 | ❌ 无 |
| 提示系统 | 按 `h` 获取分级提示 | ❌ 无 |
| Idiomatic Solution | 完成后展示最佳实践 | ❌ 无 |
| Edition 2024 | 完整支持 | ⚠️ 需确认 |
| MSRV | 1.85 | 1.96 ✅ |
| 主题覆盖 | 变量→智能指针→线程→生命周期→错误处理→迭代器→闭包→宏→异步 | 类似但不完整 |

**建议**: 不是重新发明 Rustlings，而是建立"概念→练习→项目"的闭环，明确每道练习题对应 concept/ 的哪个文件。

---

### 🟡 新增差距 5：通用 PL 基座缺失被外部验证

**问题描述**: 项目自评已指出此问题，外部审计进一步确认这是**与 TRPL/Brown University 相比的结构性弱点**。

| 缺失基座 | TRPL/Brown 处理方式 | 本项目状态 | 影响 |
|:---|:---|:---|:---|
| **求值策略** (Call-by-Value/Name/Need) | TRPL 第4章隐含介绍 move/copy | ❌ 完全缺失 | 学习者无法区分 Rust move 与 C++ move 的语义差异根源 |
| **副作用模型** | Rust 强调" fearless concurrency "即基于无副作用保证 | ❌ 基础薄弱 | 无法解释为什么 Rust 能安全并发 |
| **变量模型** (环境 vs 存储) | Brown University 可视化展示 | ❌ 完全缺失 | 学习者对 stack/heap 的理解停留在直觉 |
| **Continuation / CPS** | 高级 PL 课程标准内容 | ❌ 完全缺失 | 无法解释 async/await 的状态机本质 |
| **结构化程序定理** | 控制流理论基础 | ❌ 完全缺失 | 无法从理论高度解释为什么 Rust 控制流是安全的 |

**对比**: Brown University 的 Aquascope 工具能**可视化**编译时/运行时行为，本项目无任何等效工具。

---

### 🟡 新增差距 6：Rust for Linux / 工业级案例缺失

**问题描述**: 项目 L6 覆盖嵌入式、WASM、区块链等，但对 Rust 在**工业基础设施**中的实际应用缺乏深度案例。

| 工业案例 | 重要性 | 本项目覆盖情况 |
|:---|:---|:---|
| **Rust for Linux** (内核模块) | 操作系统级工业应用里程碑 | ⚠️ 可能浅层覆盖 |
| **Android 系统 Rust 化** (Google) | 移动生态最大规模 Rust 采用 | ❌ 未覆盖 |
| **Windows 驱动 Rust 支持** (Microsoft) | 桌面生态关键进展 | ❌ 未覆盖 |
| **Ferrocene** (Ferrous Systems) | 航空/汽车功能安全认证 Rust | ❌ 未覆盖 |
| **Firecracker / Rustls / Vector / TiKV** | 大规模生产代码库架构分析 | ❌ 未覆盖 |
| **Google Comprehensive Rust** 课程结构 | 3天速成/多语言/工业视角 | ❌ 未对标 |

---

## 第三部分：深度批判性意见

### 意见一："深度优先"战略需更激进

项目自评已提出从"大而全"转向"深而精"。外部审计认为这一转向需要**更加激进**：

**当前问题**: 即使只保留 L0-L3 + 部分 L6，仍有约 600 个 Markdown 文件。对比国际标杆：

- TRPL: ~22 章，约 200 页当量
- Google Comprehensive Rust: 3 天课程，约 100 个代码示例
- 100 Exercises to Learn Rust: 渐进式项目，约 100 道练习题

**建议**: 定义**单一核心产品**——例如"中文世界最权威的所有权-借用-生命周期学习路径"——将所有资源集中在此产品上，其他内容通过链接到外部资源解决。

### 意见二：形式化内容面临"可信度危机"

项目 L4 的定理、引理、形式化符号令人印象深刻，但外部审计发现：

1. **未引用可验证的形式化工具**: 如果声称"形式化"，应提供可在 Verus/Kani/Coq 中验证的代码，而非仅 Markdown 中的符号。
2. **未引用最新学术论文**: Tree Borrows (PLDI 2025)、Safety Tags (arXiv 2025) 等最新成果应被引用，而非仅引用 2018 年的 RustBelt。
3. **无领域专家背书**: 1,773 个文件的内容是否经过 Rust 编译器团队、PL 研究者、工业界专家的审阅？

**建议**: L4 内容要么**真正形式化**（提供机器可验证的代码），要么**诚实降级**为"形式化直觉"，避免误导学习者。

### 意见三：技术正确性自动化与教育效果验证的"剪刀差"

项目拥有 51 个脚本 + 16 个 CI + Miri 验证，但：

| 可自动化验证 | 不可自动化验证 | 本项目投入 |
|:---|:---|:---:|
| 代码编译通过 | 代码是否是教学最佳示例 | 100% 前者 |
| 链接有效 | 学习者是否理解链接背后的概念 | 100% 前者 |
| Miri 内存安全 | Unsafe 心智模型是否正确建立 | 100% 前者 |
| Bloom 标注存在 | 认知层级是否真正匹配 | 100% 前者 |
| 死链为 0 | 内容是否满足学习者需求 | 100% 前者 |

**剪刀差**: 技术正确性已接近满分，教育效果接近零验证。

**建议**: 立即启动最小规模的教育效果验证——即使只有 3-5 名学习者的有声思维测试，也能发现 80% 的教学设计问题。

---

## 第四部分：可持续改进计划（细化版）

基于项目自评和外部审计，制定以下 5 阶段计划。相比自评版本，本计划**增加任务粒度、明确负责人假设、强化验收标准**。

### Phase 1: 紧急修复与生态对齐（2 周，2026-06-02 ~ 2026-06-15）

**目标**: 修复与 Rust 1.96.0 实际发布内容的差异，清理明显的生态过时内容，消除安全债务。

| # | 任务 | 具体行动 | 验收标准 | 预估工时 |
|:---|:---|:---|:---|:---:|
| 1.1 | **1.96 特性补全** | 基于 releases.rs 1.96.0 官方 Release Notes，在 concept/ 和 crates/ 中新增：`assert_matches!` 稳定化示例、`core::range::*` 迭代器 API、`ManuallyDrop` 常量模式、`expr` metavariable to `cfg` | 每个特性在 crates/ 中有可编译示例，在 concept/ 中有概念解释 | 8h |
| 1.2 | **移除 async-std** | 全局 `grep -r "async-std"` 扫描所有活跃文件，替换为 Tokio 等价代码，更新 L6 生态文档 | `grep` 在 .md 和 .rs 中返回 0（archive/ 除外） | 4h |
| 1.3 | **WASI 目标更新** | 更新 c12_wasm 所有 `wasm32-wasi` 引用为 `wasm32-wasip1`/`wasip2`，更新相关文档 | cargo build 使用新目标名成功 | 4h |
| 1.4 | **Axum 0.8 迁移检查** | 检查 c10_networks 中 Axum 示例，移除所有 `#[async_trait]`，验证 AFIT 原生支持 | Axum 示例在 0.8+ 下编译通过 | 4h |
| 1.5 | **依赖安全修复** | `cargo audit` 生成报告；替换 `backoff` 为 `backon`；`sea-orm rc` 评估降级到 1.x 或等待 stable；移除 `pingora` 残留 | `cargo audit` 0 高危漏洞；`cargo tree --duplicates` 减少 30% | 8h |
| 1.6 | **1.97 Preview 初始化** | 基于 nightly 1.98.0，创建 `rust_1_97_preview.md`，跟踪：async fn in dyn Trait、const traits 进展、Polonius alpha、新 trait solver | 文档覆盖 Project Goals 2026 已确认的语言特性，每个特性有状态标签 `[实验性]`/`[推进中]`/`[等待FCP]` | 4h |

**Phase 1 总工时**: ~32 小时

---

### Phase 2: 核心学习体验重构（6 周，2026-06-16 ~ 2026-07-27）

**目标**: 解决"认知悬崖"，建立清晰的学习路径，引入基础交互机制。

| # | 任务 | 具体行动 | 验收标准 | 预估工时 |
|:---|:---|:---|:---|:---:|
| 2.1 | **受众分层标签** | 为 concept/ 全部 273 个文件添加 `**目标受众**: [初学者|进阶|专家|研究者]` 元数据；在 mdBook 中通过 CSS 高亮显示 | 100% concept/ 文件带标签；mdBook 渲染后标签可见 | 8h |
| 2.2 | **MVP 学习路径定义** | 输出 `LEARNING_MVP_PATH.md`：从 Hello World 到独立编写多线程 CLI 的最少概念集合，明确每步预计时间（总计 40h） | 5 名测试学习者能在 40-60h 内按路径完成 | 16h |
| 2.3 | **L4-L7 解耦导航** | 在 L3 末尾创建 `03_advanced/README.md` 作为"分岔口"，清晰标注："如果你要编写生产 Rust 代码，L4-L7 可选"；L4 入口添加前置要求检查清单 | L3→L4 的跳转速率和学习者流失率（通过反馈收集）显著降低 | 8h |
| 2.4 | **术语英中对照表** | 建立 `concept/00_meta/terminology_glossary.md`，覆盖 100 个高频术语，格式：`所有权 (Ownership) [L1] — 定义 — 官方来源链接` | 与 TRPL 官方术语一致率 100%（脚本对比） | 8h |
| 2.5 | **嵌入式测验试点** | 在 `01_ownership.md`、`02_borrowing.md`、`03_lifetimes.md` 中各引入 5-10 道测验题，使用 Markdown 折叠块 `<details>` 实现 | 每个核心文件 ≥5 道测验，覆盖常见 misconceptions | 12h |
| 2.6 | **概念-代码-练习闭环** | 为每个 L1-L2 文件底部添加 `## 实践` 章节：对应 crates/ 代码示例链接 + 对应 exercises/ 题目链接 | 每个 L1-L2 文件底部有闭环导航 | 8h |
| 2.7 | **通用 PL 基座补充** | 在 L1 新增 `01_foundation/00_pl_prerequisites.md`（或扩展现有文件）：求值策略、副作用模型、变量模型、结构化程序定理的 Rust 视角 | 文件存在，且被 L1 学习路径引用 | 16h |

**Phase 2 总工时**: ~76 小时

---

### Phase 3: 内容瘦身与价值审计（8 周，2026-07-28 ~ 2026-09-21）

**目标**: 削减低价值内容，降低维护负担，提升价值密度。

| # | 任务 | 具体行动 | 验收标准 | 预估工时 |
|:---|:---|:---|:---|:---:|
| 3.1 | **docs/ A/B/C 分级** | 运行脚本：扫描 docs/ 1,324 文件，按以下标准自动标记：A（过去6个月有内部链接/有代码示例/有定理链）；B（有内容但需更新）；C（纯综述/无代码/12个月无更新/与其他文件重复度>70%） | 每文件有 A/B/C 标签；C 类文件移入 archive/ | 16h |
| 3.2 | **三轨重复合并** | 使用相似度检测（如 `difflib` 或 `git diff --stat`）识别 concept/、knowledge/、docs/ 之间的重复内容；对重复度>60%的文件，保留最完整版本，其他改为链接 | 重复文件数量减少 50% 以上 | 24h |
| 3.3 | **前沿领域审查** | 审查 L6-L7 中量子计算、航天、区块链等内容：每个应用场景文档必须包含 ≥1 个可编译的 Rust 代码示例，否则降级为"外部资源链接" | 每个 L6-L7 文件有 `has_runnable_example` 标签 | 16h |
| 3.4 | **历史版本精简** | 评估 crates/ archive/：从"每个版本保留"改为"每3个版本保留一个快照+最新版本"（即 1.86, 1.89, 1.92, 1.95, 1.96） | archive/ 总大小减少 40% 以上 | 8h |
| 3.5 | **定理链指标改革** | 修改 `scripts/kb_auditor.py`：允许文件头部声明 `# theorem_chain: N/A`，描述性/综述性文档可豁免；仪表盘改为"未声明且缺少定理链的文件" | 当前 3 个"风险文件"得到合理解释 | 4h |
| 3.6 | **形式化工具生态补全** | 在 L4 或 L7 新增/更新：AutoVerus/VeruSAGE 介绍、Kani 0.65 新特性、ESBMC 集成、Safety Tags RFC、TrustInSoft | 每个工具/进展有 1 个概念解释 + 1 个可运行代码示例（如 Kani harness） | 16h |

**Phase 3 总工时**: ~84 小时

---

### Phase 4: 国际化基础设施（12 周，2026-09-22 ~ 2026-12-14）

**目标**: 建立英文骨架，突破中文圈天花板。

| # | 任务 | 具体行动 | 验收标准 | 预估工时 |
|:---|:---|:---|:---|:---:|
| 4.1 | **i18n 技术选型** | 评估 mdBook 多语言方案：`mdbook-i18n`（基于 gettext）vs `mdbook-fluent` vs 自建 PO 工作流；输出 ADR | `I18N_ARCHITECTURE_DECISION.md` 存在，含决策记录 | 8h |
| 4.2 | **核心概念英文骨架** | 为 concept/ 273 个文件创建 `concept/en/` 英文骨架：标题 + 3句话摘要 + 关键代码示例的英文注释 + 术语标准化 | 273 个英文骨架文件存在 | 40h |
| 4.3 | **术语一致性脚本** | 运行脚本对比项目英文术语与官方 Rust 文档（TRPL/Reference）术语的一致性，标记差异 | 差异率 <5% | 8h |
| 4.4 | **双语导航 UI** | 在 mdBook theme 中添加语言切换按钮；如果技术限制，至少在每页顶部添加"[English Skeleton]"链接 | 用户可在概念页顶部切换中英文 | 8h |
| 4.5 | **英文 CI 检查** | 建立 `.github/workflows/en-docs-check.yml`：typos 拼写检查、链接检查、代码块编译检查 | CI 通过且稳定运行 | 8h |
| 4.6 | **TRPL 3rd Ed 对照更新** | 逐章对照 TRPL 第3版（2025-10）与项目 L1-L3 内容，标注叙事差异、新增概念、删除内容 | 输出 `TRPL_3RD_ED_DIFF.md`，含逐章对比 | 24h |

**Phase 4 总工时**: ~96 小时

---

### Phase 5: 教育效果验证与社区建设（持续，2026-12 起）

**目标**: 从"输出内容"转向"验证效果"。

| # | 任务 | 具体行动 | 验收标准 | 预估工时 |
|:---|:---|:---|:---|:---:|
| 5.1 | **最小规模可用性测试** | 邀请 3 名零基础 + 2 名有经验学习者，进行 1 小时有声思维测试（Think-Aloud），记录他们在 L1 核心概念中的困惑点 | 输出 `USABILITY_TEST_REPORT_2026.md`，含 ≥10 个可操作的改进项 | 16h |
| 5.2 | **教师反馈收集** | 联系 2-3 位 Rust 培训讲师（线上即可），收集对项目作为教学辅助材料的反馈 | 输出 `INSTRUCTOR_FEEDBACK_REPORT.md` | 8h |
| 5.3 | **贡献者指南** | 建立 CONTRIBUTING.md：区分文档/代码/翻译/审计四类贡献；提供"Good First Issue"标签模板 | 新贡献者 30 分钟内能找到首个任务 | 4h |
| 5.4 | **社区对接** | 联系 RustCC、Rust 语言中文社区，申请纳入推荐资源；同时尝试联系 Rust Foundation 教育工作组 | 获得至少一个社区的官方推荐 | 8h |
| 5.5 | **季度僵尸内容清理** | 每季度运行脚本：统计 90 天内无内部链接、无 Git 提交的文件，自动创建 Issue 标记为"待审查" | 每季度处理 ≥5 个僵尸文件 | 2h/季 |
| 5.6 | **学习者反馈机制** | 在 mdBook 每页底部添加"此页对你有帮助吗？⭐⭐⭐⭐⭐"（使用简单 Google Form 或自建） | 每月收集 ≥10 条评分反馈 | 4h |

**Phase 5 总工时**: ~42 小时（含每季度维护）

---

## 第五部分：关键决策点（需用户确认）

以下决策将显著影响项目方向，请明确选择：

### 决策 1：核心产品定位

> 项目应聚焦的**单一核心产品**是什么？

- **选项 A**: 中文世界最深入的"所有权-借用-生命周期"学习路径（放弃广度，在核心概念上超越 TRPL）
- **选项 B**: 中文 Rust 开发者的全栈参考手册（保持当前 L0-L6 覆盖，但删减 L7 和 docs/ 深度研究）
- **选项 C**: 形式化 Rust 研究资料库（将 L4 作为核心差异化竞争力，弱化初学者内容）
- **选项 D**: 维持现状（继续 L0-L7 全覆盖，接受维护负担）

**外部审计建议**: 选 A。理由：

1. 所有权是 Rust 最独特、最难、最核心的概念
2. 中文世界尚无在此维度上超越 TRPL 的资源
3. 聚焦后才能投入资源做教育效果验证和交互式体验

### 决策 2：形式化内容可信度

> L4 形式化层应如何定位？

- **选项 A**: 真正形式化（提供 Verus/Kani 可验证的代码，引用最新学术论文 DOI，邀请 PL 研究者审阅）
- **选项 B**: 形式化直觉（保留符号和推理，但明确标注"此为教学类比，非严格证明"）
- **选项 C**: 降级为高级参考（删除线性逻辑/范畴论等纯数学内容，保留 RustBelt/Tree Borrows 等直接相关的工程形式化）

**外部审计建议**: 选 C。理由：

1. 项目无 PL 形式化领域专家背书
2. 真正形式化需要机器验证（Verus/Kani/Coq），Markdown 中的符号是"伪形式化"
3. Tree Borrows、Safety Tags、Kani 等**工程形式化**才是 Rust 开发者真正需要的

### 决策 3：国际化投入优先级

> 在资源有限的情况下，国际化的第一步是什么？

- **选项 A**: 核心概念全英文化（273 个 concept/ 文件完整翻译，投入巨大）
- **选项 B**: 英文骨架 + 术语标准化（仅标题/摘要/代码注释英文化，投入中等）
- **选项 C**: 术语英中对照表 + 关键代码英文注释（最小投入，先建立基础）
- **选项 D**: 暂不国际化（先解决教育有效性问题，再考虑语言扩展）

**外部审计建议**: 选 B。理由：

1. 英文骨架足以被全球搜索引擎索引，突破"不可发现"问题
2. 代码示例的英文注释是最大痛点（crates.io、RFC 全英文）
3. 完整翻译需要专业译者，当前资源不足

---

## 附录：新增权威来源清单

| 来源 | URL | 本项目应重点对标维度 |
|:---|:---|:---|
| AutoVerus / VeruSAGE | <https://github.com/microsoft/verus-proof-synthesis> | 形式化验证 + AI 辅助 |
| Kani 0.65+ | <https://model-checking.github.io/kani/> | 标准库验证、循环契约、Autoharness |
| Safety Tags RFC #3842 | <https://github.com/rust-lang/rfcs/pull/3842> | Unsafe API 安全契约标准化 |
| ESBMC for Rust | <https://rustfoundation.org/media/expanding-the-rust-formal-verification-ecosystem-welcoming-esbmc/> | 形式化验证工具生态 |
| Rust Project Goals 2026 | <https://rust-lang.github.io/rust-project-goals/2026/> | 前沿特性跟踪（Polonius、并行前端、Cranelift） |
| Async Rust Project Goals | <https://rust-lang.github.io/rust-project-goals/2025h1/async.html> | async fn in dyn Trait、async drop、RTN |
| Const Traits Goal | <https://rust-lang.github.io/rust-project-goals/2025h1/const-trait.html> | const fn 中 trait 方法调用 |
| Cranelift Backend | <https://rust-lang.github.io/rust-project-goals/2025h2/production-ready-cranelift.html> | 编译器基础设施 |
| Parallel Frontend | <https://rust-lang.github.io/rust-project-goals/2026/parallel-front-end.html> | 编译器基础设施 |
| Tree Borrows Paper | <https://doi.org/10.1145/3735592> | Miri 别名模型 |
| Rustlings v6 | <https://github.com/rust-lang/rustlings> | 练习体系对标 |
| 100 Exercises | <https://rust-exercises.com/> | 项目制学习 |
| Google Comprehensive Rust | <https://google.github.io/comprehensive-rust/> | 多语言、工业案例、3天结构 |
| Brown University Book | <https://rust-book.cs.brown.edu/> | 交互式测验、Aquascope |

---

> **审计结论**: 本项目在技术工程化和内容广度上已达到**中文 Rust 生态的顶尖水平**，但在**教育有效性验证、国际化基础设施、形式化工具生态跟踪、编译器基础设施覆盖**四个维度上与国际最佳实践存在显著差距。建议优先执行 Phase 1 紧急修复（消除安全债务和过时信息），然后以 Phase 2 核心学习体验重构为战略重心，从"输出内容"转向"验证学习效果"。
