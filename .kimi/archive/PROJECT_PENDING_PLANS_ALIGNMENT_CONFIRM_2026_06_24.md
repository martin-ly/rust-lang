# 项目未完成计划与任务梳理确认稿

> **生成时间**：2026-06-24
> **项目基线**：`rust-toolchain.toml` = nightly；workspace `edition = "2024"`；`rust-version = "1.96.0"`
> **主控文件**：`.kimi/EXECUTION_CHECKLIST_2026_06_22.md`（历史计划 `.kimi/EXECUTION_PLAN_CONFIRMED_2026_06_03.md` 已标记为 `[历史参考]`）
> **最近硬截止**：**2026-07-09 Rust 1.97.0 发布日**

---

## 1. 项目现状速览

- 当前处于 4 周执行周期（2026-06-23 ~ 2026-07-20）中期，核心里程碑是 **2026-07-09 Rust 1.97.0 发布日执行**。
- 大量前置治理（async-std/WASI 清理、来源占位符修复、重复文件合并、模块 8 国际化对齐）已在 6 月 22 日前部分完成。
- 未闭环事项集中在：**1.97 发布执行**、**权威来源事实修正**、**L3 可运行测验与学习闭环**、**内容去重/C-class 元数据**、**Compiler/Cargo 深度内容**、**形式化/安全关键示例**。
- 多个版本的 roadmap/检查表并存，存在口径不一致风险。

---

## 2. 未完成计划与任务总表

| 主题 | 关键未完成项 | 来源文件 | 目标/截止 | 权威网络对照 | 风险/备注 |
|---|---|---|---|---|---|
| **A. Rust 1.97 发布日执行** | 1) 执行 07-09 发布清单；2) `rust-toolchain.toml` 切到 `1.97.0`；3) 激活 `crates/c08_algorithms/src/rust_197_features.rs` 占位；4) 全 workspace `cargo test/clippy`；5) `rust_1_97_preview.md` 转正/迁移；6) 补充 1.97 特性练习；7) 更新 `CHANGELOG.md [3.1.0]` | `.kimi/EXECUTION_CHECKLIST_2026_06_22.md` A3/A4 `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md` `.kimi/plan_rust_1_97_stabilization.md` | **2026-07-09** / v3.1.0 | [releases.rs](https://releases.rs/)；[Rust Blog](https://blog.rust-lang.org/) | 上游特性可能推迟，需保留等效实现并标注状态 |
| **B. Rust 1.96 覆盖缺口** | rustdoc 1.96 改进文档；`NonZero` 范围迭代练习；`AssertUnwindSafe From` 练习；s390x inline asm；指针 "valid for read/write" 契约；target specs 内部变更 | `reports/RUST_1_96_FULL_AUDIT_2026_05_31.md` | 1.96.0+ | [Rust release notes](https://doc.rust-lang.org/beta/releases.html) | 项目版本号超前，需逐条核对实际稳定版本 |
| **C. 权威来源事实偏差修正** | 1) `content/emerging/async_closures.md` 改为 **1.85.0 stable**；2) `knowledge/06_ecosystem/02_edition_2024.md` 版本号 1.85.0+，区分 `gen` 关键字保留与 gen blocks nightly；3) `crates/c06_async/src/async_closures_preview.rs` 时间线；4) 全局 `&const` → `&raw const`；5) 统一稳定度标注模板 | `reports/COMPREHENSIVE_AUTHORITATIVE_ALIGNMENT_DIFF_2026_06_23.md` `reports/CONCEPT_00META_SOURCE_ALIGNMENT_2026_06_22.md` `reports/WEB_AUTHORITY_ALIGNMENT_UPDATE_2026_06_22.md` | v3.0 | [Rust 1.85 release](https://blog.rust-lang.org/2025/02/20/Rust-1.85.0.html)；[RFC 3668](https://github.com/rust-lang/rfcs/pull/3668)；[gen blocks tracking #117078](https://github.com/rust-lang/rust/issues/117078) | 同一 gap 在多处报告重复标注，需统一收口 |
| **D. 内容去重、清理与价值审计** | 1) 合并剩余 8 组高相似文件；2) C-class 元数据头 50% 覆盖；3) 完全重复文件移入 `archive/`；4) `docs/` 883 项问题修复；5) 更新 `CONTENT_OVERLAP_DETECTION` / `C_CLASS_GOVERNANCE_PLAN` | `.kimi/EXECUTION_CHECKLIST_2026_06_22.md` B3/B4 `reports/DUPLICATE_MERGE_PLAN_2026_06_21.md` `reports/C_CLASS_DIRECTORY_AUDIT_2026_06_22.md` `reports/DOCS_VALUE_AUDIT_2026_06_09.md` | 2026-07-20 | 项目内部质量指标 | 文件量大，人工审核耗时；去重前继续扩写会放大重复 |
| **E. L3 学习测验与练习闭环** | 1) 设计/实现 **24 个 L3 可运行测验**并接入 CI；2) `concept/01_foundation` + `02_intermediate` 至少各 5 篇补 `## 实践`；3) 术语表扩至 **150 术语**并双语标注；4) `LEARNING_MVP_PATH.md` 精化 | `.kimi/EXECUTION_CHECKLIST_2026_06_22.md` C1-C4 `.kimi/EXECUTION_PLAN_CONFIRMED_2026_06_03.md` Phase 2 | 2026-07-20 | [Brown Rust Book quizzes](https://rust-book.cs.brown.edu/)；[TRPL 3rd Ed](https://nostarch.com/rust-programming-language-3e) | 教育效果需真实学习者验证 |
| **F. TRPL 3rd / Brown Book 对齐** | 1) 所有权/借用文档引用 Brown 研究；2) `async.md` 标注 TRPL Ch17 对应；3) 修复 concept/ 旧版 TRPL 链接；4) 逐章对照审计 | `reports/TRPL_3RD_ED_BROWN_BOOK_ALIGNMENT_AUDIT_2026_06_19.md` `reports/BROWN_BOOK_OWNERSHIP_INVENTORY_MAPPING_2026_06_19.md` | 2026 Q4 | [TRPL 3rd Ed (No Starch)](https://nostarch.com/rust-programming-language-3e)；[Brown Rust Book](https://rust-book.cs.brown.edu/) | 注意版权/引用合规 |
| **G. 形式化与工程形式化工具** | 1) `crates/` 增加 **Kani** 函数/循环合约示例；2) Safety Tags / BorrowSanitizer / Tree Borrows / AutoVerus/Verus 概念页与可编译示例；3) Rust for Linux 案例更新；4) 形式化工具文档交叉引用 | `.kimi/EXECUTION_CHECKLIST_2026_06_22.md` D1-D4 `reports/COMPILER_CARGO_CONTENT_ROADMAP_2026_06_21.md` `docs/research_notes/10_comprehensive_systematic_review_and_100_percent_plan.md` | v3.0 | [Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/)；[Kani](https://model-checking.github.io/kani/)；[Verus](https://verus-lang.github.io/verus/) | 上游工具版本快速演进；负责人多为虚拟角色 |
| **H. Safety-Critical / 合规** | 1) 任命工作组负责人、首批 5 人培训、试点、预算；2) MC/DC Coverage、Safety-Critical Lints、FLS/MISRA 对齐；3) 教育培训与四级认证体系 | `knowledge/04_expert/safety_critical/06_roadmaps/03_sustainable_roadmap_and_plans.md` `docs/04_research/04_safety_critical_alignment_2026.md` | 2026+ | Rust Project Goals 2026 — Safety-Critical Rust；[Ferrocene](https://ferrocene.dev/) | 需要具体负责人/预算，当前为规划阶段 |
| **I. 编译器/Cargo/工具链深度内容** | 1) rustc query system / new trait solver 概念页；2) MIR/codegen/LLVM backend；3) Cargo resolver v3 / public-private deps / build scripts / registries；4) Cranelift / parallel frontend / build-std / Pin/RTN/Field Projections 跟踪 | `.kimi/EXECUTION_CHECKLIST_2026_06_22.md` E1-E4 `reports/COMPILER_CARGO_CONTENT_ROADMAP_2026_06_21.md` `concept/07_future/rust_1_98_preview.md` | 2026-07-20 | [rustc-dev-guide](https://rustc-dev-guide.rust-lang.org/)；[Cargo Book](https://doc.rust-lang.org/cargo/)；Rust Project Goals 2026 | 与 `rust_1_98_preview.md` 交叉引用需同步 |
| **J. Crates 文档/代码重组** | 1) C02 Phase5 整合；2) C04 4-Tier 体系 Tier 2-4 补全；3) C06 async 文档 6 阶段重组；4) C08 1.97 占位激活；5) C12 WASM Level 1-3 任务清单 | `crates/c02_type_system/docs/PHASE5_INTEGRATION_PLAN_2025_10_22.md` `crates/c04_generic/docs/C04_RESTRUCTURING_PLAN_2025_10_22.md` `crates/c06_async/docs/REORGANIZATION_PLAN.md` `crates/c12_wasm/docs/RUST_192_FEATURE_ROADMAP.md` | 1.92–1.97 | crate 官方文档；Rust release notes | 各 crate 内完成报告/思维导图/示例集大量重复 |
| **K. 生态迁移与依赖安全** | 1) async-std 文档层 7 个中优先级文件清理；2) `async_trait` → AFIDT/dynosaur；3) Sea-ORM 2.0 stable 迁移；4) WASI 目标迁移确认；5) cargo-vet / hickory-proto / rsa / heapless 漏洞跟踪 | `reports/ASYNC_STD_CLEANUP_INVENTORY_2026_06_22.md` `reports/WASI_TARGET_MIGRATION_INVENTORY_2026_06_22.md` `reports/SUPPLY_CHAIN_AUDIT_2026_06_22.md` `.kimi/EXECUTION_CHECKLIST_2026_06_22.md` A1/A2 | v3.0 / 持续 | [async-std deprecation](https://crates.io/crates/async-std)；[Rust WASI targets update](https://blog.rust-lang.org/2024/04/09/updates-to-rusts-wasi-targets/)；crates.io security advisories | 上游 crate 发布节奏不可控；`cargo audit` 仍需本地脚本兜底 |
| **L. 国际化与社区验证** | 1) 术语表 150 术语中英双语；2) TRPL 3rd 逐章对照；3) 3 名零基础 + 2 名有经验可用性测试；4) 教师反馈；5) 社区背书；6) `CONTRIBUTING.md` 更新 | `.kimi/EXECUTION_PLAN_CONFIRMED_2026_06_03.md` Phase 5 `.kimi/EXECUTION_CHECKLIST_2026_06_22.md` C4 | 2026 Q4 | TRPL 3rd Ed；Rust 中文社区 | i18n 策略存在漂移（纯中文 / 双语 / 英文骨架） |
| **M. Effect System 遗留** | 1) `const_trait_impl_preview.md` 深度重写（`~const` 已标注废弃方向）；2) Pre-pre RFC 社区讨论独立章节；3) Effect System 独立书籍章节（可选） | `.kimi/plan_effect_system_2026_06.md` | 后续 | Rust Project Goals 2026 — Const Traits | 上游语法未最终确定 |
| **N. 通用 PL 基座与语义空间** | 1) 变量模型、求值策略、副作用与纯度、控制流理论、数据抽象谱系；2) C/C++ ABI 与对象模型对比；3) 模式组合代数、算法-模式-工作流语义桥；4) RFC 跟踪系统、定理链分级 | `reports/SEMANTIC_SPACE_CRITICAL_AUDIT_2026_05_24.md` `reports/CONTENT_AUDIT_CRITICAL_REVIEW_2026_05_24.md` | v3.0 后 | PL 经典文献；[Rust Reference](https://doc.rust-lang.org/reference/) | 领域专家审阅；低优先级 |

---

## 3. 网络权威内容对齐结论

以下是与本项目关键任务对应的官方/权威来源，建议作为事实校验基线：

| 项目内容 | 权威来源 | 关键结论 |
|---|---|---|
| **async closures / AsyncFn traits** | [Rust 1.85.0 release notes](https://blog.rust-lang.org/2025/02/20/Rust-1.85.0.html)、[RFC 3668](https://github.com/rust-lang/rfcs/pull/3668) | **Rust 1.85.0 stable** 已稳定；不是 nightly/1.97 特性。项目中任何标注为 preview/nightly 的 async closures 文档/代码需更新。 |
| **Rust 2024 Edition** | [Rust 2024 Edition Guide](https://doc.rust-lang.org/edition-guide/rust-2024/index.html)、[Phoronix 1.85 报道](https://www.phoronix.com/news/Rust-1.85-Released) | **Rust 1.85.0** 随 2024 Edition 一起稳定。`edition = "2024"` 是 opt-in，与 2018/2021 可混用。 |
| **`gen` 关键字 vs `gen {}` blocks** | [RFC 3513](https://rust-lang.github.io/rfcs/3513-gen-blocks.html)、[tracking issue #117078](https://github.com/rust-lang/rust/issues/117078)、[Rust Unstable Book](https://doc.rust-lang.org/stable/unstable-book/language-features/gen-blocks.html) | 2024 Edition **保留 `gen` 关键字**；`gen {}` / `gen fn` 仍处于 **nightly/unstable**，需 `#![feature(gen_blocks)]`。项目中需明确区分二者。 |
| **trait upcasting** | [Rust 1.86.0 release notes](https://blog.rust-lang.org/2025/04/03/Rust-1.86.0/) | **Rust 1.86.0 stable** 已稳定。 |
| **`#[target_feature]` on safe functions** | [Rust 1.86.0 release notes](https://blog.rust-lang.org/2025/04/03/Rust-1.86.0/) | **Rust 1.86.0 stable** 已稳定 `target_feature_11`。 |
| **`get_disjoint_mut` / `HashMap::get_disjoint_mut`** | [Rust 1.86.0 release notes](https://blog.rust-lang.org/2025/04/03/Rust-1.86.0/) | **Rust 1.86.0 stable** 已稳定。 |
| **`asm_goto` / inline assembly label operands** | [Rust 1.87.0 release notes](https://blog.rust-lang.org/2025/05/15/Rust-1.87.0/)、[releases.rs 1.87](https://releases.rs/docs/1.87.0/) | **Rust 1.87.0 stable** 已稳定。 |
| **precise capturing `+ use<...>` in traits** | [Rust 1.87.0 release notes](https://blog.rust-lang.org/2025/05/15/Rust-1.87.0/) | **Rust 1.87.0 stable** 已扩展到 trait 定义中的返回位置 `impl Trait`。 |
| **let chains** | [Rust 1.88.0 release notes](https://doc.rust-lang.org/beta/releases.html)、[RFC 2497](https://github.com/rust-lang/rfcs/blob/master/text/2497-if-let-chains.md) | 在 2024 Edition 中稳定；随版本推进，需以官方 release notes 为准。 |
| **`&raw const` / `&raw mut`** | [Rust Reference — Raw References](https://doc.rust-lang.org/reference/expressions.html) | 官方语法为 `&raw const T` / `&raw mut T`，项目中 `&const` 写法需全局替换。 |
| **async-std 弃用** | [crates.io async-std](https://crates.io/crates/async-std)、[Fedora Deprecate async-std](https://fedoraproject.org/wiki/Changes/Deprecate_async-std)、[internals 讨论](https://internals.rust-lang.org/t/async-std-deprecation/23395) | **async-std 已停止维护**（v1.13.1 起），推荐迁移至 `smol` 或 `tokio`。 |
| **WASI 目标重命名** | [Rust Blog — Updates to Rust's WASI targets](https://blog.rust-lang.org/2024/04/09/updates-to-rusts-wasi-targets/) | `wasm32-wasi` 已在 **Rust 1.84 stable（2025-01-09）** 移除；应使用 `wasm32-wasip1`（WASI 0.1）和 `wasm32-wasip2`（WASI 0.2）。 |
| **TRPL 第 3 版** | [No Starch TRPL 3e](https://nostarch.com/rust-programming-language-3e)、[doc.rust-lang.org/book](https://doc.rust-lang.org/book/) | 2026-03 出版，基于 Rust 2024 Edition；新增第 17 章异步基础、Miri、Brown 所有权研究。 |
| **Brown University Rust Book** | [rust-book.cs.brown.edu](https://rust-book.cs.brown.edu/) | 交互式测验 + Aquascope 可视化；所有权章节与 TRPL 不同，可作为本项目 L3 测验设计参考。 |
| **Rust Project Goals 2026** | [rust-lang.github.io/rust-project-goals](https://rust-lang.github.io/rust-project-goals/) | 重点关注：BorrowSanitizer、Safety-Critical Rust、Rust for Linux、next-gen trait solver、const traits、Polonius、MC/DC coverage、FLS 发布节奏等。 |

---

## 4. 主要冲突与风险

1. **多版 roadmap 并行，口径不一致**
   - `EXECUTION_PLAN_2026_06_02.md`、`COMPREHENSIVE_ALIGNMENT_AND_EXECUTION_PLAN_2026_05_30.md`、`COMPREHENSIVE_CRITICAL_ANALYSIS_AND_ROADMAP_2026_06_03.md`、`EXECUTION_PLAN_CONFIRMED_2026_06_03.md`、`EXECUTION_CHECKLIST_2026_06_22.md` 同时存在。
   - **状态**：已以 `EXECUTION_CHECKLIST_2026_06_22.md` 为唯一执行主控；`EXECUTION_PLAN_2026_06_02.md`、`EXECUTION_PLAN_CONFIRMED_2026_05_29.md`、`EXECUTION_PLAN_CONFIRMED_2026_06_03.md` 已标记为 `[历史参考]`。

2. **周计划与 4 周检查表冲突**
   - `reports/EXECUTION_PLAN_2026_06_09_WEEK1_4.md`（06-09 ~ 07-07）与 `EXECUTION_CHECKLIST_2026_06_22.md`（06-23 ~ 07-20）时间范围不同。
   - 前者计划产出 `LEARNING_MVP_PATH_EN.md`，后者 i18n 策略为“中文为主 + 关键术语中英双语”。

3. **Knowledge 模块 8 统计数据冲突**
   - `reports/KNOWLEDGE_MODULE8_ALIGNMENT_2026_06_22.md` 称已补充 89 个文件；
   - 同日 `reports/WEB_AUTHORITY_ALIGNMENT_UPDATE_2026_06_22.md` 称 knowledge/ 核心文件仍有 **108 个缺少**模块 8。
   - 需统一统计口径。

4. **版本号领先于真实稳定版本**
   - 项目当前 MSRV 为 1.96.0，目标 1.97.0；但权威网络可验证的 stable 最新为 1.87–1.88（截至 2025 年中）。
   - 若 07-09 上游 1.97 实际内容未完全按预期落地，需有 **fallback 机制**（保留等效实现、更新状态）。

5. **形式化/安全关键负责人缺位**
   - 大量任务分配给“Rust Formal Methods Research Team”或“Rust 安全关键系统工作组”等虚拟角色，无具体个人/预算/时间表。

6. **内容重复未收敛前继续扩写**
   - `concept/`、`knowledge/`、`docs/` 三轨重复；`crates/` 内完成报告/思维导图/示例集彼此重复。
   - 在去重完成前继续扩写会进一步放大维护债务。

---

## 5. 建议优先级

| 优先级 | 任务 | 理由 |
|---|---|---|
| **P0** | **Rust 1.97 发布日执行** | 唯一硬截止在 2026-07-09，不可推迟 |
| **P0** | **权威来源事实修正**（async closures、Edition 2024、`gen`、`&raw const`） | 直接影响内容可信度，需在 1.97 前完成 |
| **P1** | **内容去重**（剩余 8 组高相似文件） | 避免扩写放大重复，应前置 |
| **P1** | **C-class 元数据头推进**（50% 覆盖） | v3.0 质量基线 |
| **P1** | **L3 可运行测验与 `## 实践` 章节** | 支撑学习闭环和教育效果验证 |
| **P2** | **Compiler/Cargo 深度概念页**、**形式化工具示例** | 支撑 L4 专家级内容 |
| **P3** | **通用 PL 基座**、**安全关键工作组落地**、**国际化社区验证** | 长期建设，可放 1.97 之后分批推进 |

---

## 6. 待你确认的问题

1. **主控文件**：✅ 已确认以 `.kimi/EXECUTION_CHECKLIST_2026_06_22.md` 为唯一执行主控；`EXECUTION_PLAN_*` 早期版本已标记为 `[历史参考]`。
2. **1.97 发布日**：若上游 Rust 1.97.0 某些特性未如预期稳定，是否同意保留等效实现并更新状态，而不是强行删除占位？是否需要我现在先跑一遍 `cargo test` / `cargo clippy` 预检？
3. **权威事实修正**：是否同意我立即按第 3 节权威来源修正 async closures / Edition 2024 / `gen` / `&raw const` 等事实偏差？
4. **去重优先**：是否同意在继续大规模新增内容前，优先完成剩余 8 组高相似文件合并和 C-class 元数据覆盖？
5. **输出形式**：是否需要我基于本确认稿生成一份**可执行的逐周排期**（到具体文件/负责人）？

---

*本文件为梳理确认稿，未对项目文件做任何修改，等待你确认后再进入执行阶段。*
