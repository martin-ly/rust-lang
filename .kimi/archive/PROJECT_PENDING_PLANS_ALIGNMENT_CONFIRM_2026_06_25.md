# 项目未完成计划与任务全面梳理（权威网络对齐确认稿）

> **生成时间**：2026-06-25
> **主控文件**：`.kimi/EXECUTION_CHECKLIST_2026_06_22.md`（4 周周期：2026-06-23 ~ 2026-07-20）
> **唯一硬截止**：**2026-07-09** Rust 1.97.0 发布日执行
> **权威来源校验日期**：2026-06-25

---

## 1. 执行摘要

- **当前项目状态**：4 周执行清单中 Week 1 / Week 2 / Week 4 已全部完成；**Week 3 仅剩 7 项 Rust 1.97 发布日任务**，受上游硬截止约束，无法提前完成。
- **工作区健康度**：
  - `cargo check --workspace` ✅ 通过
  - `cargo audit --no-fetch` ✅ 0 安全漏洞
  - `docs/` 损坏链接 ✅ **0**（已从 1,917 修复至 0）
  - `docs/` C 类价值问题 ✅ **107**（已从 643 降至 107）
- **权威网络对齐后唯一不可变日期**：Rust 1.97.0 stable 将于 **2026-07-09** 发布（[Rust Forge](https://forge.rust-lang.org/)）。
- **下一步建议**：在 07-09 之前，优先完成不受上游阻塞的 **权威来源事实修正**（async closures / Edition 2024 / `&raw const`）和 **Rust 1.96 覆盖缺口回填**。

---

## 2. 未完成计划总览（按优先级）

### P0 — 硬截止 2026-07-09

| 编号 | 任务 | 来源文件 | 依赖/风险 | 权威来源 |
|---|---|---|---|---|
| A3.1 | 执行 Rust 1.97 发布日清单 | `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md` | 上游实际发布 | [Rust Forge](https://forge.rust-lang.org/)：Stable 1.96 / Beta 1.97 (Jul 9) / Nightly 1.98 (Aug 20) |
| A3.2 | `rust-toolchain.toml` → `channel = "1.97.0"` | `rust-toolchain.toml` | A3.1 | 同上 |
| A3.3 | 激活 `crates/c08_algorithms/src/rust_197_features.rs` 占位 | `crates/c08_algorithms/src/rust_197_features.rs` | `VecDeque::retain_back` 可能推迟 | [PR #151973](https://github.com/rust-lang/rust/pull/151973)：已 FCP 完成、disposition-merge，但仍有小概率推迟 |
| A3.4 | `cargo test --workspace` | 全 workspace | A3.2/A3.3 | Rust 1.97.0 stable |
| A3.5 | 刷新 `concept/07_future/rust_1_97_preview.md` 并迁移到稳定文档目录 | `concept/07_future/rust_1_97_preview.md` | A3.1 | 待发布日 Release Notes |
| A3.6 | 完善 `CHANGELOG.md [3.1.0]` | `CHANGELOG.md` | A3.1/A3.3 | 同上 |
| A3.7 | 更新术语表中 1.97 术语状态 | `concept/00_meta/terminology_glossary.md` | 上游实际稳定内容 | 同上 |

### P1 — 建议在 07-09 前完成（无上游阻塞）

| 主题 | 当前问题 | 权威事实 | 建议动作 | 权威来源 |
|---|---|---|---|---|
| **async closures** | `concept/03_advanced/24_async_closures.md:378` 仍标注“需要 nightly feature gate”；多处 preview 标记未更新 | **Rust 1.85.0（2025-02-20）已稳定** async closures / `AsyncFn*` traits | 全局修正为 `1.85.0 stable`，更新示例与状态标记 | [Announcing Rust 1.85.0](https://blog.rust-lang.org/2025/02/20/Rust-1.85.0/)、[RFC 3668](https://github.com/rust-lang/rfcs/pull/3668) |
| **Rust 2024 Edition** | `knowledge/06_ecosystem/02_edition_2024.md` 等文件版本号/状态可能滞后；`gen` 关键字与 `gen {}` blocks 易混淆 | **Rust 2024 Edition 在 1.85.0 stable**；`gen` 是 2024 Edition 保留关键字；`gen {}` / `gen fn` 仍为 nightly，需 `#![feature(gen_blocks)]` | 修正 Edition 版本号为 `1.85.0+`；明确区分“关键字保留”与“gen blocks 不稳定” | [Edition Guide — Rust 2024](https://doc.rust-lang.org/edition-guide/rust-2024/index.html)、[RFC 3513](https://rust-lang.github.io/rfcs/3513-gen-blocks.html)、[tracking issue #117078](https://github.com/rust-lang/rust/issues/117078) |
| **`&raw const` / `&raw mut`** | 项目中存在非官方术语 `&const` | 官方语法为 `&raw const T` / `&raw mut T`，**1.82.0 stable** 已稳定 | 全局搜索替换 `&const` → `&raw const`，统一术语 | [Rust 1.82.0 release notes](https://blog.rust-lang.org/2024/10/17/Rust-1.82.0/)、[Rust Reference — Raw References](https://doc.rust-lang.org/reference/expressions.html) |
| **Rust 1.96 覆盖缺口** | rustdoc 1.96 改进、`NonZero` 范围迭代、`AssertUnwindSafe From`、s390x inline asm、“valid for read/write”契约等尚未完整覆盖 | Rust 1.96.0（2026-05-28）已稳定上述特性 | 补文档/练习，标注稳定版本 | [Rust 1.96.0 release notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/)、[releases.rs 1.96](https://releases.rs/docs/1.96.0/) |
| **内容去重收尾** | 8 组高相似文件未合并；C-class 元数据覆盖需继续推进 | 项目内部质量指标 | 合并剩余 ≥0.90 相似对；将 C-class 问题数从 107 继续压降 | `reports/C_CLASS_GOVERNANCE_PLAN_2026_06_09.md` |

### P2 — 07-09 之后推进

| 主题 | 关键未完成项 | 权威/参考来源 |
|---|---|---|
| **编译器/Cargo 深度内容** | rustc query system、new trait solver、MIR/codegen/LLVM、Cargo resolver v3 / public-private deps / build scripts / registries、Cranelift / parallel frontend / build-std | [rustc-dev-guide](https://rustc-dev-guide.rust-lang.org/)、[Cargo Book](https://doc.rust-lang.org/cargo/)、[Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/) |
| **形式化工具示例** | Kani 函数/循环合约可运行示例、Safety Tags / BorrowSanitizer / Tree Borrows / AutoVerus/Verus 概念页与代码示例交叉引用 | [Kani docs](https://model-checking.github.io/kani/)、[Verus docs](https://verus-lang.github.io/verus/)、[Tree Borrows paper](https://plv.mpi-sws.org/treerabs/)、[Safety Tags RFC #3842](https://github.com/rust-lang/rfcs/pull/3842) |
| **生态迁移** | Sea-ORM 2.0 stable 迁移、`async_trait` → AFIDT/dynosaur 跟踪、WASI 目标确认 | [SeaORM releases](https://github.com/SeaQL/sea-orm/releases)、[AFIDT tracking](https://github.com/rust-lang/rust/issues/133882)、[WASI target update blog](https://blog.rust-lang.org/2024/04/09/updates-to-rusts-wasi-targets/) |
| **TRPL 3rd / Brown Book 对齐** | 所有权/借用文档引用 Brown 研究、`async.md` 标注 TRPL Ch17、逐章对照审计 | [TRPL 3rd Ed (No Starch)](https://nostarch.com/rust-programming-language-3e)、[Brown Rust Book](https://rust-book.cs.brown.edu/) |

### P3 — 长期 / 需外部条件

| 主题 | 关键未完成项 | 备注 |
|---|---|---|
| **Effect System / const traits** | `const_trait_impl_preview.md` 深度重写（`~const` 方向已废弃）；Pre-pre RFC 独立章节 | 上游语法未最终确定，建议保持跟踪 |
| **Safety-Critical 工作组落地** | 负责人/预算/认证体系/培训试点 | 当前为规划文档阶段 |
| **国际化与社区验证** | 可用性测试、教师反馈、社区背书、英文版 LEARNING_MVP_PATH | 建议纳入 2026 Q4 |

---

## 3. 权威网络对齐关键结论

| 项目内容 | 权威结论 | 来源 |
|---|---|---|
| **Rust 1.97.0 发布日** | **2026-07-09**（Beta 周期结束） | [Rust Forge — Current Release Versions](https://forge.rust-lang.org/) |
| **`VecDeque::truncate_front`** | PR #151973 已 FCP 完成，disposition-merge，**大概率进入 1.97** | [GitHub PR #151973](https://github.com/rust-lang/rust/pull/151973)、[releases.rs](https://releases.rs/) |
| **`VecDeque::retain_back`** | 同 PR #151973，但历史上曾有从 nightly 移除记录，**存在推迟到 1.98 的小概率风险** | 同上 |
| **async closures / `AsyncFn*`** | **1.85.0 stable** | [Rust 1.85.0 blog](https://blog.rust-lang.org/2025/02/20/Rust-1.85.0/) |
| **Rust 2024 Edition** | **1.85.0 stable** | [Edition Guide](https://doc.rust-lang.org/edition-guide/rust-2024/index.html) |
| **`gen` 关键字保留** | **Rust 2024 Edition** | [RFC 3513](https://rust-lang.github.io/rfcs/3513-gen-blocks.html) |
| **`gen {}` / `gen fn` blocks** | 仍为 nightly，tracking issue #117078 | [tracking issue #117078](https://github.com/rust-lang/rust/issues/117078) |
| **`&raw const` / `&raw mut`** | **1.82.0 stable** | [Rust 1.82.0 blog](https://blog.rust-lang.org/2024/10/17/Rust-1.82.0/) |
| **trait upcasting** | **1.86.0 stable** | [Rust 1.86.0 blog](https://blog.rust-lang.org/2025/04/03/Rust-1.86.0/) |
| **`#[target_feature]` on safe functions** | **1.86.0 stable** | [Rust 1.86.0 blog](https://blog.rust-lang.org/2025/04/03/Rust-1.86.0/) |
| **`HashMap::get_disjoint_mut`** | **1.86.0 stable** | [Rust 1.86.0 blog](https://blog.rust-lang.org/2025/04/03/Rust-1.86.0/) |
| **`asm_goto` / inline asm label operands** | **1.87.0 stable** | [Rust 1.87.0 blog](https://blog.rust-lang.org/2025/05/15/Rust-1.87.0/) |
| **precise capturing `+ use<...>` in traits** | **1.87.0 stable** | [Rust 1.87.0 blog](https://blog.rust-lang.org/2025/05/15/Rust-1.87.0/) |
| **Sea-ORM 2.0 stable** | 截至 2026-06-25 仍未发布；最新稳定版 **1.1.20**，rc 最新 **2.0.0-rc.41** | [crates.io/sea-orm](https://crates.io/crates/sea-orm)、[GitHub releases](https://github.com/SeaQL/sea-orm/releases) |
| **async-std 状态** | 已停止维护（v1.13.1 起），推荐 smol/tokio | [crates.io/async-std](https://crates.io/crates/async-std)、[Fedora deprecation](https://fedoraproject.org/wiki/Changes/Deprecate_async-std) |
| **WASI 目标** | `wasm32-wasi` 已在 Rust 1.84 stable 移除；使用 `wasm32-wasip1` / `wasm32-wasip2` | [Rust WASI target update blog](https://blog.rust-lang.org/2024/04/09/updates-to-rusts-wasi-targets/) |

---

## 4. 主要风险与阻塞

| 风险 | 影响 | 缓解措施 |
|---|---|---|
| Rust 1.97.0 某特性未如期稳定（尤其是 `retain_back`） | A3.3 / A3.5 / A3.7 | 保留等效实现；在 `rust_197_features.rs`、`CHANGELOG.md`、`rust_1_97_preview.md` 中标注“推迟至 1.98” |
| `cargo audit` 网络不可用 | 依赖安全审计 | 已配置本地 advisory-db；使用 `--no-fetch` 兜底 |
| Sea-ORM 2.0 stable 继续延迟 | 生态迁移 | 继续跟踪 rc 版本；评估是否回退 1.x（当前 workspace 功能正常，暂不回退） |
| AFIDT / `dyn async Trait` 未 stable | `async_trait` 移除 | 文档侧标记为“实验性/跟踪中”，代码侧保持 `async_trait` |
| 多版 roadmap 口径不一致 | 执行混乱 | **已统一主控为 `.kimi/EXECUTION_CHECKLIST_2026_06_22.md`**；早期 `EXECUTION_PLAN_*` 已标记 `[历史参考]` |

---

## 5. 建议执行顺序

1. **本周内（2026-06-25 ~ 2026-07-02）** —— 不受上游阻塞：
   - [ ] 全局修正 async closures / Edition 2024 / `&raw const` 事实偏差。
   - [ ] 补充 Rust 1.96 覆盖缺口（`assert_matches!`、`core::range`、`NonZero` 范围迭代、`AssertUnwindSafe From`、s390x inline asm）。
   - [ ] 继续推进 C-class 元数据覆盖与剩余高相似文件合并。

2. **2026-07-09 发布日当天** —— 按 `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md` 执行 A3.x 系列。

3. **发布日后（2026-07-10 ~ 2026-07-20）**：
   - [ ] 回填 `CHANGELOG.md [3.1.0]` 实际条目。
   - [ ] 归档发布日清单。
   - [ ] 启动 Compiler/Cargo 深度内容、形式化工具示例、TRPL 3rd 对齐。

4. **2026 Q4**：
   - [ ] 国际化与社区验证（可用性测试、教师反馈、英文版路径）。
   - [ ] Safety-Critical 工作组落地评估。

---

## 6. 请你确认

1. **主控文件**：是否确认继续以 `.kimi/EXECUTION_CHECKLIST_2026_06_22.md` 为唯一执行主控？
2. **1.97 发布日策略**：若 `VecDeque::retain_back` 未进入 1.97.0，是否同意**保留等效实现并标注“推迟至 1.98”**，而不是删除占位？
3. **P1 权威事实修正**：是否同意我立即全局修正 async closures / Edition 2024 / `&raw const` 的事实偏差，并补充 Rust 1.96 覆盖缺口？
4. **内容瘦身**：是否同意在去重完成前，暂停大规模新增 `concept/` / `knowledge/` / `docs/` 内容，优先处理剩余高相似文件与 C-class 元数据？
5. **Sea-ORM / AFIDT 策略**：是否同意继续跟踪上游，代码侧保持现状，文档侧更新为“实验性/跟踪中”？
6. **输出形式**：是否需要我基于本确认稿生成一份**可执行的逐周排期表**（细化到文件/命令）？

---

*本文件为梳理与确认稿，未对项目文件做任何修改。待你确认后进入执行阶段。*
