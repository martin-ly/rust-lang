# 项目未完成计划与任务全面梳理（2026-06-26 实际验证版）

> **生成时间**：2026-06-26
> **主控文件**：`.kimi/EXECUTION_CHECKLIST_2026_06_22.md`（4 周周期：2026-06-23 ~ 2026-07-20）
> **唯一硬截止**：**2026-07-09** Rust 1.97.0 发布日执行
> **权威来源校验日期**：2026-06-26
> **前置参考**：`.kimi/PROJECT_PENDING_PLANS_ALIGNMENT_CONFIRM_2026_06_25.md`、`.kimi/PROJECT_WEEKLY_SCHEDULE_2026_06_25.md`

---

## 1. 执行摘要

### 1.1 当前项目状态（经实际验证）

| 检查项 | 命令 | 结果 | 备注 |
|---|---|---|---|---|
| 编译 | `cargo check --workspace` | ✅ 通过（~11.6s） | 无错误 |
| 安全审计 | `cargo audit --no-fetch` | ✅ 0 安全漏洞 | `.cargo/audit.toml` 显式忽略 6 个 RUSTSEC 并记录 rationale |
| 文档价值审计 | `python scripts/docs_value_audit.py docs --days-old 90` | ✅ A=0 / B=0 / **C=0** | 扫描 232 个文件；C-class 已清零 |
| 链接健康 | `python scripts/check_links.py` | ✅ 损坏 0 | 总链接 91,806，有效 32,876，外部 58,921，仅锚点 27,730 |
| 工具链 | `rust-toolchain.toml` | `channel = "nightly"` | 注释说明使用 nightly 1.98.0，MSRV 1.96.0 stable |
| Workspace 版本 | 根 `Cargo.toml` | **未定义** | `[workspace.package]` 无 `version` 字段，各 crate 自行管理 |
| 1.97 占位代码 | `crates/c08_algorithms/src/rust_197_features.rs` | 存在，389 行 | 无 TODO/FIXME，已含等效实现与注释 |

### 1.2 与 06-25 报告的关键差异

| 指标 | `reports/PROJECT_COMPREHENSIVE_STATUS_2026_06_25.md` | 2026-06-26 实际验证 | 说明 |
|---|---|---|---|---|
| `docs/` C-class 问题数 | 228 | **0** | 06-25 之后又做了归档/修复，已清零 |
| 损坏链接数 | 1,917 | **0** | 链接检查脚本已修复或阈值策略调整 |
| `cargo audit` 忽略项 | 3 个 unmaintained + 3 个安全 advisory | 6 个 RUSTSEC 均在忽略列表 | 配置已统一 |

> 这意味着 **B 工作流（内容去重与质量基线）的量化目标已提前达成**，但长期维护规则（阶段 4）仍需落地。

### 1.3 权威网络对齐结论

- **Rust 1.97.0 stable 将于 2026-07-09 发布**（[Rust Forge](https://forge.rust-lang.org/)、[releases.rs](https://releases.rs/docs/1.97.0/) 一致确认）。
- **async closures / Rust 2024 Edition 已于 Rust 1.85.0（2025-02-20）stable**。
- **Rust 1.96.0（2026-05-28）已 stable**：`assert_matches!`、`core::range`、NonZero 范围迭代、`AssertUnwindSafe From`、s390x inline asm、Cargo CVE-2026-5222/5223 修复等。
- **PR #151973 `VecDeque::truncate_front` / `retain_back`**：截至 2026-06-26 仍列于 [releases.rs Ongoing Stabilization PRs](https://releases.rs/)，标签为 `finished-final-comment-period` / `disposition-merge` / `to-announce`，**尚未合并进 1.97 beta**。进入 1.97 的概率较 06-25 判断有所下降，推迟至 1.98 的风险上升。
- **Sea-ORM 2.0 stable**：截至 2026-06-26 仍未发布，最新为 **2.0.0-rc.41**（2026-06-18）。
- **AFIDT / `dyn async Trait`**：仍为实验性，tracking issue #133882，年内稳定概率低。

---

## 2. 未完成计划总览（按优先级）

### P0 — 硬截止 2026-07-09

| 编号 | 任务 | 来源文件 | 依赖/风险 | 权威来源 |
|---|---|---|---|---|---|
| A3.1 | 执行 Rust 1.97 发布日清单 | `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md` | 上游实际发布 | [Rust Forge](https://forge.rust-lang.org/)、[releases.rs 1.97](https://releases.rs/docs/1.97.0/) |
| A3.2 | `rust-toolchain.toml` → `channel = "1.97.0"` | `rust-toolchain.toml` | A3.1 | 同上 |
| A3.3 | 激活 `crates/c08_algorithms/src/rust_197_features.rs` 占位 | `crates/c08_algorithms/src/rust_197_features.rs` | `VecDeque::truncate_front`/`retain_back` 可能推迟 | [PR #151973](https://github.com/rust-lang/rust/pull/151973)、[releases.rs](https://releases.rs/) |
| A3.4 | `cargo test --workspace` | 全 workspace | A3.2/A3.3 | Rust 1.97.0 stable |
| A3.5 | 刷新 `concept/07_future/rust_1_97_preview.md` 并迁移到稳定文档目录 | `concept/07_future/rust_1_97_preview.md` | A3.1 | 发布日 Release Notes |
| A3.6 | 完善 `CHANGELOG.md [3.1.0]` | `CHANGELOG.md` | A3.1/A3.3 | 同上 |
| A3.7 | 更新术语表中 1.97 术语状态 | `concept/00_meta/terminology_glossary.md` | 上游实际稳定内容 | 同上 |

### P1 — 建议在 07-09 前完成（无上游阻塞）

| 主题 | 当前问题 | 权威事实 | 建议动作 |
|---|---|---|---|---|---|
| **async closures** | 部分文档仍标 nightly-only 或 preview | **Rust 1.85.0（2025-02-20）已 stable** async closures / `AsyncFn*` traits | 全局修正为 `1.85.0 stable`，更新示例与状态标记 |
| **Rust 2024 Edition** | 版本号/状态可能滞后；`gen` 关键字与 `gen {}` blocks 易混淆 | **Rust 2024 Edition 在 1.85.0 stable**；`gen` 是 2024 Edition 保留关键字；`gen {}` / `gen fn` 仍为 nightly（`#![feature(gen_blocks)]`） | 修正 Edition 版本号为 `1.85.0+`；明确区分“关键字保留”与“gen blocks 不稳定” |
| **`&raw const` / `&raw mut`** | 项目中存在非官方术语 `&const` | 官方语法为 `&raw const T` / `&raw mut T`，**1.82.0 stable** 已稳定 | 全局搜索替换 `&const` → `&raw const`，统一术语 |
| **Rust 1.96 覆盖缺口** | `assert_matches!`、`core::range`、`NonZero` 范围迭代、`AssertUnwindSafe From`、s390x inline asm 等尚未完整覆盖 | Rust 1.96.0（2026-05-28）已 stable 上述特性 | 补文档/练习，标注稳定版本 |
| **C-class 长期维护规则** | 阶段 4 规则未完全落地 | 项目内部质量指标 | 禁止在 C 类目录新建文件；每季度重复检测；90 天决策机制 |

### P2 — 07-09 之后推进

| 主题 | 关键未完成项 | 权威/参考来源 |
|---|---|---|---|---|---|---|---|---|
| **编译器/Cargo 深度内容** | rustc query system、new trait solver、MIR/codegen/LLVM、Cargo resolver v3 / public-private deps / build scripts / registries、Cranelift / parallel frontend / build-std | [rustc-dev-guide](https://rustc-dev-guide.rust-lang.org/)、[Cargo Book](https://doc.rust-lang.org/cargo/)、[Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/) |
| **形式化工具示例** | Kani 函数/循环合约可运行示例扩展、Safety Tags / BorrowSanitizer / Tree Borrows / AutoVerus/Verus 概念页与代码示例交叉引用 | [Kani docs](https://model-checking.github.io/kani/)、[Verus docs](https://verus-lang.github.io/verus/)、[Tree Borrows paper](https://plv.mpi-sws.org/treerabs/)、[Safety Tags RFC #3842](https://github.com/rust-lang/rfcs/pull/3842) |
| **生态迁移** | Sea-ORM 2.0 stable 迁移、`async_trait` → AFIDT/dynosaur 跟踪、WASI 目标确认 | [SeaORM releases](https://github.com/SeaQL/sea-orm/releases)、[AFIDT tracking](https://github.com/rust-lang/rust/issues/133882)、[WASI target update blog](https://blog.rust-lang.org/2024/04/09/updates-to-rusts-wasi-targets/) |
| **TRPL 3rd / Brown Book 对齐** | 所有权/借用文档引用 Brown 研究、`async.md` 标注 TRPL Ch17、逐章对照审计 | [TRPL 3rd Ed (No Starch)](https://nostarch.com/rust-programming-language-3e)、[Brown Rust Book](https://rust-book.cs.brown.edu/) |

### P3 — 长期 / 需外部条件

| 主题 | 关键未完成项 | 备注 |
|---|---|---|---|
| **Effect System / const traits** | `const_trait_impl_preview.md` 深度重写（`~const` 方向已废弃）；Pre-pre RFC 独立章节 | 上游语法未最终确定，建议保持跟踪 |
| **Safety-Critical 工作组落地** | 负责人/预算/认证体系/培训试点 | 当前为规划文档阶段 |
| **国际化与社区验证** | 可用性测试、教师反馈、社区背书、英文版 LEARNING_MVP_PATH | 建议纳入 2026 Q4 |

---

## 3. 权威网络对齐关键结论

| 项目内容 | 权威结论 | 来源 |
|---|---|---|---|
| **Rust 1.97.0 发布日** | **2026-07-09** | [Rust Forge](https://forge.rust-lang.org/)、[releases.rs 1.97](https://releases.rs/docs/1.97.0/) |
| **`VecDeque::truncate_front` / `retain_back`** | PR #151973 标签 `finished-final-comment-period` / `disposition-merge` / `to-announce`，但 **仍列于 releases.rs Ongoing Stabilization PRs，未确认进入 1.97** | [GitHub PR #151973](https://github.com/rust-lang/rust/pull/151973)、[releases.rs](https://releases.rs/) |
| **async closures / `AsyncFn*`** | **1.85.0 stable（2025-02-20）** | [Announcing Rust 1.85.0](https://blog.rust-lang.org/2025/02/20/Rust-1.85.0/)、[RFC 3668](https://github.com/rust-lang/rfcs/pull/3668) |
| **Rust 2024 Edition** | **1.85.0 stable** | [Edition Guide — Rust 2024](https://doc.rust-lang.org/edition-guide/rust-2024/index.html) |
| **`gen` 关键字保留** | **Rust 2024 Edition** | [RFC 3513](https://rust-lang.github.io/rfcs/3513-gen-blocks.html) |
| **`gen {}` / `gen fn` blocks** | 仍为 nightly，tracking issue #117078 | [tracking issue #117078](https://github.com/rust-lang/rust/issues/117078) |
| **`&raw const` / `&raw mut`** | **1.82.0 stable** | [Rust 1.82.0 release notes](https://blog.rust-lang.org/2024/10/17/Rust-1.82.0/) |
| **trait upcasting** | **1.86.0 stable** | [Rust 1.86.0 blog](https://blog.rust-lang.org/2025/04/03/Rust-1.86.0/) |
| **`#[target_feature]` on safe functions** | **1.86.0 stable** | [Rust 1.86.0 blog](https://blog.rust-lang.org/2025/04/03/Rust-1.86.0/) |
| **`HashMap::get_disjoint_mut`** | **1.86.0 stable** | [Rust 1.86.0 blog](https://blog.rust-lang.org/2025/04/03/Rust-1.86.0/) |
| **`assert_matches!` / `debug_assert_matches!`** | **1.96.0 stable** | [Rust 1.96.0 blog](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/)、[releases.rs 1.96](https://releases.rs/docs/1.96.0/) |
| **`core::range` Copy 类型** | **1.96.0 stable** | 同上 |
| **NonZero 整数范围迭代** | **1.96.0 stable** | 同上 |
| **`From<T> for AssertUnwindSafe<T>`** | **1.96.0 stable** | 同上 |
| **s390x vector registers inline asm** | **1.96.0 stable** | 同上 |
| **Sea-ORM 2.0 stable** | 截至 2026-06-26 仍未发布；最新 **2.0.0-rc.41**（2026-06-18） | [crates.io/sea-orm](https://crates.io/crates/sea-orm)、[GitHub releases](https://github.com/SeaQL/sea-orm/releases) |
| **async-std 状态** | 已停止维护（v1.13.1 起），推荐 smol/tokio | [crates.io/async-std](https://crates.io/crates/async-std)、[Fedora deprecation](https://fedoraproject.org/wiki/Changes/Deprecate_async-std) |
| **WASI 目标** | `wasm32-wasi` 已在 Rust 1.84 stable 移除；使用 `wasm32-wasip1` / `wasm32-wasip2` | [Rust WASI target update blog](https://blog.rust-lang.org/2024/04/09/updates-to-rusts-wasi-targets/) |

---

## 4. 主要风险与阻塞

| 风险 | 影响 | 缓解措施 |
|---|---|---|---|
| Rust 1.97.0 某特性未如期稳定（尤其是 `VecDeque::truncate_front`/`retain_back`） | A3.3 / A3.5 / A3.6 / A3.7 | 保留等效实现；在 `rust_197_features.rs`、`CHANGELOG.md`、`rust_1_97_preview.md` 中标注“推迟至 1.98” |
| `cargo audit` 网络不可用 | 依赖安全审计 | 已配置本地 advisory-db；使用 `--no-fetch` 兜底 |
| Sea-ORM 2.0 stable 继续延迟 | 生态迁移 | 继续跟踪 rc 版本；代码侧保持 1.x / rc，文档侧更新状态 |
| AFIDT / `dyn async Trait` 未 stable | `async_trait` 移除 | 文档侧标记为“实验性/跟踪中”，代码侧保持 `async_trait` |
| 多版 roadmap 口径不一致 | 执行混乱 | **已统一主控为 `.kimi/EXECUTION_CHECKLIST_2026_06_22.md`**；早期 `EXECUTION_PLAN_*` 已标记 `[历史参考]` |
| Workspace 根无统一 `version` | CHANGELOG [3.1.0] 与 Cargo.toml 对齐困难 | 发布日前决定是否补充 `[workspace.package].version = "3.1.0"` |

---

## 5. 建议执行顺序

1. **本周内（2026-06-26 ~ 2026-07-02）** —— 不受上游阻塞：
   - [ ] 全局修正 async closures / Edition 2024 / `&raw const` 事实偏差。
   - [ ] 补充 Rust 1.96 覆盖缺口（`assert_matches!`、`core::range`、`NonZero` 范围迭代、`AssertUnwindSafe From`、s390x inline asm）。
   - [ ] 确认是否补充 `[workspace.package].version = "3.1.0"`。

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
2. **1.97 发布日策略**：鉴于 PR #151973 截至 06-26 仍未出现在 releases.rs 1.97 已确认特性列表中，若 `VecDeque::truncate_front` / `retain_back` 未进入 1.97.0，是否同意**保留等效实现并标注“推迟至 1.98”**，而不是删除占位？
3. **P1 权威事实修正**：是否同意我立即全局修正 async closures / Edition 2024 / `&raw const` 的事实偏差，并补充 Rust 1.96 覆盖缺口？
4. **Workspace 版本号**：`CHANGELOG.md [3.1.0]` 已预置，但根 `Cargo.toml` `[workspace.package]` 无 `version` 字段。是否同意补充 `version = "3.1.0"` 以与 CHANGELOG 对齐？
5. **内容治理策略**：`docs/` C-class 已实际清零，是否同意把工作重心从“大规模归档”转向“长期维护规则落地”（禁止新建、季度检测、90 天决策）？
6. **Sea-ORM / AFIDT 策略**：是否同意继续跟踪上游，代码侧保持现状，文档侧更新为“实验性/跟踪中”？
7. **输出形式**：是否需要我基于本确认稿生成一份**可执行的逐周排期表**（细化到文件/命令），或直接进入执行？

---

*本文件为梳理与确认稿，未对项目源文件做任何修改。待你确认后进入执行阶段。*
