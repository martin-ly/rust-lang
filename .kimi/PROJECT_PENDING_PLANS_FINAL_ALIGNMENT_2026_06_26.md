# 本项目未完成计划与任务最终梳理（2026-06-26 执行后版）

> **生成时间**：2026-06-26 17:21（当前会话）
> **主控文件**：`.kimi/EXECUTION_CHECKLIST_2026_06_26_CONFIRMED.md`
> **唯一硬截止**：**2026-07-09** Rust 1.97.0 stable 发布日
> **权威来源校验日期**：2026-06-26
> **前置参考**：`.kimi/PROJECT_PENDING_PLANS_ALIGNMENT_CONFIRM_2026_06_26.md`

---

## 1. 当前项目状态（经本会话实际验证）

| 检查项 | 命令 | 结果 | 备注 |
|---|---|---|---|
| 编译 | `cargo check --workspace` | ✅ 通过（~8.6s） | 0 错误 |
| 全量测试 | `cargo test --workspace` | ✅ 通过 | 含 doctests，25 ignored |
| Clippy | `cargo clippy --workspace --all-features -- -D warnings` | ✅ 通过 | 0 warning |
| 安全审计 | `cargo audit --no-fetch` | ✅ 0 安全漏洞 | 6 个 RUSTSEC 已显式忽略并记录 rationale |
| 文档价值审计 | `python scripts/docs_value_audit.py docs --days-old 90` | ✅ **A=0 / B=0 / C=0** | 233 个文件，问题已清零 |
| 1.96 对齐测验 | `cargo test --test l3_rust_196_alignment` | ✅ **10 passed** | 新建 `exercises/tests/l3_rust_196_alignment.rs` |
| 工具链 | `rust-toolchain.toml` | `channel = "nightly"` | 注释说明 nightly 1.98.0，MSRV 1.96.0 stable |
| Workspace 版本 | 根 `Cargo.toml` | ✅ `version = "3.1.0"` | 与 CHANGELOG [3.1.0] 对齐 |
| 未提交改动 | `git status --short` | **35 个文件已修改 / 6 个未跟踪** | 集中在 P1 权威修正、1.96 覆盖、C-class 治理 |

### 1.1 与 06-26 上午确认稿的关键差异

`.kimi/PROJECT_PENDING_PLANS_ALIGNMENT_CONFIRM_2026_06_26.md` 中列出的 **P1 任务已全部在本地工作区完成**（尚未 commit），当前仅剩 **P0 硬截止 2026-07-09** 及之后的滚动任务。

| 指标 | 06-26 确认稿 | 本会话实际验证 | 说明 |
|---|---|---|---|
| `docs/` C-class 问题数 | 0 | **0** | 已稳定 |
| `&const` 非官方术语残留 | 待修正 | **0 处** | `concept/` / `knowledge/` / `docs/` / `book/` 已全局扫描 |
| async closures nightly 错误标注 | 待修正 | **仅 1 处教学反例保留**（`concept/03_advanced/24_async_closures.md:378` 明确标注“❌，1.85.0+ stable”） | 其余已修正 |
| Rust 1.96 覆盖缺口 | 待补充 | **已补充**：`docs/06_toolchain/06_22_rust_1_96_features.md`、`concept/07_future/rust_1_96_stabilized.md`、`exercises/tests/l3_rust_196_alignment.rs` | 10 个测验全通过 |
| Workspace version | 未定义 | **已补充 `3.1.0`** | 与 CHANGELOG 对齐 |
| C-class 长期维护规则 | 阶段 4 进行中 | **阶段 4 已勾选完成** | `reports/C_CLASS_GOVERNANCE_PLAN_2026_06_09.md` 已更新 |

---

## 2. 真正未完成的计划与任务（按优先级）

### P0 — 硬截止 2026-07-09（唯一不可提前完成的任务）

| 编号 | 任务 | 来源文件 | 依赖/风险 | 权威来源 |
|---|---|---|---|---|
| A3.1 | 执行 Rust 1.97 发布日清单 | `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md` | 上游实际发布 | [Rust Forge](https://forge.rust-lang.org/)、[releases.rs 1.97](https://releases.rs/docs/1.97.0/) |
| A3.2 | `rust-toolchain.toml` → `channel = "1.97.0"` | `rust-toolchain.toml` | A3.1 | 同上 |
| A3.3 | 激活 `crates/c08_algorithms/src/rust_197_features.rs` 占位 | `crates/c08_algorithms/src/rust_197_features.rs` | `VecDeque::truncate_front`/`retain_back` 可能推迟 | [PR #151973](https://github.com/rust-lang/rust/pull/151973)、[releases.rs](https://releases.rs/) |
| A3.4 | `cargo test --workspace` | 全 workspace | A3.2/A3.3 | Rust 1.97.0 stable |
| A3.5 | 刷新 `concept/07_future/rust_1_97_preview.md` 并迁移 | `concept/07_future/rust_1_97_preview.md` | A3.1 | 发布日 Release Notes |
| A3.6 | 完善 `CHANGELOG.md [3.1.0]` | `CHANGELOG.md` | A3.1/A3.3 | 同上 |
| A3.7 | 更新术语表中 1.97 术语状态 | `concept/00_meta/terminology_glossary.md` | 上游实际稳定内容 | 同上 |

### P1 — 发布日后期稳定化（2026-07-10 ~ 2026-07-20）

| 编号 | 任务 | 来源 | 验收标准 |
|---|---|---|---|
| A4.1 | 最终回填 `CHANGELOG.md [3.1.0]` 实际条目 | `.kimi/EXECUTION_CHECKLIST_2026_06_26_CONFIRMED.md` | 未进入 1.97 的特性标注“推迟至 1.98” |
| A4.2 | 归档发布日清单 | `archive/project_reports/` | 原清单含 `[ARCHIVED]` 标记 |
| A4.3 | 全 workspace 回归 | `cargo check` / `cargo test` / `cargo clippy` / `cargo audit --no-fetch` | 全绿 |
| A4.4 | 启动 P2 深度内容 | 编译器/Cargo、形式化工具、TRPL/Brown 对齐 | 至少 2 个文件新增实践章节 |

### P2 — 2026 Q3 滚动推进

| 主题 | 关键未完成项 | 权威/参考来源 |
|---|---|---|
| **编译器/Cargo 深度内容** | rustc query system 实践、new trait solver 对比示例、Cargo resolver v3 / `public = true`、MIR/codegen/LLVM | [rustc-dev-guide](https://rustc-dev-guide.rust-lang.org/)、[Cargo Book](https://doc.rust-lang.org/cargo/)、[Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/) |
| **形式化工具示例** | 扩展 Kani 函数/循环合约示例到 c03/c04；Safety Tags / BorrowSanitizer / AutoVerus / Tree Borrows 概念页交叉引用 | [Kani docs](https://model-checking.github.io/kani/)、[Verus docs](https://verus-lang.github.io/verus/)、[Safety Tags RFC #3842](https://github.com/rust-lang/rfcs/pull/3842) |
| **生态迁移** | Sea-ORM 2.0 stable 迁移评估、AFIDT/dynosaur 跟踪、WASI 目标再次确认 | [SeaORM releases](https://github.com/SeaQL/sea-orm/releases)、[AFIDT tracking #133882](https://github.com/rust-lang/rust/issues/133882) |
| **TRPL 3rd / Brown Book 对齐** | 建立逐章对照映射表、所有权文档引用 Brown 研究、`async.md` 标注 TRPL Ch17 | [TRPL 3rd Ed](https://nostarch.com/rust-programming-language-3e)、[Brown Rust Book](https://rust-book.cs.brown.edu/) |

### P3 — 长期 / 需外部条件 / 2026 Q4

| 主题 | 关键未完成项 | 备注 |
|---|---|---|
| **国际化与社区验证** | 英文骨架 80% 覆盖、术语一致性脚本强制模式、TRPL 对照、Brown Inventory 练习、3+2 可用性测试、教师反馈 | `.kimi/I18N_Q4_2026_PLAN.md` |
| **Effect System / const traits** | `const_trait_impl_preview.md` 深度重写（`~const` 方向已废弃）；Pre-pre RFC 独立章节 | 上游语法未最终确定 |
| **Safety-Critical 工作组落地** | 负责人/预算/认证体系/培训试点评估 | 当前为规划文档阶段 |
| **Rust 1.98 稳定化** | 预计 2026-10-01；`rust-toolchain.toml` / `CHANGELOG.md [3.2.0]` | 依赖上游发布 |

---

## 3. 权威网络对齐关键结论（本会话更新）

| 项目内容 | 权威结论 | 来源 |
|---|---|---|
| **Rust 1.97.0 发布日** | **2026-07-09** | [releases.rs 1.97](https://releases.rs/docs/1.97.0/)、[Rust Forge](https://forge.rust-lang.org/) |
| **`VecDeque::truncate_front` / `retain_back`** | PR #151973 标签为 `finished-final-comment-period` / `disposition-merge` / `to-announce`，但仍列于 [releases.rs Ongoing Stabilization PRs](https://releases.rs/)。**进入 1.97 的概率下降，推迟至 1.98 的风险上升** | [GitHub PR #151973](https://github.com/rust-lang/rust/pull/151973)、[releases.rs](https://releases.rs/) |
| **Rust 1.96.0** | **2026-05-28 stable**：`assert_matches!`、`core::range` Copy 类型、NonZero 范围迭代、`AssertUnwindSafe From`、`LazyCell`/`LazyLock From`、s390x vector asm、Cargo CVE-2026-5222/5223 | [Rust 1.96.0 blog](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/)、[releases.rs 1.96](https://releases.rs/docs/1.96.0/) |
| **async closures / `AsyncFn*`** | **Rust 1.85.0 stable（2025-02-20）** | [Rust 1.85.0 blog](https://blog.rust-lang.org/2025/02/20/Rust-1.85.0/) |
| **Rust 2024 Edition** | **Rust 1.85.0 stable** | [Edition Guide](https://doc.rust-lang.org/edition-guide/rust-2024/index.html) |
| **`gen` 关键字保留** | **Rust 2024 Edition** | [RFC 3513](https://rust-lang.github.io/rfcs/3513-gen-blocks.html) |
| **`gen {}` / `gen fn` blocks** | 仍为 nightly，tracking issue #117078 | [tracking issue #117078](https://github.com/rust-lang/rust/issues/117078) |
| **`&raw const` / `&raw mut`** | **1.82.0 stable**，官方语法 | [Rust 1.82.0 blog](https://blog.rust-lang.org/2024/10/17/Rust-1.82.0/) |
| **Sea-ORM 2.0 stable** | 截至 2026-06-26 仍未发布；最新 **2.0.0-rc.41**（2026-06-18） | [crates.io/sea-orm](https://crates.io/crates/sea-orm)、[GitHub releases](https://github.com/SeaQL/sea-orm/releases) |
| **AFIDT / `dyn async Trait`** | 仍为实验性；tracking issue #133882 | [GitHub tracking issue](https://github.com/rust-lang/rust/issues/133882) |

---

## 4. 主要风险与阻塞

| 风险 | 影响 | 缓解措施 | 当前状态 |
|---|---|---|---|
| Rust 1.97.0 某特性未如期稳定（尤其 `retain_back`） | A3.3 / A3.5 / A3.6 / A3.7 | 保留等效实现；在 `rust_197_features.rs`、`rust_1_97_preview.md`、`CHANGELOG.md` 中标注“推迟至 1.98” | 已准备，风险上升 |
| `cargo audit` 网络不可用 | 安全审计 | 已配置本地 advisory-db；使用 `--no-fetch` 兜底 | 已就绪 |
| Sea-ORM 2.0 stable 继续延迟 | 生态迁移 | 文档侧持续跟踪 rc 版本；代码侧保持现状 | 已就绪 |
| AFIDT / `dyn async Trait` 未 stable | `async_trait` 移除 | 文档标注为“实验性/跟踪中”；代码侧保留 `async_trait` | 已就绪 |
| 工作区 35 个已修改文件未提交 | 状态丢失风险 | 建议本会话结束后立即 commit | **待处理** |

---

## 5. 建议下一步行动

1. **立即 commit 当前工作区改动**：P1 权威修正、1.96 覆盖、workspace version、C-class 治理已完成，应提交避免丢失。
2. **等待 2026-07-09**：执行 `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md`。
3. **2026-07-10 ~ 07-20**：回填 CHANGELOG、归档清单、启动 P2 深度内容。
4. **2026 Q3**：持续推进编译器/Cargo、形式化工具、生态迁移、TRPL/Brown 对齐。
5. **2026 Q4**：按 `.kimi/I18N_Q4_2026_PLAN.md` 启动国际化与社区验证。

---

## 6. 请你确认

1. **当前 P1 完成状态**：是否确认 async closures / Edition 2024 / `&raw const` 修正、Rust 1.96 覆盖、workspace version、C-class 治理、Sea-ORM/AFIDT 状态更新 **已全部完成**？
2. **提交策略**：是否同意我现在将当前 35 个已修改文件 + 6 个未跟踪文件 **提交到当前分支**（提交信息建议：`docs: P1 authoritative alignment, Rust 1.96 coverage, workspace version, C-class governance`）？
3. **1.97 发布日策略**：鉴于 `retain_back` 进入 1.97 的概率下降，是否确认**保留等效实现并标注“推迟至 1.98”**，不删除占位？
4. **后续执行主控**：是否确认继续以 `.kimi/EXECUTION_CHECKLIST_2026_06_26_CONFIRMED.md` 为唯一执行主控，按周执行到 2026-08-31？
5. **是否需要我现在继续推进**：
   - A) 仅提交当前改动，等待 07-09；
   - B) 提交后继续做 Week 5+ 的 P2 深度内容；
   - C) 先整理/压缩旧 `.kimi/` 和 `reports/` 历史文件，再推进新任务。

---

*本文件为 2026-06-26 执行后最终梳理稿，已对本项目文件做只读验证，未修改源文件。*
