# 项目后续执行检查清单（2026-06-26 确认版）

> **创建日期**: 2026-06-26
> **执行周期**: 2026-06-26 ~ 2026-07-20
> **主控来源**: `.kimi/EXECUTION_CHECKLIST_2026_06_22.md`
> **对齐确认**: `.kimi/PROJECT_PENDING_PLANS_ALIGNMENT_CONFIRM_2026_06_26.md`
> **唯一硬截止**: **2026-07-09** Rust 1.97.0 stable 发布日
> **确认状态**: 已与用户对齐 7 项关键决策

---

## 决策摘要（已确认）

1. ✅ 以 `.kimi/EXECUTION_CHECKLIST_2026_06_22.md` 为唯一执行主控。
2. ✅ 若 `VecDeque::truncate_front` / `retain_back` 未进入 1.97.0，保留等效实现并标注“推迟至 1.98”。
3. ✅ **P1 权威事实修正作为最优先任务**：立即全局修正 async closures / Edition 2024 / `&raw const`，并补充 Rust 1.96 覆盖缺口。
4. ✅ 根 `Cargo.toml` 补充 `[workspace.package].version = "3.1.0"`。
5. ✅ `docs/` C-class 已清零，工作重心转向长期维护规则落地。
6. ✅ Sea-ORM / AFIDT 继续跟踪上游；代码侧保持现状，文档侧更新为“实验性/跟踪中”。
7. ✅ 生成本可执行逐周排期表，按表执行。

---

## 工作流 A：P1 权威事实修正与 1.96 覆盖缺口回填（最优先，2026-06-26 ~ 2026-07-02）

### A1. 全局修正 async closures 事实偏差

- **权威事实**: async closures / `AsyncFn*` traits 已于 **Rust 1.85.0（2025-02-20）stable**。
- **修改范围**: 全仓库 Markdown（`concept/`、`knowledge/`、`docs/`、`book/`、`crates/` 文档）。
- **关键文件**: `concept/03_advanced/24_async_closures.md`、`content/emerging/async_closures.md`、`crates/c06_async/docs/ASYNC_CLOSURES_GUIDE.md` 等。
- **命令**: `grep -Rin "nightly.*async.*closure\|async.*closures.*nightly\|needs.*nightly.*async" concept/ knowledge/ docs/ book/ crates/ --include="*.md"`
- **验收标准**:
  - 所有相关位置标注为 **Rust 1.85.0 stable**；
  - 移除 "nightly-only" / "needs nightly" / "🧪" 等错误标记；
  - `Box<dyn AsyncFn(...)>` 示例保持 `compile_fail`（非 dyn-compatible 是事实）。

### A2. 全局修正 Rust 2024 Edition 事实偏差

- **权威事实**: Rust 2024 Edition 于 **1.85.0 stable**；`gen` 是 2024 Edition 保留关键字；`gen {}` / `gen fn` 仍为 nightly（`#![feature(gen_blocks)]`）。
- **修改范围**: `knowledge/06_ecosystem/02_edition_2024.md`、`concept/07_future/19_rust_edition_preview.md` 及全仓库提及 Edition 2024 / gen blocks 的文件。
- **命令**: `grep -Rin "Edition 2024\|2024 edition\|gen blocks\|gen fn" concept/ knowledge/ docs/ book/ --include="*.md"`
- **验收标准**:
  - 版本号统一为 **1.85.0+**；
  - 明确区分：`gen` 关键字在 2024 Edition 保留；`gen {}` / `gen fn` 仍为 nightly。

### A3. 全局修正 `&raw const` / `&raw mut` 术语

- **权威事实**: 官方语法为 `&raw const T` / `&raw mut T`，**1.82.0 stable** 已稳定。
- **修改范围**: 全仓库 Markdown（含 `&const` 或 `&raw` 错误写法）。
- **命令**: `grep -Rin "&const" concept/ knowledge/ docs/ book/ --include="*.md"`
- **验收标准**:
  - 不存在 `&const` 非官方术语；
  - 统一为 `&raw const T` / `&raw mut T`，并标注 **1.82.0 stable**。

### A4. 补充 Rust 1.96 覆盖缺口

- **权威事实**: Rust 1.96.0（2026-05-28）已 stable：
  - `assert_matches!` / `debug_assert_matches!`
  - `core::range::{Range, RangeIter, RangeFrom, RangeFromIter, RangeToInclusive, RangeToInclusiveIter}`
  - `NonZero` 整数范围迭代
  - `From<T> for AssertUnwindSafe<T>`
  - `From<T> for LazyCell<T, F>` / `LazyLock<T, F>`
  - s390x vector registers inline assembly
  - `valid for read/write` 定义重构
  - Cargo CVE-2026-5222 / 5223 修复
- **新建/修改文件**:
  - `docs/06_toolchain/06_22_rust_1_96_features.md`
  - `concept/07_future/rust_1_96_stabilized.md`
  - `exercises/tests/l3_rust_196_alignment.rs`
- **命令**:

  ```bash
  cargo check --workspace
  cd exercises && cargo test --test l3_rust_196_alignment
  cd .. && cargo test --workspace
  ```

- **验收标准**:
  - 每个特性标注稳定版本号与官方来源；
  - 新增/修改的测试全部通过。

### A5. 更新 Sea-ORM / AFIDT 状态文档

- **权威事实**:
  - Sea-ORM 2.0 stable 未发布，最新 `2.0.0-rc.41`（2026-06-18）；
  - AFIDT / `dyn async Trait` 实验性，tracking issue #133882。
- **修改文件**:
  - `crates/c10_networks/Cargo.toml`（注释更新检查日期）
  - `reports/SEA_ORM_2_0_RELEASE_TRACKING_2026_06_22.md`
  - 所有含 `async_trait` / `AFIDT` / `dyn async` 的文档
- **命令**: `grep -Rin "async_trait\|AFIDT\|dyn async" concept/ knowledge/ docs/ crates/ --include="*.md" --include="*.rs"`
- **验收标准**:
  - Sea-ORM 状态：stable 未发布，当前跟踪 `2.0.0-rc.41`；代码侧保持现状。
  - AFIDT/`dyn async Trait`：文档侧标注为“实验性/跟踪中”，代码侧保持 `async_trait`。

### A6. 补充 Workspace Version

- **修改文件**: 根 `Cargo.toml`
- **操作**: 在 `[workspace.package]` 下添加 `version = "3.1.0"`。
- **验收标准**: `cargo check --workspace` 通过；CHANGELOG [3.1.0] 与 workspace version 一致。

### A7. C-class 长期维护规则落地

- **修改文件**: `reports/C_CLASS_GOVERNANCE_PLAN_2026_06_09.md`
- **内容**: 将阶段 4 规则写入项目规范：
  - 禁止在 C 类目录新建文件（除非明确标记为临时研究）；
  - 每季度运行一次 `scripts/detect_content_overlap.py`；
  - 研究笔记完成 90 天后必须决定：迁移到主轨 / 归档 / 删除；
  - 每次归档后运行 `fix_archived_research_notes_links.py`。
- **验收标准**: 阶段 4 所有条目勾选完成。

---

## 工作流 B：Rust 1.97.0 发布日执行（2026-07-09）

按 `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md` 执行，关键调整：

| 阶段 | 任务 | 风险处理 |
|---|---|---|
| 0 | 确认 Rust 1.97.0 已发布 | 若延迟，按实际发布日顺延 |
| 1 | `rust-toolchain.toml` → `channel = "1.97.0"` | — |
| 2 | 激活 `crates/c08_algorithms/src/rust_197_features.rs` | `truncate_front`/`retain_back` 未进则保留等效实现并标注 1.98 |
| 3 | `cargo check` / `cargo test` / `cargo clippy` | 修复 1.97 引入的警告 |
| 4 | 刷新 `rust_1_97_preview.md` 并迁移 | — |
| 5 | 补充 1.97 特性测验 | — |
| 6 | 完善 CHANGELOG [3.1.0] | 未进入 1.97 的特性标注“推迟至 1.98” |
| 7 | 更新术语表、提交、归档清单 | — |

---

## 工作流 C：发布日后稳定化（2026-07-10 ~ 2026-07-20）

- [ ] 最终回填 `CHANGELOG.md [3.1.0]` 实际条目。
- [ ] 归档发布日清单到 `archive/project_reports/`。
- [ ] 全 workspace 回归：`cargo check` / `cargo test` / `cargo clippy` / `cargo audit --no-fetch`。

---

## 工作流 D：P2 深度内容冲刺（2026-06-26 完成）

本轮冲刺覆盖四个轨道，均已在 2026-06-26 完成并验证。

### D1. rustc query system / 增量编译实践

- [x] 扩展 `concept/04_formal/19_rustc_query_system.md` §4，新增可观测实验步骤与输出解读。
- [x] 创建 `examples/incremental_practice/` 独立可运行示例，含 `math` / `greet` / `analyze` 三模块与单元测试。
- [x] 验证：`cargo test` 3 passed；`-Z incremental-info` 冷编译 / 无修改 / 修改后输出与文档一致。

### D2. Cargo resolver v3 / MSRV workspace 可运行示例

- [x] 修正 §7.2 解析策略描述，使用实际生效的 `incompatible-rust-versions` / `CARGO_RESOLVER_INCOMPATIBLE_RUST_VERSIONS`。
- [x] 新增 `concept/06_ecosystem/60_cargo_dependency_resolution.md` 第九章可运行实践。
- [x] 创建 `examples/resolver_v3_practice/` 独立 workspace，演示混合 MSRV（1.70 / 1.84 / 1.96）与 resolver v3 fallback/allow 行为。
- [x] 验证：`cargo check --workspace` 通过；`cargo tree --duplicates` 正确显示 `indexmap` 1.x / 2.x 重复。

### D3. Kani 独立概念页

- [x] 新建 `concept/04_formal/32_kani.md`（327 行），系统介绍 Kani 原理、核心概念、可运行示例、项目内示例导航与限制。
- [x] 在 `concept/04_formal/22_modern_verification_tools.md` 增加指向新独立页的交叉链接。
- [x] 风格对齐 `31_miri.md`，链接到 `crates/c01/c02/c08` 的 `kani_examples.rs`。

### D4. TRPL / Brown Book 对齐剩余旧版链接修复

- [x] 扫描 `concept/` 下 242 个 Markdown 文件，将泛化 `https://doc.rust-lang.org/book/` 链接替换为 TRPL 3rd Ed 具体章节。
- [x] 对所有权/借用/生命周期/并发/异步相关 15 个文件补充 Brown University Interactive Book 章节链接。
- [x] 生成完整报告 `reports/TRPL_GENERIC_LINK_FIX_2026_06_26.md`。
- [x] 验证：`grep -R "doc.rust-lang.org/book/)" concept/` 无剩余泛化链接。

### D5. 交付物汇总

| 交付物 | 路径 | 状态 |
|:---|:---|:---:|
| rustc query system 实践章节 | `concept/04_formal/19_rustc_query_system.md` | ✅ |
| 增量编译示例 | `examples/incremental_practice/` | ✅ |
| Cargo resolver v3 实践章节 | `concept/06_ecosystem/60_cargo_dependency_resolution.md` | ✅ |
| MSRV workspace 示例 | `examples/resolver_v3_practice/` | ✅ |
| Kani 独立概念页 | `concept/04_formal/32_kani.md` | ✅ |
| Kani 交叉链接 | `concept/04_formal/22_modern_verification_tools.md` | ✅ |
| TRPL/Brown 链接修复报告 | `reports/TRPL_GENERIC_LINK_FIX_2026_06_26.md` | ✅ |
| 自动化脚本 | `scripts/fix_generic_trpl_links.py` | ✅ |

---

## 每日/每周例行仪式

### 每日

| 仪式 | 命令 | 通过标准 |
|---|---|---|
| 编译基线 | `cargo check --workspace` | 0 错误 |
| 快速测试 | `cargo test --workspace`（或受影响 crate） | 0 失败 |

### 每周（建议周五）

| 仪式 | 命令 | 通过标准 |
|---|---|---|
| 全量检查 | `cargo check --workspace && cargo clippy --workspace --all-features -- -D warnings && cargo test --workspace` | 全绿 |
| 安全审计 | `cargo audit --no-fetch` | 0 安全漏洞；`unmaintained` 已记录 rationale |
| 链接检查 | `python scripts/check_links.py` | 损坏 0 |
| 文档价值审计 | `python scripts/docs_value_audit.py docs --days-old 90` | A/B 类 0，C-class 保持 0 |
| 去重扫描 | `python scripts/detect_content_overlap.py` | 无 ≥0.90 相似对 |
| 进度摘要 | 新建 `.kimi/WEEKLY_PROGRESS_2026_MM_DD.md` | 含本周完成、关键数字、阻塞项、下周计划 |

---

## 风险与 Fallback 动作

| 风险 | 影响范围 | Fallback 动作 | 触发条件 |
|---|---|---|---|
| Rust 1.97.0 某特性未稳定 | A3.x | 保留等效实现，标注“推迟至 1.98” | 07-09 Release Notes 未包含 |
| `cargo audit` 网络不可用 | 安全审计 | 使用 `--no-fetch` + 本地 advisory-db | 网络失败 |
| Sea-ORM 2.0 stable 继续延迟 | 生态迁移 | 文档跟踪 rc.41，代码保持现状 | 08-31 仍未发布 |
| AFIDT 未 stable | `async_trait` 移除 | 文档标注实验性，代码保留 `async_trait` | 年内未稳定 |
| Workspace version 补充后 crate 冲突 | 编译 | 检查各 crate `Cargo.toml` 是否已声明 version | `cargo check` 失败 |

---

*本清单基于用户 2026-06-26 确认生成，立即进入执行。*
