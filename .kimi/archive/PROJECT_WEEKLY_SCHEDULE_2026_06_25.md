# 项目逐周执行排期表（2026-06-25 ~ 2026-08-31）

> **生成日期**: 2026-06-25
> **主控文件**: `.kimi/EXECUTION_CHECKLIST_2026_06_22.md`
> **对齐确认**: `.kimi/PROJECT_PENDING_PLANS_ALIGNMENT_CONFIRM_2026_06_25.md`
> **唯一硬截止**: **2026-07-09** Rust 1.97.0 stable 发布日
> **输出形式**: 可执行排期，细化到文件路径、命令与验收标准。

---

## 1. 执行前提与假设

| 假设项 | 内容 |
| :--- | :--- |
| **当前日期** | 2026-06-25（周四） |
| **工具链** | 项目当前使用 nightly；`cargo check --workspace` 通过。 |
| **Rust 1.97.0 发布日** | 预计 **2026-07-09**（Rust Forge）。 |
| **Rust 1.98.0 nightly 周期** | 预计 2026-08-20 进入 beta；2026-10-01 稳定。 |
| **工作区健康基线** | `cargo check --workspace` ✅、`cargo audit --no-fetch` ✅ 0 漏洞、`docs/` 损坏链接 ✅ 0、`docs/` C-class 问题 ✅ 228。 |
| **主控口径** | 以 `.kimi/EXECUTION_CHECKLIST_2026_06_22.md` 为唯一执行主控；早期 `EXECUTION_PLAN_*` 仅作历史参考。 |
| **版本号约定** | 项目 workspace 下一版本为 `[3.1.0]`（已预置在 `CHANGELOG.md` 顶部）。 |

---

## 2. 逐周排期（2026-06-23 ~ 2026-08-31）

> 每周结构：周次 / 日期 / 主题 / 具体任务（含文件路径、命令、验收标准）/ 依赖与阻塞。

### Week 1：收尾预发布前置（2026-06-23 ~ 2026-06-29）

| 维度 | 内容 |
| :--- | :--- |
| **主题** | 权威事实修正收尾 + Rust 1.97 发布日前置最后检查 |
| **整体目标** | 在 06-30 前完成所有不受 07-09 上游阻塞的 P1 修正，确保 Week 2 只剩余等待上游发布。 |

#### 任务清单

- [ ] **A1.9** 全局修正 async closures 事实偏差
  - **修改文件**: `concept/03_advanced/24_async_closures.md:378`
  - **命令**: `grep -R "nightly.*async.*closure\|async.*closures.*nightly\|needs.*nightly.*async" concept/ knowledge/ docs/ --include="*.md"`
  - **验收标准**: 所有 async closures / `AsyncFn*` traits 标注为 **Rust 1.85.0 stable（2025-02-20）**；preview 标记改为 ✅。
  - **依赖**: 无。

- [ ] **A1.10** 全局修正 Rust 2024 Edition 事实偏差
  - **修改文件**: `knowledge/06_ecosystem/02_edition_2024.md`、`concept/07_future/19_rust_edition_preview.md`
  - **命令**: `grep -R "Edition 2024\|2024 edition\|gen blocks\|gen fn" concept/ knowledge/ docs/ --include="*.md" | head -50`
  - **验收标准**: 版本号统一为 **1.85.0+**；明确区分：`gen` 关键字在 2024 Edition 保留；`gen {}` / `gen fn` 仍为 nightly（`#![feature(gen_blocks)]`）。
  - **依赖**: 无。

- [ ] **A1.11** 全局修正 `&raw const` / `&raw mut` 术语
  - **修改文件**: 全仓库 Markdown（含 `&const` 或 `&raw` 错误写法）
  - **命令**: `grep -R "&const" concept/ knowledge/ docs/ book/ --include="*.md"`
  - **验收标准**: 不存在 `&const` 非官方术语；统一为 `&raw const T` / `&raw mut T`，并标注 **1.82.0 stable**。
  - **依赖**: 无。

- [ ] **A1.12** 运行本周基线健康检查
  - **命令**: `cargo check --workspace && cargo clippy --workspace --all-features -- -D warnings`
  - **验收标准**: 0 编译错误、0 Clippy warning。
  - **依赖**: 前述文字修改不得破坏代码。

---

### Week 2：Rust 1.96 覆盖缺口回填 + 上游等待（2026-06-30 ~ 2026-07-06）

| 维度 | 内容 |
| :--- | :--- |
| **主题** | Rust 1.96 覆盖缺口回填 + Sea-ORM/AFIDT 状态更新 + C-class 治理收尾 |
| **整体目标** | 完成 1.96 稳定特性文档化；确认上游 1.97 beta 状态；将 C-class 问题数从 228 压降至 150 以下。 |

#### 任务清单

- [ ] **A2.7** 回填 Rust 1.96 覆盖缺口
  - **新建/修改文件**:
    - `docs/06_toolchain/06_22_rust_1_96_features.md`
    - `concept/07_future/rust_1_96_stabilized.md`
    - `exercises/tests/l3_rust_196_alignment.rs`
  - **命令**:

    ```bash
    cd exercises && cargo test --test l3_ecosystem_alignment
    cd .. && cargo test --workspace
    ```

  - **验收标准**:
    - 覆盖 `assert_matches!`、`core::range`、`NonZero` 范围迭代、`AssertUnwindSafe From`、s390x inline asm、rustdoc 1.96 改进。
    - 每个特性标注稳定版本号与官方来源。
    - 新增/修改的测试全部通过。
  - **依赖**: 无（1.96 已稳定）。

- [ ] **A2.8** 更新 Sea-ORM / AFIDT 状态文档
  - **修改文件**:
    - `crates/c10_networks/Cargo.toml`（注释更新检查日期）
    - `reports/SEA_ORM_2_0_RELEASE_TRACKING_2026_06_22.md`
    - 所有含 `async_trait` 与 `AFIDT`/`dyn async Trait` 的文档
  - **命令**: `grep -R "async_trait\|AFIDT\|dyn async" concept/ knowledge/ docs/ crates/ --include="*.md" --include="*.rs" | head -80`
  - **验收标准**:
    - Sea-ORM 状态：stable 未发布，当前跟踪 `2.0.0-rc.41`；代码侧保持现状。
    - AFIDT/`dyn async Trait`：文档侧标注为“实验性/跟踪中”（tracking issue #133882），代码侧保持 `async_trait`。
    - `Cargo.toml` 注释日期更新为 2026-07-06 或更早。
  - **依赖**: 无。

- [ ] **B2.5** C-class 治理收尾：目标 150 以下
  - **脚本**: `scripts/docs_value_audit.py docs --days-old 90`
  - **辅助脚本**: `scripts/maintenance/archive_research_notes_candidates.py --stale-days 60`
  - **验收标准**:
    - `docs/` C-class 问题数 ≤ 150。
    - 归档文件已移动并添加 `[ARCHIVED]` 标记。
    - 运行 `scripts/maintenance/fix_archived_research_notes_links.py` 修复引用残留。
  - **依赖**: 无。

- [ ] **A2.9** 上游预检：Rust 1.97.0 beta 状态
  - **命令**: `rustup check` 或访问 <https://releases.rs>
  - **验收标准**: 确认 1.97.0 stable 尚未发布（预期 07-09）；记录当前 beta 版本到 `.kimi/RELEASE_PREFLIGHT_2026_07_06.md`。
  - **依赖**: 网络。

---

### Week 3：Rust 1.97 发布周（2026-07-07 ~ 2026-07-13）

| 维度 | 内容 |
| :--- | :--- |
| **主题** | Rust 1.97.0 stable 切换 + 文档/测试/CHANGELOG 刷新 |
| **整体目标** | 在 07-09 当天完成发布日清单；07-10 ~ 07-13 完成迁移、归档与回归测试。 |

详见下方 [第 4 节：1.97 发布周日程](#4-rust-197-发布周-2026-07-07--2026-07-13-日计划)。

**本周汇总任务**:

- [ ] 07-09 当天执行 `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md`
- [ ] 07-10 ~ 07-11 完成 `rust_1_97_preview.md` 迁移到 `docs/06_toolchain/06_21_rust_1_97_features.md`
- [ ] 07-12 更新 `CHANGELOG.md [3.1.0]`、`terminology_glossary.md` 1.97 术语状态
- [ ] 07-13 全 workspace 回归 + 归档发布日清单

---

### Week 4：发布日后期稳定化（2026-07-14 ~ 2026-07-20）

| 维度 | 内容 |
| :--- | :--- |
| **主题** | CHANGELOG 回填、迁移测试、文档归档、启动 P2 深度内容 |
| **整体目标** | 确保 3.1.0 版本可交付；为 Q3 深度内容铺路。 |

#### 任务清单

- [ ] **A4.3** 最终回填 `CHANGELOG.md [3.1.0]` 实际条目
  - **修改文件**: `CHANGELOG.md`
  - **命令**: `git diff CHANGELOG.md`
  - **验收标准**:
    - 列出所有实际进入 1.97 的 API（`VecDeque::truncate_front`、`retain_back` 等）。
    - 未进入 1.97 的特性标注“推迟至 1.98”。
    - 包含工具链升级、文档更新、测试新增摘要。
  - **依赖**: 1.97 发布日结果。

- [ ] **A4.4** 归档发布日清单
  - **操作**: `cp .kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md archive/project_reports/`
  - **修改文件**: `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md` 顶部添加 `[ARCHIVED]` 标记
  - **验收标准**: 原清单移动到归档目录，主控清单更新为完成状态。
  - **依赖**: A3.x 全部完成。

- [ ] **A4.5** 迁移测试与稳定性验证
  - **命令**:

    ```bash
    cargo check --workspace
    cargo test --workspace
    cargo clippy --workspace --all-features -- -D warnings
    cargo audit --no-fetch
    ```

  - **验收标准**: 全绿通过；`cargo audit` 0 漏洞。
  - **依赖**: A3.2/A3.4。

- [ ] **E4.4** 启动编译器/Cargo 深度内容 Phase 2
  - **目标文件**:
    - `concept/04_formal/19_rustc_query_system.md`
    - `concept/04_formal/26_trait_solver_in_rustc.md`
    - `concept/06_ecosystem/67_llvm_backend_and_codegen.md`
    - `concept/06_ecosystem/60_cargo_dependency_resolution.md`
  - **任务**: 为上述文件补充可运行示例或 `rust,ignore` 伪代码；建立与 `rust_1_98_preview.md` 的交叉引用。
  - **验收标准**: 至少 2 个文件新增实践章节或示例。
  - **依赖**: 无。

---

### Week 5：形式化工具示例落地（2026-07-21 ~ 2026-07-27）

| 维度 | 内容 |
| :--- | :--- |
| **主题** | Kani / Verus / Safety Tags / BorrowSanitizer / Tree Borrows 可运行示例 |
| **整体目标** | 将形式化工具概念页从“概念”推进到“可验证代码”。 |

#### 任务清单

- [ ] **D5.1** 扩展 Kani 函数合约与循环合约示例
  - **修改文件**:
    - `crates/c01_ownership_borrow_scope/src/kani_examples.rs`
    - `crates/c02_type_system/src/kani_examples.rs`
  - **新增文件**:
    - `crates/c03_control_fn/src/kani_examples.rs`
    - `crates/c04_generic/src/kani_examples.rs`
  - **命令**:

    ```bash
    cargo check --workspace
    cargo test -p c01_ownership_borrow_scope
    cargo test -p c02_type_system
    ```

  - **验收标准**:
    - 每个 crate 至少新增 2 个 Kani 合约/循环合约示例。
    - `cfg(kani)` 已加入对应 `Cargo.toml` 的 `unexpected_cfgs`。
  - **依赖**: Kani 0.66 可用。

- [ ] **D5.2** Safety Tags / BorrowSanitizer / AutoVerus 概念页交叉引用
  - **修改文件**:
    - `concept/04_formal/22_safety_tags.md`
    - `concept/04_formal/23_borrow_sanitizer.md`
    - `concept/04_formal/24_autoverus.md`
    - `concept/04_formal/25_tree_borrows_deep_dive.md`
  - **命令**: `scripts/check_links.py`
  - **验收标准**: 四篇文档相互引用完整；新增内部链接不引入断链。
  - **依赖**: 无。

- [ ] **D5.3** 更新 Rust for Linux 形式化工具交叉引用
  - **修改文件**: `concept/07_future/19_rust_for_linux.md`
  - **验收标准**: 关联 Safety Tags、BorrowSanitizer、Tree Borrows、AutoVerus/Verus 的链接可点击且指向正确。
  - **依赖**: D5.2。

---

### Week 6：TRPL 3rd / Brown Book 对齐启动（2026-07-28 ~ 2026-08-03）

| 维度 | 内容 |
| :--- | :--- |
| **主题** | 权威教材对齐：所有权/借用/async 逐章对照 |
| **整体目标** | 建立 TRPL 3rd / Brown Rust Book 与项目文档的映射表。 |

#### 任务清单

- [ ] **F6.1** 建立 TRPL 3rd 对照映射表
  - **新建文件**: `docs/00_meta/TRPL_3RD_ALIGNMENT_2026_07.md`
  - **验收标准**:
    - 列出 TRPL 3rd 各章对应的项目文件路径。
    - 对 `concept/01_foundation/` 所有权/借用章节标注 Brown Book 研究引用。
    - 对 `concept/03_advanced/async.md` 标注 TRPL Ch17 对齐说明。
  - **依赖**: 无。

- [ ] **F6.2** Brown Book 所有权研究引用落地
  - **修改文件**:
    - `concept/01_foundation/01_ownership.md`
    - `concept/01_foundation/02_borrowing.md`
    - `concept/01_foundation/03_lifetimes.md`
  - **验收标准**: 每篇在“参考与延伸阅读”新增 Brown Rust Book 对应章节链接与一句话对照说明。
  - **依赖**: 无。

- [ ] **F6.3** `async.md` TRPL Ch17 对齐
  - **修改文件**: `concept/03_advanced/async.md`
  - **验收标准**: 文档顶部或结尾明确引用 TRPL Ch17，并说明项目内容与 TRPL 的差异/补充点。
  - **依赖**: 无。

---

### Week 7：编译器/Cargo 深度内容推进（2026-08-04 ~ 2026-08-10）

| 维度 | 内容 |
| :--- | :--- |
| **主题** | rustc query system / trait solver / MIR / codegen / Cargo resolver v3 |
| **整体目标** | 将 E 工作流从“概念页存在”推进到“有示例、有图解、有练习”。 |

#### 任务清单

- [ ] **E7.1** rustc query system 实践章节
  - **修改文件**: `concept/04_formal/19_rustc_query_system.md`
  - **验收标准**: 新增“如何阅读 rustc 源码”小节；包含 `rustc_driver` 入口点说明与 `-Z query-dep-graph` 示例。
  - **依赖**: 无。

- [ ] **E7.2** trait solver 对比示例
  - **修改文件**: `concept/04_formal/26_trait_solver_in_rustc.md`
  - **验收标准**: 新增“旧 solver vs 新 solver”行为差异示例（至少 1 个可编译、1 个 `rust,ignore` 说明）。
  - **依赖**: 无。

- [ ] **E7.3** Cargo resolver v3 / public-private deps 示例
  - **修改文件**: `concept/06_ecosystem/60_cargo_dependency_resolution.md`
  - **验收标准**: 更新 resolver v3 状态；补充 `public = true` 用法示例。
  - **依赖**: 无。

- [ ] **E7.4** 新增 L4 编译器测验
  - **新建文件**: `exercises/tests/quizzes/l4_compiler.rs`
  - **命令**: `cd exercises && cargo test --test quizzes`
  - **验收标准**: 至少 6 个测验，覆盖 query system / trait solver / MIR 基础概念。
  - **依赖**: E7.1 ~ E7.3。

---

### Week 8：生态迁移与 1.98 预览刷新（2026-08-11 ~ 2026-08-17）

| 维度 | 内容 |
| :--- | :--- |
| **主题** | Sea-ORM 2.0 / AFIDT / WASI 生态迁移 + nightly 1.98 状态刷新 |
| **整体目标** | 生态文档与上游最新状态对齐；为 8 月 20 日 nightly 1.99 切换做准备。 |

#### 任务清单

- [ ] **A8.1** 复查 Sea-ORM 2.0 stable 状态
  - **命令**:

    ```bash
    cargo search sea-orm --limit 5
    curl -s https://crates.io/api/v1/crates/sea-orm | jq '.crate.max_stable_version, .crate.newest_version'
    ```

  - **修改文件**:
    - `reports/SEA_ORM_2_0_RELEASE_TRACKING_2026_06_22.md`
    - 含 Sea-ORM 的文档与 `Cargo.toml`
  - **验收标准**:
    - 若已发布 2.0.0 stable：评估并执行升级。
    - 若未发布：更新跟踪日期与版本号，代码侧保持现状。
  - **依赖**: 上游发布状态。

- [ ] **A8.2** AFIDT / `dyn async Trait` 状态刷新
  - **命令**: 检查 <https://github.com/rust-lang/rust/issues/133882>
  - **修改文件**: 所有含 AFIDT 跟踪标记的文档
  - **验收标准**: 文档状态与 tracking issue 最新标签一致。
  - **依赖**: 上游状态。

- [ ] **A8.3** 刷新 `concept/07_future/rust_1_98_preview.md`
  - **验收标准**:
    - 更新 Pin ergonomics / Reborrow traits / Field Projections / RTN / async drop 进展。
    - 补充 2026-08 以来 nightly 示例。
  - **依赖**: nightly 1.98 实际状态。

- [ ] **A8.4** WASI 目标再次确认
  - **命令**: `rustup target list | grep wasi`
  - **验收标准**: `wasm32-wasi` 旧名未再使用；示例统一为 `wasm32-wasip1` / `wasm32-wasip2`。
  - **依赖**: 无。

---

### Week 9：国际化与社区验证准备（2026-08-18 ~ 2026-08-24）

| 维度 | 内容 |
| :--- | :--- |
| **主题** | i18n 策略落地 + 学习路径可用性评估 + 社区验证计划 |
| **整体目标** | 为 2026 Q4 国际化与教师反馈做准备；整理英文版 MVP 路径骨架。 |

#### 任务清单

- [ ] **I9.1** 确认 i18n 策略文档
  - **修改文件**: `concept/00_meta/LEARNING_MVP_PATH.md`
  - **验收标准**: 在文件顶部明确“中文为主 + 关键术语中英双语 + 代码注释英文”策略。
  - **依赖**: 无。

- [ ] **I9.2** 生成英文版 MVP 路径骨架
  - **新建文件**: `docs/00_meta/LEARNING_MVP_PATH_EN.md`
  - **验收标准**:
    - 只翻译目录结构与关键术语，不翻译大段教学文本。
    - 链接指向中文原文，标注 `(Chinese)`。
  - **依赖**: `LEARNING_MVP_PATH.md` 内容稳定。

- [ ] **I9.3** 社区验证计划草稿
  - **新建文件**: `reports/I18N_COMMUNITY_VALIDATION_PLAN_2026_Q4.md`
  - **验收标准**: 包含可用性测试方案、教师反馈渠道、社区背书目标、时间节点。
  - **依赖**: 无。

- [ ] **I9.4** 关键术语双语标注第二批
  - **命令**: `scripts/add_bilingual_annotations.py concept/04_formal/ concept/06_ecosystem/`
  - **验收标准**: 至少 50 个新增术语标注；运行 `scripts/check_links.py` 无新增断链。
  - **依赖**: 无。

---

### Week 10：8 月收尾与 Q4 规划（2026-08-25 ~ 2026-08-31）

| 维度 | 内容 |
| :--- | :--- |
| **主题** | 月度健康检查 + 8 月总结 + Q4 计划细化 |
| **整体目标** | 固化 8 月成果；输出 9 月与 Q4 执行草案。 |

#### 任务清单

- [ ] **R10.1** 8 月全量健康检查
  - **命令**:

    ```bash
    cargo check --workspace
    cargo test --workspace
    cargo clippy --workspace --all-features -- -D warnings
    cargo audit --no-fetch
    scripts/check_links.py
    scripts/docs_value_audit.py docs --days-old 90
    ```

  - **验收标准**:
    - 编译/测试/Clippy/审计全绿。
    - 损坏链接数 ≤ 5（或 0）。
    - C-class 问题数 ≤ 150（目标 100）。
  - **依赖**: 无。

- [ ] **R10.2** 生成 8 月进度摘要
  - **新建文件**: `.kimi/WEEKLY_PROGRESS_2026_08_31.md`
  - **验收标准**: 覆盖 A/B/C/D/E/F/I 各工作流、关键数字、阻塞项、9 月计划。
  - **依赖**: R10.1。

- [ ] **R10.3** 起草 9 月执行草案
  - **新建文件**: `.kimi/EXECUTION_CHECKLIST_2026_09.md`
  - **验收标准**:
    - 包含 Rust 1.98 beta（8/20）跟进、Rust 1.99 nightly 新特性、Safety-Critical 工作组评估启动。
    - 与 Q4 i18n/社区验证计划衔接。
  - **依赖**: I9.3。

---

## 3. Pre-1.97 冲刺期（2026-06-25 ~ 2026-07-08）

> 本阶段只做**不受上游阻塞**的 P1 任务，确保 07-09 当天只执行需要上游实际发布的步骤。

### 3.1 全局事实修正

| 主题 | 权威事实 | 修改范围 | 命令示例 | 验收标准 |
| :--- | :--- | :--- | :--- | :--- |
| **async closures** | 1.85.0 stable | `concept/03_advanced/24_async_closures.md` 及全仓库 | `grep -R "nightly.*async.*closure" concept/ knowledge/ docs/ --include="*.md"` | 所有相关位置标注 `1.85.0 stable`；移除 nightly 警告 |
| **Rust 2024 Edition** | 1.85.0 stable；`gen` 保留关键字；`gen {}` nightly | `knowledge/06_ecosystem/02_edition_2024.md`、`concept/07_future/19_rust_edition_preview.md` | `grep -R "Edition 2024\|gen blocks\|gen fn" concept/ knowledge/ docs/ --include="*.md"` | 版本号统一为 `1.85.0+`；明确区分关键字与 blocks |
| **`&raw const` / `&raw mut`** | 官方语法 `&raw const T` / `&raw mut T`；1.82.0 stable | 全仓库 Markdown | `grep -R "&const" concept/ knowledge/ docs/ book/ --include="*.md"` | 无 `&const` 残留；统一术语并标注版本 |

### 3.2 Rust 1.96 覆盖缺口回填

| 特性 | 文件路径 | 命令 | 验收标准 |
| :--- | :--- | :--- | :--- |
| `assert_matches!` | `docs/06_toolchain/06_22_rust_1_96_features.md` | `cargo test --workspace` | 提供可编译示例，标注 `1.96.0` |
| `core::range` / `Range*` 改进 | 同上 | `cargo check --workspace` | 覆盖 `Range::is_empty`、边界迭代等 |
| `NonZero` 范围迭代 | 同上 + `exercises/tests/l3_rust_196_alignment.rs` | `cargo test --test l3_rust_196_alignment` | 示例 `NonZeroU32::range` 行为 |
| `AssertUnwindSafe From<T>` | 同上 | `cargo test --workspace` | 示例 `AssertUnwindSafe::from` |
| s390x inline asm | 同上 | `cargo check --workspace` | 说明目标与约束 |
| rustdoc 1.96 改进 | `docs/06_toolchain/06_22_rust_1_96_features.md` | 手动审阅 | 列出 search / trait impl 显示改进 |

### 3.3 Sea-ORM / AFIDT 状态文档更新

| 项目 | 当前状态 | 文件路径 | 验收标准 |
| :--- | :--- | :--- | :--- |
| **Sea-ORM 2.0** | 未发布；最新 rc.41 | `crates/c10_networks/Cargo.toml`、`reports/SEA_ORM_2_0_RELEASE_TRACKING_2026_06_22.md` | 注释日期更新；文档状态为“跟踪中，代码保持 1.x / rc” |
| **AFIDT / `dyn async Trait`** | 实验性；tracking issue #133882 | 所有含 `async_trait` 的文档 | 文档标注“实验性/跟踪中”；代码侧保留 `async_trait` |

### 3.4 C-class 治理 / 去重评估

| 任务 | 文件/脚本 | 目标 | 命令 | 验收标准 |
| :--- | :--- | :--- | :--- | :--- |
| C-class 问题数压降 | `scripts/docs_value_audit.py` | 从 228 降至 ≤ 150 | `scripts/docs_value_audit.py docs --days-old 90` | C-class 数 ≤ 150 |
| 归档陈旧 research notes | `scripts/maintenance/archive_research_notes_candidates.py` | 清理 60+ 天未更新文件 | `scripts/maintenance/archive_research_notes_candidates.py --stale-days 60` | 归档文件含 `[ARCHIVED]` 标记 |
| 修复归档引用残留 | `scripts/maintenance/fix_archived_research_notes_links.py` | 无断链 | 同左 | `scripts/check_links.py` 无新增内部断链 |
| 去重扫描复查 | `scripts/detect_content_overlap.py` | 确认无 ≥0.90 相似对 | `scripts/detect_content_overlap.py` | 输出无 ≥0.90 对 |

---

## 4. Rust 1.97 发布周（2026-07-07 ~ 2026-07-13）日计划

> 本节基于 `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md` 细化到每日。

### 2026-07-07（周一）—— 发布日前置最终检查

- [ ] 08:00 上游状态确认：`rustup check` 或访问 <https://releases.rs>
- [ ] 08:15 确认当前 toolchain 仍可使用；备份 `Cargo.lock`：`cp Cargo.lock Cargo.lock.pre-1.97`
- [ ] 09:00 创建发布日工作分支：`git checkout -b rust-1.97-release-day`
- [ ] 10:00 预跑全 workspace：`cargo check --workspace && cargo test --workspace`
- [ ] 11:00 更新 `.kimi/RELEASE_PREFLIGHT_2026_07_07.md` 记录当前 beta 版本与预检结果
- [ ] 14:00 再次检查 `crates/c08_algorithms/src/rust_197_features.rs` 占位注释是否清晰
- [ ] 16:00 对照 Rust 1.97 Release Notes（若提前发布）进行 A3.x 前置准备
- [ ] 18:00 输出当日简短进度到 `.kimi/WEEKLY_PROGRESS_2026_07_07.md`

### 2026-07-08（周二）—— 待命与文档预填

- [ ] 09:00 复查 <https://blog.rust-lang.org/> 是否已提前发布 1.97.0 公告
- [ ] 10:00 若公告已出：预先起草 `CHANGELOG.md [3.1.0]` 条目（但不提交）
- [ ] 14:00 若公告未出：继续完成 Week 2 剩余 P1 任务（C-class 压降 / 1.96 文档）
- [ ] 17:00 确认发布日执行环境（网络、rustup、git 权限）
- [ ] 18:00 输出当日进度

### 2026-07-09（周三）—— 发布日执行

按 `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md` 完整执行：

| 阶段 | 时间 | 任务 | 命令/文件 | 验收标准 |
| :--- | :--- | :--- | :--- | :--- |
| 0 | 09:00 ~ 09:15 | 环境确认 | `rustup check`、`rustc --version` | 1.97.0 stable 已可用 |
| 1 | 09:15 ~ 09:30 | 工具链切换 | 修改 `rust-toolchain.toml` → `channel = "1.97.0"`；`rustup show` | `rustc --version` 输出 1.97.0 |
| 2 | 09:30 ~ 11:00 | Crate 代码激活 | `crates/c08_algorithms/src/rust_197_features.rs` | `VecDeque::truncate_front` 真实 API 可用并取消注释；`retain_back` 按 Release Notes 决定是否激活 |
| 3 | 11:00 ~ 12:00 | 全 Workspace 验证 | `cargo check --workspace`、`cargo test --workspace`、`cargo clippy --workspace -- -D warnings` | 0 错误、0 warning |
| 4 | 13:00 ~ 15:00 | 文档状态刷新 | `concept/07_future/rust_1_97_preview.md` → 迁移到 `docs/06_toolchain/06_21_rust_1_97_features.md` | 状态标记更新为 ✅ Stable；原文件加重定向说明 |
| 5 | 15:00 ~ 16:30 | 练习补全 | `exercises/tests/` 新增 1.97 特性测验 | `cd exercises && cargo test` 通过 |
| 6 | 16:30 ~ 17:30 | CHANGELOG 与版本号 | `CHANGELOG.md [3.1.0]`、workspace version | 条目完整；若使用语义化版本则更新 `Cargo.toml` |
| 7 | 17:30 ~ 18:00 | 提交与归档 | `git commit -m "chore: stabilize Rust 1.97.0 support"`、创建 PR、更新主控清单 | 代码进入 review/合并流程 |

### 2026-07-10（周四）—— 发布日收尾

- [ ] 09:00 确认 PR 已创建或代码已合并
- [ ] 10:00 更新 `concept/00_meta/terminology_glossary.md` 中 1.97 术语状态
- [ ] 11:00 搜索全仓库 `1.97` / `nightly` 标记，统一刷新状态
- [ ] 14:00 运行 `cargo test --workspace` 验证合并后状态
- [ ] 16:00 更新 `.kimi/EXECUTION_CHECKLIST_2026_06_22.md` 中 A3.x 为完成
- [ ] 18:00 输出当日进度

### 2026-07-11（周五）—— 发布日归档

- [ ] 09:00 将 `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md` 归档到 `archive/project_reports/`
- [ ] 10:00 生成 `.kimi/WEEKLY_PROGRESS_2026_07_11.md`（Week 3 总结）
- [ ] 14:00 运行 `scripts/check_links.py` 确认迁移未引入断链
- [ ] 16:00 运行 `scripts/docs_value_audit.py docs --days-old 90` 记录发布日后 C-class 基数
- [ ] 18:00 周末封版前最终 `cargo check --workspace`

### 2026-07-12（周六）—— 休息日/可选补充

- [ ] （可选）审阅社区反馈或修复发布日遗留小问题
- [ ] （可选）更新 `concept/07_future/rust_1_98_preview.md` 中 1.97 相关背景

### 2026-07-13（周日）—— 周切换准备

- [ ] 10:00 确认 Week 3 所有 A3.x 条目关闭
- [ ] 12:00 准备 Week 4 任务环境（编译器/Cargo 深度内容 Phase 2）
- [ ] 16:00 输出 Week 3 最终关闭报告

---

## 5. Post-1.97 稳定化（2026-07-14 ~ 2026-07-20）

> 本阶段将发布日工作固化为可交付版本，并启动 P2 深度内容。

### 5.1 CHANGELOG 与版本收尾

| 任务 | 文件 | 命令 | 验收标准 |
| :--- | :--- | :--- | :--- |
| 最终回填 `[3.1.0]` 条目 | `CHANGELOG.md` | `git diff CHANGELOG.md` | 包含 1.97 API、文档、测试、工具链升级摘要 |
| 更新 workspace version | 根 `Cargo.toml` | `cargo check --workspace` | version 与 CHANGELOG 一致 |
| 关闭发布日清单 | `.kimi/EXECUTION_CHECKLIST_2026_06_22.md` | 手动勾选 A3.x | 所有 A3.x 为 ✅ |
| 归档发布日清单 | `archive/project_reports/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md` | `cp` + 标记 | 原文件顶部含 `[ARCHIVED]` |

### 5.2 迁移、测试、归档

| 任务 | 文件/命令 | 验收标准 |
| :--- | :--- | :--- |
| 迁移 1.97 预览文档 | `concept/07_future/rust_1_97_preview.md` → `docs/06_toolchain/06_21_rust_1_97_features.md` | 原文件含重定向说明；新文件状态全为 ✅ Stable |
| 新增 1.97 练习 | `exercises/tests/l3_rust_197_alignment.rs` | `cargo test --test l3_rust_197_alignment` 通过 |
| 全 workspace 回归 | `cargo test --workspace` | 全绿 |
| 术语表更新 | `concept/00_meta/terminology_glossary.md` | 1.97 术语状态改为 ✅ Stable |
| 链接检查 | `scripts/check_links.py` | 无新增内部断链 |

### 5.3 启动 P2 深度内容

| 任务 | 文件 | 验收标准 |
| :--- | :--- | :--- |
| rustc query system 实践 | `concept/04_formal/19_rustc_query_system.md` | 新增示例或阅读指引 |
| trait solver 深度 | `concept/04_formal/26_trait_solver_in_rustc.md` | 新增新旧 solver 对比示例 |
| LLVM backend / codegen | `concept/06_ecosystem/67_llvm_backend_and_codegen.md` | 新增 MIR → LLVM IR 流程说明 |
| Cargo resolver v3 | `concept/06_ecosystem/60_cargo_dependency_resolution.md` | 更新 v3 状态与 `public` 示例 |

---

## 6. 2026 Q3 / Q4 规划要点

> 本排期覆盖到 8 月底；Q3 后续与 Q4 作为滚动规划，在 Week 10 细化。

### 6.1 Q3 剩余重点（2026-09-01 ~ 2026-09-30）

| 主题 | 关键任务 | 预计文件 | 依赖 |
| :--- | :--- | :--- | :--- |
| **Rust 1.98 beta 跟进** | 8/20  nightly 1.99 切换后，刷新 `rust_1_98_preview.md` | `concept/07_future/rust_1_98_preview.md` | Rust 1.98 beta 发布 |
| **Rust 1.99 nightly 新特性** | Pin ergonomics / Reborrow traits / Field Projections / RTN / async drop | `crates/c02_type_system/src/rust_198_features.rs` | nightly 实际特性 |
| **形式化工具可运行示例** | Kani 循环合约、Verus 规范示例、Miri Tree Borrows | `crates/c01_ownership_borrow_scope/src/kani_examples.rs`、`crates/c04_generic/src/kani_examples.rs` | 工具链可用 |
| **编译器/Cargo 深度** | rustc query system、MIR、Cargo resolver v3、build scripts | `concept/04_formal/19_*`、`concept/06_ecosystem/60_*`、`59_*`、`62_*`、`63_*` | 无 |

### 6.2 Q4 重点（2026-10-01 ~ 2026-12-31）

| 主题 | 关键任务 | 预计文件/活动 | 依赖 |
| :--- | :--- | :--- | :--- |
| **国际化与社区验证** | 可用性测试、教师反馈、社区背书、英文版 LEARNING_MVP_PATH | `reports/I18N_COMMUNITY_VALIDATION_PLAN_2026_Q4.md`、`docs/00_meta/LEARNING_MVP_PATH_EN.md` | 内部内容质量基线 |
| **TRPL 3rd / Brown Book 对齐** | 逐章对照审计、所有权文档引用 Brown 研究 | `docs/00_meta/TRPL_3RD_ALIGNMENT_2026_*.md` | TRPL 3rd 出版进度 |
| **Safety-Critical 工作组落地** | 负责人/预算/认证体系/培训试点评估 | `reports/SAFETY_CRITICAL_ROADMAP_2026_Q4.md` | 组织决策 |
| **Rust 1.98 稳定化** | 按 `.kimi/EXECUTION_RUST_1_98_RELEASE_*.md` 执行 | `rust-toolchain.toml`、`CHANGELOG.md [3.2.0]` | Rust 1.98.0 stable 发布 |

---

## 7. 每日/每周例行仪式

> 每周必须执行；可集中在周一上午或周五下午完成。

### 每日（工作日）

| 仪式 | 命令 | 通过标准 |
| :--- | :--- | :--- |
| 编译基线 | `cargo check --workspace` | 0 错误 |
| 快速测试 | `cargo test --workspace`（或受影响 crate） | 0 失败 |

### 每周（建议周五下午）

| 仪式 | 命令 | 通过标准 |
| :--- | :--- | :--- |
| 全量检查 | `cargo check --workspace && cargo clippy --workspace --all-features -- -D warnings && cargo test --workspace` | 全绿 |
| 安全审计 | `cargo audit --no-fetch` | 0 安全漏洞；`unmaintained` 已记录 rationale |
| 链接检查 | `python scripts/check_links.py` | 新增内部链接无断链；外部链接失败记录到 `reports/` |
| 文档价值审计 | `python scripts/docs_value_audit.py docs --days-old 90` | C-class 问题数 ≤ 150（目标 100） |
| 去重扫描 | `python scripts/detect_content_overlap.py` | 无 ≥0.90 相似对 |
| 进度摘要 | 新建 `.kimi/WEEKLY_PROGRESS_2026_MM_DD.md` | 包含本周完成、关键数字、阻塞项、下周计划 |

### 每月（最后一个工作日）

| 仪式 | 命令/活动 | 通过标准 |
| :--- | :--- | :--- |
| 月度健康报告 | 汇总 4 次周审计结果 | 输出 `reports/MONTHLY_HEALTH_2026_0X.md` |
| 依赖升级评估 | `cargo update --dry-run` | 记录可升级依赖与风险 |
| 主控清单刷新 | 更新 `.kimi/EXECUTION_CHECKLIST_2026_*.md` | 关闭已完成条目，滚动新增下月任务 |
| 归档旧进度文件 | 移动 60 天前 `.kimi/WEEKLY_PROGRESS_*.md` 到 `archive/` | 目录整洁 |

---

## 8. 风险与 Fallback 动作

| 风险 | 影响范围 | Fallback 动作 | 触发条件 |
| :--- | :--- | :--- | :--- |
| **Rust 1.97.0 某特性未如期稳定**（尤其 `retain_back`） | A3.3、A3.5、A3.6、A3.7 | 在 `rust_197_features.rs`、`rust_1_97_preview.md`、`CHANGELOG.md` 中标注“推迟至 1.98”，保留等效实现 | 07-09 Release Notes 未包含该特性 |
| **`cargo audit` 网络不可用** | 安全审计 | 使用 `.cargo/audit.toml` 本地配置 + `--no-fetch`；必要时用 `scripts/supply_chain_audit.py` 手动解析 | `cargo audit` 拉取 advisory-db 失败 |
| **Sea-ORM 2.0 stable 继续延迟** | 生态迁移 | 文档侧持续跟踪 rc 版本；代码侧保持 1.x / rc；评估是否回退 1.x（当前不建议） | 08-31 仍未发布 |
| **AFIDT / `dyn async Trait` 未 stable** | `async_trait` 移除 | 文档标注为“实验性/跟踪中”；代码侧继续保留 `async_trait` | 年内未稳定 |
| **Kani 0.66 与 nightly 不兼容** | 形式化示例 | 降级到 Kani 0.65；示例改为 `rust,ignore` 并标注原因 | `cargo kani` 构建失败 |
| **C-class 文件治理进度落后** | 内容质量 | 优先处理 `docs/research_notes/` 与 `docs/rust-ownership-decidability/`；按目录分批；必要时提高归档阈值 | Week 2 结束时 C-class 数 > 200 |
| **多版 roadmap 口径不一致** | 执行混乱 | 严格以本排期与 `.kimi/EXECUTION_CHECKLIST_2026_06_22.md` 为主控；早期 `EXECUTION_PLAN_*` 仅作历史参考 | 出现任务来源争议 |
| **发布日当天网络/工具链异常** | A3.x 全部 | 使用已下载的 beta/nightly 工具链先行本地验证；延迟到次日网络恢复后补跑 | `rustup` 无法下载 1.97.0 |

---

## 9. 附录：常用命令速查

```bash
# 编译与测试
cargo check --workspace
cargo test --workspace
cargo clippy --workspace --all-features -- -D warnings

# 安全审计
cargo audit --no-fetch

# 文档质量与链接
python scripts/check_links.py
python scripts/docs_value_audit.py docs --days-old 90
python scripts/detect_content_overlap.py

# 去重与归档
python scripts/maintenance/archive_research_notes_candidates.py --stale-days 60
python scripts/maintenance/fix_archived_research_notes_links.py

# 双语标注
python scripts/add_bilingual_annotations.py concept/01_foundation/ concept/02_intermediate/ concept/03_advanced/

# 工具链确认
rustup show
rustc --version
```

---

*本文件基于 `.kimi/PROJECT_PENDING_PLANS_ALIGNMENT_CONFIRM_2026_06_25.md` 与 `.kimi/EXECUTION_CHECKLIST_2026_06_22.md` 生成，未修改任何项目源文件。*
