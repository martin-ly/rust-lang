# P2-Q3 滚动深化执行计划（2026-07-21 ~ 09-30）

> **计划层级**: P2 — 第三季度滚动深化任务
> **时间范围**: 2026-07-21 ~ 2026-09-30
> **目标**: 完成编译器/Cargo 深度内容、形式化工具示例、生态迁移跟踪、权威教材对齐，为 Q4 国际化与社区验证奠定内容基础。
> **用户确认**: 2026-07-09 确认执行并全部完成
> **状态**: ✅ 全部 11 项任务已完成（2026-07-09）

---

## 1. 执行原则

1. **质量门禁优先**: 每项任务完成后必须跑通 `cargo check/test/clippy --workspace`、`python scripts/kb_auditor.py`、`python scripts/detect_content_overlap.py`。
2. **Canonical 唯一来源**: 新增或修改的概念解释优先归入 `concept/`；`knowledge/`/`docs/` 仅保留摘要、重定向或专项深入。
3. **可验证产出**: 每个任务必须对应一个可验证的产出物（文件、示例、报告、映射表）。
4. **阻塞透明**: 遇到上游未稳定、工具链不支持等情况，立即记录到本文件 §6 阻塞项，不强行推进。

---

## 2. 任务总览

| 编号 | 任务 | 模块 | 负责人 | 目标产出 | 建议月份 |
|---|---|---|---|---|---|
| P2-11 | `concept/03_advanced/01_async/02_async.md` 顶部标注对应 TRPL Ch17 | 教材对齐 | TBD | 单文件更新 | 7 月下旬 |
| P2-9 | TRPL 3rd Ed 逐章对照表落地到 `learning_mvp_path.md` | 教材对齐 | TBD | 完整映射表 | 7 月下旬 ~ 8 月上旬 |
| P2-1 | 完善 `concept/04_formal/19_rustc_query_system.md` 实践章节 | 编译器 | TBD | 新增实践章节 | 7 月下旬 |
| P2-5 | Kani 函数/循环合约示例扩展到 `c03_control_fn`、`c04_generic` | 形式化工具 | TBD | Kani 示例代码 | 7 月下旬 ~ 8 月上旬 |
| P2-10 | Brown Book 所有权研究引用在所有权文档中显式落地 | 教材对齐 | TBD | 引用段落/页 | 8 月上旬 |
| P2-2 | 在 `concept/04_formal/26_trait_solver_in_rustc.md` 增加 new solver 对比示例 | 编译器 | TBD | 对比示例 + 说明 | 8 月上旬 |
| P2-6 | Safety Tags / BorrowSanitizer / AutoVerus / Tree Borrows 概念页交叉引用并加入 SUMMARY | 形式化工具 | TBD | 交叉引用 + SUMMARY 更新 | 8 月中旬 |
| P2-3 | Cargo resolver v3 / `public = true` 示例 | Cargo | TBD | 可运行 workspace 示例 | 8 月中旬 |
| P2-7 | Sea-ORM 2.0 stable 迁移评估 | 生态迁移 | TBD | 评估报告 | 8 月中旬 ~ 9 月上旬 |
| P2-8 | AFIDT / dynosaur / WASI 目标再次确认 | 生态迁移 | TBD | 状态更新报告 | 9 月上旬 |
| P2-4 | MIR / codegen / LLVM 入门内容补齐 | 编译器 | TBD | 新增/完善概念页 | 8 月下旬 ~ 9 月上旬 |

---

## 3. 详细任务拆解

### 模块一：编译器 / Cargo 深度（P2-1 / P2-2 / P2-3 / P2-4）

#### P2-1: 完善 `concept/04_formal/19_rustc_query_system.md` 实践章节

- **目标**: 让 query system 概念页从纯理论变为“可动手”。
- **关键动作**:
  1. 阅读 rustc 源码中 `compiler/rustc_middle/src/ty/context.rs` 的 `TyCtxt` 定义。
  2. 选取一个最小 query（如 `type_of` 或 `predicates_of`），画出调用链。
  3. 在文档中增加一个“动手”小节：展示如何通过 `rustc_interface` 或 `rustc_driver` 调用 query（如果可行），或用伪代码 + 注释说明。
  4. 使用 Mermaid/ASCII 图替代 Aquascope 可视化。
- **验收标准**:
  - 文件包含 ≥1 个 code block 或 diagram。
  - 文件顶部保留 **EN** 标题和 **Summary** 摘要。
  - `python scripts/kb_auditor.py` 通过。
- **风险**: 依赖 rustc nightly 源码，示例可能随版本变化。若 `rustc_interface` 在当前 nightly 不可用，改为纯源码走读 + 图示。

#### P2-2: 在 `concept/04_formal/26_trait_solver_in_rustc.md` 增加 new solver 对比示例

- **目标**: 解释 rustc 中 old solver 与 new trait solver（`-Ztrait-solver=next`）的差异。
- **关键动作**:
  1. 准备 1~2 个典型 trait 解析场景（如 `impl Trait for T where T: TraitA + TraitB` 的嵌套解析）。
  2. 展示在 old solver 与 new solver 下的行为差异（通过 `rustc +nightly -Ztrait-solver=next`）。
  3. 在文档中增加对比表格和最小可复现示例。
- **验收标准**:
  - 文档包含 old/new solver 对比表。
  - 至少 1 个可运行的 `.rs` 示例或 shell 命令块。
  - 新增示例通过 `cargo +nightly check`（如放入 `crates/` 需加 `cfg(nightly)`）。

#### P2-3: Cargo resolver v3 / `public = true` 示例

- **目标**: 用可运行示例说明 resolver v3 和 public dependency 如何解决 feature unification 问题。
- **关键动作**:
  1. 在 `crates/` 下新建一个最小 workspace（或在现有 workspace 中新增示例 crate）。
  2. 设计一个场景：crate A 依赖 crate B 和 crate C，B 和 C 都依赖 D；通过 `public = true` 让 A 能看到 D 的 feature 而 B/C 的内部 feature 不互相污染。
  3. 用 `cargo tree -e features` 展示差异。
  4. 在 `concept/` 或 `docs/` 写配套解释页。
- **验收标准**:
  - workspace 可在 stable Rust 下 `cargo check` / `cargo tree`。
  - 文档说明 resolver v3 与 v2 的关键差异。
  - 不引入新的 nightly dependency。

#### P2-4: MIR / codegen / LLVM 入门内容补齐

- **目标**: 在 `concept/04_formal/` 下补齐 MIR 基础与 codegen 入门内容。
- **关键动作**:
  1. 确认现有 `concept/04_formal/` 中 MIR 相关内容位置，避免重复。
  2. 新增或完善一个页面，包含：
     - 什么是 MIR 及其在 rustc pipeline 中的位置。
     - 如何用 `rustc +nightly --emit=mir` 查看 MIR。
     - 一个最小示例的 MIR 片段解读。
     - MIR opt level 的演示（`-Z mir-opt-level=0..3`）。
  3. 简要提及 codegen / LLVM IR 的入口，但不深入 LLVM 细节。
- **验收标准**:
  - 新增/更新文件通过 kb auditor。
  - 至少 2 个可复现的 shell 命令示例。
  - 概念页链接到 rustc book 或 rustc dev guide。

---

### 模块二：形式化工具扩展（P2-5 / P2-6）

#### P2-5: Kani 函数/循环合约示例扩展到 `c03_control_fn`、`c04_generic`

- **目标**: 在现有 `c06_async` Kani 示例基础上，向控制流和泛型 crate 扩展。
- **关键动作**:
  1. 在 `crates/c03_control_fn/` 下新增 `kani_proofs/` 或 `tests/kani/` 目录。
  2. 编写 2~3 个证明：
     - 函数合约（pre/post condition）。
     - 循环不变式（loop invariant）。
     - 边界条件验证（如 `for` 循环不越界）。
  3. 在 `crates/c04_generic/` 下编写泛型函数/Trait bound 的 Kani 证明示例。
  4. 更新对应 `concept/` 页面，链接到示例。
- **验收标准**:
  - 每个 Kani 示例可在 Linux/WSL nightly 下 `cargo kani` 通过。
  - 在 Windows 上至少保证 `cargo check` 不失败（用 `cfg` 或文档说明）。
  - 新增代码通过 clippy。

#### P2-6: Safety Tags / BorrowSanitizer / AutoVerus / Tree Borrows 概念页交叉引用并加入 SUMMARY

- **目标**: 把形式化/内存模型相关概念页织成网，提升可发现性。
- **关键动作**:
  1. 定位以下概念页（如存在）：
     - Safety Tags / Stacked Borrows / Tree Borrows
     - BorrowSanitizer / MIRI
     - AutoVerus / Verus
  2. 在每页底部增加 "See also" 或 "Related" 小节，链接到其他相关页。
  3. 检查 `concept/SUMMARY.md`，将未链接的页面加入对应章节。
  4. 如发现某主题缺失，创建一个重定向 stub 指向最相关的页面。
- **验收标准**:
  - 所有相关页都有 ≥1 个交叉引用。
  - `concept/SUMMARY.md` 包含这些页面。
  - 无新增重复内容。

---

### 模块三：生态迁移跟踪（P2-7 / P2-8）

#### P2-7: Sea-ORM 2.0 stable 迁移评估

- **目标**: 评估 Sea-ORM 2.0 对本项目示例/文档的影响，形成迁移指南或决策记录。
- **关键动作**:
  1. 监控 Sea-ORM 2.0 发布状态（当前 2.0.0-rc.41）。
  2. 若 9 月底前发布 stable：
     - 找出项目中所有使用 Sea-ORM 的位置（`crates/`、`examples/`、`docs/`）。
     - 列出破坏性变更。
     - 给出迁移步骤和示例代码更新。
  3. 若未发布 stable：
     - 输出一份 "rc 预览评估"，标注风险与预计迁移时间。
- **验收标准**:
  - 产出一份 Markdown 报告，放入 `reports/` 或 `docs/06_ecosystem/`。
  - 报告包含受影响文件清单、变更点、迁移步骤。
  - 如有代码改动，通过 `cargo check/test`。

#### P2-8: AFIDT / dynosaur / WASI 目标再次确认

- **目标**: 更新三个实验性生态特性的跟踪状态。
- **关键动作**:
  1. AFIDT（async fn in dyn trait）: 确认是否已稳定或仍需 `async_trait` / `dynosaur`。
  2. dynosaur: 检查最新版本与 stable 兼容性。
  3. WASI: 确认 `wasm32-wasip1` / `wasm32-wasip2` 目标状态，更新相关示例。
  4. 更新 `concept/07_future/` 中的对应跟踪页。
- **验收标准**:
  - 每个特性都有当前状态说明（stable / nightly / experimental）。
  - 文档中包含最小可运行示例或明确说明不可运行原因。
  - 无过期链接。

---

### 模块四：权威教材对齐（P2-9 / P2-10 / P2-11）

#### P2-9: TRPL 3rd Ed 逐章对照表落地到 `learning_mvp_path.md`

- **目标**: 建立 TRPL 第 3 版 22 章与本项目 `concept/` 页面的完整映射。
- **关键动作**:
  1. 获取 TRPL 3rd Ed 目录结构（22 章）。
  2. 为每一章找到本项目中最接近的 `concept/` 页面（可能多对多）。
  3. 在 `learning_mvp_path.md` 中新增 "TRPL 3rd Ed 对照表" 章节。
  4. 对缺失覆盖的章节，标注 "待补充" 并链接到相关 issue 或计划。
- **验收标准**:
  - 22 章全部有映射条目。
  - 每个条目包含链接。
  - 通过 kb auditor 死链检查。

#### P2-10: Brown Book 所有权研究引用在所有权文档中显式落地

- **目标**: 在所有权相关文档中显式引用 Brown University 所有权研究（如 *Amber* / *Oxide* / *Aeneas* 等）。
- **关键动作**:
  1. 确认 Brown Book / 相关论文的权威链接。
  2. 选择 1~2 个合适的 `concept/01_foundation/ownership/` 页面或 `docs/rust-ownership-decidability/` 页面。
  3. 新增 "学术背景" 或 "延伸阅读" 小节，列出引用并简要说明与本项目解释的关系。
- **验收标准**:
  - 至少 1 个页面新增 Brown Book 引用。
  - 引用格式统一（建议使用 APA/MLA 或项目既定格式）。
  - 无版权问题，仅引用公开链接或 bibtex。

#### P2-11: `concept/03_advanced/01_async/02_async.md` 顶部标注对应 TRPL Ch17

- **目标**: 明确 async 概念页与 TRPL 教材的对应关系。
- **关键动作**:
  1. 在 `02_async.md` 顶部新增一个提示框："本页对应 TRPL 3rd Ed Chapter 17: Async and Await"。
  2. 简要说明本页覆盖范围与 TRPL 章节的异同。
- **验收标准**:
  - 单文件改动，不影响其他内容。
  - 通过 kb auditor。

---

## 4. 时间线

### 7 月下旬（07-21 ~ 07-31）

- [ ] P2-11: `02_async.md` 标注 TRPL Ch17
- [ ] P2-9: TRPL 对照表（启动，完成 ≥50%）
- [ ] P2-1: rustc query system 实践章节
- [ ] P2-5: Kani 示例扩展（启动）

### 8 月

- [ ] P2-9: TRPL 对照表（收尾）
- [ ] P2-10: Brown Book 引用落地
- [ ] P2-2: trait solver 对比示例
- [ ] P2-5: Kani 示例扩展（收尾）
- [ ] P2-6: 形式化工具交叉引用 + SUMMARY
- [ ] P2-3: Cargo resolver v3 / public = true 示例
- [ ] P2-7: Sea-ORM 2.0 迁移评估（启动）

### 9 月

- [ ] P2-7: Sea-ORM 2.0 迁移评估（收尾）
- [ ] P2-8: AFIDT / dynosaur / WASI 状态确认
- [ ] P2-4: MIR / codegen / LLVM 入门补齐
- [ ] Q3 复盘与质量门禁回归

---

## 5. 验收与质量门禁

每项任务完成后必须通过：

```bash
# Rust 侧
cargo check --workspace
cargo test --workspace
cargo clippy --workspace --tests -- -D warnings

# 文档侧
python scripts/kb_auditor.py
python scripts/detect_content_overlap.py
python scripts/lint_filenames.py --all

# 供应链（按需）
cargo vet
cargo audit --no-fetch
```

如某任务需要 nightly feature，必须在 `crates/` 中用 `cfg(nightly)` 隔离，并在文档中说明。

---

## 6. 阻塞项与风险

| 编号 | 阻塞项 | 影响任务 | 当前状态 | 应对策略 |
|---|---|---|---|---|
| B-1 | Aquascope 集成阻塞 | P2-1 / P2-2 可视化 | 不可用 | 用 Mermaid/ASCII 替代 |
| B-2 | `#[optimize]` / `ptr::try_cast_aligned` / ATPIT 等未稳定 | P2-2 / P2-4 | 上游未稳定 | 不纳入 P2-Q3，仅跟踪 |
| B-4 | Sea-ORM 2.0 stable 未发布 | P2-7 | 当前 rc.41 | 若 9 月底未 stable，改为 rc 预览评估 |
| B-5 | AFIDT / dyn async trait 实验性 | P2-8 | 稳定概率低 | 仅做状态跟踪，不承诺示例 |
| B-7 | `mdbook-i18n-helpers` 是否引入 | P2 文档结构 | 待 Q4 决策 | 不影响 P2，Q4 做 POC |

---

## 7. 关联文件

- 上级计划: `.kimi/SUSTAINABLE_IMPROVEMENT_PLAN_2026_06_28_CONFIRMED.md`
- 发布日清单: `.kimi/archive/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md`
- Q4 国际化计划: `.kimi/archive/I18N_Q4_2026_PLAN.md`
- 术语表: `concept/00_meta/terminology_glossary.md`
- 学习路径: `docs/01_learning/learning_mvp_path.md`

---

## 8. 完成总结（2026-07-09）

全部 11 项任务已执行完毕，质量门禁全部通过。

| 编号 | 完成状态 | 关键产出 |
|---|---|---|
| P2-11 | ✅ | `concept/03_advanced/01_async/02_async.md` 顶部 TRPL Ch17 提示框 + 节次映射 |
| P2-9 | ✅ | `docs/01_learning/learning_mvp_path.md` TRPL 3rd Ed 22 章全映射表 |
| P2-1 | ✅ | `concept/04_formal/05_rustc_internals/19_rustc_query_system.md` 新增动手实验章节 |
| P2-5 | ✅ | `crates/c03_control_fn/src/kani_examples.rs` + `crates/c04_generic/src/kani_examples.rs` 函数/循环合约示例 |
| P2-10 | ✅ | `concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md` Brown Book 学术引用段落 |
| P2-2 | ✅ | `concept/04_formal/05_rustc_internals/26_trait_solver_in_rustc.md` old/new solver 对比实验 |
| P2-6 | ✅ | `concept/04_formal/04_model_checking/` 多页新增 Safety Tags / BorrowSanitizer / AutoVerus / Tree Borrows 交叉索引表 |
| P2-3 | ✅ | `crates/c17_resolver_v3_public_demo/` 可运行 workspace + `concept/06_ecosystem/01_cargo/11_resolver_v3_public_feature_unification.md` |
| P2-7 | ✅ | `reports/SEA_ORM_2_0_MIGRATION_ASSESSMENT_2026_07_09.md`（结论：No-Go，维持 rc.42） |
| P2-8 | ✅ | `reports/ECOSYSTEM_TARGET_RECONFIRMATION_2026_07_09.md`（AFIDT nightly；dynosaur 0.3.1 stable；wasm32-wasip2 Tier 2） |
| P2-4 | ✅ | `concept/04_formal/05_rustc_internals/20_mir_codegen_llvm_primer.md` 已提前在 crates/docs 整治中创建 |

**验证结果**: `cargo check/test/clippy --workspace` ✅、`python scripts/kb_auditor.py --link-check` ✅（0 死链/0 跨层）、`python scripts/detect_content_overlap.py` ✅（0 重复）、`cargo vet --locked` ✅、`cargo audit --no-fetch` ✅、`mdbook build` ✅。

---

## 9. 进度更新记录

| 日期 | 更新内容 | 更新人 |
|---|---|---|
| 2026-07-07 | 初稿完成 | Agent |
| 2026-07-09 | 全部 11 项任务完成，质量门禁通过 | Agent |

---

*本计划已执行完毕，后续工作转入 Q4 国际化与社区验证阶段。*
