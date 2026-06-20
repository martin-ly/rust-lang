> **⚠️ 历史文档提示**：
>
> 本文档包含 `async-std`、`wasm32-wasi` 等已归档或已重命名的生态引用。
> 其中技术观点反映了对应时间点的社区状态，可能与当前（Rust 1.96+）推荐实践不一致。
> 学习时请以 `concept/`、`knowledge/` 及官方文档为准。
>
> - `async-std` 已进入维护模式，新项目建议优先考虑 Tokio / smol。
> - `wasm32-wasi` 已重命名为 `wasm32-wasip1`；WASI Preview 2 目标为 `wasm32-wasip2`。

---

# Rust 分层概念知识体系 — 全球权威对齐对称差审计报告

> **审计日期**: 2026-06-08
> **项目基线**: v2.5.3 | Rust 1.96.0 stable / 1.98.0-nightly | Edition 2024
> **权威来源**: blog.rust-lang.org, releases.rs, rust-project-goals, Cargo CHANGELOG, TRPL 3rd Ed, Brown University Interactive Book, Google Comprehensive Rust
> **报告类型**: 全量对称差 (A Δ B) + 改进路线图

---

## 执行摘要

本次审计在已有报告（`COMPREHENSIVE_CRITICAL_ANALYSIS_AND_ROADMAP_2026_06_03.md`、`RUST_1_96_FULL_AUDIT_2026_05_31.md`、`RUST_195_EVOLUTION_SYMMETRIC_DIFFERENCE_ANALYSIS_2026_05_08.md`）基础上，对齐 **2026-06-08** 为止的最新国际化权威内容，发现以下关键对称差：

| 维度 | 关键发现 | 紧迫度 |
|:---|:---|:---:|
| **1.97 beta 覆盖空白** | 距离 1.97 stable（2026-07-09）仅剩 31 天，项目对 1.97 即将稳定的 15+ 项特性几乎零覆盖 | 🔴 紧急 |
| **Project Goals 2026 进展断层** | 2026-05-18 官方更新后，Cranelift（资金断裂）、cargo-script（被 block）、Polonius（#150551 已合并）、BorrowSanitizer（RustConf 演讲已接受）等状态已变更，项目未同步 | 🔴 紧急 |
| **1.98 nightly 跟踪文档滞后** | 工具链已升级至 1.98.0-nightly，但 `rust_197_preview.md` / `rust_198_preview.md` 未系统更新 30+ 个正在进行中的 stabilization PR | 🟡 高 |
| **生态过时内容残留** | async-std、static mut、wasm32-wasi、backoff、旧 async_trait 等虽已识别，但未完全清零 | 🟡 高 |
| **国际教学最佳实践** | 与 Brown University（OOPSLA Distinguished Paper）、Google Comprehensive Rust、100 Exercises 相比，缺少嵌入式测验、可视化、双语骨架、渐进式项目 | 🟡 高 |
| **内容膨胀与价值密度** | 1,773 Markdown / 46 万行文档的维护阈值已突破，需启动系统性瘦身 | 🟢 中 |

---

## 第一部分：对称差 A \ B（项目缺失的权威内容）

### 1.1 🔴 紧急：Rust 1.97 beta 特性覆盖空白

**权威来源**: [releases.rs](https://releases.rs/) | [Rust Forge](https://forge.rust-lang.org/) | GitHub rust-lang/rust stabilization PRs

以下特性已进入 **FCP / PFCP / 等待合并** 阶段，极大概率随 1.97 stable（2026-07-09）发布。项目当前几乎无任何覆盖：

| 特性 | 状态 | 影响 Crate | 建议补充方式 |
|:---|:---|:---|:---|
| `VecDeque::retain_back` / `truncate_front` | FCP 完成 | `c08_algorithms` | 新增算法示例 + 概念解释 |
| `supertrait_item_shadowing` | PFCP | `c04_generic` | trait 设计模式更新 |
| `alignment_type` / `ptr_alignment_type` | PFCP | `c02_type_system`, `c13_embedded` | 内存对齐深度文档 |
| `stack-protector` | PFCP | `c07_process`, `docs/06_toolchain` | 安全加固指南 |
| `breakpoint` function | PFCP | `c03_control_fn` | 调试工具链文档 |
| `float_algebraic` | FCP | `c08_algorithms` | 浮点优化注解 |
| `RandomSource` / `DefaultRandomSource` | 等待 t-libs-api | `c02_type_system` | 随机数源抽象 |
| `box_vec_non_null` | PFCP | `c02_type_system` | 智能指针 API |
| `int_format_into` | 等待 t-libs-api | `c02_type_system` | 格式化性能优化 |
| `proc_macro_value` | 等待 review | `c11_macro_system` | 过程宏进阶 |
| C-variadic function definitions | PFCP | `c13_embedded`, `c07_process` | FFI 深度指南 |
| `core::range::{legacy, RangeFull, RangeTo}` | FCP 完成 | `c02_type_system` | Range 体系完整性 |
| Cargo `-m` shorthand for `--manifest-path` | 1.97 已确认 | 全局 | CLI 速查更新 |
| Cargo improved `-p` error messages | 1.97 已确认 | 全局 | 工具链文档 |
| Cargo `-Zscript` edition pinning education | nightly | `docs/06_toolchain` | Cargo Script 指南更新 |

**缺失后果**: 若 1.97 发布后项目无覆盖，将出现与 1.96 发布时类似的"追前沿、忘当下"症状，学习者无法获取最新稳定特性的中文深度资料。

---

### 1.2 🔴 紧急：Rust Project Goals 2026 进展断层

**权威来源**: [Project Goals Update — April 2026](https://blog.rust-lang.org/2026/05/18/project-goals-2026-04/) (2026-05-18)

以下 Flagship/重要 Goal 的状态自 2026-05-08 报告以来已发生重大变化，项目未同步：

#### Flagship: Beyond the `&`

| 特性 | 2026-05-08 报告状态 | 2026-05-18 官方最新状态 | 项目差距 |
|:---|:---|:---|:---|
| **Pin Ergonomics** | "Nightly 实验" | `&pin mut` borrowck 草稿 PR 已开；**2026-04 发现当前方法可能不正确**（无法区分 pinned borrow 和 normal-to-pinned coercion） | 🔴 未跟踪最新技术障碍 |
| **Field Projections** | "设计会议进行中" | **`field_of!` 宏已合并到 nightly**；`Field` trait 实验可用；t-lang 设计会议反馈极为正面（Josh: "beloved, pervasive feature"） | 🔴 **完全缺失 nightly 示例** |
| **Reborrow Traits** | "PR 已开，推进中" | PR 等待 review； reviewer 提出可能需大规模重构 `Rvalue::Ref` / `ExprKind::Ref`（若成为 blocker 将严重延迟） | 🔴 未覆盖最新 blocker 风险 |

#### Flagship: Flexible, fast(er) compilation

| 特性 | 最新状态 | 项目差距 |
|:---|:---|:---|
| **Cranelift backend** | **未完成（lack of funding）** — Trifecta Tech Foundation 资金不足 | 🟡 项目可能仍标记为"进行中"，需修正为"资金断裂，暂停" |
| **build-std** | RFC #3874 FCP 完成，#3875 推进中；Adam Gemmell 已开 cargo#16675 早期实现草图 | 🟡 缺少跟踪文档 |
| **Relink don't Rebuild** | 未完成（note） | 🟢 状态未变 |

#### Flagship: Higher-level Rust

| 特性 | 最新状态 | 项目差距 |
|:---|:---|:---|
| **cargo-script** | **FCP 已结束，但被 edition policy block**（lang/edition 方面未决） | 🔴 项目可能仍标记为"FCP已通过"，需修正 |
| **Ergonomic ref-counting** | 继续推进 | 🟢 状态未变 |

#### Flagship: Unblocking dormant traits

| 特性 | 最新状态 | 项目差距 |
|:---|:---|:---|
| **Polonius** | **#150551 已合并，"感觉可稳定化（stabilizable）"**；2026 年目标稳定化 alpha | 🔴 项目未更新此重大里程碑 |
| **Next-gen trait solver** | 新的 crater run 中；与 Niko 合作制定 cycle semantics RFC | 🟡 缺少最新进展 |
| **Evolving trait hierarchies** | **被 Supertrait `auto impl` 和 Arbitrary Self Types 2026 目标取代** | 🔴 项目可能仍引用旧目标名 |

#### 其他关键 Goal

| 特性 | 最新状态 | 项目差距 |
|:---|:---|:---|
| **BorrowSanitizer** | **取代 "Emit Retags in Codegen"**；2026-04 已准备发送 retag intrinsics PR；**RustConf 2026 演讲已接受**；测试通过率 80%；性能接近 Miri | 🔴 **项目完全缺失 BorrowSanitizer 内容** |
| **Rust for Linux** | `#![register_tool]` RFC 讨论正面；`-Zdirect-access-external-data` 已合并；**edition 迁移工具化讨论**（Inside Rust, 2026-05-13） | 🟡 缺少 edition 迁移专题 |
| **std::offload / autodiff** | `std::autodiff` 部分进入 CI；`std::offload` 性能测试优秀，将亮相 EuroLLVM 2026 | 🔴 项目缺失 GPU/自动微分前沿内容 |
| **C++/Rust Interop** | Overloading 实验 PR 已进行两轮 review；新 contractor 加入；Outreachy 申请人贡献代码示例 | 🔴 项目缺失 C++ 互操作深度内容 |
| **Const Generics** | mGCA 进展迅速；`min_adt_const_params` 接近 RFC 规格；GCA（非 min 版）由 camelid 推进 | 🟡 需更新概念文档 |
| **FLS (Ferrocene Language Specification)** | 发布节奏稳定化目标；1.94.0 提前完成，正向 1.95.0 推进 | 🔴 项目缺失安全关键 Rust 官方规格跟踪 |
| **Unsafe Fields** | 推进中，2026 继续 | 🟢 状态未变 |
| **MemorySanitizer / ThreadSanitizer** | 稳定化中 | 🟡 缺少指南 |
| **public/private dependencies** | 稳定化中 | 🟡 缺少指南 |

#### 2026-06-02 最新动态

| 动态 | 来源 | 项目差距 |
|:---|:---|:---|
| **Rust Foundation Maintainers Fund** 启动 | [blog.rust-lang.org/2026/06/02](https://blog.rust-lang.org/2026/06/02/) | 🔴 项目缺失 |

---

### 1.3 🟡 高优先级：1.98 nightly 前沿实验跟踪不足

**权威来源**: [releases.rs Ongoing Stabilization PRs](https://releases.rs/)

项目 `rust-toolchain.toml` 已升级至 `nightly`（实际 1.98.0），但以下 20+ 个正在进行中的 stabilization PR 未在项目中系统跟踪：

| 特性 | PR 状态 | 建议位置 |
|:---|:---|:---|
| `size_of_val_raw`, `align_of_val_raw`, `Layout::for_value_raw` | 等待 review | `c01_ownership` |
| `#[optimize]` attribute | Blocked | `docs/06_toolchain` |
| `ptr::try_cast_aligned` | Blocked | `c02_type_system` |
| `fN::BITS` | 等待 crater | `c02_type_system` |
| `fn_align` / `#[align(N)]` on functions | Blocked | `c03_control_fn` |
| `offset_of_slice` | 等待作者 | `c02_type_system` |
| `debug_closure_helpers` | Blocked | `c03_control_fn` |
| `-Cmin-function-alignment` | Blocked | `docs/06_toolchain` |
| `more_qualified_paths` | 等待作者 | `c04_generic` |
| `substr_range` / `subslice_range` | 等待 review | `c02_type_system` |
| `tcp_deferaccept` | 等待作者 | `c10_networks` |
| `-Zprofile-sample-use` | PFCP | `docs/06_toolchain` |
| `-Zinstrument-mcount` | 等待作者 | `docs/06_toolchain` |
| `-Cdebuginfo-compression` | 等待作者 | `docs/06_toolchain` |
| `doc_cfg` | Blocked | `docs/06_toolchain` |
| `derive(CoercePointee)` | Blocked, FCP 完成 | `c04_generic` |
| ATPIT (associated type position impl Trait) | Blocked, PFCP | `c04_generic` |
| Frontmatter / Cargo Script | Blocked | `docs/06_toolchain` |
| Never type `!` | Blocked | `c02_type_system` |
| `refcell_try_map` | 等待作者 | `c02_type_system` |

**问题**: 项目使用 nightly 工具链运行 CI，但学习者无法从项目中了解 nightly 中正在酝酿哪些未来特性。这削弱了 nightly 工具链的"预览价值"。

---

### 1.4 🟡 高优先级：国际教学最佳实践差距

**权威来源**: Brown University Interactive Book (OOPSLA 2023, 2024 Distinguished Paper) | Google Comprehensive Rust | 100 Exercises to Learn Rust | Rustlings v6

| 维度 | 国际最佳实践 | 本项目状态 | 差距 |
|:---|:---|:---|:---:|
| **嵌入式测验** | Brown: 每章嵌入式 Quiz，即时反馈；留存率提升 30-40% | ❌ 无 | **显著** |
| **所有权可视化** | Aquascope: 编译时/运行时行为可视化 | ❌ 无 | **显著** |
| **渐进式项目** | 100 Exercises: 票务系统→并发→异步，项目制深度 | ⚠️ rustlings 风格练习存在，但项目制深度不足 | 中等 |
| **多语言支持** | TRPL 社区翻译 15+ 语言；Google: 多语言 | ❌ 纯中文，无 i18n 基础设施 | **显著** |
| **浏览器内运行** | Rust Playground 嵌入 / Rustfinity | ❌ 无 | 中等 |
| **术语双语化** | 核心术语强制英中对照 | ⚠️ `terminology_glossary.md` 存在但未强制执行 | 中等 |
| **AI 辅助警告** | 社区共识：先建立所有权心智模型，再使用 AI | ⚠️ 有 AI 指南，但需强化强调顺序 | 待确认 |

---

## 第二部分：对称差 B \ A（项目冗余/过时的内容）

### 2.1 🔴 生态过时内容（已识别但未清零）

| 内容 | 问题 | 当前状态 | 建议处理 |
|:---|:---|:---|:---|
| `async-std` | 2025-03 停止维护 | 66 文件已标记但部分仍引用 | 全局清零 grep |
| `static mut` | 2024 Edition deny-by-default | `docs/` 12 处文档示例未更新 | 批量替换为 `Atomic*` / `Cell` / `OnceLock` |
| `wasm32-wasi` | 已移除，分 `wasip1`/`wasip2` | 部分已更新，需最终确认 | 全局审计 |
| `#[async_trait]` | Axum 0.8+ 原生 AFIT | `c10_networks` 可能仍使用 | 迁移检查 |
| `backoff` crate | unmaintained (RUSTSEC-2025-0012) | workspace 仍引用 | 替换为内部实现 |
| `sea-orm` rc | `2.0.0-rc.40` 持续数月未转正 | 依赖中使用 | 降级或等待 stable |
| Cranelift backend | 官方状态: 未完成（lack of funding） | 可能标记为"进行中" | **修正为"资金断裂，跟踪中"** |
| cargo-script | 官方状态: FCP 结束但被 edition policy block | 可能标记为"FCP已通过" | **修正为"FCP结束，被 block"** |

### 2.2 🟡 结构性冗余

| 内容 | 问题 | 建议处理 |
|:---|:---|:---|
| **内容膨胀** | 1,773 Markdown / 46 万行文档 / 1,507 Rust 文件 | 启动 "Great Documentation Slimming"：docs/ 活跃文件削减 50% |
| **版本中心制** | `rust_194/195/196/197_features.rs` 分散同一特性 | 改为"特性中心制"：每个重要特性一个文档，内部标注版本演进 |
| **三轨重复** | `concept/`/`knowledge/`/`docs/` 相似度 >60% 的文件 | 检测合并，重复减少 50% |
| **archive/ 无限增长** | 历史报告和代码归档无清理机制 | 建立 12 个月保质期 + 季度僵尸内容清理 |

---

## 第三部分：改进 / 完善 / 修正计划

> **总体策略**: 从"大而全"转向"深而精"。核心原则：
>
> 1. **版本追新**: 每个 stable 发布前 2 周完成特性覆盖
> 2. **状态同步**: 每月同步一次 Project Goals 跟踪状态
> 3. **生态清零**: 过时依赖/内容发现后 1 周内处理
> 4. **价值密度**: 12 个月无更新内容自动进入待审查队列

---

### Phase 0: 紧急补丁（2026-06-08 ~ 2026-06-14，1 周）

| # | 任务 | 具体行动 | 验收标准 | 工时 |
|:---|:---|:---|:---|:---:|
| 0.1 | **1.97 Preview 初始化** | 基于 releases.rs 30+  stabilization PR 和 nightly 1.98.0，创建 `rust_197_preview.md` | 覆盖 15+ 即将稳定特性 | 4h |
| 0.2 | **Project Goals 状态修正** | 修正 Cranelift/cargo-script/Poloniues/Evolving trait hierarchies 等 5+ 处状态描述 | 与 2026-05-18 官方更新一致 | 2h |
| 0.3 | **BorrowSanitizer 紧急补充** | 创建 `concept/07_future/borrow_sanitizer.md`：与 Miri 的互补关系、使用方法、进展状态 | 含概念 + 权威来源链接 | 2h |
| 0.4 | **Field Projections nightly 示例** | 创建 `crates/c04_generic/src/field_projections_preview.rs`：基于官方 `field_of!` 示例 | 可编译 nightly 示例 | 2h |
| 0.5 | **async-std / static mut / backoff 清零** | 全局搜索替换，验证编译 | `cargo audit` + `grep` 清零 | 3h |

**Phase 0 总工时**: ~13 小时

---

### Phase 1: 1.96/1.97 特性深度对齐（2026-06-15 ~ 2026-07-13，4 周）

| # | 任务 | 具体行动 | 验收标准 | 工时 |
|:---|:---|:---|:---|:---:|
| 1.1 | **`assert_matches!` 深度补全** | 确认 `concept/02_intermediate/05_assert_matches.md` 覆盖 1.96 stable 全部语义；补充失败诊断示例 | 含可编译示例 + 失败输出 | 2h |
| 1.2 | **`core::range::*` 体系完整性** | 补充 `RangeFull`/`RangeTo` 前瞻（1.97 即将稳定）+ `legacy` 模块说明 | 覆盖 Copy 友好特性全景 | 3h |
| 1.3 | **`From<T>` for cell types 深度解释** | `LazyCell`/`LazyLock`/`AssertUnwindSafe` 的 `From<T>` 语义 + 使用场景 | 含 3 个可编译场景 | 2h |
| 1.4 | **1.97 特性预研模块** | `c08_algorithms`: `VecDeque::truncate_front` / `retain_back`；`c02_type_system`: `alignment_type`；`c04_generic`: `supertrait_item_shadowing` | 每特性 1 概念 + 1 示例 | 8h |
| 1.5 | **Cargo 1.97 工具链更新** | `-m` shorthand、`-p` 错误改进、`-Zcargo-lints` 新增 lints | 文档 + 速查表更新 | 2h |
| 1.6 | **CVE-2026-5222/5223 安全公告最终确认** | 验证 `concept/06_ecosystem/01_toolchain.md` 或安全文档中已覆盖 | 文档覆盖 + 来源链接 | 1h |
| 1.7 | **rustdoc 1.96 改进补充** | Deprecation notes rendering、`missing_doc_code_examples`、Sidebar 分离 | `docs/06_toolchain` 新增小节 | 2h |
| 1.8 | **Polonius Alpha 里程碑更新** | 更新 `concept/03_advanced/03_unsafe.md` 或专门跟踪文档：#150551 已合并，2026 年目标稳定化 | 状态准确 + 来源链接 | 1h |

**Phase 1 总工时**: ~21 小时

---

### Phase 2: Project Goals 2026 深度跟踪（2026-07-14 ~ 2026-08-10，4 周）

| # | 任务 | 具体行动 | 验收标准 | 工时 |
|:---|:---|:---|:---|:---:|
| 2.1 | **Reborrow Traits 最新状态** | 更新跟踪文档：PR blocker 风险（`Rvalue::Ref` 重构）、derive 宏需求 | 含风险分析 + 来源链接 | 2h |
| 2.2 | **Pin Ergonomics 技术障碍跟踪** | 更新：`&pin mut` borrowck 发现的方法论问题（2026-04） | 状态准确 | 2h |
| 2.3 | **build-std 跟踪** | RFC #3874 FCP 完成、#3875 进展、cargo#16675 草图 | 1 概念 + 1 配置示例 | 2h |
| 2.4 | **Rust for Linux 深化** | `#![register_tool]`、`-Zdirect-access-external-data`、edition 迁移工具化（MIR 比较方案） | 1 深度指南 + 1 可编译框架 | 6h |
| 2.5 | **C++/Rust Interop 预研** | Overloading 实验、Crubit、cxx 对比 | 1 概念文档 + 1 代码示例 | 4h |
| 2.6 | **Const Generics mGCA 更新** | `min_adt_const_params` 接近 RFC；GCA 进展 | 更新 `c04_generic` 概念 | 3h |
| 2.7 | **std::offload / autodiff 预研** | GPU 编程、自动微分前沿 | 1 概念文档（标注 nightly-only） | 3h |
| 2.8 | **FLS / 安全关键 Rust 跟踪** | Ferrocene Language Specification 发布节奏、Miri/BorrowSanitizer 互补 | 1 概念文档 | 2h |
| 2.9 | **MemorySanitizer / ThreadSanitizer 指南** | 稳定化中特性的使用指南 | 1 工具链文档 | 2h |

**Phase 2 总工时**: ~26 小时

---

### Phase 3: 内容瘦身与价值审计（2026-08-11 ~ 2026-09-21，6 周）

与 `COMPREHENSIVE_CRITICAL_ANALYSIS_AND_ROADMAP_2026_06_03.md` Phase 3 基本一致，但增加：

| # | 任务 | 补充说明 | 工时 |
|:---|:---|:---|:---:|
| 3.1 | **docs/ A/B/C 价值审计** | 新增标准：若文件引用的 Rust 版本 < 1.90 且未标注历史价值，自动降级为 C | 12h |
| 3.2 | **版本中心制 → 特性中心制** | 将 `rust_194/195/196_features.rs` 中重复出现的特性（如 `async fn` in trait）提取为独立特性文档 | 8h |
| 3.3 | **archive/ 自动清理机制** | 脚本：90 天无提交 + 无内部链接 → 自动标记"僵尸" | 4h |
| 3.4 | **定理链指标改革** | 允许描述性文档声明 `# theorem_chain: N/A` | 2h |

**Phase 3 总工时**: ~26 小时

---

### Phase 4: 国际对齐与教育有效性（2026-09-22 ~ 2026-11-02，6 周）

| # | 任务 | 具体行动 | 工时 |
|:---|:---|:---|:---:|
| 4.1 | **核心术语双语化强制执行** | 扩展 `terminology_glossary.md` 至 150 术语；脚本检查 `concept/` 核心文件术语覆盖 | 6h |
| 4.2 | **英文骨架试点** | `concept/01_foundation/` 10 个核心文件：标题 + 3 句英文摘要 + 代码英文注释 | 8h |
| 4.3 | **嵌入式测验试点** | `01_ownership.md`、`02_borrowing.md`、`03_lifetimes.md` 各 5-10 道 Markdown 折叠测验 | 12h |
| 4.4 | **TRPL 3rd Ed 对照审计** | 逐章对比 TRPL 第 3 版（2025-10）与 L1-L3 | 16h |
| 4.5 | **概念-代码-练习闭环** | 每个 L1-L2 文件底部添加 `## 实践`：链接到 crates/ + exercises/ | 6h |
| 4.6 | **受众分层标签强制执行** | 每个 `concept/` 文件添加 `[初学者|进阶|专家|研究者]` | 6h |

**Phase 4 总工时**: ~54 小时

---

### Phase 5: 持续运营机制（2026-11-03 起，长期）

| # | 机制 | 频率 | 负责人 |
|:---|:---|:---|:---|
| 5.1 | **Release Notes 同步** | 每 6 周（Rust 发布周期） | 自动化脚本 + 人工复核 |
| 5.2 | **Project Goals 状态同步** | 每月 | 跟踪文档维护者 |
| 5.3 | **cargo audit / outdated 扫描** | 每周 | CI 自动化 |
| 5.4 | **僵尸内容清理** | 每季度 | 脚本 + 人工审核 |
| 5.5 | **术语一致性检查** | 每季度 | 脚本 |
| 5.6 | **国际资源对标** | 每半年 | 内容团队 |

---

## 第四部分：关键决策点（需您确认）

### 决策 1：1.97 覆盖策略

- **选项 A**: 在 1.97 stable 发布前（2026-07-09，仅剩 31 天）完成 Phase 0 + Phase 1 核心任务 — **推荐**
- **选项 B**: 等 1.97 发布后再补充（可能延迟 2-4 周）
- **选项 C**: 仅覆盖高影响特性（`VecDeque::truncate_front`, `supertrait_item_shadowing`, `alignment_type`），其余延后

### 决策 2：BorrowSanitizer 定位

- **选项 A**: 作为 Miri 的互补工具，创建独立概念文档 + nightly 示例 — **推荐**
- **选项 B**: 仅在 L7 未来层简要提及，不深入
- **选项 C**: 暂不覆盖，等其稳定化后再补充

### 决策 3：内容瘦身力度

- **选项 A**: 激进瘦身（docs/ 削减 50%，archive/ 清理 40%）— **推荐**
- **选项 B**: 温和瘦身（docs/ 削减 30%，archive/ 清理 20%）
- **选项 C**: 维持现状，仅标记分级

### 决策 4：国际化投入

- **选项 A**: 先完成核心概念英文骨架（`concept/` 10 文件试点）+ 术语双语化 — **推荐**
- **选项 B**: 全面推进 `concept/` 273 文件英文骨架
- **选项 C**: 维持现状，专注中文社区

---

## 附录：权威来源索引

| 来源 | URL | 最后核对日期 |
|:---|:---|:---:|
| Rust 1.96.0 Release Notes | blog.rust-lang.org/2026/05/28/Rust-1.96.0/ | 2026-06-08 |
| Rust Project Goals April 2026 | blog.rust-lang.org/2026/05/18/project-goals-2026-04/ | 2026-06-08 |
| releases.rs | releases.rs/ | 2026-06-08 |
| Cargo CHANGELOG | doc.rust-lang.org/beta/cargo/CHANGELOG.html | 2026-06-08 |
| Rust Forge | forge.rust-lang.org/ | 2026-06-08 |
| CVE-2026-5223 | blog.rust-lang.org/2026/05/25/cve-2026-5223/ | 2026-06-08 |
| CVE-2026-5222 | blog.rust-lang.org/2026/05/25/cve-2026-5222/ | 2026-06-08 |
| Rust Foundation Maintainers Fund | blog.rust-lang.org/2026/06/02/ | 2026-06-08 |
| Inside Rust: Rust for Linux edition migration | blog.rust-lang.org/inside-rust/2026/05/13/... | 2026-06-08 |

---

> **报告结论**: 本项目在技术工程化和内容广度上已达中文 Rust 生态顶尖水平，但在**版本前瞻覆盖（1.97 仅剩 31 天）**、**Project Goals 状态同步**、**BorrowSanitizer 等前沿工具缺失**、**内容膨胀**四个维度上存在紧急差距。建议立即执行 **Phase 0 紧急补丁**（1 周，~13h），确保 1.97 发布前完成前瞻覆盖；随后按 Phase 1-4 逐步深化。
>
> **总预估投入**: Phase 0-4 合计 ~140 小时（按每天 4 小时，约 35 个工作日/1.75 个月）。
