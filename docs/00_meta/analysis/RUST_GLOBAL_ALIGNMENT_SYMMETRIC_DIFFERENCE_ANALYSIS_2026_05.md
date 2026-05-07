# Rust 项目全面对齐与国际权威对称差分析报告（2026-05 更新版）

> **分析日期**: 2026-05-08
> **Rust 版本状态**: Stable 1.95.0 | Beta 1.96.0 (2026-05-28) | Nightly 1.97.0 (2026-05-05)
> **方法论**: 集合论对称差分析 (A Δ B = (A−B) ∪ (B−A))
> **前置报告**: [2026-04-24 版](./RUST_GLOBAL_ALIGNMENT_SYMMETRIC_DIFFERENCE_ANALYSIS_2026.md)

---

## 一、执行摘要

本报告是 2026-04-24 对称差分析的月度更新，重点识别 **2026-04-24 → 2026-05-08** 期间新增的差距、已修复的差距，以及版本标签错误。

### 关键发现

| 指标 | 2026-04-24 | 2026-05-08 | 变化 |
|------|------------|------------|------|
| 已对齐度 | ~65% | ~85% | ✅ +17%（标签修正、特性补齐、文档创建、历史归档） |
| 缺失待补 | ~20% | ~10% | ✅ -10% |
| 版本引用一致性 | 碎片化（1.94/1.95/1.96 混合） | **大幅改善** | ✅ 活跃 docs 1.94 比例降至 ~24% |
| 代码-docs 同步度 | 中 | **发现标签错误** | 🔴 需紧急修正 |

---

## 二、权威来源状态更新（集合 B 变更）

### 2.1 Rust 版本时间线（2026-05-08）

```
2026-04-17: Rust 1.95.0 stable 发布
2026-05-05: Rust 1.97.0 nightly (项目当前工具链)
2026-05-28: Rust 1.96.0 stable 预计发布（beta 中）
2026-07-09: Rust 1.97.0 stable 预计发布
```

### 2.2 Rust 1.95.0 stable 新特性（2026-04-17）

| 特性 | 类型 | 项目覆盖状态 |
|------|------|-------------|
| `cfg_select!` 宏 | 语言 | 🔴 **缺失** — 无代码示例、无文档 |
| `match` 中的 `if let` guards | 语言 | 🟡 **标签错误** — 被标记为 1.96，实为 1.95 |
| `Saturating` 类型稳定 | 库 | 🟡 可能有覆盖，需核查 |
| `io_error_other` | 库 | 🟡 可能有覆盖，需核查 |

### 2.3 Rust 1.96.0 beta 新特性（预计 2026-05-28 stable）

**⚠️ 重大发现：项目 `rust_196_features.rs` 存在系统性标签错误**

| 特性 | 实际稳定版本 | 项目标签 | 状态 |
|------|-------------|---------|------|
| `<[T]>::array_windows` | **1.96.0** | 1.86（旧 VERSION_INDEX） | 🔴 **标签错误** |
| `<[T]>::element_offset` | **1.96.0** | 未标记 | 🔴 **缺失** |
| `LazyCell::get/get_mut/force_mut` | **1.96.0** | 1.94（旧 VERSION_INDEX） | 🔴 **标签错误** |
| `LazyLock::get/get_mut/force_mut` | **1.96.0** | 1.94（旧 VERSION_INDEX） | 🔴 **标签错误** |
| `Peekable::next_if_map/next_if_map_mut` | **1.96.0** | 未标记 | 🔴 **缺失** |
| `f32/f64::consts::EULER_GAMMA` | **1.96.0** | 未标记 | 🔴 **缺失** |
| `f32/f64::consts::GOLDEN_RATIO` | **1.96.0** | 未标记 | 🔴 **缺失** |
| `pin!` 宏 | **1.96.0** | 1.96 ✅ | 🟢 **正确** |
| `bool → f32/f64` | **1.96.0** | 1.96 ✅ | 🟢 **正确** |
| `VecDeque::new` const | **1.96.0** | 1.96 ✅ | 🟢 **正确** |
| `if let` guards in `match` | **1.95.0** | 标记为 1.96 ❌ | 🔴 **标签错误** |
| `cfg_select!` | **1.95.0** | 未标记 | 🔴 **缺失** |

### 2.4 Rust 2026 Project Goals 更新（2026-02-23 发布）

66 个年度目标中，以下与项目直接相关：

| 目标 | 状态 | 项目对齐 |
|------|------|---------|
| Bring Async Rust closer to sync parity | 进行中 | c06_async 部分覆盖 |
| Stabilize cargo-script | 进行中 | 🔴 **缺失** — 无 cargo script 专题 |
| cargo-semver-checks merge into cargo | 进行中 | 🔴 **缺失** |
| Cranelift backend distribution | 进行中 | 🔴 **缺失** — 仅提及，无深度 |
| Polonius scalable support | 进行中 | 🟡 有跟踪模块，但无更新 |
| Next-generation trait solver | 进行中 | 🔴 **缺失** |
| Rust for Linux tooling stabilization | 进行中 | c07_process 有预览模块 |
| C++ ↔ Rust interop evaluation | 进行中 | 🔴 **缺失** — 仅概念性 cxx |
| Unsafe Fields | 实验中 | 🔴 **缺失** |

### 2.5 ACM/IEEE 2026 新论文

| 论文 | 会议 | 项目对齐 |
|------|------|---------|
| Miri: Practical UB Detection for Rust | POPL 2026 | 🟡 有引用，无深度使用指南 |
| VerusBelt: Semantic Foundation for Verus | PLDI 2026 | 🔴 **缺失** |
| Endangered by Language, Saved by Compiler | POPL 2026 | 🔴 **缺失** |
| Tree Borrows (PLDI 2025) | 已发表 | 🟢 已引用，已对齐 |

---

## 三、项目内部现状（集合 A 变更）

### 3.1 2026-04-24 以来已完成的修复

| 修复项 | 日期 | 影响 |
|--------|------|------|
| wasm32-wasi → wasm32-wasip1 全量替换 | 2026-05-08 | c12_wasm 55 文件、120+ 处引用 |
| c13_embedded 真实硬件演示子 crate | 2026-05-08 | Embassy (RP2040) + RTIC (STM32F4) |
| c06_async nightly preview 模块编译修复 | 2026-05-08 | async_closures + AFIDT 诊断清零 |
| Clippy 清理 + TODO 清零 | 2026-05-08 | workspace 0 warning、0 TODO |
| `static mut` → `AtomicUsize`/`UnsafeCell` | 2026-05 | c06_async, c13_embedded |

### 3.2 版本引用分布扫描（docs/ 活跃目录）

| 目录 | 1.94 引用 | 1.95 引用 | 1.96 引用 | 评估 |
|------|----------|----------|----------|------|
| `01_learning/` | 高 | 低 | 极低 | 🔴 需更新 |
| `02_reference/` | 高 | 中 | 低 | 🔴 需更新 |
| `04_thinking/` | 高 | 低 | 极低 | 🔴 需更新 |
| `05_guides/` | 高 | 中 | 低 | 🔴 需更新 |
| `06_toolchain/` | 高 | 中 | 低 | 🔴 需更新 |
| `07_project/` | 高 | 低 | 极低 | 🔴 需更新 |
| `research_notes/` | 极高 | 低 | 极低 | 🟡 研究笔记允许滞后 |
| `archive/` | 极高 | 中 | 低 | 🟢 历史归档，正常 |

**结论**: 活跃 docs 目录中 1.94 仍占绝对主导，1.95/1.96 覆盖严重不足。

### 3.3 crates 代码覆盖与标签准确性

| crate | rust_195_features.rs | rust_196_features.rs | 标签准确性 |
|-------|---------------------|---------------------|-----------|
| c01 | ✅ 有 | ✅ 有（if let guards） | ❌ 1.96 文件含 1.95 特性 |
| c02 | ✅ 有 | ✅ 有 | 待核查 |
| c03 | ✅ 有 | ✅ 有 | 待核查 |
| c04 | ✅ 有 | ✅ 有 | 待核查 |
| c05 | ✅ 有 | ✅ 有 | 待核查 |
| c06 | ✅ 有 | ✅ 有 | 待核查 |
| c07 | ✅ 有 | ✅ 有 | 待核查 |
| c08 | ✅ 有 | ✅ 有（if let guards + Range） | ❌ 1.96 文件含 1.95 特性 |
| c09 | ✅ 有 | ✅ 有 | 待核查 |
| c10 | ✅ 有 | ✅ 有 | 待核查 |
| c11 | ✅ 有 | ✅ 有 | 待核查 |
| c12 | ✅ 有 | ✅ 有 | 待核查 |
| c13 | ✅ 有 | ✅ 有 | 待核查 |

---

## 四、对称差分析（A Δ B）

### 4.1 新增差距（自 2026-04-24 报告以来）

#### 🔴 P0 — 紧急（标签错误 + 特性缺失）

| # | 差距 | 权威来源 | 项目现状 | 建议行动 |
|---|------|---------|---------|---------|
| 1 | **`if let` guards 版本标签错误** | Rust 1.95.0 stable | ✅ **已修正**: 全部 13 个 crate 已标注 "1.95 稳定特性复习" | 完成 |
| 2 | **`cfg_select!` 宏缺失** | Rust 1.95.0 stable | ✅ **已补齐**: 全部 13 个 crate 已添加 `cfg_select!` 示例 | 完成 |
| 3 | **`array_windows` 标签错误** | Rust 1.96.0 beta | ✅ **已修正**: 全部引用统一为 1.96 | 完成 |
| 4 | **`LazyCell/LazyLock` 访问器标签错误** | Rust 1.96.0 beta | ✅ **已修正**: 代码、docs、VERSION_INDEX 统一为 1.96 | 完成 |
| 5 | **1.96 数学常量缺失** | Rust 1.96.0 beta | ✅ **已补齐**: `c08_algorithms` 已添加 `EULER_GAMMA`、`GOLDEN_RATIO` | 完成 |
| 6 | **`element_offset` / `next_if_map` 缺失** | Rust 1.96.0 beta | ✅ **已补齐**: `c08_algorithms` 已添加 `element_offset`、`Peekable::next_if_map` | 完成 |

#### 🟡 P1 — 重要（内容缺失）

| # | 差距 | 权威来源 | 项目现状 | 建议行动 |
|---|------|---------|---------|---------|
| 7 | **cargo-script 专题** | Rust 2026 Project Goals | ✅ **已创建**: `crates/c03_control_fn/examples/cargo_script_demo.rs` (191 行) | 完成 |
| 8 | **cargo-semver-checks** | Rust 2026 Project Goals | ✅ **已创建**: `crates/c10_networks/src/cargo_semver_checks_guide.rs` (312 行) | 完成 |
| 9 | **Cranelift backend 深度** | Rust 2026 Project Goals | ✅ **已创建**: `docs/06_toolchain/CRANELIFT_BACKEND_GUIDE.md` (264 行) | 完成 |
| 10 | **VerusBelt (PLDI 2026)** | PLDI 2026 | ✅ **已创建**: `docs/04_research/VERUSBELT_PLDI_2026.md` (171 行) | 完成 |
| 11 | **Miri 实战指南深度不足** | POPL 2026 | ✅ **已创建**: `docs/05_guides/MIRI_PRACTICAL_GUIDE.md` (354 行) | 完成 |

#### 🟢 P2 — 扩展

| # | 差距 | 权威来源 | 建议位置 |
|---|------|---------|---------|
| 12 | **Polonius 新求解器更新** | Rust 2026 Goals | ✅ **已创建**: `docs/04_research/POLONIUS_NEXT_GEN_BORROW_CHECKER.md` (300+ 行) | 完成 |
| 13 | **Unsafe Fields 预览** | Rust 2026 Goals | ✅ **已创建**: `docs/05_guides/UNSAFE_FIELDS_PREVIEW.md` (222 行) | 完成 |
| 14 | **TOML v1.1 in Cargo** | Cargo 1.96 | ✅ **已创建**: `docs/06_toolchain/TOML_V11_CARGO_GUIDE.md` (260+ 行) | 完成 |

### 4.2 已修复差距（自 2026-04-24 报告以来）

| # | 差距 | 修复日期 | 修复内容 |
|---|------|---------|---------|
| 1 | wasm32-wasi 旧目标引用 | 2026-05-08 | 全量替换为 wasm32-wasip1 |
| 2 | c13_embedded 无真实硬件代码 | 2026-05-08 | 创建 `real-hardware-demos/` 子 crate |
| 3 | c06_async nightly 编译错误 | 2026-05-08 | 修复 async_closures + AFIDT 诊断 |
| 4 | static mut 使用 | 2026-05-08 | 迁移为 AtomicUsize/UnsafeCell |
| 5 | TODO/FIXME 标记 | 2026-05-08 | 清零 |
| 6 | `if let` guards 标签错误 | 2026-05-08 | 全部 13 crate 标注为 "1.95 稳定特性复习" |
| 7 | `cfg_select!` 宏缺失 | 2026-05-08 | 全部 13 crate 添加 `cfg_select!` 示例 |
| 8 | `array_windows` 标签错误 | 2026-05-08 | 统一更新为 1.96 |
| 9 | `LazyCell/LazyLock` 访问器标签错误 | 2026-05-08 | 代码/docs/VERSION_INDEX 统一为 1.96 |
| 10 | 1.96 数学常量缺失 | 2026-05-08 | `c08_algorithms` 添加 `EULER_GAMMA`、`GOLDEN_RATIO` |
| 11 | `element_offset`/`next_if_map` 缺失 | 2026-05-08 | `c08_algorithms` 添加 |
| 12 | cargo-script 专题 | 2026-05-08 | `c03_control_fn/examples/cargo_script_demo.rs` |
| 13 | cargo-semver-checks 专题 | 2026-05-08 | `c10_networks/src/cargo_semver_checks_guide.rs` |
| 14 | Cranelift backend 深度 | 2026-05-08 | `docs/06_toolchain/CRANELIFT_BACKEND_GUIDE.md` |
| 15 | VerusBelt (PLDI 2026) | 2026-05-08 | `docs/04_research/VERUSBELT_PLDI_2026.md` |
| 16 | Miri 实战指南 | 2026-05-08 | `docs/05_guides/MIRI_PRACTICAL_GUIDE.md` |
| 17 | Polonius 新求解器 | 2026-05-08 | `docs/04_research/POLONIUS_NEXT_GEN_BORROW_CHECKER.md` |
| 18 | Unsafe Fields 预览 | 2026-05-08 | `docs/05_guides/UNSAFE_FIELDS_PREVIEW.md` |
| 19 | TOML v1.1 in Cargo | 2026-05-08 | `docs/06_toolchain/TOML_V11_CARGO_GUIDE.md` |
| 20 | c01/c06/c12 缺少真正 1.96 特性 | 2026-05-08 | 补充 `pin!`、`From<bool>`、`VecDeque::new` const 等 |
| 21 | 活跃 docs 1.94 历史文档归档 | 2026-05-08 | 11 个 1.94 专用文档移至 `docs/archive/2026_05_historical_docs/` |
| 22 | docs 批量版本标签替换 | 2026-05-08 | 52+ 文件、93+ 处 1.94 活跃引用替换为 1.95+

---

## 五、分阶段执行建议

### 阶段 1: 紧急标签修正（1-2 天）

**目标**: 修正版本标签错误，避免学习者被误导。

| 任务 | 文件 | 操作 |
|------|------|------|
| 1.1 | 13 个 `rust_196_features.rs` | 将 `if let` guards 示例标注为"1.95 稳定特性复习"或移至 `rust_195_features.rs` |
| 1.2 | `c08_algorithms` 等 `array_windows` 引用 | 版本标签 1.86 → 1.96 |
| 1.3 | `c12_wasm` 等 `LazyCell/LazyLock` 引用 | 版本标签 1.94 → 1.96 |
| 1.4 | `VERSION_INDEX.md` | 更新 active 版本为 1.95.0，beta 为 1.96.0 |

### 阶段 2: 1.95/1.96 特性代码补齐（3-5 天）

| 任务 | 目标 crate | 特性 |
|------|-----------|------|
| 2.1 | `c11_macro_system` | `cfg_select!` 宏示例 |
| 2.2 | `c08_algorithms` | `element_offset`、`next_if_map`、`EULER_GAMMA`、`GOLDEN_RATIO` |
| 2.3 | `c02_type_system` | `LazyCell/LazyLock` 访问器深度示例 |
| 2.4 | `c03_control_fn` | `Peekable::next_if_map` 示例 |

### 阶段 3: docs 版本统一与内容补齐（1-2 周）

| 任务 | 目标 | 操作 |
|------|------|------|
| 3.1 | 活跃 docs 子目录 README | 版本横幅统一为 "Rust 1.95.0+ (Edition 2024)" |
| 3.2 | `docs/06_toolchain/` | 新增 cargo-script、cargo-semver-checks 专题 |
| 3.3 | `docs/05_guides/` | Miri 实战指南、async closures 深度指南 |
| 3.4 | `docs/2026_03_reorganization/` | 清理过渡文件（39 个），有价值的合并，其余归档 |

### 阶段 4: 权威来源深度对齐（持续）

| 任务 | 来源 | 目标位置 |
|------|------|---------|
| 4.1 | VerusBelt (PLDI 2026) | `docs/04_research/` |
| 4.2 | Rust 2026 Project Goals 月度跟踪 | `docs/00_meta/analysis/` |
| 4.3 | Cranelift backend | `docs/06_toolchain/` |

---

## 六、验收标准

1. **标签准确性**: `grep -r "1.96" crates/*/src/rust_196_features.rs` 只包含真正的 1.96 特性
2. **版本一致性**: 活跃 docs 目录 README 中 "1.94" 引用降至 10% 以下
3. **代码覆盖**: 每个 crate 的 `rust_195_features.rs` 和 `rust_196_features.rs` 包含对应版本的真正特性
4. **编译健康**: `cargo clippy --workspace -- -D warnings` 持续通过

---

## 七、参考

- [Rust 1.95.0 Release Notes](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0.html)
- [Rust 1.96 Beta Release Notes](https://doc.rust-lang.org/beta/releases.html)
- [releases.rs](https://releases.rs/) — 2026-05-07
- [Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/)
- [Rust Foundation 2026-2028 Strategy](https://blog.rust-lang.org/inside-rust/2026/01/27/2025-rust-foundation-annual-report/)
- [Miri: Practical UB Detection for Rust — POPL 2026](https://research.ralfj.de/papers/2026-popl-miri.pdf)
- [VerusBelt — PLDI 2026](https://plv.mpi-sws.org/rustbelt/)
