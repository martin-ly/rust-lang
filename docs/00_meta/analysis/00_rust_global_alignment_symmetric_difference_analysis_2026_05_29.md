# Rust 项目全面对齐与权威国际化对称差分析报告（2026-05-29）

> **分级**: [B]
> **Bloom 层级**: L2-L3 (理解/应用)
> **分析日期**: 2026-05-29
> **Rust 版本状态**: Stable 1.96.0 | Beta 1.97.0 | Nightly 1.98.0 (项目工具链)
> **方法论**: 集合论对称差分析 (A Δ B = (A−B) ∪ (B−A))
> **前置报告**: [2026-05-08 版](./00_rust_global_alignment_symmetric_difference_analysis_2026_05.md)

---

## 📑 目录

- [Rust 项目全面对齐与权威国际化对称差分析报告（2026-05-29）](#rust-项目全面对齐与权威国际化对称差分析报告2026-05-29)
  - [📑 目录](#目录)
  - [一、执行摘要](#一执行摘要)
    - [关键发现](#关键发现)
    - [核心结论](#核心结论)
  - [二、权威来源状态（集合 B）](#二权威来源状态集合-b)
    - [2.1 Rust 版本时间线](#21-rust-版本时间线)
    - [2.2 Rust 1.95.0 stable（2026-04-16）完整特性](#22-rust-1950-stable2026-04-16完整特性)
      - [语言特性](#语言特性)
      - [标准库稳定 API（1.95）](#标准库稳定-api195)
      - [编译器/工具链](#编译器工具链)
    - [2.3 Rust 1.96.0 stable（2026-05-28）完整特性](#23-rust-1960-stable2026-05-28完整特性)
      - [语言特性](#语言特性)
      - [标准库稳定 API（1.96）](#标准库稳定-api196)
      - [兼容性变更](#兼容性变更)
    - [2.4 Nightly 1.97/1.98 推进中特性](#24-nightly-197198-推进中特性)
    - [2.5 Rust 2026 Project Goals 关键目标](#25-rust-2026-project-goals-关键目标)
    - [2.6 Rust for Linux 高影响力特性](#26-rust-for-linux-高影响力特性)
  - [三、项目内部现状（集合 A）](#三项目内部现状集合-a)
    - [3.1 已覆盖特性（按版本）](#31-已覆盖特性按版本)
    - [3.2 版本标签状态](#32-版本标签状态)
    - [3.3 活跃文档统计](#33-活跃文档统计)
  - [四、对称差分析（A Δ B）](#四对称差分析a-δ-b)
    - [4.1 B−A：权威来源有、项目缺失](#41-ba权威来源有项目缺失)
      - [🔴 P0 — 紧急（学习者无法获取）](#p0--紧急学习者无法获取)
      - [🟡 P1 — 重要（内容不完整）](#p1--重要内容不完整)
      - [🟢 P2 — 扩展（前瞻/生态）](#p2--扩展前瞻生态)
    - [4.2 A−B：项目有、权威来源已变更/过时](#42-ab项目有权威来源已变更过时)
    - [4.3 优先级矩阵](#43-优先级矩阵)
  - [五、后续推进完善计划](#五后续推进完善计划)
    - [阶段 1：紧急标签修正 + 核心 API 补齐（3-5 天）](#阶段-1紧急标签修正--核心-api-补齐3-5-天)
    - [阶段 2：标准库 API 补齐（5-7 天）](#阶段-2标准库-api-补齐5-7-天)
    - [阶段 3：Nightly 前瞻专题（7-10 天）](#阶段-3nightly-前瞻专题7-10-天)
    - [阶段 4：生态与前瞻对齐（持续）](#阶段-4生态与前瞻对齐持续)
    - [时间线](#时间线)
  - [六、验收标准](#六验收标准)
  - [七、参考](#七参考)

---

## 一、执行摘要

本次分析在 2026-05-08 报告基础上，结合 **Rust 1.96.0 stable 正式发布**（2026-05-28）和 **nightly 1.98.0** 最新进展，进行全量对称差更新。

### 关键发现

| 指标 | 2026-05-08 | 2026-05-29 | 变化 |
|------|------------|------------|------|
| 核心特性对齐度 | ~92% | ~88% | ⚠️ −4%（1.96 发布后新增 gap） |
| 1.95 API 完整覆盖 | ~35% | ~35% | ⚠️ 无变化 |
| 1.96 特性覆盖 | ~60% | ~65% | ✅ +5%（1.96 发布后补齐） |
| Nightly 前瞻覆盖 | ~30% | ~35% | ✅ +5% |
| 版本标签准确率 | 大幅改善 | **稳定** | ✅ 无新增标签错误 |

### 核心结论

> **1.95 标准库新 API 是最大 gaps**：`Vec::push_mut`、`Atomic*::update`、`Layout::dangling_ptr` 等 1.95 稳定的大量 API 仍**无任何代码示例**。
>
> **1.96 语言特性基本对齐**：`assert_matches!`、`core::range`、`NonZero` 迭代等核心特性已覆盖。
>
> **Nightly 前瞻需加速**：`gen` blocks、`never_type`、`cargo-script` 等社区高度关注的特性，仅有 preview 文件，缺乏深度内容。

---

## 二、权威来源状态（集合 B）

### 2.1 Rust 版本时间线

```
2026-04-16: Rust 1.95.0 stable 发布
2026-05-28: Rust 1.96.0 stable 发布 ✅
2026-07-09: Rust 1.97.0 stable 预计发布（Beta 中）
2026-08-20: Rust 1.98.0 stable 预计发布（Nightly 中）
```

### 2.2 Rust 1.95.0 stable（2026-04-16）完整特性

#### 语言特性

| 特性 | 状态 | 项目覆盖 |
|------|------|---------|
| `if let` guards on match arms | 1.95 stable | 🟡 覆盖但标注为 1.96 |
| `cfg_select!` 宏 | 1.95 stable | 🔴 **缺失** — 无专门指南 |
| `--remap-path-scope` 稳定化 | 1.95 stable | 🟡 仅在 cheatsheet 提及 |
| C-style variadic functions (`system` ABI) | 1.95 stable | 🔴 **缺失** |
| `asm_cfg` 稳定化 | 1.95 stable | 🔴 **缺失** |
| `const_item_interior_mutations` lint | 1.95 stable | 🔴 **缺失** |
| `function_casts_as_integer` lint | 1.95 stable | 🔴 **缺失** |
| Pointer byte-by-byte copy in const eval | 1.95 stable | 🔴 **缺失** |

#### 标准库稳定 API（1.95）

| API | 模块 | 项目覆盖 |
|-----|------|---------|
| `cfg_select!` | `core::macros` | 🔴 **缺失** |
| `mod core::range` | `core::range` | ✅ 已覆盖 |
| `core::range::Range` / `RangeIter` | `core::range` | ✅ 已覆盖 |
| `core::range::RangeFrom` / `RangeFromIter` | `core::range` | ✅ 已覆盖 |
| `core::range::RangeToInclusive` / `RangeToInclusiveIter` | `core::range` | ✅ 已覆盖 |
| `core::hint::cold_path` | `core::hint` | 🔴 **缺失** |
| `assert_matches!` / `debug_assert_matches!` | `std::assert_matches` | ✅ 已覆盖 |
| `Vec::push_mut` / `Vec::insert_mut` | `alloc::vec::Vec` | 🔴 **缺失** |
| `VecDeque::push_front_mut` / `push_back_mut` / `insert_mut` | `alloc::collections::VecDeque` | 🔴 **缺失** |
| `LinkedList::push_front_mut` / `push_back_mut` | `alloc::collections::LinkedList` | 🔴 **缺失** |
| `AtomicPtr::update` / `try_update` | `core::sync::atomic` | 🔴 **缺失** |
| `AtomicBool::update` / `try_update` | `core::sync::atomic` | 🔴 **缺失** |
| `Atomic{In,Un}::update` / `try_update` | `core::sync::atomic` | 🔴 **缺失** |
| `bool: TryFrom<{integer}>` | `core::convert` | 🔴 **缺失** |
| `<*const T>::as_ref_unchecked` | `core::ptr` | 🔴 **缺失** |
| `<*mut T>::as_ref_unchecked` / `as_mut_unchecked` | `core::ptr` | 🔴 **缺失** |
| `Layout::dangling_ptr` | `core::alloc` | 🔴 **缺失** |
| `Layout::repeat` / `repeat_packed` / `extend_packed` | `core::alloc` | 🔴 **缺失** |
| `MaybeUninit<[T;N]>: From<[MaybeUninit<T>;N]>` | `core::mem` | 🔴 **缺失** |
| `Cell<[T;N]>: AsRef<[Cell<T>;N]>` / `AsRef<[Cell<T>]>` | `core::cell` | 🔴 **缺失** |
| `Cell<[T]>: AsRef<[Cell<T>]>` | `core::cell` | 🔴 **缺失** |
| `fmt::from_fn` (const context) | `core::fmt` | 🔴 **缺失** |
| `ControlFlow::is_break` / `is_continue` (const) | `core::ops` | 🔴 **缺失** |
| `From<bool> for {f32,f64}` | `core::convert` | ✅ 已覆盖 |
| `VecDeque::new` (const context) | `alloc::collections` | ✅ 已覆盖 |
| `std::path::MAIN_SEPARATOR_STR` | `std::path` | ✅ 已覆盖 |
| `impl DerefMut for PathBuf` | `std::path` | ✅ 已覆盖 |
| `Saturating` 类型稳定 | `core::num` | 🟡 concept 提及，无代码 |
| `io_error_other` | `std::io` | 🟡 concept 提及，无代码 |

#### 编译器/工具链

| 特性 | 状态 | 项目覆盖 |
|------|------|---------|
| `-Cjump-tables=bool` 稳定化 | 1.95 stable | 🟡 仅在 changelog 提及 |
| 29 RISC-V target features | 1.95 stable | 🔴 **缺失** |
| Unicode 17 | 1.95 stable | 🔴 **缺失** |

### 2.3 Rust 1.96.0 stable（2026-05-28）完整特性

#### 语言特性

| 特性 | 状态 | 项目覆盖 |
|------|------|---------|
| `expr` metavariable to `cfg` | 1.96 stable | ✅ 已覆盖 |
| Never type coercion in tuple expressions | 1.96 stable | 🟡 概念提及，无代码 |
| s390x vector registers in inline assembly | 1.96 stable | 🔴 **缺失** |
| `ManuallyDrop` as patterns | 1.96 stable | ✅ 已覆盖 |

#### 标准库稳定 API（1.96）

| API | 模块 | 项目覆盖 |
|-----|------|---------|
| `assert_matches!` / `debug_assert_matches!` | `std::assert_matches` | ✅ 已覆盖 |
| `From<T> for AssertUnwindSafe<T>` | `std::panic` | ✅ 已覆盖 |
| `From<T> for LazyCell<T,F>` / `LazyLock<T,F>` | `std::cell` / `std::sync` | ✅ 已覆盖 |
| `core::range::RangeToInclusive` / `RangeToInclusiveIter` | `core::range` | ✅ 已覆盖 |
| `core::range::RangeFrom` / `RangeFromIter` | `core::range` | ✅ 已覆盖 |
| `core::range::Range` / `RangeIter` | `core::range` | ✅ 已覆盖 |
| `NonZero` range iteration | `core::num` | ✅ 已覆盖 |

#### 兼容性变更

| 变更 | 影响 | 项目覆盖 |
|------|------|---------|
| Stop passing `--allow-undefined` on wasm targets | WASM 链接器 | ✅ 已覆盖 |
| Remove `-Csoft-float` | 编译器标志 | 🔴 **缺失** |
| `import S::{self as Other}` 不再允许 | 导入语法 | 🔴 **缺失** |
| `export_name`/`link_name` 多属性优先级 | FFI | 🔴 **缺失** |
| `c_double` → `f32` on AVR | 嵌入式 | 🔴 **缺失** |

### 2.4 Nightly 1.97/1.98 推进中特性

来自 [releases.rs](https://releases.rs/) 和 GitHub PR 追踪：

| 特性 | 状态 | 预计稳定 | 项目覆盖 |
|------|------|---------|---------|
| `never_type` (`!`) | PR #155697 FCP 中 | 1.97+ | 🟡 preview 文件 |
| `gen` blocks (coroutines) | 活跃开发中 | 1.98+ | 🟡 preview 文件 |
| `explicit_tail_calls` | 活跃开发中 | 未定 | 🔴 **缺失** |
| `c_variadic` function definitions | PR #155942 PFCP | 1.97+ | 🔴 **缺失** |
| `Path::is_empty` | PR 审查中 | 1.97+ | 🔴 **缺失** |
| `PathBuf::into_string` | PR 审查中 | 1.97+ | 🔴 **缺失** |
| `Result::map_or_default` / `Option::map_or_default` | PR 审查中 | 1.97+ | 🔴 **缺失** |
| `float_algebraic` | PR 审查中 | 1.97+ | 🔴 **缺失** |
| `core::range::{legacy, RangeFull, RangeTo}` | PR #156629 FCP | 1.97+ | 🔴 **缺失** |
| `-Zprofile-sample-use` / `-Zdebug-info-for-profiling` | PR 审查中 | 未定 | 🔴 **缺失** |

### 2.5 Rust 2026 Project Goals 关键目标

来自 [Rust 2026 Project Goals](https://blog.rust-lang.org/inside-rust/2026/03/27/program-management-update-2026-02/)：

| 目标 | 优先级 | 项目覆盖 |
|------|--------|---------|
| Bring Async Rust closer to sync parity | P0 | 🟡 c06_async 部分覆盖 |
| Stabilize cargo-script | P0 | 🔴 **缺失** — 无专题 |
| cargo-semver-checks merge into cargo | P1 | 🔴 **缺失** |
| Cranelift backend distribution | P1 | 🔴 **缺失** — 仅提及 |
| Polonius scalable support | P1 | 🟡 有跟踪模块，无更新 |
| Next-generation trait solver | P1 | 🔴 **缺失** |
| Rust for Linux tooling stabilization | P1 | 🟡 c13_embedded 有预览 |
| C++ ↔ Rust interop evaluation | P1 | 🔴 **缺失** — 仅概念性 cxx |
| Unsafe Fields | P2 | 🔴 **缺失** |

### 2.6 Rust for Linux 高影响力特性

来自 [Inside Rust Blog 2026-02](https://blog.rust-lang.org/inside-rust/2026/03/27/program-management-update-2026-02/)：

| 特性 | 影响 | 项目覆盖 |
|------|------|---------|
| Arbitrary self types | 自定义 receiver | 🔴 **缺失** |
| Field projections | 字段投影 | 🔴 **缺失** |
| Immovable types + guaranteed destructors | `Pin` 替代方案 | 🟡 preview 文件 |
| ADT const params | 常量泛型扩展 | 🔴 **缺失** |
| `rustdoc --output-format=doctest` | 文档测试 | 🔴 **缺失** |
| Relaxing orphan rules (coherence domain) | 多 crate 一致性 | 🔴 **缺失** |

---

## 三、项目内部现状（集合 A）

### 3.1 已覆盖特性（按版本）

| 版本 | 特性 | 文件位置 |
|------|------|---------|
| 1.95 | `if let` guards | 14 crates + cheatsheet |
| 1.95 | `core::range` 模块 | c02_type_system, concept |
| 1.95 | `assert_matches!` | c02_type_system, concept |
| 1.95 | `NonZero` range iteration | c02_type_system |
| 1.95 | `From<bool> for {f32,f64}` | c02_type_system |
| 1.95 | `VecDeque::new` const | c02_type_system, c13_embedded |
| 1.95 | `pin!` 宏 | c13_embedded, common |
| 1.95 | `DerefMut for PathBuf` | c13_embedded |
| 1.95 | `MAIN_SEPARATOR_STR` | c02_type_system |
| 1.96 | `expr` metavariable to `cfg` | c11_macro_system |
| 1.96 | `ManuallyDrop` as patterns | c02_type_system |
| 1.96 | `From<T> for LazyCell/LazyLock` | c02_type_system, concept |
| 1.96 | WASM `--allow-undefined` 移除 | c12_wasm |

### 3.2 版本标签状态

| 特性 | 实际版本 | 项目标签 | 状态 |
|------|---------|---------|------|
| `if let` guards | **1.95** | 1.96 | ⚠️ 待修正 |
| `From<bool> for {f32,f64}` | **1.68** | 1.68 ✅ | ✅ 已修正 |
| `VecDeque::new` const | **1.68** | 1.68 ✅ | ✅ 已修正 |
| `assert_matches!` | **1.95** | 1.96 | ⚠️ 部分标注有误 |
| `core::range` | **1.95** | 1.96 | ⚠️ 部分标注有误 |

### 3.3 活跃文档统计

| 目录 | Markdown 文件数 | 损坏链接 | 状态 |
|------|----------------|---------|------|
| `concept/` | ~200 | 0 | ✅ |
| `docs/` (非 archive) | ~300 | 0 | ✅ |
| `crates/` | 17 crates | 0 error 0 warning | ✅ |

---

## 四、对称差分析（A Δ B）

### 4.1 B−A：权威来源有、项目缺失

#### 🔴 P0 — 紧急（学习者无法获取）

| 特性/API | 来源版本 | 影响 | 建议归属 |
|---------|---------|------|---------|
| `cfg_select!` 宏 + 使用指南 | 1.95 | 编译期条件选择新范式 | c11_macro_system, docs |
| `Vec::push_mut` / `Vec::insert_mut` | 1.95 | 容器 API 重大改进 | c08_algorithms |
| `VecDeque::push_front_mut` / `push_back_mut` / `insert_mut` | 1.95 | 双端队列可变访问 | c08_algorithms |
| `LinkedList::push_front_mut` / `push_back_mut` | 1.95 | 链表可变访问 | c08_algorithms |
| `Atomic*::update` / `try_update` | 1.95 | 原子操作新范式 | c05_threads |
| `core::hint::cold_path` | 1.95 | 分支预测优化 | c05_threads, c08_algorithms |
| `Layout::dangling_ptr` / `repeat` / `extend_packed` | 1.95 | 内存布局 API | c02_type_system |
| `<*const/mut T>::as_ref_unchecked` / `as_mut_unchecked` | 1.95 | 裸指针安全转换 | c02_type_system |

#### 🟡 P1 — 重要（内容不完整）

| 特性/API | 来源版本 | 影响 | 建议归属 |
|---------|---------|------|---------|
| `bool: TryFrom<{integer}>` | 1.95 | 类型转换 | c02_type_system |
| `MaybeUninit` 数组转换 | 1.95 | 未初始化内存 | c02_type_system |
| `Cell<[T;N]>: AsRef` | 1.95 | 内部可变性 | c02_type_system |
| `Saturating` 类型 + 运算 | 1.95 | 饱和算术 | c02_type_system |
| `io_error_other` | 1.95 | 错误处理 | c10_networks |
| `fmt::from_fn` (const) | 1.95 | 格式化 | c02_type_system |
| `ControlFlow::is_break/is_continue` (const) | 1.95 | 控制流 | c03_control_fn |
| `--remap-path-scope` 深度指南 | 1.95 | 编译器标志 | docs |
| `-Cjump-tables=bool` | 1.95 | 编译器优化 | docs |
| C-style variadic functions | 1.95 | FFI | c10_networks |
| `asm_cfg` | 1.95 | 内联汇编 | c13_embedded |

#### 🟢 P2 — 扩展（前瞻/生态）

| 特性 | 来源 | 影响 | 建议归属 |
|------|------|------|---------|
| `gen` blocks 深度专题 | nightly | 生成器/协程 | c06_async, concept |
| `never_type` (`!`) 深度专题 | nightly (FCP) | 类型系统核心 | c02_type_system, concept |
| `cargo-script` 专题 | 2026 Goals | 脚本化 Rust | docs |
| `cargo-semver-checks` | 2026 Goals | 语义版本检查 | docs |
| Cranelift backend | 2026 Goals | 替代后端 | docs |
| Next-gen trait solver | 2026 Goals | 类型系统 | concept |
| Polonius 更新 | 2026 Goals | 借用检查器 | concept |
| Rust for Linux 深度专题 | 2026 Goals | 内核开发 | c13_embedded, concept |
| C++ ↔ Rust interop | 2026 Goals | 跨语言 | docs |
| Unsafe Fields | 实验中 | 内存安全 | concept |
| Arbitrary self types | RfL | 自定义 receiver | concept |
| Field projections | RfL | 字段投影 | concept |
| ADT const params | RfL | 常量泛型 | concept |
| Coherence domain / orphan rules | RfL | 一致性规则 | concept |

### 4.2 A−B：项目有、权威来源已变更/过时

| 项目内容 | 问题 | 建议动作 |
|---------|------|---------|
| `if let` guards 标注为 1.96 | 实际 1.95 stable | 修正所有标签 |
| `From<bool> for {f32,f64}` 在 `rust_196_features.rs` 中 | 实际 1.68，文件已正确标注 | 无需修正 |
| `VecDeque::new` const 在 exercises 中 | 实际 1.68，已修正 | ✅ 已修正 |
| `assert_matches!` 部分标注为 1.96 | 实际 1.95 | 修正标签 |
| `core::range` 部分标注为 1.96 | 实际 1.95 | 修正标签 |
| `wasm32-wasi` target 名称 | 已重命名为 `wasm32-wasip1` | 已修复 ✅ |
| `PinCoerceUnsized` 在 cheatsheet 中 | nightly-only，stable 不支持 | 标注为 nightly 前瞻 |
| `gen` blocks 在 cheatsheet 中 | nightly-only，stable 不支持 | 标注为 nightly 前瞻 |

### 4.3 优先级矩阵

```
影响高 +  effort 低 → 优先做
影响高 +  effort 高 → 计划做
影响低 +  effort 低 → 顺手做
影响低 +  effort 高 → 延后做
```

| 象限 | 任务 | effort | 影响 |
|------|------|--------|------|
| 优先做 | 版本标签修正（if let guards 等） | 低 | 高 |
| 优先做 | `cfg_select!` 专题指南 | 中 | 高 |
| 优先做 | `Vec::push_mut` / `VecDeque::push_*_mut` 代码示例 | 中 | 高 |
| 计划做 | `Atomic*::update` 代码示例 | 中 | 高 |
| 计划做 | `core::hint::cold_path` 代码示例 | 低 | 高 |
| 计划做 | `Layout::*_packed` 代码示例 | 中 | 中 |
| 计划做 | `gen` blocks 深度专题 | 高 | 高 |
| 计划做 | `never_type` 深度专题 | 高 | 高 |
| 顺手做 | `bool: TryFrom<{integer}>` | 低 | 中 |
| 顺手做 | `MaybeUninit` 数组转换 | 低 | 中 |
| 延后做 | Cranelift / cargo-semver-checks | 高 | 低 |
| 延后做 | Rust for Linux 深度专题 | 高 | 中 |

---

## 五、后续推进完善计划

### 阶段 1：紧急标签修正 + 核心 API 补齐（3-5 天）

**目标**：修正版本标签错误，补齐 P0 级缺失内容。

| 编号 | 任务 | 归属 | 交付物 | 验收标准 |
|------|------|------|--------|---------|
| T1.1 | 全量版本标签修正 | scripts | `scripts/version_fact_check.py` 通过 | 0 ERROR |
| T1.2 | `cfg_select!` 宏专题 | c11_macro_system | `CFG_SELECT_MACRO_GUIDE.md` + 代码 | 可运行示例 |
| T1.3 | `Vec::push_mut` / `insert_mut` | c08_algorithms | `rust_195_features.rs` 补充 | doctest 通过 |
| T1.4 | `VecDeque::push_*_mut` / `insert_mut` | c08_algorithms | `rust_195_features.rs` 补充 | doctest 通过 |
| T1.5 | `LinkedList::push_*_mut` | c08_algorithms | `rust_195_features.rs` 补充 | doctest 通过 |
| T1.6 | `Atomic*::update` / `try_update` | c05_threads | `rust_195_features.rs` 补充 | doctest 通过 |
| T1.7 | `core::hint::cold_path` | c05_threads / c08_algorithms | `rust_195_features.rs` 补充 | doctest 通过 |

### 阶段 2：标准库 API 补齐（5-7 天）

**目标**：补齐 P1 级标准库新 API。

| 编号 | 任务 | 归属 | 交付物 |
|------|------|------|--------|
| T2.1 | `Layout::dangling_ptr` / `repeat` / `extend_packed` | c02_type_system | 代码 + 概念说明 |
| T2.2 | `<*const/mut T>::as_ref_unchecked` / `as_mut_unchecked` | c02_type_system | 代码 + 安全分析 |
| T2.3 | `bool: TryFrom<{integer}>` | c02_type_system | 代码示例 |
| T2.4 | `MaybeUninit` 数组转换 | c02_type_system | 代码示例 |
| T2.5 | `Cell<[T;N]>: AsRef` | c02_type_system | 代码示例 |
| T2.6 | `Saturating` 类型 | c02_type_system | 代码 + 概念说明 |
| T2.7 | `io_error_other` | c10_networks | 代码示例 |
| T2.8 | `--remap-path-scope` 深度指南 | docs | 配置指南 |

### 阶段 3：Nightly 前瞻专题（7-10 天）

**目标**：创建 `gen` blocks 和 `never_type` 的深度专题。

| 编号 | 任务 | 归属 | 交付物 |
|------|------|------|--------|
| T3.1 | `gen` blocks 深度专题 | c06_async, concept | 概念文件 + crate 代码 |
| T3.2 | `never_type` (`!`) 深度专题 | c02_type_system, concept | 概念文件 + crate 代码 |
| T3.3 | `explicit_tail_calls` 预览 | concept | preview 文件更新 |
| T3.4 | `c_variadic` function definitions | c10_networks | preview 文件 + 代码 |
| T3.5 | `cargo-script` 专题 | docs | 使用指南 |

### 阶段 4：生态与前瞻对齐（持续）

**目标**：对齐 Rust 2026 Project Goals 和 Rust for Linux 需求。

| 编号 | 任务 | 归属 | 优先级 |
|------|------|------|--------|
| T4.1 | Next-gen trait solver 概念更新 | concept | P1 |
| T4.2 | Polonius 更新 | concept | P1 |
| T4.3 | Rust for Linux 深度专题 | c13_embedded, concept | P1 |
| T4.4 | C++ ↔ Rust interop 评估 | docs | P2 |
| T4.5 | Unsafe Fields 预览 | concept | P2 |
| T4.6 | Arbitrary self types 预览 | concept | P2 |
| T4.7 | Field projections 预览 | concept | P2 |
| T4.8 | ADT const params 预览 | concept | P2 |
| T4.9 | Coherence domain / orphan rules | concept | P2 |

### 时间线

```
Week 1 (2026-05-29 ~ 06-04): 阶段 1 — 标签修正 + P0 API 补齐
Week 2 (2026-06-05 ~ 06-11): 阶段 2 — P1 标准库 API 补齐
Week 3 (2026-06-12 ~ 06-18): 阶段 3 — Nightly 前瞻专题
Week 4+ (2026-06-19 ~     ): 阶段 4 — 生态对齐（持续）
```

---

## 六、验收标准

| 阶段 | 验收标准 |
|------|---------|
| 阶段 1 | `cargo test --workspace` 全通过；`version_fact_check.py` 0 ERROR；P0 API 全部有可运行示例 |
| 阶段 2 | 1.95 标准库新 API 覆盖率 ≥ 80%；`cargo clippy` 0 warning |
| 阶段 3 | `gen` blocks 和 `never_type` 专题有完整概念文件 + 可运行代码 |
| 阶段 4 | Rust 2026 Goals 相关特性均有至少 preview 文件；每季度更新一次 |

---

## 七、参考

> **[来源: Rust Official Docs]**
> **[来源: Rust Standard Library - doc.rust-lang.org/std]**
> **[来源: Rust Reference - doc.rust-lang.org/reference]**
> **[来源: RFCs - github.com/rust-lang/rfcs]**
> **[来源: releases.rs]**
> **[来源: blog.rust-lang.org]**
> **[来源: Inside Rust Blog]**
> **[来源: Rust Forge]**

| 来源 | URL | 用途 |
|------|-----|------|
| Rust Release Notes | <https://doc.rust-lang.org/beta/releases.html> | 版本特性 |
| releases.rs | <https://releases.rs/docs/1.96.0/> | 详细变更日志 |
| Rust Blog | <https://blog.rust-lang.org/releases/latest/> | 发布公告 |
| Inside Rust Blog | <https://blog.rust-lang.org/inside-rust/> | 内部进展 |
| Rust Forge | <https://forge.rust-lang.org/> | 版本时间线 |
| RFC Book | <https://rust-lang.github.io/rfcs/> | 设计规范 |
| GitHub Tracking Issues | <https://github.com/rust-lang/rust/issues> | 特性追踪 |
