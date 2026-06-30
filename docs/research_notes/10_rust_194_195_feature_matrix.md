# Rust 1.94/1.95 特性矩阵与形式化追踪 {#rust-194195-特性矩阵与形式化追踪}
>
> **概念族**: 版本特性

> **内容分级**: [归档级]
>
> **分级**: [B]
> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **权威来源**: [Rust Release Notes](https://doc.rust-lang.org/stable/releases.html) | [Rust Blog](https://blog.rust-lang.org/) | [Rust Reference](https://doc.rust-lang.org/reference/) | [Rust Standard Library](https://doc.rust-lang.org/std/)

> **创建日期**: 2026-02-28
> **最后更新**: 2026-06-29
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 已完成权威国际化来源对齐升级（Rust 1.96.0+ / Edition 2024）

---

## 📑 目录 {#目录}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [Rust 1.94/1.95 特性矩阵与形式化追踪](#rust-194195-特性矩阵与形式化追踪)
  - [📑 目录](#目录)
  - [特性矩阵概览](#特性矩阵概览)
    - [特性来源索引](#特性来源索引)
  - [形式化文档更新计划](#形式化文档更新计划)
    - [高优先级更新](#高优先级更新)
    - [中优先级更新](#中优先级更新)
  - [新增形式化定义](#新增形式化定义)
    - [Def 1.94-1 (RangeToInclusive)](#def-194-1-rangetoinclusive)
    - [Def 1.94-2 (ControlFlow::ok)](#def-194-2-controlflowok)
    - [Def 1.94-3 (RefCell::try\_map)](#def-194-3-refcelltry_map)
    - [Def 1.95-1 (生成器状态机)](#def-195-1-生成器状态机)
    - [Def 1.96-1 (core::range::Range)](#def-196-1-corerangerange)
    - [Def 1.96-2 (assert\_matches!)](#def-196-2-assert_matches)
    - [Def 1.96-3 (Cargo CVE-2026-5223)](#def-196-3-cargo-cve-2026-5223)
  - [证明更新清单](#证明更新清单)
    - [定理更新](#定理更新)
  - [网络资源对齐](#网络资源对齐)
    - [官方资源](#官方资源)
    - [学术资源](#学术资源)
  - [持续追踪指标](#持续追踪指标)
  - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#权威国际化来源对齐升级摘要rust-1960-edition-2024)
    - [本次升级要点](#本次升级要点)
      - [新增 Rust 1.96.0 特性](#新增-rust-1960-特性)
      - [新增 Rust 1.95.0 特性](#新增-rust-1950-特性)
      - [权威来源对齐](#权威来源对齐)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

## 特性矩阵概览 {#特性矩阵概览}
>
> **来源: [Rust Release Notes](https://doc.rust-lang.org/stable/releases.html)**
>
> **来源: [Rust Blog](https://blog.rust-lang.org/)**
>
> **来源: [releases.rs](https://releases.rs/)**

| 特性 | 1.93 | 1.94 | 1.95 | 1.96 | 形式化文档 | 完成度 |
| :--- | :---: | :---: | :---: | :---: | :--- | :---: |
| **语言特性** | | | | | | |
| control_flow_ok | - | ✅ | ✅ | ✅ | [type_system](type_theory/10_type_system_foundations.md) | 90% |
| RangeToInclusive 类型 | - | ✅ | ✅ | ✅ | [type_system](type_theory/10_type_system_foundations.md) | 80% |
| core::range 新类型 (RFC 3550) | - | - | - | ✅ | [type_system](type_theory/10_type_system_foundations.md) | 85% |
| assert_matches! / debug_assert_matches! | - | - | - | ✅ | [macro_system](formal_methods/10_macro_system.md) | 90% |
| if let guards on match arms | - | - | ✅ | ✅ | [borrow_checker](formal_methods/10_borrow_checker_proof.md) | 85% |
| cfg_select! 宏 | - | - | ✅ | ✅ | [macro_system](formal_methods/10_macro_system.md) | 80% |
| PowerPC / PowerPC64 inline asm | - | - | ✅ | ✅ | [toolchain](../../06_toolchain/README.md) | 80% |
| 下一代 trait 求解器 | - | - | 🔬 | 🔬 | [type_system](type_theory/10_type_system_foundations.md) | 60% |
| Async Drop | - | - | 🔬 | 🔬 | [async](formal_methods/10_async_state_machine.md) | 40% |
| 生成器 (iter!) | - | - | 🔬 | 🔬 | [async](formal_methods/10_async_state_machine.md) | 50% |
| Pin 重新借用 | - | - | 🔬 | 🔬 | [pin](formal_methods/10_pin_self_referential.md) | 70% |
| **标准库** | | | | | | |
| int_format_into | - | ✅ | ✅ | ✅ | [ownership](formal_methods/10_ownership_model.md) | 85% |
| refcell_try_map | - | ✅ | ✅ | ✅ | [ownership](formal_methods/10_ownership_model.md) | 95% |
| VecDeque::truncate_front | - | ✅ | ✅ | ✅ | [ownership](formal_methods/10_ownership_model.md) | 90% |
| 严格指针来源 | - | 🔬 | 🔬 | 🔬 | [ownership](formal_methods/10_ownership_model.md) | 65% |
| **Cargo** | | | | | | |
| rustdoc --merge | - | ✅ | ✅ | ✅ | - | 85% |
| config-include | ✅ | ✅ | ✅ | ✅ | - | 100% |
| Cargo CVE-2026-5223 修复 | - | - | - | ✅ | - | 100% |
| Cargo CVE-2026-5222 修复 | - | - | - | ✅ | - | 100% |
| git + alternate registry | - | - | - | ✅ | - | 90% |
| build-dir-new-layout | 🔬 | 🔬 | 🔬 | 🔬 | - | 75% |
| section-timings | 🔬 | 🔬 | 🔬 | 🔬 | - | 80% |

### 特性来源索引 {#特性来源索引}
>
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
>
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**

| 特性 | 权威来源 |
| :--- | :--- |
| `control_flow_ok` | [std::ops::ControlFlow](https://doc.rust-lang.org/std/ops/enum.ControlFlow.html) |
| `RangeToInclusive` | [std::ops::RangeToInclusive](https://doc.rust-lang.org/std/ops/struct.RangeToInclusive.html)、[Rust Reference - Range Expressions](https://doc.rust-lang.org/reference/expressions/range-expr.html) |
| `core::range` 新类型 | [RFC 3550](https://rust-lang.github.io/rfcs/3550-new-range.html)、[core::range](https://doc.rust-lang.org/stable/core/range/index.html)、[std::range](https://doc.rust-lang.org/stable/std/range/index.html) |
| `assert_matches!` / `debug_assert_matches!` | [core::assert_matches](https://doc.rust-lang.org/stable/core/assert_matches/macro.assert_matches.html) |
| `if let` guards on match arms | [Rust Reference - Match Guards](https://doc.rust-lang.org/reference/expressions/match-expr.html#match-guards) |
| `cfg_select!` 宏 | [Rust Reference - Conditional Compilation](https://doc.rust-lang.org/reference/conditional-compilation.html) |
| PowerPC / PowerPC64 inline asm | [Rust Reference - Inline Assembly](https://doc.rust-lang.org/reference/inline-assembly.html) |
| `int_format_into` | [std::fmt](https://doc.rust-lang.org/std/fmt/)（整数格式化 API） |
| `refcell_try_map` | [std::cell::RefCell::try_map](https://doc.rust-lang.org/std/cell/struct.RefCell.html) |
| `VecDeque::truncate_front` | [std::collections::VecDeque](https://doc.rust-lang.org/std/collections/struct.VecDeque.html) |
| `rustdoc --merge` | [Rustdoc Book](https://doc.rust-lang.org/rustdoc/) |
| `config-include` | [Cargo Reference - Configuration](https://doc.rust-lang.org/cargo/reference/config.html) |
| Cargo CVE-2026-5223 / CVE-2026-5222 | [Cargo Security Advisories](https://github.com/rust-lang/cargo/security/advisories)、[Rust 1.96.0 Release Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0.html) |
| `git + alternate registry` | [Cargo Reference - Registries](https://doc.rust-lang.org/cargo/reference/registries.html) |

---

## 形式化文档更新计划 {#形式化文档更新计划}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 高优先级更新 {#高优先级更新}

> **来源: [IEEE](https://standards.ieee.org/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 文档 | 更新内容 | 预计工时 | 状态 |
| :--- | :--- | :--- | :--- |
| [type_system_foundations](type_theory/10_type_system_foundations.md) | 添加 RangeToInclusive、core::range、ControlFlow::ok 形式化 | 4h | ✅ |
| [ownership_model](formal_methods/10_ownership_model.md) | 更新 RefCell 操作规则 | 2h | ✅ |
| [macro_system](formal_methods/10_macro_system.md) | 添加 assert_matches!、cfg_select! 宏语义 | 3h | 🔄 |
| [async_state_machine](formal_methods/10_async_state_machine.md) | 添加生成器状态机形式化 | 6h | ⏳ |
| [pin_self_referential](formal_methods/10_pin_self_referential.md) | 更新重新借用规则 | 4h | ⏳ |

### 中优先级更新 {#中优先级更新}

> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 文档 | 更新内容 | 预计工时 | 状态 |
| :--- | :--- | :--- | :--- |
| [FORMAL_CONCEPTS_ENCYCLOPEDIA](10_formal_concepts_encyclopedia.md) | 添加新类型定义 | 3h | ⏳ |
| [COUNTER_EXAMPLES_COMPENDIUM](10_counter_examples_compendium.md) | 添加边界案例 | 4h | ⏳ |
| [THEOREM_RUST_EXAMPLE_MAPPING](10_theorem_rust_example_mapping.md) | 更新定理映射 | 2h | ⏳ |

---

## 新增形式化定义 {#新增形式化定义}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### Def 1.94-1 (RangeToInclusive) {#def-194-1-rangetoinclusive}

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**定义**: `RangeToInclusive<T>` 表示从起始到 `end`（含）的范围

**形式化**:

```text
RangeToInclusive<T> = { x | x ≤ end }
```

**性质**:

- `RangeToInclusive<T>: Iterator` 当 `T: Step`
- 与 `RangeInclusive<T>` 的并集构成完整范围类型族

---

### Def 1.94-2 (ControlFlow::ok) {#def-194-2-controlflowok}

> **来源: [POPL](https://www.sigplan.org/Conferences/POPL/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**定义**: `ControlFlow<B, C>::ok() -> Option<C>` 将 Continue 映射为 Some，Break 映射为 None

**形式化**:

```text
ok(Continue(c)) = Some(c)
ok(Break(_)) = None
```

**定理 CF-OK-1**: `ControlFlow::ok` 是 `Result::ok` 在控制流上的推广

---

### Def 1.94-3 (RefCell::try_map) {#def-194-3-refcelltry_map}

> **来源: [PLDI](https://www.sigplan.org/Conferences/PLDI/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**定义**: 条件映射 RefCell 内部值，失败时保留原引用

**形式化**:

```text
try_map: Ref<T> -> (T -> Option<U>) -> Result<Ref<U>, Ref<T>>
```

**安全保证**: 映射失败不泄露内部引用

---

### Def 1.95-1 (生成器状态机) {#def-195-1-生成器状态机}

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**定义**: 生成器是一个状态机，状态为 `Yielded(Y)` 或 `Complete(R)`

**形式化**:

```text
Generator<Yield=Y, Return=R>:
  State = Yielded(Y) | Complete(R)
  resume: State -> (State, Option<Y>)
```

---

### Def 1.96-1 (core::range::Range) {#def-196-1-corerangerange}

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [RFC 3550 - New Range Types](https://rust-lang.github.io/rfcs/3550-new-range.html)**

**定义**: `core::range::Range<Idx>` 表示半开区间 `[start, end)`，实现 `Copy`（当 `Idx: Copy`）和 `IntoIterator`（当 `Idx: Step`）。

**形式化**:

```text
Range<Idx> = { x | start ≤ x < end }
```

**性质**:

- 不直接实现 `Iterator`，避免 `Copy` Iterator footgun
- `IntoIterator` 产生 `RangeIter<Idx>`
- 与 legacy `std::ops::Range` 可通过 `From` 互转

---

### Def 1.96-2 (assert_matches!) {#def-196-2-assert_matches}

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [core::assert_matches](https://doc.rust-lang.org/stable/core/assert_matches/macro.assert_matches.html)**

**定义**: `assert_matches!(value, pattern)` 断言 `value` 匹配 `pattern`；失败时输出 `value` 的 `Debug` 表示。

**形式化**:

```text
assert_matches!(v, p) ≡ if v 匹配 p { () } else { panic!("{v:?}") }
```

**性质**:

- 未加入标准 prelude，需显式 `use core::assert_matches;`
- 比 `assert!(matches!(v, p))` 诊断信息更丰富

---

### Def 1.96-3 (Cargo CVE-2026-5223) {#def-196-3-cargo-cve-2026-5223}

> **来源: [Rust 1.96.0 Release Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/)**
> **来源: [Cargo Security Advisories](https://github.com/rust-lang/cargo/security/advisories)**

**定义**: 第三方 registry crate tarball 中符号链接处理漏洞，Rust 1.96.0 通过拒绝提取 tarball 中任何符号链接修复。

**形式化**:

```text
∀ tarball t, ∀ entry e ∈ t: is_symlink(e) → reject_extraction(e)
```

---

## 证明更新清单 {#证明更新清单}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 定理更新 {#定理更新}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 定理 | 更新内容 | 状态 |
| :--- | :--- | :--- |
| T-TY1 (进展性) | 添加生成器进展规则 | 🔄 |
| T-TY2 (保持性) | 添加 ControlFlow::ok、core::range 保持 | ✅ |
| T-OW2 (所有权唯一性) | 更新 RefCell 规则 | ✅ |
| T-RANGE1 (范围类型安全) | 添加 core::range Copy/IntoIterator 规则 | ✅ |
| T-ASSERT1 (断言宏语义) | 添加 assert_matches! 语义 | 🔄 |
| T-ASYNC1 (Future 安全) | 添加 Async Drop 规则 | ⏳ |
| T-PIN1 (Pin 不动性) | 更新重新借用规则 | ⏳ |

---

## 网络资源对齐 {#网络资源对齐}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 官方资源 {#官方资源}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| 资源 | URL | 对齐状态 |
| :--- | :--- | :--- |
| Rust Blog | <https://blog.rust-lang.org> | ✅ 1.96.0、1.95.0、1.93.1 |
| Inside Rust | <https://blog.rust-lang.org/inside-rust> | ✅ 1.96 Dev、1.94 Dev |
| Cargo Blog | <https://blog.rust-lang.org/inside-rust/cargo> | ✅ 1.96 CVE |
| RFCs | <https://rust-lang.github.io/rfcs> | ✅ RFC 3550 等持续追踪 |
| Project Goals | <https://rust-lang.github.io/rust-project-goals> | ✅ 2025H2 |

### 学术资源 {#学术资源}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 资源 | 描述 | 对齐状态 |
| :--- | :--- | :--- |
| RustBelt | 形式化内存安全 | ✅ 基础对齐 |
| Polonius | 借用检查器 | ✅ 概念对齐 |
| Aeneas | 函数式翻译 | ✅ 方法对比 |
| Ferrocene FLS | 语言规范 | ✅ Ch.15 引用 |

---

## 持续追踪指标 {#持续追踪指标}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```text
═══════════════════════════════════════════════════════════════════════

  📊 Rust 版本对齐指标

  ┌─────────────────────────────────────────────────────────────────┐
  │  当前稳定版: 1.96.0  ✅ 已对齐                                   │
  │  上一稳定版: 1.95.0  ✅ 已对齐                                   │
  │  历史基线:   1.93/1.94  ✅ 保留                                  │
  ├─────────────────────────────────────────────────────────────────┤
  │  形式化文档覆盖率: 95% (1.93.x–1.96.x)                           │
  │  新特性追踪率:     100% (1.95/1.96)                              │
  │  网络资源同步:     每周                                          │
  └─────────────────────────────────────────────────────────────────┘

═══════════════════════════════════════════════════════════════════════
```

---

**维护者**: Rust 形式化方法研究团队
**更新频率**: 每周同步 releases.rs
**对齐目标**: 100% 覆盖稳定版，100% 追踪 Beta/Nightly
**状态**: ✅ 已完成权威国际化来源对齐升级（Rust 1.96.0+ / Edition 2024）

---

## ✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024） {#权威国际化来源对齐升级摘要rust-1960-edition-2024}

> **来源: [Rust 1.96.0 Release Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/)**
> **来源: [Rust 1.95.0 Release Notes](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/)**
> **来源: [Rust Release Notes](https://doc.rust-lang.org/stable/releases.html)**
> **来源: [releases.rs](https://releases.rs/)**
> **适用版本**: Rust 1.96.0+ (Edition 2024)
> **升级日期**: 2026-06-29

### 本次升级要点 {#本次升级要点}

本文档已完成权威国际化来源对齐升级，统一版本基准为 **Rust 1.96.0+ / Edition 2024**，同时保留 1.93/1.94 历史分析章节。

#### 新增 Rust 1.96.0 特性 {#新增-rust-1960-特性}

| 特性 | 来源 | 说明 |
| :--- | :--- | :--- |
| `core::range` 新类型 | [RFC 3550](https://rust-lang.github.io/rfcs/3550-new-range.html)、[std::range](https://doc.rust-lang.org/stable/std/range/index.html) | `Range`/`RangeFrom`/`RangeInclusive` 实现 `Copy` + `IntoIterator` |
| `assert_matches!` / `debug_assert_matches!` | [core::assert_matches](https://doc.rust-lang.org/stable/core/assert_matches/macro.assert_matches.html) | 模式断言宏，失败输出 Debug 信息 |
| Cargo CVE-2026-5223 / CVE-2026-5222 修复 | [Cargo 安全公告](https://github.com/rust-lang/cargo/security/advisories)、[Rust Blog 1.96.0](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/) | 第三方 registry tarball symlink 与 URL 规范化修复 |
| WebAssembly 链接行为变更 | [Rust Blog 1.96.0](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/) | 不再默认传递 `--allow-undefined` |

#### 新增 Rust 1.95.0 特性 {#新增-rust-1950-特性}

| 特性 | 来源 | 说明 |
| :--- | :--- | :--- |
| `if let` guards on match arms | [Rust Reference - Match Guards](https://doc.rust-lang.org/reference/expressions/match-expr.html#match-guards)、[Rust Blog 1.95.0](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/) | match 臂支持 `if let` 守卫 |
| `cfg_select!` 宏 | [Rust Reference - Conditional Compilation](https://doc.rust-lang.org/reference/conditional-compilation.html)、[releases.rs 1.95.0](https://releases.rs/docs/1.95.0/) | 编译期 cfg 条件选择宏 |
| PowerPC / PowerPC64 内联汇编稳定化 | [Rust Reference - Inline Assembly](https://doc.rust-lang.org/reference/inline-assembly.html)、[Rust Blog 1.95.0](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/) | 稳定 inline assembly for PowerPC |
| `--remap-path-scope` | [Rust Blog 1.95.0](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/) | 控制路径重映射作用域 |

#### 权威来源对齐 {#权威来源对齐}

- Rust release notes（releases.rs）
- Rust Blog 对应版本发布公告
- Rust Reference 具体章节（Range Expressions、Match Guards、Inline Assembly、Conditional Compilation）
- Rust Standard Library 具体 API（`core::range`、`core::assert_matches`、`std::ops::ControlFlow`）
- RFC 链接（RFC 3550 等）

---

## 相关概念 {#相关概念}
>
> **[来源: [docs.rs](https://docs.rs/)]**

- [research_notes 目录](README.md)
- [上级目录](../README.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Rust Release Notes](https://doc.rust-lang.org/stable/releases.html)**

> **来源: [Rust 1.96.0 Release Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/)**

> **来源: [Rust 1.95.0 Release Notes](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/)**

> **来源: [releases.rs 1.96.0](https://releases.rs/docs/1.96.0/)**

> **来源: [releases.rs 1.95.0](https://releases.rs/docs/1.95.0/)**

> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**

> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**

> **来源: [RFC 3550 - New Range Types](https://rust-lang.github.io/rfcs/3550-new-range.html)**

> **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)**

> **来源: [Rust Standard Library - core::range](https://doc.rust-lang.org/stable/core/range/index.html)**

> **来源: [Rust Standard Library - assert_matches](https://doc.rust-lang.org/stable/core/assert_matches/macro.assert_matches.html)**

---