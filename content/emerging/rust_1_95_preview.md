# Rust 1.95 稳定特性全景

> **版本**: Rust 1.95.0 (Stable)
> **发布日期**: 2026-04-16
> **状态**: ✅ 已稳定
> **Edition**: 2024 (默认)
> **MSRV**: 1.95.0

---

> 本文档汇总 Rust 1.95.0 所有稳定特性及项目内对应示例位置。
> 完整速查表请见 [`docs/02_reference/quick_reference/rust_195_features_cheatsheet.md`](../../docs/02_reference/quick_reference/rust_195_features_cheatsheet.md)。

---

## 📋 目录

- [Rust 1.95 稳定特性全景](.#rust-195-稳定特性全景)
  - [📋 目录](.#-目录)
  - [🎯 版本概览](.#-版本概览)
  - [🚀 语言特性](.#-语言特性)
    - [1. `if let` guards (1.95.0)](.#1-if-let-guards-1950)
    - [2. `cfg_select!` (1.95.0)](.#2-cfg_select-1950)
    - [3. `use<..>` precise capturing (Edition 2024)](.#3-use-precise-capturing-edition-2024)
    - [4. RPITIT / AFIT (1.75+ 稳定，1.95 深入)](.#4-rpitit--afit-175-稳定195-深入)
  - [📦 标准库 API](.#-标准库-api)
    - [1. `Atomic*::update` / `try_update`](.#1-atomicupdate--try_update)
    - [2. `Vec::push_mut` / `insert_mut`](.#2-vecpush_mut--insert_mut)
    - [3. `VecDeque` / `LinkedList` mut 方法](.#3-vecdeque--linkedlist-mut-方法)
    - [4. `core::range::RangeInclusive` 算法](.#4-corerangerangeinclusive-算法)
    - [5. `std::hint::cold_path`](.#5-stdhintcold_path)
    - [6. `bool` → 整数 `TryFrom`](.#6-bool--整数-tryfrom)
  - [📊 与 1.94 / 1.96 对比](.#-与-194--196-对比)
  - [🔄 迁移指南](.#-迁移指南)
    - [嵌套 match → `if let` guards](.#嵌套-match--if-let-guards)
    - [嵌套 `cfg!` → `cfg_select!`](.#嵌套-cfg--cfg_select)
    - [CAS 循环 → `Atomic::update`](.#cas-循环--atomicupdate)
  - [📁 项目内对应示例](.#-项目内对应示例)
  - [🔗 参考资源](.#-参考资源)

---

## 🎯 版本概览

Rust 1.95 主要聚焦于：

- **语言特性**: `if let` guards、`cfg_select!`、`use<..>` precise capturing (Edition 2024)
- **API 扩展**: `Atomic::update`、集合 `push_mut`/`insert_mut`、`core::range` 算法、`cold_path`
- **性能**: 编译器增量编译优化、并行宏扩展
- **生态对齐**: WASI Preview 2 组件模型工具链成熟

---

## 🚀 语言特性

### 1. `if let` guards (1.95.0)

**描述**: 在 match arm 中使用 `if let P = expr && condition` 进行条件模式匹配。

```rust
match token {
    Some(s) if let Ok(n) = s.parse::<u32>() && n > 0 => {
        // n 在此作用域内可用
        process_positive(n);
    }
    _ => skip(),
}
```

**关键限制**: guard 中绑定的变量**不可**在 arm body 外部使用。

**与 let chains 区别**: guard 是 match-arm 级别；let chains (1.88+) 是表达式级别。

**项目示例**: `crates/c03_control_fn/src/if_let_guards_deep_dive.rs`

---

### 2. `cfg_select!` (1.95.0)

**描述**: 在表达式位置进行多分支条件编译，替代嵌套 `cfg!` 宏。

```rust
let page_size = cfg_select! {
    target_os = "windows" => 4096_usize,
    target_os = "linux" => 4096_usize,
    target_os = "macos" => 16384_usize,
    _ => 4096_usize,
};
```

**适用场景**: 跨平台常量、条件表达式、特征门控逻辑。

**项目示例**: `crates/c08_algorithms/src/rust_195_features.rs`

---

### 3. `use<..>` precise capturing (Edition 2024)

**描述**: 精确控制 `impl Trait` 捕获的生命周期和类型参数。

```rust
// 2021 Edition: 自动捕获所有生命周期
fn make_iter<'a>(s: &'a str) -> impl Iterator<Item = char> + 'a { ... }

// 2024 Edition: 精确捕获
fn make_iter<'a>(s: &'a str) -> impl Iterator<Item = char> + use<'a> { ... }
```

**优势**: 减少不必要的约束、改善 API 演进兼容性。

**项目示例**: `crates/c02_type_system/src/precise_capturing_guide.rs`

---

### 4. RPITIT / AFIT (1.75+ 稳定，1.95 深入)

**描述**: Trait 关联类型和异步函数中的 `impl Trait`。

```rust
trait Producer {
    fn make(&self) -> impl Product;  // RPITIT
    async fn fetch(&self) -> impl Product;  // AFIT
}
```

**项目示例**: `crates/c02_type_system/src/type_system_frontier.rs`

---

## 📦 标准库 API

### 1. `Atomic*::update` / `try_update`

**描述**: 原子性读取-修改-写入，替代手动的 CAS 循环。

```rust
use std::sync::atomic::AtomicUsize;

let counter = AtomicUsize::new(0);
let new = counter.update(|old| old + 1);  // 无 CAS 循环
let maybe = counter.try_update(|old| if old < 100 { Some(old + 1) } else { None });
```

**项目示例**: `crates/c05_threads/src/rust_195_features.rs`

---

### 2. `Vec::push_mut` / `insert_mut`

**描述**: 插入元素并返回 `&mut T`。

```rust
let mut vec = vec![1, 2, 3];
let new_ref: &mut i32 = vec.push_mut(42);
*new_ref *= 2;  // 立即修改新元素
```

**项目示例**: `crates/c08_algorithms/src/rust_195_features.rs`

---

### 3. `VecDeque` / `LinkedList` mut 方法

**描述**: `push_front_mut`、`push_back_mut`、`insert_mut`。

```rust
use std::collections::VecDeque;

let mut deque = VecDeque::new();
let front = deque.push_front_mut("first");
*front = "FIRST";
```

**项目示例**: `crates/c02_type_system/src/rust_195_features.rs`

---

### 4. `core::range::RangeInclusive` 算法

**描述**: 范围上的集合运算（交集、并集、包含检测）。

```rust
use core::range::RangeInclusive;

let a = RangeInclusive::new(1, 5);
let b = RangeInclusive::new(3, 7);
assert!(a.intersects(&b));
```

**项目示例**: `crates/c08_algorithms/src/rust_195_features.rs`

---

### 5. `std::hint::cold_path`

**描述**: 标记不太可能执行的分支，优化编译器代码布局。

```rust
fn parse_number(s: &str) -> Result<i32, ParseError> {
    if s.is_empty() {
        std::hint::cold_path();
        return Err(ParseError::Empty);
    }
    s.parse().map_err(|_| ParseError::Invalid)
}
```

**项目示例**: `crates/c07_process/src/rust_195_features.rs`

---

### 6. `bool` → 整数 `TryFrom`

**描述**: `bool` 可以安全转换为整数类型。

```rust
let flag: bool = true;
let n: u8 = u8::try_from(flag).unwrap();  // 1
```

**项目示例**: `crates/c03_control_fn/src/rust_195_features.rs`

---

## 📊 与 1.94 / 1.96 对比

| 特性 | 1.94 | 1.95 | 1.96 | 影响 |
|------|------|------|------|------|
| `array_windows` | ✅ | ✅ | ✅ | - |
| `LazyCell/LazyLock` | ✅ | ✅ | ✅ | - |
| `if let` guards | ❌ | ✅ | ✅ | **重大** |
| `cfg_select!` | ❌ | ✅ | ✅ | **中等** |
| `use<..>` precise capturing | Edition 2024 | ✅ | ✅ | **中等** |
| `Atomic::update` | ❌ | ✅ | ✅ | **中等** |
| `push_mut` / `insert_mut` | ❌ | ✅ | ✅ | **中等** |
| `core::range` 算法 | ❌ | ✅ | ✅ | **低** |
| `cold_path` | ❌ | ✅ | ✅ | **低** |
| `bool` TryFrom | ❌ | ✅ | ✅ | **低** |
| `impl Trait` in assoc type (full) | 部分 | ✅ | ✅ | **重大** |
| `never_type` (`!`) | 部分 | 大部分 | 目标完整 | **中等** |
| `const` 泛型表达式 | nightly | nightly | 推进 | **长期** |

---

## 🔄 迁移指南

### 嵌套 match → `if let` guards

```rust
// ❌ Rust 2021: 嵌套 match
match token {
    Some(s) => match s.parse::<u32>() {
        Ok(n) if n > 0 => process(n),
        _ => skip(),
    },
    _ => skip(),
}

// ✅ Rust 2024 + 1.95: if let guard
match token {
    Some(s) if let Ok(n) = s.parse::<u32>() && n > 0 => process(n),
    _ => skip(),
}
```

### 嵌套 `cfg!` → `cfg_select!`

```rust
// ❌ 嵌套 cfg! 混乱
let size = if cfg!(target_os = "windows") { 4096 }
           else if cfg!(target_os = "macos") { 16384 }
           else { 4096 };

// ✅ cfg_select! 清晰
let size = cfg_select! {
    target_os = "windows" => 4096,
    target_os = "macos" => 16384,
    _ => 4096,
};
```

### CAS 循环 → `Atomic::update`

```rust
// ❌ 手动 CAS 循环
loop {
    let old = counter.load(Relaxed);
    if counter.compare_exchange(old, old + 1, Relaxed, Relaxed).is_ok() {
        break;
    }
}

// ✅ Atomic::update
let new = counter.update(|old| old + 1);
```

---

## 📁 项目内对应示例

| 特性 | 主要示例位置 | 练习位置 |
|------|-------------|---------|
| `if let` guards | `crates/c03_control_fn/src/if_let_guards_deep_dive.rs` | `exercises/src/rust_195_feature_exercises.rs` |
| `cfg_select!` | `crates/c08_algorithms/src/rust_195_features.rs` | `exercises/src/rust_195_feature_exercises.rs` |
| `Atomic::update` | `crates/c05_threads/src/rust_195_features.rs` | `exercises/src/rust_195_feature_exercises.rs` |
| `push_mut` | `crates/c08_algorithms/src/rust_195_features.rs` | `exercises/src/rust_195_feature_exercises.rs` |
| `cold_path` | `crates/c07_process/src/rust_195_features.rs` | `exercises/src/rust_195_feature_exercises.rs` |
| `use<..>` precise capturing | `crates/c02_type_system/src/precise_capturing_guide.rs` | - |
| `core::range` | `crates/c08_algorithms/src/rust_195_features.rs` | - |
| `bool` TryFrom | `crates/c03_control_fn/src/rust_195_features.rs` | - |

---

## 🔗 参考资源

- [Rust 1.95 Release Notes](https://releases.rs/docs/1.95.0/)
- [项目对称差分析报告 v2.0](../../reports/RUST_195_EVOLUTION_SYMMETRIC_DIFFERENCE_ANALYSIS_2026_05_08.md)
- [Async Closures 深度指南](../../crates/c06_async/docs/ASYNC_CLOSURES_GUIDE.md)
- [Cargo Script 指南](../../docs/06_toolchain/cargo_script_guide.md)
- [Safety Tags 预研](../../docs/05_guides/SAFETY_TAGS_GUIDE.md)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
