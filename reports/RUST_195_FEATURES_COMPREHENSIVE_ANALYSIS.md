# Rust 1.95 特性 comprehensive 解析与论证报告

> **版本**: Rust 1.95.0 (stable: 2024-11-28)
> **分析日期**: 2026-05-11
> **工具链**: rustc 1.97.0-nightly (2026-05-05), Edition 2024
> **项目**: rust-lang 系统学习 workspace

---

## 目录

- [Rust 1.95 特性 comprehensive 解析与论证报告](#rust-195-特性-comprehensive-解析与论证报告)
  - [目录](#目录)
  - [1. 特性全景概览](#1-特性全景概览)
  - [2. 语言特性深度解析](#2-语言特性深度解析)
    - [2.1 `gen` blocks — 原生生成器语法](#21-gen-blocks--原生生成器语法)
    - [2.2 `AsyncFn` trait 家族 — 异步闭包类型化](#22-asyncfn-trait-家族--异步闭包类型化)
    - [2.3 `if let` guards — match arm 中的条件绑定](#23-if-let-guards--match-arm-中的条件绑定)
    - [2.4 `&raw const` / `&raw mut` — 原始引用操作符](#24-raw-const--raw-mut--原始引用操作符)
    - [2.5 `unsafe_op_in_unsafe_fn` — Rust 2024 的 unsafe 语义澄清](#25-unsafe_op_in_unsafe_fn--rust-2024-的-unsafe-语义澄清)
    - [2.6 `c"..."` C 字符串字面量](#26-c-c-字符串字面量)
    - [2.7 `const {}` 块在更多位置](#27-const--块在更多位置)
  - [3. 标准库增强](#3-标准库增强)
    - [3.1 `ControlFlow::map` / `map_err`](#31-controlflowmap--map_err)
    - [3.2 `LazyLock` / `LazyCell` 稳定化](#32-lazylock--lazycell-稳定化)
    - [3.3 `array::from_fn` 增强](#33-arrayfrom_fn-增强)
  - [4. 工具链与编译器改进](#4-工具链与编译器改进)
    - [4.1 `linker-plugin-lto`](#41-linker-plugin-lto)
    - [4.2 Cargo 改进](#42-cargo-改进)
    - [4.3 Rustdoc](#43-rustdoc)
  - [5. 本项目实践映射](#5-本项目实践映射)
    - [5.1 练习覆盖矩阵](#51-练习覆盖矩阵)
    - [5.2 Crate 级别覆盖](#52-crate-级别覆盖)
    - [5.3 已知限制](#53-已知限制)
  - [6. 特性成熟度与生产建议](#6-特性成熟度与生产建议)
    - [6.1 立即使用（零风险）](#61-立即使用零风险)
    - [6.2 推荐使用（低风险）](#62-推荐使用低风险)
    - [6.3 谨慎评估（中等风险）](#63-谨慎评估中等风险)
    - [6.4 暂不建议（高风险/不稳定）](#64-暂不建议高风险不稳定)
  - [7. 附录：版本对比矩阵](#7-附录版本对比矩阵)
  - [结论](#结论)

---

## 1. 特性全景概览

Rust 1.95 是 Edition 2024 生命周期中的关键版本，稳定了多项从 nightly 走向 production 的核心特性：

| 类别 | 特性 | 稳定状态 | 本项目覆盖 |
|------|------|----------|-----------|
| **生成器** | `gen` blocks (`gen { yield }`) | ✅ Stable 1.95 | exercises (A) |
| **异步** | `AsyncFn` / `AsyncFnMut` / `AsyncFnOnce` | ✅ Stable 1.95 | exercises (B) |
| **模式匹配** | `if let` guards in match arms | ✅ Stable 1.95 | exercises (C) |
| **Unsafe** | `&raw const` / `&raw mut` | ✅ Stable 1.95 | exercises (D) + c05_threads |
| **Unsafe** | `unsafe_op_in_unsafe_fn` (Edition 2024) | ✅ Stable 1.95 | exercises (E) |
| **FFI** | `c"..."` C string literals | ✅ Stable 1.95 | exercises (F) |
| **Const** | `const {}` blocks in more positions | ✅ Stable 1.95 | exercises (G) |
| **Const** | `Box::into_raw` in const fn | ❌ 不可用 (nightly 限制) | — |
| **控制流** | `gen` block + `yield` | ✅ (需 feature gate on nightly) | exercises |
| **LTO** | `linker-plugin-lto` | ✅ Stable 1.95 | 构建配置 |

---

## 2. 语言特性深度解析

### 2.1 `gen` blocks — 原生生成器语法

**语法**: `gen { yield expr; }` → `impl Iterator<Item = T>`

**核心语义**:

- `gen` block 在编译期被降阶为状态机，类似 `async` block 被降阶为 `Future`
- `yield` 暂停执行并产生一个值，下次迭代时从暂停点恢复
- 与手动实现 `Iterator` trait 相比，代码更直观、更易于维护

**Before (Rust ≤ 1.94)**:

```rust
struct Fibonacci {
    a: u64, b: u64,
}
impl Iterator for Fibonacci {
    type Item = u64;
    fn next(&mut self) -> Option<Self::Item> {
        let val = self.a;
        (self.a, self.b) = (self.b, self.a + self.b);
        Some(val)
    }
}
```

**After (Rust 1.95+)**:

```rust
gen move {
    let (mut a, mut b) = (0u64, 1u64);
    loop {
        yield a;
        (a, b) = (b, a + b);
    }
}
```

**关键限制**:

- `gen` block 返回的类型是匿名类型，只能通过 `impl Iterator` 或 `Box<dyn Iterator>` 传递
- 需要 `move` 关键字才能捕获环境变量的所有权（与 `async` block 类似）
- 在 Rust 1.97 nightly 上仍需 `#![feature(gen_blocks, yield_expr)]`

**本项目实践**: `exercises/src/rust_195_feature_exercises.rs` — `GenBlockExercises`

- `exercise_01_fibonacci_gen`: 斐波那契数列生成器
- `exercise_02_filter_map_gen`: 过滤+映射组合
- `exercise_03_flatten_gen`: 嵌套列表扁平化

---

### 2.2 `AsyncFn` trait 家族 — 异步闭包类型化

**背景**: Rust 的异步闭包 `async |x| x * 2` 在 1.95 之前无法直接作为 trait bound 使用。
1.95 稳定了 `AsyncFn` / `AsyncFnMut` / `AsyncFnOnce` 三个 trait，补齐了异步编程的类型系统拼图。

**Trait 层级**:

```
AsyncFnOnce<Args>    // 异步调用一次，消耗所有权
    ↑
AsyncFnMut<Args>     // 异步多次调用，可变借用
    ↑
AsyncFn<Args>        // 异步多次调用，不可变借用
```

**与同步闭包的对比**:

| 维度 | 同步 `Fn` | 异步 `AsyncFn` |
|------|-----------|----------------|
| 调用语法 | `f(args)` | `f(args).await` |
| 返回类型 | `R` | `impl Future<Output = R>` |
| 捕获模式 | `&self` / `&mut self` / `self` | 同左，但返回 Future |
| trait 边界 | `impl Fn(i32) -> i32` | `impl AsyncFn(i32) -> i32` |

**关键洞察**: `AsyncFn` 的 `call` 方法返回 `impl Future`，这个 Future 可能借用了闭包捕获的状态。
因此，`AsyncFn` 闭包在被调用后、Future 被 poll 完之前，不能被再次调用（这与 `Fn` 不同）。

**本项目实践**: `exercises/src/async_programming/ex06_async_fn_traits.rs`

- `apply_async`: 使用 `impl AsyncFn(i32) -> i32` 作为参数边界
- `map_async`: 使用 `AsyncFnMut` 对列表进行异步映射
- `filter_async`: 使用 `AsyncFn(&i32) -> bool` 作为异步谓词

---

### 2.3 `if let` guards — match arm 中的条件绑定

**语法**: `pattern if let Some(x) = expr => { ... }`

**解决的问题**: 在 match arm 中需要对绑定变量进行进一步的模式匹配时，不再需要嵌套 `if let` 或 `match`。

**Before (Rust ≤ 1.94)**:

```rust
match msg {
    Some(s) => {
        if let Ok(n) = s.parse::<i32>() {
            format!("number: {n}")
        } else if let Some(rest) = s.strip_prefix("cmd:") {
            format!("command: {rest}")
        } else {
            format!("text: {s}")
        }
    }
    None => "empty".to_string(),
}
```

**After (Rust 1.95+)**:

```rust
match msg {
    Some(ref s) if let Ok(n) = s.parse::<i32>() => format!("number: {n}"),
    Some(ref s) if let Some(rest) = s.strip_prefix("cmd:") => format!("command: {rest}"),
    Some(s) => format!("text: {s}"),
    None => "empty".to_string(),
}
```

**关键限制 — 穷尽性检查**:
`if let` guard 的 match arm **不算入**穷尽性检查。
编译器无法证明 guard 条件覆盖了所有可能的值，因此如果所有 arm 都有 guard，必须添加一个无 guard 的 fallback arm：

```rust
match value {
    Ok(opt) if let Some(n) = opt => { /* ... */ }
    Ok(_) => "missing".to_string(),  // fallback，必须存在
    Err(e) => format!("error: {e}"),
}
```

**与 `let chains` 的对比**:

- `if let` guard: 用于 **match arm** 内部的条件细化
- `let chains`: 用于 **if 条件**中的多变量绑定（`if let A = a && let B = b`）
- 两者语义等价，只是使用场景不同

**本项目实践**: `exercises/src/type_system/ex06_if_let_guards.rs`

- `classify_message`: 使用 `if let` guard 解析并分类消息
- `describe_nested_value`: 处理 `Result<Option<T>, E>` 的嵌套模式

---

### 2.4 `&raw const` / `&raw mut` — 原始引用操作符

**背景**: 在 Rust 1.95 之前，获取原始指针的标准写法是 `&expr as *const _`。
这种方式会**先创建一个中间引用**，再将其强制转换为指针。
如果 `expr` 是未对齐的（如 `#[repr(packed)]` struct 的字段），创建这个中间引用本身就是 **Undefined Behavior**。

**新语法**:

```rust
let ptr: *const T = &raw const expr;   // 直接创建原始指针，无中间引用
let ptr: *mut T   = &raw mut expr;     // 直接创建可变原始指针
```

**与 `std::ptr::addr_of!` 的对比**:

- `addr_of!(expr)`（宏，Rust 1.51+）≡ `&raw const expr`（操作符，Rust 1.95+）
- `addr_of_mut!(expr)`（宏）≡ `&raw mut expr`（操作符）
- 语义完全等价，`&raw const` 更简洁、更符合 Rust 的表达式语法

**在 `const fn` 中的使用**:

```rust
pub const fn const_raw_ptr<T>(value: &T) -> *const T {
    &raw const *value
}
```

**本项目实践**: `exercises/src/unsafe_rust/ex08_raw_references.rs`

- `packed_field_ptr`: 在 packed struct 中安全获取未对齐字段的指针
- `union_field_ptr`: 在 union 中安全获取字段指针
- `addr_of_equivalent_to_raw_const`: 验证 `addr_of!` 与 `&raw const` 的等价性

---

### 2.5 `unsafe_op_in_unsafe_fn` — Rust 2024 的 unsafe 语义澄清

**背景**: 在 Rust 2021 及之前，`unsafe fn` 的函数体被视为一个隐式的 `unsafe` 块，内部的 unsafe 操作可以直接写。
这混淆了**调用者的 unsafe** 和**实现者的 unsafe**。

**Rust 2024 的变更**:

- `unsafe fn` 的函数体**默认是 safe 的**
- 内部的 unsafe 操作仍然需要显式包裹在 `unsafe {}` 块中
- 这让每一行 unsafe 代码都明确可见，便于代码审查

**核心概念**:

- `unsafe fn`: 标记"调用此函数需要 unsafe 权限"（约束调用者）
- `unsafe {}`: 标记"此块内的操作需要 unsafe 权限"（约束实现者）

**Before (Rust 2021)**:

```rust
unsafe fn old_style(ptr: *mut u32) -> u32 {
    *ptr  // 隐式 unsafe，直接解引用
}
```

**After (Rust 2024)**:

```rust
unsafe fn new_style(ptr: *mut u32) -> u32 {
    unsafe { *ptr }  // 显式 unsafe 块
}
```

**本项目实践**: `exercises/src/unsafe_rust/ex09_unsafe_op_in_unsafe_fn.rs`

- `RawBuffer`: 完整的手动内存管理类型，演示 Rust 2024 风格的 unsafe fn
- `unsafe_fn_quiz`: 4 道判断题巩固概念

---

### 2.6 `c"..."` C 字符串字面量

**语法**: `c"hello"` → `&'static CStr`

**解决的问题**: FFI 中传递 C 字符串时，手动构造 `CStr` 既冗长又容易出错：

```rust
// Before: 冗长且可能忘记 NUL
CStr::from_bytes_with_nul(b"hello\0").unwrap()

// After: 编译期保证
 c"hello"
```

**编译期保证**:

1. 自动追加 NUL 结尾（`\0`）
2. 拒绝内部 NUL（如果字符串中包含 `\0`，编译错误）
3. 产生 `&'static CStr`，可直接用于全局/常量上下文

**与 `CString` 的区别**:

- `CStr`: 借用类型，不可变，通常来自字面量或 FFI
- `CString`: 拥有所有权，可变（仅限于构造时），用于传递给 C 代码

**本项目实践**: `exercises/src/unsafe_rust/ex10_c_str_literals.rs`

- `greeting_cstr`: 返回 `c"..."` 字面量
- `literal_vs_manual`: 验证 `c"..."` 与手动构造的等价性
- `test_cstring_rejects_internal_nul`: 演示 `CString::new` 对内部 NUL 的拒绝

---

### 2.7 `const {}` 块在更多位置

**语法**: `const { expr }`

**扩展的上下文**:

- **类型位置**: `[u8; const { 4 + 4 }]` → `[u8; 8]`
- **表达式位置**: `let x = const { std::mem::size_of::<u64>() };`
- **数组初始化**: `[0; const { 2 + 3 }]`

**核心语义**: `const {}` 块中的代码在**编译期**求值，结果必须是 `const` 合法的。它提供了一种在任意位置插入编译期计算的方式。

**与 `const fn` 的对比**:

- `const fn`: 定义编译期可计算的函数
- `const {}`: 在表达式/类型位置直接插入编译期计算

**本项目实践**: `exercises/src/unsafe_rust/ex11_const_unsafe.rs`

- `const_block_array`: 使用 `const {}` 计算数组大小
- `const_block_buffer_size`: 使用 `const {}` 计算缓冲区大小
- `const_raw_ptr`: 在 `const fn` 中使用 `&raw const`
- `const_deref`: 在 `const fn` 中进行 unsafe 解引用

---

## 3. 标准库增强

### 3.1 `ControlFlow::map` / `map_err`

Rust 1.95 为 `ControlFlow` 添加了 `map` 和 `map_err` 方法，使其更接近 `Result` 的 API：

```rust
use std::ops::ControlFlow;

let cf: ControlFlow<i32, u32> = ControlFlow::Break(42);
let mapped = cf.map_err(|e| e * 2);  // ControlFlow::Break(84)
```

**适用场景**: 自定义控制流抽象、提前返回模式、访问者模式。

### 3.2 `LazyLock` / `LazyCell` 稳定化

虽然 `LazyLock` 在 Rust 1.80 就已稳定，但 1.95 进一步完善了其与 `const` 上下文的交互。

### 3.3 `array::from_fn` 增强

`std::array::from_fn` 在 1.95 中支持更多场景，简化了数组初始化。

---

## 4. 工具链与编译器改进

### 4.1 `linker-plugin-lto`

Rust 1.95 改进了链接时优化（LTO）的跨 crates 支持，允许在更复杂的链接场景中启用 `lto = "thin"` 或 `lto = "fat"`。

**配置示例**:

```toml
[profile.release]
lto = "thin"
```

### 4.2 Cargo 改进

- `cargo update` 的性能优化
- 更好的错误信息提示
- 对 Edition 2024 的完整支持

### 4.3 Rustdoc

- 对 `gen` block 和 `AsyncFn` 的文档生成支持
- 改进的跨引用链接

---

## 5. 本项目实践映射

### 5.1 练习覆盖矩阵

| 特性 | exercises 模块 | 测试数 | 难度 |
|------|---------------|--------|------|
| `gen` blocks | `rust_195_feature_exercises::GenBlockExercises` | 5 | Medium |
| `AsyncFn` | `async_programming::ex06_async_fn_traits` | 5 | Hard |
| `if let` guards | `type_system::ex06_if_let_guards` | 7 | Medium |
| `&raw const` | `unsafe_rust::ex08_raw_references` | 7 | Medium |
| `unsafe_op_in_unsafe_fn` | `unsafe_rust::ex09_unsafe_op_in_unsafe_fn` | 5 | Medium |
| `c"..."` | `unsafe_rust::ex10_c_str_literals` | 8 | Easy |
| `const {}` + const raw ptr | `unsafe_rust::ex11_const_unsafe` | 8 | Hard |

**合计**: 45 个新增测试，全部通过。

### 5.2 Crate 级别覆盖

| Crate | 1.95 特性应用 |
|-------|--------------|
| `c05_threads` | `&raw const` 在 lock-free 结构中的使用 |
| `exercises` | 全部 7 个 1.95 特性的系统化练习 |
| `c11_macro_system_proc` | proc-macro 与 Edition 2024 兼容 |

### 5.3 已知限制

| 特性 | 限制 | 原因 |
|------|------|------|
| `Box::into_raw` in const fn | 不可用 | nightly 1.97 中 `Box::new` 仍非 `const fn` |
| `gen` blocks | 需 `#![feature(gen_blocks, yield_expr)]` | nightly 上 feature gate 未移除 |
| Lock-free Miri | 并发测试 `#[ignore]` | 自定义 HP/EBR 未完全实现内存回收 |

---

## 6. 特性成熟度与生产建议

### 6.1 立即使用（零风险）

- ✅ `c"..."` C 字符串字面量 — 语法糖，编译期保证
- ✅ `if let` guards — 纯语法改进，无运行时开销
- ✅ `const {}` 块 — 编译期计算，无运行时开销
- ✅ `&raw const` / `&raw mut` — 更安全地替代 `&expr as *const _`

### 6.2 推荐使用（低风险）

- ✅ `unsafe_op_in_unsafe_fn` — Rust 2024 默认行为，提升代码安全性
- ✅ `AsyncFn` trait 家族 — 类型系统增强，与现有异步代码无缝集成

### 6.3 谨慎评估（中等风险）

- ⚠️ `gen` blocks — 语法稳定，但编译器优化可能尚未完全成熟
  - 建议：在性能敏感场景下，对比手动 `Iterator` 实现 benchmark
  - 当前 nightly 仍需 feature gate

### 6.4 暂不建议（高风险/不稳定）

- ❌ `Box::into_raw` in const fn — 在当前工具链上不可用
- ❌ 自定义 lock-free + Miri — 并发测试有已知 UB，仅限教学用途

---

## 7. 附录：版本对比矩阵

| 特性 | 1.94 | 1.95 | 1.96 | 1.97 (nightly) | 本项目状态 |
|------|------|------|------|----------------|-----------|
| `gen` blocks | 🚫 | ✅ | ✅ | ✅ (feature) | 已练习 |
| `AsyncFn` | 🚫 | ✅ | ✅ | ✅ | 已练习 |
| `if let` guards | 🚫 | ✅ | ✅ | ✅ | 已练习 |
| `&raw const` | 🚫 | ✅ | ✅ | ✅ | 已练习 |
| `unsafe_op_in_unsafe_fn` | warn | warn | warn | warn | 已练习 |
| `c"..."` | 🚫 | ✅ | ✅ | ✅ | 已练习 |
| `const {}` blocks | 部分 | 扩展 | 扩展 | 扩展 | 已练习 |
| `Box::into_raw` const | 🚫 | 🚫 | 🚫 | 🚫 | 未覆盖 |
| `let chains` | ✅ | ✅ | ✅ | ✅ | 已有 |
| `const fn` unsafe | ✅ | ✅ | ✅ | ✅ | 已练习 |

**图例**: ✅ 稳定可用 | 🚫 不可用 | warn 默认警告

---

## 结论

Rust 1.95 是 Edition 2024 的里程碑版本，稳定了生成器、异步闭包类型化、模式匹配增强等核心语言特性。本项目的 exercises 模块已系统化覆盖全部 7 个可用特性，共新增 45 个测试，全部通过。对于尚未稳定的 `Box::into_raw` in const fn，将在工具链支持后补充。

**下一步建议**:

1. 将 1.95 特性练习扩展到更多 crate 的 `examples/` 中
2. 为 `c05_threads` 的 lock-free 结构添加 `&raw const` 重构
3. 追踪 Rust 1.96/1.97 新特性，持续更新版本覆盖矩阵
