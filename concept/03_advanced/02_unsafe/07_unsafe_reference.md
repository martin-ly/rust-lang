# Unsafe 参考（Unsafe Reference）

> **EN**: Unsafe Reference
> **Summary**: Rust Reference 对 `unsafe` 的规范：`unsafe` 关键字、`unsafe` 块、函数、trait、实现的外部契约，以及"不被视为 unsafe 的行为"。 Normative description of Rust `unsafe`: the keyword, unsafe blocks, functions, traits, implementations, external contracts, and behaviors not considered unsafe.
> **Rust 版本**: 1.97.0+ (Edition 2024)
>
> **受众**: [专家]
> **内容分级**: [专家级]
> **Bloom 层级**: L2-L4
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×Ana — 规范分析
> **前置依赖**: [Unsafe Rust](01_unsafe.md) · [Behavior Considered Undefined](../../04_formal/01_ownership_logic/06_behavior_considered_undefined.md) · [Variables](../06_low_level_patterns/09_variables.md)
> **后置概念**: [Inline Assembly](../05_inline_assembly/01_inline_assembly.md) · [FFI Advanced](../04_ffi/02_ffi_advanced.md) · [Custom Allocators](../06_low_level_patterns/01_custom_allocators.md)
> **定理链**: Unsafe Keyword → Unsafe Block → Unsafe Operation → UB Contract
>
> **来源**:
> [Rust Reference — Unsafety](https://doc.rust-lang.org/reference/unsafe-keyword.html) ·
> [Rust Reference — Behavior Not Considered Unsafe](https://doc.rust-lang.org/reference/behavior-not-considered-unsafe.html) ·
> [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) ·
> [O'Hearn — Separation Logic and Shared Mutable Data](https://doi.org/10.1017/S0960129501001003) ·
> [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) ·
> [TRPL — Unsafe Rust](https://doc.rust-lang.org/book/ch19-01-unsafe-rust.html)

---

> **跨层回溯**: [智能指针（Smart Pointer）](../../02_intermediate/02_memory_management/04_smart_pointers.md) · [内部可变性](../../02_intermediate/02_memory_management/02_interior_mutability.md)

---

## 📑 目录

- [Unsafe 参考（Unsafe Reference）](#unsafe-参考unsafe-reference)
  - [📑 目录](#-目录)
  - [认知路径](#认知路径)
  - [反命题决策树](#反命题决策树)
  - [一、`unsafe` 关键字的四种用法](#一unsafe-关键字的四种用法)
  - [二、Unsafe 块的能力](#二unsafe-块的能力)
  - [三、外部契约与 unsafe trait](#三外部契约与-unsafe-trait)
  - [四、不被视为 unsafe 的行为](#四不被视为-unsafe-的行为)
  - [五、安全抽象层](#五安全抽象层)
  - [四、不被视为 unsafe 的行为](#四不被视为-unsafe-的行为-1)
  - [五、与 Undefined Behavior 的边界](#五与-undefined-behavior-的边界)
  - [六、Unsafe 与内存模型](#六unsafe-与内存模型)
  - [七、Unsafe 与运行时](#七unsafe-与运行时)
  - [八、相关概念](#八相关概念)
  - [过渡段](#过渡段)
  - [反向推理](#反向推理)
  - [📋 关键属性](#-关键属性)
  - [🔗 概念关系](#-概念关系)
  - [国际权威参考 / International Authority References（P1 学术 · P2 生态）](#国际权威参考--international-authority-referencesp1-学术--p2-生态)
  - [⚠️ 反例与陷阱：对 `static mut` 取引用（Edition 2024 硬错误）](#️-反例与陷阱对-static-mut-取引用edition-2024-硬错误)

---

## 认知路径

1. **问题识别**: 为什么 Unsafe 参考值得关注？`unsafe` 是 Rust 与底层系统交互的边界，理解其规范是编写安全抽象层的基础。
2. **概念建立**: 掌握 `unsafe` 关键字的四种用法、`unsafe` 块的能力和外部契约。
3. **机制推理**: 通过 ⟹ 定理链将 `unsafe` 关键字、块、操作和 UB 契约串联起来。
4. **边界辨析**: 借助反命题/反例理解 Unsafe 参考的适用边界。
5. **迁移应用**: 将 Unsafe 参考与内存模型、运行时（Runtime）、FFI 和内联汇编（Inline Assembly）链接，形成跨层知识网络。

---

## 反命题决策树

> **反命题 1**: "Unsafe 参考覆盖所有危险行为" ⟹ 不成立。死锁、内存泄漏和无限循环等虽然危险，但不属于 `unsafe` 操作。

> **反命题 2**: "忽略 Unsafe 参考的细节也能写出正确 unsafe 代码" ⟹ 不成立。违反 UB 契约会导致未定义行为，且往往难以调试。

## 一、`unsafe` 关键字的四种用法

| 用法 | 形式 | 说明 |
|:---|:---|:---|
| `unsafe` 块 | `unsafe { ... }` | 在块内执行 unsafe 操作 |
| `unsafe` 函数 | `unsafe fn foo() {}` | 调用者需保证前置条件 |
| `unsafe` trait | `unsafe trait Foo {}` | 实现者需保证不变式 |
| `unsafe` 实现 | `unsafe impl Foo for T {}` | 实现 unsafe trait |

## 二、Unsafe 块的能力

在 `unsafe` 块内允许：

1. 解引用（Reference）裸指针 `*const T` / `*mut T`
2. 调用 `unsafe` 函数或方法
3. 访问 `union` 的字段
4. 访问可变 `static`
5. 实现 `unsafe` trait
6. 调用 extern 函数
7. 使用 `asm!` 内联汇编（Inline Assembly）

> `unsafe` 块**不**禁用借用（Borrowing）检查器；它只放宽上述操作限制。(Source: [Rust Reference — Unsafe Blocks](https://doc.rust-lang.org/reference/expressions/block-expr.html#unsafe-blocks))

```rust
let mut x = 5;
let r = &mut x as *mut i32;
unsafe {
    *r += 1;
}
assert_eq!(x, 6);
```

## 三、外部契约与 unsafe trait

`unsafe trait` 用于标记实现者必须手动保证的契约：(Source: [Rust Reference — Unsafe Traits](https://doc.rust-lang.org/reference/items/traits.html#unsafe-traits))

```rust
unsafe trait Zeroable {
    // 实现者必须保证该类型的所有位模式都是合法的
}

unsafe impl Zeroable for u32 {}
```

常见 unsafe trait：

| Trait | 契约 | 实现者责任 |
|:---|:---|:---|
| `Send` | 可跨线程转移所有权（Ownership） | 类型在线程间转移是安全的 |
| `Sync` | 可跨线程共享引用（Reference） | 类型在多线程共享引用是安全的 |
| `GlobalAlloc` | 全局内存分配器 | `alloc`/`dealloc` 行为符合约定 |

## 四、不被视为 unsafe 的行为

Rust 将以下行为归类为**危险但不属于 `unsafe` 操作**：

| 行为 | 说明 | 后果 |
|:---|:---|:---|
| 死锁 | 锁的循环等待 | 程序挂起，但不触发 UB |
| 内存泄漏 | 分配后未释放 | 资源浪费，但不触发 UB |
| 无限循环 | 无法终止的循环 | 程序无响应 |
| 算术溢出（debug） | 调试模式下 panic | 程序终止 |
| 竞争条件（逻辑层） | 非原子操作（Atomic Operations）导致错误结果 | 逻辑错误，不一定是 UB |

> 关键区别：`unsafe` 操作指的是可能直接导致**未定义行为**的操作；死锁和泄漏虽然严重，但属于定义良好的行为。(Source: [Rust Reference — Behavior Not Considered Unsafe](https://doc.rust-lang.org/reference/behavior-not-considered-unsafe.html))

## 五、安全抽象层

将 unsafe 操作封装为 safe API 时，必须确保：

- 所有公开 safe 函数的输入都满足 unsafe 前置条件。
- 不变式在类型层面尽可能编码（如 `NonNull<T>` 保证非空）。
- 文档中明确说明调用者无需满足的不变式与内部已保证的不变式。

```rust
use std::ptr::NonNull;

/// Safe wrapper：调用者无需检查空指针
pub struct SafeBox<T> {
    ptr: NonNull<T>,
}

impl<T> SafeBox<T> {
    pub fn new(value: T) -> Self {
        let b = Box::new(value);
        Self {
            ptr: unsafe { NonNull::new_unchecked(Box::into_raw(b)) },
        }
    }
}
```

- 文档清楚说明调用者/实现者的责任。

```rust
use std::ptr::NonNull;

pub struct SafeBox<T> {
    ptr: NonNull<T>,
}

impl<T> SafeBox<T> {
    pub fn new(value: T) -> Self {
        let boxed = Box::new(value);
        SafeBox {
            ptr: NonNull::from(Box::leak(boxed)),
        }
    }

    pub fn get(&self) -> &T {
        unsafe { self.ptr.as_ref() }
    }
}
```

## 四、不被视为 unsafe 的行为

以下行为虽然危险，但**不**属于 `unsafe` 操作：

| 行为 | 说明 |
|:---|:---|
| 死锁 | 活性问题，非安全性问题 |
| 内存泄漏 | `std::mem::forget` 是 safe 的 |
| 无限循环 | 程序行为问题 |
| 非终止递归 | 栈溢出，safe 代码也可能发生 |
| 整数溢出（debug） | debug 模式会 panic；release 下按 two's complement 回绕，不是 UB |

## 五、与 Undefined Behavior 的边界

`unsafe` 代码必须避免 UB。完整 UB 清单见 [Behavior Considered Undefined](../../04_formal/01_ownership_logic/06_behavior_considered_undefined.md)。

常见 unsafe 契约包括：

- 裸指针必须有效且对齐。
- `union` 字段访问必须对应实际存储的变体。
- `unsafe` trait 的实现必须满足文档中的不变式。

## 六、Unsafe 与内存模型

unsafe 代码必须遵守 Rust 内存模型：(Source: [Rust Reference — Memory Model](https://doc.rust-lang.org/reference/memory-model.html))

- 正确区分已初始化/未初始化字节。
- 不丢失指针 provenance。
- 遵守别名规则（Stacked Borrows / Tree Borrows）。

详见 [Memory Model](06_memory_model.md)。

## 七、Unsafe 与运行时

部分运行时（Runtime）功能依赖 unsafe 实现：

- `#[global_allocator]` 需要 `unsafe impl GlobalAlloc`。
- `panic_handler` 在 `no_std` 环境中常用 unsafe。
- FFI 调用必须在 unsafe 块中。

详见 [Rust Runtime](../06_low_level_patterns/07_rust_runtime.md) 和 [Panic](../../02_intermediate/03_error_handling/03_panic.md)。

## 八、相关概念

| 概念 | 关系 |
|:---|:---|
| [Unsafe Rust](01_unsafe.md) | 本页是 `unsafe` 的规范参考视图 |
| [Memory Model](06_memory_model.md) | unsafe 代码必须遵守内存模型 |
| [Rust Runtime](../06_low_level_patterns/07_rust_runtime.md) | 运行时组件依赖 unsafe 实现 |
| [Panic](../../02_intermediate/03_error_handling/03_panic.md) | panic 处理涉及 unsafe 边界 |
| [Behavior Considered Undefined](../../04_formal/01_ownership_logic/06_behavior_considered_undefined.md) | unsafe 代码必须避免 UB |
| [Inline Assembly](../05_inline_assembly/01_inline_assembly.md) | 内联汇编在 unsafe 块中使用 |
| [FFI Advanced](../04_ffi/02_ffi_advanced.md) | FFI 调用需要 unsafe |

---

> **权威来源**:
> [Rust Reference — Unsafe Keyword](https://doc.rust-lang.org/reference/unsafe-keyword.html) ·
> [Rust Reference — Behavior Not Considered Unsafe](https://doc.rust-lang.org/reference/behavior-not-considered-unsafe.html) ·
> [Rust Reference — Unsafe Blocks](https://doc.rust-lang.org/reference/expressions/block-expr.html#unsafe-blocks) ·
> [TRPL — Unsafe Rust](https://doc.rust-lang.org/book/ch19-01-unsafe-rust.html)

## 过渡段

> **过渡**: 从 unsafe 关键字语义过渡到 unsafe 块，可以理解“关键字只是契约声明，块才是边界”。
>
> **过渡**: 从 unsafe 块过渡到 unsafe trait 与实现，可以建立“unsafe 不仅是表达式，也是类型系统（Type System）契约”的视角。
>
> **过渡**: 从 unsafe 操作清单过渡到 soundness 责任，可以理解调用者与被调用者之间的信任边界。
>

## 反向推理

> **反向推理**: 代码在 safe 函数中触发 UB ⟸ 说明 unsafe 边界划分错误，存在未封装的不安全操作。
>
> **反向推理**: unsafe trait 实现被标记为 unsound ⟸ 说明实现未维持 trait 文档声明的不变量。
>

---

## 📋 关键属性

| 属性 | 取值 / 判定 | 依据 |
|---|---|---|
| 四种语法 | `unsafe fn` / `unsafe {}` 块 / `unsafe trait` / `unsafe impl`（及 `extern`） | 本文 §一 |
| 五种能力 | 解引用裸指针、调用 unsafe 函数、访问 `static mut`、实现 unsafe trait、访问 union 字段 | 本文 §二 |
| 非 unsafe 行为 | 整数溢出、内存泄漏、多数逻辑错误不属于 unsafe 范畴 | 本文 §四 |
| 安全抽象 | 将 unsafe 封装在安全 API 之后是核心工程模式 | 本文 §五 |
| UB 边界 | 仅当 unsafe 内违反有效性不变量时才构成 UB | 本文 §五–§六 |

## 🔗 概念关系

- **上位（is-a）**：[Unsafe](01_unsafe.md) 的参考手册式速查页。
- **下位（实例）**：四种 unsafe 语法形态、五种超能力、安全抽象模式。
- **组合**：与 [Unsafe 边界全景](02_unsafe_boundary_panorama.md)、[内存模型](06_memory_model.md) 组合。
- **依赖**：依赖 [所有权](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) 的安全保证基线。

---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P2 生态/社区**: [docs.rs/zerocopy — 生态权威 API 文档](https://docs.rs/zerocopy) · [docs.rs/memmap2 — 生态权威 API 文档](https://docs.rs/memmap2)

---

## ⚠️ 反例与陷阱：对 `static mut` 取引用（Edition 2024 硬错误）

**反例**（rustc 1.97 实测编译失败，无错误码，static_mut_refs 硬错误））：

```rust,compile_fail
static mut COUNTER: u32 = 0;
fn main() {
    unsafe {
        let r = &mut COUNTER;
        *r += 1;
    }
}
```

对 `static mut` 创建引用在任何线程模型下都可能违反别名规则；Edition 2024 将 `static_mut_refs` 升为硬错误，这是 Unsafe Reference 章节的核心警示。

**修正**：

```rust
use std::sync::atomic::{AtomicU32, Ordering};
static COUNTER: AtomicU32 = AtomicU32::new(0);
fn main() {
    COUNTER.fetch_add(1, Ordering::SeqCst);
}
```
