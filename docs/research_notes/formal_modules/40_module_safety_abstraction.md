# 模块系统与安全抽象边界 {#模块系统与安全抽象边界}

> **EN**: Module Safety Abstraction
> **Summary**: 模块系统与安全抽象边界 Module Safety Abstraction.
> **概念族**: 形式化模块
> **内容分级**: [归档级]
>
> **分级**: [B]
> **Bloom 层级**: L5-L6 (分析/评价/创造)
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 新建完成 / 权威国际化来源对齐完成

---

## 目录 {#目录}

- [模块系统与安全抽象边界 {#模块系统与安全抽象边界}](#模块系统与安全抽象边界-模块系统与安全抽象边界)
  - [目录 {#目录}](#目录-目录)
  - [研究目标 {#研究目标}](#研究目标-研究目标)
  - [概念定义 {#概念定义}](#概念定义-概念定义)
  - [属性关系 {#属性关系}](#属性关系-属性关系)
  - [解释与论证 {#解释与论证}](#解释与论证-解释与论证)
    - [模块可见性为什么能成为安全保证 {#模块可见性为什么能成为安全保证}](#模块可见性为什么能成为安全保证-模块可见性为什么能成为安全保证)
    - [`unsafe impl` 与模块边界 {#unsafe-impl-与模块边界}](#unsafe-impl-与模块边界-unsafe-impl-与模块边界)
    - [内部可变性的安全契约 {#内部可变性的安全契约}](#内部可变性的安全契约-内部可变性的安全契约)
  - [Rust 示例 {#rust-示例}](#rust-示例-rust-示例)
    - [1. 安全封装 raw pointer {#1-安全封装-raw-pointer}](#1-安全封装-raw-pointer-1-安全封装-raw-pointer)
    - [2. 内部可变性抽象：简化版 `Cell` {#2-内部可变性抽象简化版-cell}](#2-内部可变性抽象简化版-cell-2-内部可变性抽象简化版-cell)
    - [3. `unsafe trait` 的模块内实现 {#3-unsafe-trait-的模块内实现}](#3-unsafe-trait-的模块内实现-3-unsafe-trait-的模块内实现)
  - [反例与边界 {#反例与边界}](#反例与边界-反例与边界)
  - [权威来源对照表 {#权威来源对照表}](#权威来源对照表-权威来源对照表)
  - [学术/社区来源参考 {#学术社区来源参考}](#学术社区来源参考-学术社区来源参考)

---

## 研究目标 {#研究目标}

论证 Rust 模块可见性如何构成安全抽象的边界：私有模块与私有 item 允许 crate 作者隐藏 unsafe 实现细节、维护不变式（invariant），并通过 safe API 暴露受控接口；同时讨论内部可变性（interior mutability）与可见性的协同设计。

---

## 概念定义 {#概念定义}

| 术语 | 定义 |
| :--- | :--- |
| **安全抽象边界** | 模块/类型的可见性边界使得外部代码无法直接破坏内部不变式，unsafe 代码可以在边界内依赖这些不变式，而 safe 接口承诺在任意 safe 使用下保持内存安全。 |
| **Encapsulation（封装）** | 通过私有字段/模块隐藏实现细节，仅暴露必要接口。Rust 中封装由 visibility 系统强制执行，是类型系统之外的安全基础。 |
| **内部可变性（Interior Mutability）** | 在不可变引用持有期间仍能修改数据的能力，通过 `UnsafeCell`、`Cell`、`RefCell`、`Mutex`、`RwLock`、`Atomic*` 等类型实现。 |
| **Unsafe Boundary** | safe API 与 unsafe 实现之间的分界线。调用 safe API 的代码无需 `unsafe` 块，但实现者必须在私有代码中保证 unsafe 约束。 |
| **Invariant** | 数据类型在运行时必须保持的性质。私有字段和私有函数是维护 invariant 的关键机制，因为外部代码无法绕过公共方法修改状态。 |

> **来源:** [Rustonomicon – Safe Abstraction](https://doc.rust-lang.org/nomicon/safe-unsafe-meaning.html)
>
> **来源:** [Rust API Guidelines – Unsafe Guidelines](https://rust-lang.github.io/api-guidelines/unsafe.html)
>
> **来源:** [Rustonomicon – Interior Mutability](https://doc.rust-lang.org/nomicon/interior-mutability.html)

---

## 属性关系 {#属性关系}

```text
Crate 安全边界

├── Public API

│   ├── safe fn / safe trait

│   └── 不暴露内部状态，仅通过方法操作

├── Private Implementation

│   ├── unsafe blocks / unsafe fn

│   ├── raw pointers / FFI calls

│   └── 依赖内部 invariant 保持正确

└── Visibility Lattice

    ├── pub        → 外部可访问，必须完全安全

    ├── pub(crate) → 同 crate 内可访问，仍可依赖 crate 内约定

    ├── pub(super) → 父模块内可访问

    └── private    → 最强封装，仅当前模块可见
```

**关键关系：**

1. **可见性是安全的“软边界”**：Rust 借用检查器不直接检查可见性，但可见性限制了哪些代码能构造或破坏类型的内部状态，从而间接保证 unsafe 代码所依赖的 invariant。
2. **Safe API = 公开接口 + unsafe 实现隐藏**：只要公开方法内部正确使用 unsafe，且私有字段不可被外部直接修改，safe 调用者就无法触发未定义行为。
3. **内部可变性类型依赖封装**：`RefCell` 的 borrow flag、`Rc` 的引用计数等关键状态都是私有字段；如果外部可直接写入，将破坏运行时 borrow 规则或导致 use-after-free。

> **来源:** [Rustonomicon – Working With Unsafe](https://doc.rust-lang.org/nomicon/working-with-unsafe.html)

---

## 解释与论证 {#解释与论证}

### 模块可见性为什么能成为安全保证 {#模块可见性为什么能成为安全保证}

Rust 的 unsafe 代码可以假设某些条件成立，但这些条件必须被某些机制保护。借用检查器只能验证引用规则；对于更复杂的不变式（如“指针永远有效”、“引用计数非零”），需要靠 **封装 + 不变式维护函数** 来保护。可见性系统强制外部代码只能通过受控接口访问内部状态，因此 unsafe 实现者可以在这些接口内部维持 invariant。

### `unsafe impl` 与模块边界 {#unsafe-impl-与模块边界}

`unsafe trait` 的 `unsafe impl` 是另一个安全边界：实现者向编译器保证满足 trait 的安全契约。通常，unsafe trait 的实现会放在私有模块中，由 safe wrapper 类型对外暴露。例如自定义 `Send`/`Sync` 实现。

### 内部可变性的安全契约 {#内部可变性的安全契约}

`UnsafeCell` 是内部可变性的底层原语，其本身几乎不提供安全保证。`Cell`、`RefCell`、`Mutex` 等在 `UnsafeCell` 之上添加运行时检查或同步原语，并通过私有字段限制访问方式。模块可见性确保用户无法直接拿到 `UnsafeCell` 的裸指针并绕过检查。

> **来源:** [Rust API Guidelines – Type Safety](https://rust-lang.github.io/api-guidelines/type-safety.html)

---

## Rust 示例 {#rust-示例}

### 1. 安全封装 raw pointer {#1-安全封装-raw-pointer}

```rust
// src/lib.rs

pub struct SafeHandle {

    // 私有字段，外部无法直接访问指针

    ptr: *mut u8,

}

impl SafeHandle {

    pub fn new() -> Self {

        let boxed = Box::new(0u8);

        SafeHandle {

            ptr: Box::into_raw(boxed),

        }

    }

    pub fn get(&self) -> u8 {

        // unsafe 实现，但公开接口是 safe

        unsafe { *self.ptr }

    }

    pub fn set(&mut self, value: u8) {

        unsafe { *self.ptr = value; }

    }

}

impl Drop for SafeHandle {

    fn drop(&mut self) {

        unsafe { drop(Box::from_raw(self.ptr)); }

    }

}
```

### 2. 内部可变性抽象：简化版 `Cell` {#2-内部可变性抽象简化版-cell}

```rust
use std::cell::UnsafeCell;

pub struct MyCell<T> {

    value: UnsafeCell<T>, // 私有

}

impl<T: Copy> MyCell<T> {

    pub fn new(value: T) -> Self {

        MyCell { value: UnsafeCell::new(value) }

    }

    pub fn get(&self) -> T {

        unsafe { *self.value.get() }

    }

    pub fn set(&self, value: T) {

        unsafe { *self.value.get() = value; }

    }

}
```

`value` 为私有，外部无法绕过 `get`/`set` 直接读取/写入，从而保证 `T: Copy` 这一内部可变性契约。

### 3. `unsafe trait` 的模块内实现 {#3-unsafe-trait-的模块内实现}

```rust
mod inner {

    pub struct MyType;

    // 在私有/受控位置实现 unsafe trait

    unsafe impl Sync for MyType {}

}

pub use inner::MyType;
```

---

## 反例与边界 {#反例与边界}

| 场景 | 代码 | 结果 |
| :--- | :--- | :--- |
| 公开裸指针字段 | `pub struct Bad { pub ptr: *mut u8 }` | 外部可构造悬空/重复释放指针，破坏安全 |
| `unsafe fn` 作为 public API | `pub unsafe fn raw_write(p: *mut u8, v: u8)` | 合法，但调用者需负责 invariant，不属于 safe 抽象 |
| 通过 `pub use` 暴露私有实现 | `pub use private_mod::UnsafeDetail;` | 如果 `UnsafeDetail` 本身设计为私有，会扩大信任边界 |
| `std::mem::transmute` 绕过封装 | `transmute` 到私有类型 | 私有类型无法从外部命名，但同 crate 内可滥用 |

> **来源:** [Rustonomicon – What Unsafe Can Do](https://doc.rust-lang.org/nomicon/what-unsafe-does.html)

---

## 权威来源对照表 {#权威来源对照表}

| 概念 | Rustonomicon | Rust API Guidelines | 备注 |
| :--- | :--- | :--- | :--- |
| Safe / Unsafe 含义 | [Safe Unsafe Meanings](https://doc.rust-lang.org/nomicon/safe-unsafe-meaning.html) | — | 明确 safe abstraction 的责任边界 |
| 内部可变性 | [Interior Mutability](https://doc.rust-lang.org/nomicon/interior-mutability.html) | — | `UnsafeCell` 是底层原语 |
| Unsafe 工作方式 | [Working With Unsafe](https://doc.rust-lang.org/nomicon/working-with-unsafe.html) | [Unsafe Guidelines](https://rust-lang.github.io/api-guidelines/unsafe.html) | 设计 safe wrapper 的规范 |
| API 设计 | — | [API Guidelines](https://rust-lang.github.io/api-guidelines/) | 可见性与封装的 best practice |

---

> **权威来源**: [Rustonomicon – Safe and Unsafe](https://doc.rust-lang.org/nomicon/safe-unsafe-meaning.html) | [Rustonomicon – Interior Mutability](https://doc.rust-lang.org/nomicon/interior-mutability.html) | [Rust API Guidelines – Unsafe](https://rust-lang.github.io/api-guidelines/unsafe.html) | [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)

---

## 学术/社区来源参考 {#学术社区来源参考}

> **来源**: [RustBelt](https://plv.mpi-sws.org/rustbelt/)
> **来源**: [Aeneas](https://aeneas-verification.github.io/)
> **来源**: [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)
