# Rust 运行时（The Rust Runtime）

> **EN**: The Rust Runtime
> **Summary**: Rust 运行时（Runtime）的关键属性：`#[global_allocator]` 自定义全局分配器与 `#[windows_subsystem]` Windows 子系统设置。
>
> **受众**: [专家]
> **内容分级**: [专家级]
> **Bloom 层级**: 理解 → 应用
> **A/S/P 标记**: **S** — Specification / Systems
> **双维定位**: S×Sys — 语言与运行时（Runtime）系统
> **前置依赖**: [Memory Management](../../02_intermediate/02_memory_management/03_memory_management.md) · [Custom Allocators](../06_low_level_patterns/14_custom_allocators.md) · [Linkage](../04_ffi/27_linkage.md)
> **后置概念**: [Embedded Systems](../../06_ecosystem/05_systems_and_embedded/22_embedded_systems.md) · [Unsafe Rust](03_unsafe.md)
> **定理链**: Runtime Attribute → Allocation / Subsystem → Binary Behavior
> **主要来源**: [Rust Reference — The Rust Runtime](https://doc.rust-lang.org/reference/runtime.html) · [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) · [O'Hearn — Separation Logic and Shared Mutable Data](https://doi.org/10.1017/S0960129501001003) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

>
> **来源**: [Rust Reference — The Rust Runtime](https://doc.rust-lang.org/reference/runtime.html)

---

---

## 认知路径

> **认知路径**: 本节从 "Rust 运行时（The Rust Runtime）" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 Rust 运行时（The Rust Runtime） 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 Rust 运行时（The Rust Runtime） 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与Rust 运行时（The Rust Runtime）的适用边界。
5. **迁移应用**: 将 Rust 运行时（The Rust Runtime） 与前置/后置概念链接，形成跨层知识网络。

---

## 反命题决策树

> **反命题 1**: "Rust 运行时（The Rust Runtime） 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。

> **反命题 2**: "忽略 Rust 运行时（The Rust Runtime） 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 Rust 运行时（The Rust Runtime） 规则被违反的直接信号。

> **反命题 3**: "其他语言对 Rust 运行时（The Rust Runtime） 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 Rust 运行时（The Rust Runtime） 具有语言特有的形态。

## 一、什么是 Rust 运行时

Rust 运行时（Runtime）指程序运行期间由语言定义或依赖的基础设施行为。与其他一些语言不同，Rust 的运行时非常轻量，大部分核心行为（如内存分配）都可以通过属性进行定制或替换。

---

## 二、`#[global_allocator]`

`#[global_allocator]` 用于选择程序的**全局内存分配器**。

### 规则

- 只能应用于实现了 `GlobalAlloc` trait 的 `static` 项。
- 每个项上只能使用一次。
- 整个 crate 图中只能使用一次。
- 从标准库 prelude 中导出。

### 示例

```rust
use std::alloc::System;
use core::alloc::{GlobalAlloc, Layout};

struct MyAllocator;

unsafe impl GlobalAlloc for MyAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        System.alloc(layout)
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        System.dealloc(ptr, layout)
    }
}

#[global_allocator]
static GLOBAL: MyAllocator = MyAllocator;
```

### 使用场景

- 嵌入式/裸机环境替换默认分配器。
- 性能调优（如使用 jemalloc、mimalloc）。
- 追踪分配行为、调试内存泄漏。

---

## 三、`#[windows_subsystem]`

`#[windows_subsystem]` 用于在 Windows 目标上设置链接时的**子系统**。

### 语法

```rust
#![windows_subsystem = "windows"]
```

接受值：

- `"console"`（默认）
- `"windows"`

### 行为

- 只能应用于 crate root。
- 只有第一次使用有效，后续使用会触发 future-compatibility 警告。
- 在非 Windows 目标或非 `bin` crate 类型上被忽略。

### `"console"` vs `"windows"`

| 值 | 行为 |
|:---|:---|
| `"console"` | 默认。若从已有控制台运行则附加到该控制台，否则创建新控制台窗口。 |
| `"windows"` | 脱离任何现有控制台运行。常用于不希望启动时显示控制台的 GUI 应用。 |

---

## 四、运行时假设

Rust 运行时（Runtime）还对程序行为做出一些假设，违反这些假设可能导致 UB：

- Rust 栈帧在局部变量析构完成前不应被释放（如 `longjmp` 可能违反）。
- unwinding 需遵守 panic 相关约定。

更多细节参见 [Behavior Considered Undefined](../../04_formal/01_ownership_logic/37_behavior_considered_undefined.md)。

---

## 五、关联概念

| 概念 | 关系 |
|:---|:---|
| [Custom Allocators](../06_low_level_patterns/14_custom_allocators.md) | `#[global_allocator]` 是自定义分配器的入口 |
| [Linkage](../04_ffi/27_linkage.md) | 运行时属性影响链接器行为 |
| [Application Binary Interface](../../04_formal/05_rustc_internals/38_application_binary_interface.md) | ABI 属性与运行时属性共同决定二进制输出 |
| [Embedded Systems](../../06_ecosystem/05_systems_and_embedded/22_embedded_systems.md) | 嵌入式场景经常需要替换全局分配器 |
| [Unsafe Rust](03_unsafe.md) | `GlobalAlloc` 实现需要 `unsafe` |
