# Rust 运行时（The Rust Runtime）

> **EN**: The Rust Runtime
> **Summary**: Rust 运行时的关键属性：`#[global_allocator]` 自定义全局分配器、`#[windows_subsystem]` Windows 子系统设置，以及 panic、栈展开和启动流程等运行时组件。 Key properties of the Rust runtime: `#[global_allocator]`, `#[windows_subsystem]`, and runtime components including panic, stack unwinding, and startup.
>
> **受众**: [专家]
> **内容分级**: [专家级]
> **Bloom 层级**: 理解 → 应用
> **A/S/P 标记**: **S** — Specification / Systems
> **双维定位**: S×Sys — 语言与运行时系统
> **前置依赖**: [Memory Management](../../02_intermediate/02_memory_management/03_memory_management.md) · [Custom Allocators](../06_low_level_patterns/14_custom_allocators.md) · [Linkage](../04_ffi/27_linkage.md)
> **后置概念**: [Embedded Systems](../../06_ecosystem/05_systems_and_embedded/22_embedded_systems.md) · [Unsafe Rust](03_unsafe.md) · [Panic](31_panic.md)
> **定理链**: Runtime Attribute → Allocation / Subsystem → Binary Behavior
> **主要来源**: [Rust Reference — The Rust Runtime](https://doc.rust-lang.org/reference/runtime.html) · [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) · [O'Hearn — Separation Logic and Shared Mutable Data](https://doi.org/10.1017/S0960129501001003) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/)

>
> **来源**: [Rust Reference — The Rust Runtime](https://doc.rust-lang.org/reference/runtime.html) · [Rust Reference — Attributes](https://doc.rust-lang.org/reference/attributes.html)

---

---

## 认知路径

> **认知路径**: 本节从 "Rust 运行时（The Rust Runtime）" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 Rust 运行时值得关注？运行时属性决定内存分配、Windows 子系统和 panic 行为，影响系统级和嵌入式编程。
2. **概念建立**: 掌握 `#[global_allocator]`、`#[windows_subsystem]`、panic 运行时和启动流程的核心概念。
3. **机制推理**: 通过 ⟹ 定理链将运行时属性、分配行为和二进制输出串联起来。
4. **边界辨析**: 借助反命题/反例理解 Rust 运行时的适用边界。
5. **迁移应用**: 将 Rust 运行时与自定义分配器、嵌入式系统和 panic 处理链接，形成跨层知识网络。

---

## 反命题决策树

> **反命题 1**: "Rust 运行时在所有场景下都相同" ⟹ 不成立。`#[global_allocator]`、`panic = "abort"` 和目标平台都会显著改变运行时行为。

> **反命题 2**: "忽略 Rust 运行时的细节也能写出正确代码" ⟹ 不成立。全局分配器选择错误、panic 策略不匹配和子系统设置错误会导致运行时失败。

> **反命题 3**: "其他语言对运行时的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的运行时非常轻量，大部分核心行为可通过属性和 feature 定制。

## 一、什么是 Rust 运行时

Rust 运行时（Runtime）指程序运行期间由语言定义或依赖的基础设施行为。与其他一些语言不同，Rust 的运行时非常轻量，大部分核心行为（如内存分配）都可以通过属性进行定制或替换。

运行时组件包括：

| 组件 | 说明 |
|:---|:---|
| 全局分配器 | 通过 `#[global_allocator]` 定制 |
| Panic 运行时 | 栈展开（unwind）或中止（abort） |
| 启动/终止 | `main` 之前的初始化和之后的清理 |
| 线程局部存储 | `std::thread_local!` |
| Windows 子系统 | 通过 `#[windows_subsystem]` 设置 |

## 二、Panic 运行时

Rust 支持两种 panic 运行时策略，通过 `Cargo.toml` 的 `[profile]` 段配置：

| 策略 | 配置 | 行为 | 适用场景 |
|:---|:---|:---|:---|
| Unwind | `panic = "unwind"` | 栈展开，调用析构函数 | 需要异常恢复的服务 |
| Abort | `panic = "abort"` | 立即终止进程 | 嵌入式、Wasm、体积敏感 |

```toml
[profile.release]
panic = "abort"
```

> **注意**: 即使使用 `panic = "abort"`，`unsafe` 代码仍需保持内存安全不变式。

## 三、启动与终止流程

Rust 二进制程序的启动流程：

```text
操作系统加载器
    ↓
C 运行时 (crt) 初始化
    ↓
Rust 启动代码 (std::rt::lang_start)
    ↓
调用用户 main 函数
    ↓
main 返回后清理全局状态
```

在 `no_std` 环境中，开发者通常需要提供自己的 `_start` 入口：

```rust
#![no_std]
#![no_main]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[no_mangle]
pub extern "C" fn _start() -> ! {
    // 自定义启动逻辑
    loop {}
}
```

## 四、线程局部存储

`std::thread_local!` 提供线程局部变量：

```rust
use std::cell::RefCell;

thread_local! {
    static COUNTER: RefCell<u32> = RefCell::new(0);
}

COUNTER.with(|c| {
    *c.borrow_mut() += 1;
});
```

线程局部存储的实现依赖于平台特定的运行时支持（如 ELF TLS、Windows TLS）。

## 五、`#[windows_subsystem]`

Windows 平台下，`#[windows_subsystem]` 控制可执行文件的子系统：

```rust
// 控制台程序（默认）
#![windows_subsystem = "console"]

// GUI 程序，不显示控制台窗口
#![windows_subsystem = "windows"]
```

| 子系统 | 行为 |
|:---|:---|
| `console` | 启动时分配控制台窗口 |
| `windows` | 不自动分配控制台，适合 GUI 应用 |

## 六、`#[global_allocator]`

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

## 四、Panic 运行时

Rust 的 panic 策略由 `Cargo.toml` 中的 `panic` 配置决定：

| 策略 | 行为 | 适用场景 |
|:---|:---|:---|
| `panic = "unwind"` | 栈展开，调用析构函数 | 默认，需要异常安全 |
| `panic = "abort"` | 立即中止进程 | 嵌入式、代码体积敏感 |

详见 [Panic](31_panic.md)。

## 五、运行时假设

Rust 运行时还对程序行为做出一些假设，违反这些假设可能导致 UB：

- Rust 栈帧在局部变量析构完成前不应被释放（如 `longjmp` 可能违反）。
- unwinding 需遵守 panic 相关约定。

更多细节参见 [Behavior Considered Undefined](../../04_formal/01_ownership_logic/37_behavior_considered_undefined.md)。

## 六、`no_std` 与运行时

在 `no_std` 环境下，标准库运行时不可用，程序需要：

- 自定义 panic handler。
- 自定义全局分配器（如果需要堆分配）。
- 处理启动入口（如 `_start`）。

```rust
#![no_std]
#![no_main]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}
```

## 七、关联概念

| 概念 | 关系 |
|:---|:---|
| [Custom Allocators](../06_low_level_patterns/14_custom_allocators.md) | `#[global_allocator]` 是自定义分配器的入口 |
| [Linkage](../04_ffi/27_linkage.md) | 运行时属性影响链接器行为 |
| [Application Binary Interface](../../04_formal/05_rustc_internals/38_application_binary_interface.md) | ABI 属性与运行时属性共同决定二进制输出 |
| [Embedded Systems](../../06_ecosystem/05_systems_and_embedded/22_embedded_systems.md) | 嵌入式场景经常需要替换全局分配器 |
| [Unsafe Rust](03_unsafe.md) | `GlobalAlloc` 实现需要 `unsafe` |
| [Panic](31_panic.md) | panic 策略是运行时核心部分 |
| [Memory Model](29_memory_model.md) | 分配器行为受内存模型约束 |

---

> **权威来源**: [Rust Reference — The Rust Runtime](https://doc.rust-lang.org/reference/runtime.html) · [Rust Reference — Attributes](https://doc.rust-lang.org/reference/attributes.html) · [Rust Embedded Book](https://docs.rust-embedded.org/book/)
> **内容分级**: [专家级]
