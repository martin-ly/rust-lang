# Panic 机制

> **EN**: Panic
> **Summary**: Rust panic 的规范语义：panic handler、标准行为、panic strategy、unwind 与跨 FFI boundary 的规则。
>
> **受众**: [专家]
> **内容分级**: [专家级]
> **Bloom 层级**: L2-L4
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×Ana — 规范分析
> **前置依赖**: [Panic and Abort](../../01_foundation/08_error_handling/13_panic_and_abort.md) · [Unsafe Rust](03_unsafe.md) · [The Rust Runtime](30_rust_runtime.md)
> **后置概念**: [Error Handling](../../02_intermediate/03_error_handling/04_error_handling.md) · [FFI Advanced](../04_ffi/09_ffi_advanced.md) · [Behavior Considered Undefined](../../04_formal/01_ownership_logic/37_behavior_considered_undefined.md)
> **定理链**: Panic → Handler → Strategy → Unwind → UB Boundary
> **主要来源**: [Rust Reference — Panic](https://doc.rust-lang.org/reference/panic.html) · [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) · [O'Hearn — Separation Logic and Shared Mutable Data](https://doi.org/10.1017/S0960129501001003) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [TRPL — Panic](https://doc.rust-lang.org/book/ch09-01-unrecoverable-errors-with-panic.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

>
> **来源**: [Rust Reference — Panic](https://doc.rust-lang.org/reference/panic.html)

---

---

## 认知路径

> **认知路径**: 本节从 "Panic 机制" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 Panic 机制 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 Panic 机制 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与Panic 机制的适用边界。
5. **迁移应用**: 将 Panic 机制 与前置/后置概念链接，形成跨层知识网络。

---

## 反命题决策树

> **反命题 1**: "Panic 机制 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。

> **反命题 2**: "忽略 Panic 机制 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 Panic 机制 规则被违反的直接信号。

> **反命题 3**: "其他语言对 Panic 机制 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 Panic 机制 具有语言特有的形态。

## 一、什么是 Panic

**Panic** 是 Rust 提供的机制，用于阻止函数正常返回，以响应通常不可恢复的错误条件。(Source: [Rust Reference — Panic](https://doc.rust-lang.org/reference/panic.html), [TRPL Ch9 — Unrecoverable Errors](https://doc.rust-lang.org/book/ch09-01-unrecoverable-errors-with-panic.html))

- 某些语言结构（如数组越界索引）会自动 panic。
- 标准库通过 `panic!` 宏（Macro）提供显式 panic 能力。
- panic 行为由 **panic handler** 控制。
- FFI ABI 可能改变 panic 行为。

---

## 二、`panic_handler` 属性

`#[panic_handler]` 应用于函数以定义 panic 行为。

### 签名要求

```rust
fn(&PanicInfo) -> !
```

- `PanicInfo` 包含 panic 发生位置的信息。
- 整个依赖图中必须存在**唯一一个** `panic_handler` 函数。

### `no_std` 示例

```rust
#![no_std]

use core::panic::PanicInfo;

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop {}
}
```

---

## 三、标准行为

标准库提供两种 panic handler：(Source: [Rust Reference — Panic Strategy](https://doc.rust-lang.org/reference/panic.html#panic-strategy))

| 策略 | 行为 | 可恢复性 |
|:---|:---|:---:|
| `unwind` | 展开栈，调用沿途 `Drop` | 潜在可恢复 |
| `abort` | 直接 abort 进程 | 不可恢复 |

- 并非所有目标都支持 `unwind`。
- 使用 `std` 链接时，可通过 `-C panic` 选择策略；大多数目标默认 `unwind`。
- 可通过 `std::panic::set_hook` 在运行时（Runtime）修改标准库 panic 行为。(Source: [std::panic::set_hook](https://doc.rust-lang.org/std/panic/fn.set_hook.html))
- 链接 `no_std` binary、dylib、cdylib 或 staticlib 时必须自行指定 panic handler。

---

## 四、Panic Strategy

**Panic strategy** 定义 crate 构建时支持的 panic 行为。

- 可通过 `rustc` 的 `-C panic` 选择。
- 生成 binary / dylib / cdylib / staticlib 并链接 `std` 时，`-C panic` 也决定使用哪个 panic handler。
- 使用 `abort` 策略时，优化器可以假设不会跨 Rust 栈帧 unwind，从而可能减小代码体积并提升运行速度。

### 链接限制

- `unwind` 策略的 crate 可以使用 `abort` panic handler。
- `abort` 策略的 crate 不能使用 `unwind` panic handler。
- 跨不同 panic strategy 链接 crate 时存在限制，参见 linkage/unwinding 文档。

---

## 五、Unwinding

Panic 可以是可恢复的，也可以是不可恢复的，具体取决于 panic handler 配置。

### `unwind` handler

- 当 panic 发生时，`unwind` handler 会“展开” Rust 栈帧，类似 C++ 的 `throw`。
- 展开过程中，经过的 Rust 栈帧中具有 `Drop` 实现的对象会调用 `drop`。
- 保证资源清理，就像正常离开作用域一样。

### 恢复机制

- `std::panic::catch_unwind`：在当前线程内恢复 panic。(Source: [std::panic::catch_unwind](https://doc.rust-lang.org/std/panic/fn.catch_unwind.html))
- `std::thread::spawn`：自动为子线程设置 panic 恢复，使其他线程继续运行。

---

## 六、跨 FFI Boundary 的 Unwinding

跨 FFI boundary 的 unwind 需要特别小心，错误的 ABI 声明会导致未定义行为。(Source: [Rust Reference — Unwinding](https://doc.rust-lang.org/reference/panic.html#unwinding), [Rust Reference — ABIs](https://doc.rust-lang.org/reference/items/external-blocks.html#abi))

### UB 情况

- 从通过非 unwinding ABI（如 `"C"`、`"system"`）声明的外国函数引发 unwind 进入 Rust 代码。
- 从不支持 unwind 的代码调用使用 `extern "C-unwind"` 等允许 unwind 的 ABI 声明的 Rust 函数。

### 捕获外部 unwind

使用 `catch_unwind`、`JoinHandle::join` 或让其传播到 `main`/线程根时，行为未指定：

- 进程 abort；或
- 函数返回包含不透明类型的 `Result::Err`。

### 运行时边界

- 来自不同 Rust 标准库实例的 `panic` 被视为“外部异常”。
- Rust 运行时（Runtime）产生的 unwind 必须要么导致进程终止，要么被同一运行时捕获。

---

## 七、关联概念

| 概念 | 关系 |
|:---|:---|
| [Panic and Abort](../../01_foundation/08_error_handling/13_panic_and_abort.md) | panic 与 abort 的基础概念 |
| [Error Handling](../../02_intermediate/03_error_handling/04_error_handling.md) | panic 是不可恢复错误的机制，`Result` 用于可恢复错误 |
| [FFI Advanced](../04_ffi/09_ffi_advanced.md) | 跨 FFI unwind 需要正确的 ABI |
| [Behavior Considered Undefined](../../04_formal/01_ownership_logic/37_behavior_considered_undefined.md) | 错误的 FFI unwind 是 UB |
| [The Rust Runtime](30_rust_runtime.md) | panic handler 是运行时的一部分 |

> **权威来源**: [Rust Reference — Panic](https://doc.rust-lang.org/reference/panic.html), [TRPL Ch9 — Unrecoverable Errors](https://doc.rust-lang.org/book/ch09-01-unrecoverable-errors-with-panic.html), [Rustonomicon — Panics](https://doc.rust-lang.org/nomicon/unwinding.html)
>
> **权威来源对齐变更日志**: 2026-07-10 Stage F L3 补全权威来源块与关键引用 [Authority Source Sprint Batch 10](../../00_meta/02_sources/international_authority_index.md)


---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P2 生态/社区**: [docs.rs/memmap2 — 生态权威 API 文档](https://docs.rs/memmap2) · [docs.rs/embedded-hal — 生态权威 API 文档](https://docs.rs/embedded-hal)
