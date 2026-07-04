# Unsafe 参考（Unsafe Reference）

> **EN**: Unsafe Reference
> **Summary**: Rust Reference 对 `unsafe` 的规范：`unsafe` 关键字、`unsafe` 块、函数、trait、实现的外部契约，以及“不被视为 unsafe 的行为”。
>
> **受众**: [专家]
> **内容分级**: [专家级]
> **Bloom 层级**: 理解 → 分析
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×Ana — 规范分析
> **前置依赖**: [Unsafe Rust](03_unsafe.md) · [Behavior Considered Undefined](../04_formal/37_behavior_considered_undefined.md) · [Variables](33_variables.md)
> **后置概念**: [Inline Assembly](13_inline_assembly.md) · [FFI Advanced](09_ffi_advanced.md) · [Custom Allocators](14_custom_allocators.md)
> **定理链**: Unsafe Keyword → Unsafe Block → Unsafe Operation → UB Contract
>
> **来源**: [Rust Reference — Unsafety](https://doc.rust-lang.org/reference/unsafe-keyword.html) · [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) · [O'Hearn — Separation Logic and Shared Mutable Data](https://doi.org/10.1017/S0960129501001003) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [TRPL — Unsafe Rust](https://doc.rust-lang.org/book/ch19-01-unsafe-rust.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

---


> **跨层回溯**: [智能指针（Smart Pointer）](../02_intermediate/12_smart_pointers.md) · [内部可变性](../02_intermediate/08_interior_mutability.md)

---

## 认知路径

> **认知路径**: 本节从 "Unsafe 参考（Unsafe Reference）" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 Unsafe 参考（Unsafe Reference） 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 Unsafe 参考（Unsafe Reference） 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与Unsafe 参考（Unsafe Reference）的适用边界。
5. **迁移应用**: 将 Unsafe 参考（Unsafe Reference） 与前置/后置概念链接，形成跨层知识网络。


---

## 反命题决策树

> **反命题 1**: "Unsafe 参考（Unsafe Reference） 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。

> **反命题 2**: "忽略 Unsafe 参考（Unsafe Reference） 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 Unsafe 参考（Unsafe Reference） 规则被违反的直接信号。

> **反命题 3**: "其他语言对 Unsafe 参考（Unsafe Reference） 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 Unsafe 参考（Unsafe Reference） 具有语言特有的形态。


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

> `unsafe` 块**不**禁用借用（Borrowing）检查器；它只放宽上述操作限制。

## 三、安全抽象层

将 unsafe 操作封装为 safe API 时，必须确保：

- 所有公开 safe 函数的输入都满足 unsafe 前置条件。
- 不变式在类型层面尽可能编码（如 `NonNull<T>` 保证非空）。
- 文档清楚说明调用者/实现者的责任。

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

`unsafe` 代码必须避免 UB。完整 UB 清单见 [Behavior Considered Undefined](../04_formal/37_behavior_considered_undefined.md)。

常见 unsafe 契约包括：

- 裸指针必须有效且对齐。
- `union` 字段访问必须对应实际存储的变体。
- `unsafe` trait 的实现必须满足文档中的不变式。

---

> **权威来源**: [Rust Reference — Unsafe Keyword](https://doc.rust-lang.org/reference/unsafe-keyword.html) · [Rust Reference — Behavior Not Considered Unsafe](https://doc.rust-lang.org/reference/behavior-not-considered-unsafe.html)
> **内容分级**: [专家级]
