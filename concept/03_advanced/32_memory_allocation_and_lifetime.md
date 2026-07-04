# 内存分配与生命周期（Memory Allocation and Lifetime）

> **EN**: Memory Allocation and Lifetime
> **Summary**: Rust 内存分配模型：item、heap、stack 与 box 的生命周期（Lifetimes）关系。
>
> **受众**: [专家]
> **内容分级**: [专家级]
> **Bloom 层级**: 理解 → 分析
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×Ana — 规范分析
> **前置依赖**: [Ownership](../01_foundation/01_ownership.md) · [Memory Model](29_memory_model.md) · [Variables](33_variables.md)
> **后置概念**: [Smart Pointers](../02_intermediate/12_smart_pointers.md) · [Custom Allocators](14_custom_allocators.md) · [The Rust Runtime](30_rust_runtime.md)
> **定理链**: Allocation → Box Lifetime → Heap Stability
> **主要来源**: [Rust Reference — Memory Allocation and Lifetime](https://doc.rust-lang.org/reference/memory-allocation-and-lifetime.html) · [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) · [O'Hearn — Separation Logic and Shared Mutable Data](https://doi.org/10.1017/S0960129501001003) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [TRPL — Ownership](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

>
> **来源**: [Rust Reference — Memory Allocation and Lifetime](https://doc.rust-lang.org/reference/memory-allocation-and-lifetime.html)

---


---

## 认知路径

> **认知路径**: 本节从 "内存分配与生命周期（Memory Allocation an" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 内存分配与生命周期（Memory Allocation an 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 内存分配与生命周期（Memory Allocation an 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与内存分配与生命周期（Memory Allocation an的适用边界。
5. **迁移应用**: 将 内存分配与生命周期（Memory Allocation an 与前置/后置概念链接，形成跨层知识网络。


---

## 反命题决策树

> **反命题 1**: "内存分配与生命周期（Memory Allocation an 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。

> **反命题 2**: "忽略 内存分配与生命周期（Memory Allocation an 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 内存分配与生命周期（Memory Allocation an 规则被违反的直接信号。

> **反命题 3**: "其他语言对 内存分配与生命周期（Memory Allocation an 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 内存分配与生命周期（Memory Allocation an 具有语言特有的形态。


## 一、Item 的生命周期

程序中的 **item**（函数、模块（Module）、类型）在编译期计算其值，并在 Rust 进程的内存映像中唯一存储。

- item 不是动态分配或释放的。
- item 的生命周期（Lifetimes）与整个程序相同。

---

## 二、Heap（堆）

**堆（heap）** 是 `Box<T>` 等拥有所有权（Ownership）的指针所指向的内存区域。

### 堆分配的生命周期

- 堆分配的生命周期取决于指向它的 box 值的生命周期。
- box 值可以在栈帧之间传递，也可以存储在堆上，因此堆分配可能超出创建它的栈帧。
- 堆分配保证在其整个生命周期中位于堆上的固定位置——移动 box 值本身不会导致堆内存重定位。

---

## 三、Stack（栈）

- 局部变量和临时值分配在栈帧中。
- 栈帧在函数调用时创建，在函数返回时销毁。
- 局部变量默认不可变，使用 `let mut` 声明可变。

更多细节参见 [Variables](33_variables.md)。

---

## 四、Box 与移动

```rust
let b = Box::new(42);
let c = b; // b 被 move，所有权转移到 c
```

- 移动 box 值只是复制指针，不会复制堆上的数据。
- 堆数据的所有权（Ownership）随 box 值一起转移。
- 当 box 离开作用域时，堆上的数据被释放。

---

## 五、关联概念

| 概念 | 关系 |
|:---|:---|
| [Memory Model](29_memory_model.md) | 内存分配模型是内存模型的一部分 |
| [Variables](33_variables.md) | 局部变量在栈帧中分配 |
| [Smart Pointers](../02_intermediate/12_smart_pointers.md) | `Box`、`Rc`、`Arc` 管理堆内存 |
| [Custom Allocators](14_custom_allocators.md) | 自定义分配器改变堆分配行为 |
| [The Rust Runtime](30_rust_runtime.md) | `#[global_allocator]` 影响堆分配 |
