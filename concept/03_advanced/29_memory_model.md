# Rust 内存模型（Memory Model）

> **EN**: Memory Model
> **Summary**: Rust 内存模型的核心概念：抽象字节、初始化字节、未初始化字节与 provenance，及其对未定义行为的影响。 Core concepts of the Rust memory model: abstract bytes, initialized/uninitialized bytes, and provenance, and their impact on undefined behavior.
>
> **受众**: [专家]
> **内容分级**: [专家级]
> **Bloom 层级**: 理解 → 分析
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×Ana — 规范分析
> **前置依赖**: [Unsafe Rust](03_unsafe.md) · [Ownership](../01_foundation/01_ownership.md) · [Behavior Considered Undefined](../04_formal/37_behavior_considered_undefined.md)
> **后置概念**: [Atomics and Memory Ordering](11_atomics_and_memory_ordering.md) · [Inline Assembly](13_inline_assembly.md) · [Tree Borrows](../04_formal/36_tree_borrows_deep_dive.md)
> **定理链**: Byte Model → Provenance → UB Boundary
> **主要来源**: [Rust Reference — Memory Model](https://doc.rust-lang.org/reference/memory-model.html) · [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) · [O'Hearn — Separation Logic and Shared Mutable Data](https://doi.org/10.1017/S0960129501001003) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Rust Reference — Behavior Considered Undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

>
> **来源**: [Rust Reference — Memory Model](https://doc.rust-lang.org/reference/memory-model.html)

---


> **跨层回溯**: [内存管理](../02_intermediate/03_memory_management.md)

---

## 认知路径

> **认知路径**: 本节从 "Rust 内存模型（Memory Model）" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 Rust 内存模型（Memory Model） 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 Rust 内存模型（Memory Model） 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与Rust 内存模型（Memory Model）的适用边界。
5. **迁移应用**: 将 Rust 内存模型（Memory Model） 与前置/后置概念链接，形成跨层知识网络。


---

## 反命题决策树

> **反命题 1**: "Rust 内存模型（Memory Model） 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。

> **反命题 2**: "忽略 Rust 内存模型（Memory Model） 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 Rust 内存模型（Memory Model） 规则被违反的直接信号。

> **反命题 3**: "其他语言对 Rust 内存模型（Memory Model） 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 Rust 内存模型（Memory Model） 具有语言特有的形态。


## 一、内存模型状态

> **警告**: Rust 的内存模型目前尚不完整，部分细节尚未最终确定。

Rust 内存模型定义了程序执行期间内存的状态以及哪些操作是合法的。理解内存模型对于编写正确的 `unsafe` 代码至关重要。

---

## 二、字节（Bytes）

Rust 内存的最基本单位是**字节（byte）**。与硬件字节不同，Rust 使用一种**抽象字节**，可以区分硬件字节无法区分的状态：

- **已初始化字节（initialized byte）**: 包含一个 `u8` 值，以及可选的 provenance。
- **未初始化字节（uninitialized byte）**: 不包含确定值。

> 注意：上述列表尚未保证穷尽，未来内存模型可能引入更多字节状态。

### 为什么抽象字节重要

抽象字节的区分直接影响程序是否存在未定义行为（UB）。例如：

- 读取未初始化内存是 UB（除 `union` 字段和结构体（Struct） padding 外）。
- 指针的 provenance 决定了解引用（Reference）是否合法。

---

## 三、Provenance

**Provenance** 是指针值携带的“来源”信息，说明它指向哪个分配（allocation）。Rust 编译器利用 provenance 进行优化并判断指针使用的合法性。

关键规则：

- 将带有 provenance 的指针转译为整数再转回指针，可能丢失 provenance 信息。
- 在 const 上下文中，指针 provenance 的重组受到严格限制。

---

## 四、与未定义行为的关系

内存模型与 UB 清单紧密相关：

- 访问悬垂指针指向的内存是 UB。
- 访问未初始化字节（除允许场景外）是 UB。
- 破坏指针别名规则是 UB。

参见 [Behavior Considered Undefined](../04_formal/37_behavior_considered_undefined.md) 获取完整 UB 清单。

---

## 五、实践建议

1. **避免读取未初始化内存**: 使用 `MaybeUninit<T>` 明确表示可能未初始化的值。
2. **谨慎处理 provenance**: 避免在 `unsafe` 代码中将指针与整数随意互转。
3. **关注模型演进**: Rust 内存模型仍在完善，重要代码应跟踪 Unsafe Code Guidelines 和 Miri 的更新。

---

## 六、关联概念

| 概念 | 关系 |
|:---|:---|
| [Behavior Considered Undefined](../04_formal/37_behavior_considered_undefined.md) | 内存模型定义了 UB 的边界 |
| [Tree Borrows](../04_formal/36_tree_borrows_deep_dive.md) | 别名模型是内存模型的一部分 |
| [Atomics and Memory Ordering](11_atomics_and_memory_ordering.md) | 并发内存语义依赖内存模型 |
| [Inline Assembly](13_inline_assembly.md) | 内联汇编必须遵守内存模型约束 |
