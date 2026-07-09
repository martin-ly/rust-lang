# Rust 内存模型（Memory Model）

> **EN**: Memory Model
> **Summary**: Rust 内存模型的核心概念：抽象字节、初始化字节、未初始化字节与 provenance，及其对未定义行为的影响。 Core concepts of the Rust memory model: abstract bytes, initialized/uninitialized bytes, provenance, and their impact on undefined behavior.
>
> **受众**: [专家]
> **内容分级**: [专家级]
> **Bloom 层级**: 理解 → 分析
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×Ana — 规范分析
> **前置依赖**: [Unsafe Rust](03_unsafe.md) · [Ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) · [Behavior Considered Undefined](../../04_formal/01_ownership_logic/37_behavior_considered_undefined.md)
> **后置概念**: [Atomics and Memory Ordering](../00_concurrency/11_atomics_and_memory_ordering.md) · [Inline Assembly](../05_inline_assembly/13_inline_assembly.md) · [Tree Borrows](../../04_formal/01_ownership_logic/36_tree_borrows_deep_dive.md)
> **定理链**: Byte Model → Provenance → UB Boundary
> **主要来源**: [Rust Reference — Memory Model](https://doc.rust-lang.org/reference/memory-model.html) · [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) · [O'Hearn — Separation Logic and Shared Mutable Data](https://doi.org/10.1017/S0960129501001003) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Rust Reference — Behavior Considered Undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html)

>
> **来源**: [Rust Reference — Memory Model](https://doc.rust-lang.org/reference/memory-model.html) · [Rust Reference — Behavior Considered Undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html)

---

> **跨层回溯**: [内存管理](../../02_intermediate/02_memory_management/03_memory_management.md)

---

## 认知路径

> **认知路径**: 本节从 "Rust 内存模型（Memory Model）" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 Rust 内存模型值得关注？正确编写 `unsafe` 代码、FFI 和内联汇编都需要理解内存模型边界。
2. **概念建立**: 掌握抽象字节、初始化/未初始化字节、provenance 和别名规则的核心定义。
3. **机制推理**: 通过 ⟹ 定理链将字节模型、provenance 和 UB 边界串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与 Rust 内存模型的适用边界。
5. **迁移应用**: 将 Rust 内存模型与原子操作、内联汇编、Tree Borrows 等概念链接，形成跨层知识网络。

---

## 反命题决策树

> **反命题 1**: "Rust 内存模型在所有场景下都完全确定" ⟹ 不成立。Rust 的内存模型目前尚不完整，部分细节仍在 Unsafe Code Guidelines 工作组讨论中。

> **反命题 2**: "忽略 Rust 内存模型的细节也能写出正确 unsafe 代码" ⟹ 不成立。未初始化内存读取、provenance 丢失和别名违规都是常见的 UB 来源。

> **反命题 3**: "其他语言对内存模型的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权、借用和 provenance 模型具有语言特有形态。

## 一、内存模型状态

> **警告**: Rust 的内存模型目前尚不完整，部分细节尚未最终确定。

Rust 内存模型定义了程序执行期间内存的状态以及哪些操作是合法的。理解内存模型对于编写正确的 `unsafe` 代码至关重要。

## 二、字节（Bytes）

Rust 内存的最基本单位是**字节（byte）**。与硬件字节不同，Rust 使用一种**抽象字节**，可以区分硬件字节无法区分的状态：

- **已初始化字节（initialized byte）**: 包含一个 `u8` 值，以及可选的 provenance。
- **未初始化字节（uninitialized byte）**: 不包含确定值。

> 注意：上述列表尚未保证穷尽，未来内存模型可能引入更多字节状态。

### 为什么抽象字节重要

抽象字节的区分直接影响程序是否存在未定义行为（UB）。例如：

- 读取未初始化内存是 UB（除 `union` 字段和结构体 padding 外）。
- 指针的 provenance 决定了解引用是否合法。

## 三、Provenance

**Provenance** 是指针值携带的"来源"信息，说明它指向哪个分配（allocation）。Rust 编译器利用 provenance 进行优化并判断指针使用的合法性。

关键规则：

- 将带有 provenance 的指针转译为整数再转回指针，可能丢失 provenance 信息。
- 在 const 上下文中，指针 provenance 的重组受到严格限制。

```rust
// 危险：可能丢失 provenance
let ptr: *mut u8 = alloc(layout);
let addr = ptr as usize;
let restored = addr as *mut u8; // provenance 可能无效
```

## 四、初始化与 MaybeUninit

`MaybeUninit<T>` 是处理未初始化内存的核心类型：

```rust
use std::mem::MaybeUninit;

let mut x: MaybeUninit<i32> = MaybeUninit::uninit();
x.write(42);
let val = unsafe { x.assume_init() };
```

| 操作 | 安全/Unsafe | 说明 |
|:---|:---|:---|
| `MaybeUninit::uninit()` | Safe | 创建未初始化值 |
| `write()` | Safe | 写入值 |
| `assume_init()` | Unsafe | 断言已初始化，读取值 |
| `assume_init_ref()` | Unsafe | 获取已初始化引用 |

## 五、与未定义行为的关系

内存模型与 UB 清单紧密相关：

- 访问悬垂指针指向的内存是 UB。
- 访问未初始化字节（除允许场景外）是 UB。
- 破坏指针别名规则是 UB。

参见 [Behavior Considered Undefined](../../04_formal/01_ownership_logic/37_behavior_considered_undefined.md) 获取完整 UB 清单。

## 六、别名模型：Stacked Borrows / Tree Borrows

Rust 正在从 Stacked Borrows 向 Tree Borrows 演进，作为内存模型的别名规则部分：

| 模型 | 特点 |
|:---|:---|
| Stacked Borrows | 基于栈的借用权限追踪，严格但限制较多 |
| Tree Borrows | 基于树的权限模型，对更多合法 unsafe 模式更宽容 |

Tree Borrows 详见 [Tree Borrows](../../04_formal/01_ownership_logic/36_tree_borrows_deep_dive.md)。

## 七、实践建议

1. **避免读取未初始化内存**: 使用 `MaybeUninit<T>` 明确表示可能未初始化的值。
2. **谨慎处理 provenance**: 避免在 `unsafe` 代码中将指针与整数随意互转。
3. **关注模型演进**: Rust 内存模型仍在完善，重要代码应跟踪 Unsafe Code Guidelines 和 Miri 的更新。
4. **使用 Miri 测试**: Miri 是检测内存模型违规的重要工具。

```bash
cargo +nightly miri test
```

## 八、关联概念

| 概念 | 关系 |
|:---|:---|
| [Behavior Considered Undefined](../../04_formal/01_ownership_logic/37_behavior_considered_undefined.md) | 内存模型定义了 UB 的边界 |
| [Tree Borrows](../../04_formal/01_ownership_logic/36_tree_borrows_deep_dive.md) | 别名模型是内存模型的一部分 |
| [Atomics and Memory Ordering](../00_concurrency/11_atomics_and_memory_ordering.md) | 并发内存语义依赖内存模型 |
| [Inline Assembly](../05_inline_assembly/13_inline_assembly.md) | 内联汇编必须遵守内存模型约束 |
| [Unsafe Rust](03_unsafe.md) | 内存模型主要约束 unsafe 代码 |
| [Panic](31_panic.md) | panic 时的栈展开必须保持内存安全 |

---

> **权威来源**: [Rust Reference — Memory Model](https://doc.rust-lang.org/reference/memory-model.html) · [Rust Reference — Behavior Considered Undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html) · [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) · [Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/)
> **内容分级**: [专家级]
