# 特殊类型与 Trait（Special Types and Traits）

> **EN**: Special Types and Traits
> **Summary**: Rust 编译器特殊识别的标准库类型与 trait：Box、Rc、Arc、Pin、UnsafeCell、PhantomData、运算符 trait、Deref、Drop、Copy、Clone、Send、Sync、自动 trait、Sized。
>
> **受众**: [研究者]
> **内容分级**: [研究级]
> **Bloom 层级**: L2-L4
> **权威来源**: 本文件为 `concept/` 权威页。
> **定位声明**: 本页为 Rust Reference 对应章节的**规范摘译与注解**（规范条文摘译 + 示例 + 交叉引用），非形式化推导或机器验证证明；形式化理论内容见 [rustc 中的 Trait Solver](26_trait_solver_in_rustc.md)、[类型论基础](../00_type_theory/02_type_theory.md)。依据 [A/S/P 标记规范](../../00_meta/03_audit/asp_marking_guide.md) §3.4，L4 形式化层同时容纳 S（Specification）规范分析类内容，故本页保留于 L4，Bloom 层级维持与内容相符的标注（理解/分析层的规范内容）。
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×Ana — 规范分析
> **前置依赖**: [Type System](../../01_foundation/02_type_system/04_type_system.md) · [Traits](../../02_intermediate/00_traits/01_traits.md) · [Generics](../../02_intermediate/01_generics/02_generics.md)
> **后置概念**: [Unsafe Rust](../../03_advanced/02_unsafe/03_unsafe.md) · [Pin and Unpin](../../03_advanced/01_async/06_pin_unpin.md) · [Concurrency](../../03_advanced/00_concurrency/01_concurrency.md)
> **定理链**: Special Type → Compiler Support → Safety Guarantee
> **主要来源**: [Rust Reference — Special Types and Traits](https://doc.rust-lang.org/reference/special-types-and-traits.html) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [O'Hearn — Separation Logic and Shared Mutable Data](https://doi.org/10.1017/S0960129501001003) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

>
> **来源**: [Rust Reference — Special Types and Traits](https://doc.rust-lang.org/reference/special-types-and-traits.html)

---

## 一、概述

Rust 编译器对一些标准库类型和 trait 具有特殊认知。这些类型和 trait 的行为无法仅通过普通用户代码实现，或者编译器需要它们来生成正确的代码。本章概括这些特殊类型与 trait 的核心语义。

---

## 二、特殊类型

本节从 `Box<T>`、`Rc<T>` / `Arc<T>`、`Pin<P>`、`UnsafeCell<T>`等5个方面切入，剖析「特殊类型」的核心内容。

### `Box<T>`

- `Box<T>` 的解引用（Reference） `*` 产生一个可从中 move 的 place，这是语言内置行为。
- 方法可以接受 `Box<Self>` 作为 receiver。
- 可以在定义 `T` 的同一 crate 中为 `Box<T>` 实现 trait，这不受普通泛型（Generics）的孤儿规则（Orphan Rule）限制。

### `Rc<T>` / `Arc<T>`

- 方法可以接受 `Rc<Self>` / `Arc<Self>` 作为 receiver。
- `Arc<T>` 用于跨线程共享引用（Reference）计数所有权（Ownership）。

### `Pin<P>`

- 方法可以接受 `Pin<P>` 作为 receiver。
- `Pin` 用于保证指向的值在内存中不会被移动，是自引用（Reference）结构的关键抽象。

参见 [Pin and Unpin](../../03_advanced/01_async/06_pin_unpin.md)。

### `UnsafeCell<T>`

- 用于实现**内部可变性（interior mutability）**。
- 阻止编译器对内部可变类型执行不正确的优化。
- 保证带有内部可变性的 `static` 不会被放入只读内存。

参见 [Interior Mutability](../../02_intermediate/02_memory_management/08_interior_mutability.md)。

### `PhantomData<T>`

- 零大小、最小对齐的类型。
- 被编译器视为拥有一个 `T`，用于影响方差、drop check 和自动 trait 推导。
- 常用于封装外部资源时标记所有权（Ownership）或生命周期（Lifetimes）。

---

## 三、运算符 Trait

`std::ops` 和 `std::cmp` 中的 trait 用于重载运算符、索引表达式和调用表达式：

- 算术：`Add`、`Sub`、`Mul`、`Div`、`Rem`
- 位运算：`BitAnd`、`BitOr`、`BitXor`、`Shl`、`Shr`
- 一元：`Neg`、`Not`
- 索引：`Index`、`IndexMut`
- 函数调用：`Fn`、`FnMut`、`FnOnce`
- 比较：`PartialEq`、`Eq`、`PartialOrd`、`Ord`

---

## 四、`Deref` 与 `DerefMut`

- 重载一元解引用（Reference） `*`。
- 参与方法解析和自动解引用（Reference）强制（deref coercion）。

---

## 五、`Drop`

- 提供析构函数，当值被销毁时执行。
- 实现 `Drop` 的类型不能实现 `Copy`。

---

## 六、`Copy` 与 `Clone`

本节从 `Copy` 与  `Clone` 两个层面剖析「`Copy` 与 `Clone`」。

### `Copy`

- 实现 `Copy` 的值在赋值时按位复制，而不是 move。
- 要求类型不实现 `Drop`，且所有字段都实现 `Copy`。
- 编译器为以下类型自动实现 `Copy`：
  - `Copy` 类型的元组
  - 函数指针
  - 函数项类型
  - 不捕获或只捕获 `Copy` 值的闭包（Closures）

### `Clone`

- `Copy` 的 supertrait。
- 编译器自动为内置 `Copy` 类型、`Clone` 类型的元组、以及只捕获 `Clone` 值（或不捕获）的闭包（Closures）实现。

---

## 七、`Send` 与 `Sync`

「`Send` 与 `Sync`」部分包含 `Send` 与  `Sync` 两条主线，本节依次说明。

### `Send`

- 表示类型的值可以安全地从一个线程发送到另一个线程。

### `Sync`

- 表示类型的值可以安全地在多个线程之间共享（通过 `&T`）。
- 所有用于不可变 `static` 的类型必须实现 `Sync`。

参见 [Send/Sync](../../03_advanced/00_concurrency/10_concurrency_patterns.md) 与 [Atomics and Memory Ordering](../../03_advanced/00_concurrency/11_atomics_and_memory_ordering.md)。

---

## 八、自动 Trait（Auto Traits）

`Send`、`Sync`、`Unpin`、`UnwindSafe`、`RefUnwindSafe` 是**自动 trait**。自动 trait 的特殊性质：

- 若没有为某类型显式实现或负实现，编译器会自动实现。
- 自动实现规则：
  - `&T`、`&mut T`、`*const T`、`*mut T`、`[T; n]`、`[T]` 在 `T` 满足条件时实现。
  - 函数项类型和函数指针自动实现。
  - 结构体（Struct）、枚举（Enum）、联合体、元组在所有字段实现时实现。
  - 闭包（Closures）在所有捕获类型实现时实现。
- 标准库中可能存在负实现，例如 `*mut T` 不是 `Send`。
- 自动 trait 可以作为 trait object 的额外 bound，例如 `Box<dyn Debug + Send + UnwindSafe>`。

---

## 九、`Sized`

- 表示类型在编译期大小已知，即不是动态大小类型（DST）。
- 类型参数默认 `Sized`（trait 中的 `Self` 除外），关联类型也默认 `Sized`。
- 使用 `?Sized` 可以放宽这一隐含 bound。

---

## 十、`Termination`

- 表示 `main` 函数和测试函数可接受的返回类型。
- 例如 `()`、`Result<T, E>` 等都实现 `Termination`。

---

## 十一、相关概念

| 概念 | 关系 |
|:---|:---|
| [Type System](../../01_foundation/02_type_system/04_type_system.md) | 特殊类型与 trait 是类型系统的核心组成 |
| [Traits](../../02_intermediate/00_traits/01_traits.md) | 运算符 trait、自动 trait 是 trait 系统的特殊应用 |
| [Pin and Unpin](../../03_advanced/01_async/06_pin_unpin.md) | `Pin` 是特殊类型之一 |
| [Interior Mutability](../../02_intermediate/02_memory_management/08_interior_mutability.md) | `UnsafeCell` 是内部可变性的基础 |
| [Concurrency](../../03_advanced/00_concurrency/01_concurrency.md) | `Send`/`Sync` 是并发安全（Concurrency Safety）的基石 |

---

> **权威来源**: [Rust Reference — Special Types and Traits](https://doc.rust-lang.org/reference/special-types-and-traits.html) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [O'Hearn — Separation Logic and Shared Mutable Data](https://doi.org/10.1017/S0960129501001003) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [rustc Dev Guide](https://rustc-dev-guide.rust-lang.org/)
> **权威来源对齐变更日志**: 2026-07-10 补全权威来源标注（Rust Reference、TRPL、Rustonomicon、RFCs、学术论文） [Authority Source Sprint Batch L4](../../00_meta/02_sources/international_authority_index.md)

**文档版本**: 1.0
**Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-07-10
**状态**: ✅ 权威来源对齐完成 (Batch L4)

---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P2 生态/社区**: [AeneasVerif/aeneas](https://github.com/AeneasVerif/aeneas) · [model-checking/kani — 模型检查器](https://github.com/model-checking/kani)
