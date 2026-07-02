# 特殊类型与 Trait（Special Types and Traits）

> **EN**: Special Types and Traits
> **Summary**: Rust 编译器特殊识别的标准库类型与 trait：Box、Rc、Arc、Pin、UnsafeCell、PhantomData、运算符 trait、Deref、Drop、Copy、Clone、Send、Sync、自动 trait、Sized。
>
> **受众**: [研究者]
> **内容分级**: [研究级]
> **Bloom 层级**: 理解 → 分析
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×Ana — 规范分析
> **前置依赖**: [Type System](../01_foundation/04_type_system.md) · [Traits](../02_intermediate/01_traits.md) · [Generics](../02_intermediate/02_generics.md)
> **后置概念**: [Unsafe Rust](../03_advanced/03_unsafe.md) · [Pin and Unpin](../03_advanced/06_pin_unpin.md) · [Concurrency](../03_advanced/01_concurrency.md)
> **定理链**: Special Type → Compiler Support → Safety Guarantee
>
> **来源**: [Rust Reference — Special Types and Traits](https://doc.rust-lang.org/reference/special-types-and-traits.html)

---

## 一、概述

Rust 编译器对一些标准库类型和 trait 具有特殊认知。这些类型和 trait 的行为无法仅通过普通用户代码实现，或者编译器需要它们来生成正确的代码。本章概括这些特殊类型与 trait 的核心语义。

---

## 二、特殊类型

### `Box<T>`

- `Box<T>` 的解引用 `*` 产生一个可从中 move 的 place，这是语言内置行为。
- 方法可以接受 `Box<Self>` 作为 receiver。
- 可以在定义 `T` 的同一 crate 中为 `Box<T>` 实现 trait，这不受普通泛型的孤儿规则限制。

### `Rc<T>` / `Arc<T>`

- 方法可以接受 `Rc<Self>` / `Arc<Self>` 作为 receiver。
- `Arc<T>` 用于跨线程共享引用计数所有权。

### `Pin<P>`

- 方法可以接受 `Pin<P>` 作为 receiver。
- `Pin` 用于保证指向的值在内存中不会被移动，是自引用结构的关键抽象。

参见 [Pin and Unpin](../03_advanced/06_pin_unpin.md)。

### `UnsafeCell<T>`

- 用于实现**内部可变性（interior mutability）**。
- 阻止编译器对内部可变类型执行不正确的优化。
- 保证带有内部可变性的 `static` 不会被放入只读内存。

参见 [Interior Mutability](../02_intermediate/08_interior_mutability.md)。

### `PhantomData<T>`

- 零大小、最小对齐的类型。
- 被编译器视为拥有一个 `T`，用于影响方差、drop check 和自动 trait 推导。
- 常用于封装外部资源时标记所有权或生命周期。

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

- 重载一元解引用 `*`。
- 参与方法解析和自动解引用强制（deref coercion）。

---

## 五、`Drop`

- 提供析构函数，当值被销毁时执行。
- 实现 `Drop` 的类型不能实现 `Copy`。

---

## 六、`Copy` 与 `Clone`

### `Copy`

- 实现 `Copy` 的值在赋值时按位复制，而不是 move。
- 要求类型不实现 `Drop`，且所有字段都实现 `Copy`。
- 编译器为以下类型自动实现 `Copy`：
  - `Copy` 类型的元组
  - 函数指针
  - 函数项类型
  - 不捕获或只捕获 `Copy` 值的闭包

### `Clone`

- `Copy` 的 supertrait。
- 编译器自动为内置 `Copy` 类型、`Clone` 类型的元组、以及只捕获 `Clone` 值（或不捕获）的闭包实现。

---

## 七、`Send` 与 `Sync`

### `Send`

- 表示类型的值可以安全地从一个线程发送到另一个线程。

### `Sync`

- 表示类型的值可以安全地在多个线程之间共享（通过 `&T`）。
- 所有用于不可变 `static` 的类型必须实现 `Sync`。

参见 [Send/Sync](../03_advanced/10_concurrency_patterns.md) 与 [Atomics and Memory Ordering](../03_advanced/11_atomics_and_memory_ordering.md)。

---

## 八、自动 Trait（Auto Traits）

`Send`、`Sync`、`Unpin`、`UnwindSafe`、`RefUnwindSafe` 是**自动 trait**。自动 trait 的特殊性质：

- 若没有为某类型显式实现或负实现，编译器会自动实现。
- 自动实现规则：
  - `&T`、`&mut T`、`*const T`、`*mut T`、`[T; n]`、`[T]` 在 `T` 满足条件时实现。
  - 函数项类型和函数指针自动实现。
  - 结构体、枚举、联合体、元组在所有字段实现时实现。
  - 闭包在所有捕获类型实现时实现。
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

## 十一、关联概念

| 概念 | 关系 |
|:---|:---|
| [Type System](../01_foundation/04_type_system.md) | 特殊类型与 trait 是类型系统的核心组成 |
| [Traits](../02_intermediate/01_traits.md) | 运算符 trait、自动 trait 是 trait 系统的特殊应用 |
| [Pin and Unpin](../03_advanced/06_pin_unpin.md) | `Pin` 是特殊类型之一 |
| [Interior Mutability](../02_intermediate/08_interior_mutability.md) | `UnsafeCell` 是内部可变性的基础 |
| [Concurrency](../03_advanced/01_concurrency.md) | `Send`/`Sync` 是并发安全的基石 |
