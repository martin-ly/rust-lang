# 范畴论基础 (Category Theory Foundations)

## 1. 核心概念

范畴论是数学的一个分支，它提供了一种抽象的方式来描述数学结构及其之间的关系。它关注的是对象以及对象之间的态射（morphisms），而不是对象的内部细节。当应用于计算机科学时，范畴论为类型系统、函数式编程和并发模型提供了坚实的理论基础。

在 Rust 的语境下，我们可以建立一个称为 **Hask** (或在此情境下为 **Rust** 范畴) 的范畴，其中的对应关系如下：

-   **对象 (Objects)**: Rust 中的 **类型** (e.g., `i32`, `String`, `struct Point`, `enum Option<T>`).
-   **态射 (Morphisms)**: Rust 中的 **函数** (e.g., `fn(A) -> B`).
-   **组合 (Composition)**: 态射的组合对应于 **函数调用**。
-   **单位态射 (Identity Morphism)**: 每个对象 `T` 都有一个单位态射 `id: T -> T`，在 Rust 中这对应于恒等函数 `|x| x`。

## 2. 核心构造

### 2.1. 积 (Product) 与和 (Coproduct)

范畴论中的积与和是构造新对象的基础，它们在 Rust 的代数数据类型中得到了直接体现。

-   **积 (Product)**: 两种类型 `A` 和 `B` 的积是一个新类型 `A x B`，它包含了 `A` 和 `B` 的所有信息。在 Rust 中，这由 **元组 `(A, B)`** 和 **结构体 `struct { a: A, b: B }`** 实现。

    \[
    \text{Point} = \mathbb{R} \times \mathbb{R}
    \]

-   **和 (Coproduct or Sum)**: 两种类型 `A` 和 `B` 的和是一个新类型 `A + B`，它的值要么是 `A` 类型，要么是 `B` 类型。在 Rust 中，这由 **枚举 `enum`** 实现。`Result<T, E>` 是一个典型的和类型。

    \[
    \text{Result}<T, E> = T + E
    \]

### 2.2. 函子 (Functor)

函子是范畴之间的映射，它保持了范畴的结构（即对象和态射的组合）。在 Rust 的类型系统中，**泛型类型构造器** (如 `Option<T>`, `Vec<T>`, `Result<T, E>`) 扮演了函子的角色。它们是 **自函子 (Endofunctor)**，因为它们将 **Rust** 范畴映射到自身。

一个类型构造器 `F<T>` 是一个函子，如果它提供了一个 `map` 方法：

\[
\text{map}: (A \to B) \to F(A) \to F(B)
\]

此 `map` 函数接受一个从 `A` 到 `B` 的函数，并将其"提升"为一个从 `F<A>` 到 `F<B>` 的函数，同时保持了其结构。

```rust
// Option<T> 是一个函子
let option_a: Option<i32> = Some(5);
let option_b: Option<i32> = option_a.map(|x| x + 1); // f: i32 -> i32

// Vec<T> 也是一个函子
let vec_a: Vec<i32> = vec![1, 2, 3];
let vec_b: Vec<String> = vec_a.iter().map(|x| x.to_string()).collect(); // f: &i32 -> String
```

函子的一个关键作用是允许我们在一个"容器"或"上下文"内部对值进行操作，而无需将值取出。

### 2.3. 单子 (Monad)

单子是一种特殊的函子，它为顺序化计算提供了一种强大的抽象。一个类型 `M<T>` 是一个单子，如果它除了是函子外，还提供了两个操作：

1.  **单位 (Unit / Return)**: 一个从类型 `T` 创建一个 `M<T>` 值的函数。在 Rust 中，这通常是构造器，如 `Some(value)` 或 `Ok(value)`。

    \[
    \text{return}: T \to M(T)
    \]

2.  **绑定 (Bind)**: 一个用于链接计算的函数，通常在 Rust 中实现为 `and_then` 或 `flat_map`。它接受一个 `M<T>` 和一个返回 `M<U>` 的函数 `f: T -> M<U>`，并产生一个 `M<U>`。

    \[
    \text{bind}: M(T) \to (T \to M(U)) \to M(U)
    \]

`Option<T>` 和 `Result<T, E>` 都是 Rust 中核心的单子结构，它们被用来优雅地处理可能失败或缺失值的计算序列。

```rust
fn get_user_id(name: &str) -> Option<u32> {
    if name == "admin" { Some(1) } else { None }
}

fn get_permissions(user_id: u32) -> Option<Vec<String>> {
    if user_id == 1 { Some(vec!["read".into(), "write".into()]) } else { None }
}

// 使用 and_then (bind) 来链接计算
let perms = get_user_id("admin").and_then(get_permissions);

assert_eq!(perms, Some(vec!["read".into(), "write".into()]));
```

Rust 的 `?` 运算符是 `Result` 单子 `bind` 操作的语法糖，极大地简化了错误处理的流程。

## 3. 型变 (Variance) 与函子性

型变描述了类型构造器（函子）如何处理子类型关系。

- **协变 (Covariant)**: 如果 `A` 是 `B` 的子类型 (`A <: B`)，则 `F<A> <: F<B>`。`&'a T` 对于 `T` 是协变的。
- **逆变 (Contravariant)**: 如果 `A <: B`，则 `F<B> <: F<A>`。函数类型 `fn(T)` 对于 `T` 是逆变的。
- **不变 (Invariant)**: 即使 `A <: B`，`F<A>` 和 `F<B>` 之间也没有子类型关系。`&'a mut T` 对于 `T` 是不变的。

这些规则确保了在使用泛型类型时类型安全不会被破坏。

## 4. 与线性类型的关系

Rust 的所有权系统可以被看作是实现了 **线性类型**（更准确地说是 **仿射类型**，因为值可以被丢弃）的一种方式。在线性类型系统中，资源必须被恰好使用一次。这可以在 **单子范畴 (Monoidal Category)** 的框架内进行形式化，其中资源不能被任意复制，所有权转移是一种消耗资源的态射。借用则可以看作是一种不消耗资源的临时访问态射。
