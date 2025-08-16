# 01. 泛型导论 (Introduction to Generics)

## 目录

- [01. 泛型导论 (Introduction to Generics)](#01-泛型导论-introduction-to-generics)
  - [目录](#目录)
  - [1.1. 核心概念：什么是泛型？](#11-核心概念什么是泛型)
  - [1.2. 哲学与形式化视角：作为态射的泛型](#12-哲学与形式化视角作为态射的泛型)
  - [1.3. 实践：为何及如何使用泛型？](#13-实践为何及如何使用泛型)
  - [1.4. 编译时机制：单态化 (Monomorphization)](#14-编译时机制单态化-monomorphization)

泛型 (Generics) 是 Rust 类型系统的基石之一，它赋予了开发者编写灵活、抽象且可重用代码的能力，同时维持编译时的类型安全。通过泛型，我们可以编写出不依赖于任何具体类型的函数、结构体体体体和 trait，这些代码结构体体体能够"通用地"处理多种数据类型。

## 1.1. 核心概念：什么是泛型？

泛型的核心思想是**参数化多态 (Parametric Polymorphism)**。这意味着我们可以定义一些实体，其部分类型定义由调用者在稍后指定。这些待定的类型被称为**泛型类型参数 (Generic Type Parameters)**，通常用大写字母 `T`, `U` 等来表示。

**基础定义**:

- **泛型类型 (Generic Type)**: 在定义结构体体体体或枚举时使用的占位符类型。

    ```rust
    // `T` 是一个泛型类型参数，Point 可以是任何类型的点
    struct Point<T> {
        x: T,
        y: T,
    }
    ```

- **泛型函数 (Generic Function)**: 可以接受不同类型参数的函数。

    ```rust
    // `T` 可以是任何类型，函数返回相同类型的值
    fn identity<T>(value: T) -> T {
        value
    }
    ```

## 1.2. 哲学与形式化视角：作为态射的泛型

从范畴论的形式化视角来看，Rust 的泛型可以被理解为一种**类型的态射 (morphism)**。

在范畴论中，一个范畴由"对象"和"态射"（对象间的映射）组成。如果我们将 Rust 的类型系统视为一个范畴，那么：

- **对象 (Objects)**: 是具体的类型，如 `i32`, `String`, `MyStruct`。
- **态射 (Morphisms)**: 是类型之间的函数或映射。

一个泛型函数，如 `fn identity<T>(value: T) -> T`，可以被看作是定义了一族无穷多的态射。对于范畴中的每一个对象（类型）`T`，这个泛型定义了一个从 `T` 到 `T` 的恒等态射 (identity morphism)。同样，一个泛型结构体体体体 `Wrapper<T>` 定义了一个从任意类型 `T` 到新类型 `Wrapper<T>` 的映射，这在范畴论中被称为**类型构造器 (Type Constructor)**。

这种视角揭示了泛型的本质：它不是关于某一个具体类型，而是关于**类型之间的关系和转换**。它允许我们在一个更高的抽象层次上推理代码的行为，确保其在所有适用类型上都拥有一致的、可证明的属性。

## 1.3. 实践：为何及如何使用泛型？

泛型主要解决两大问题：**代码重复**和**类型抽象**。

**场景**: 假设我们需要一个函数来找到一个 `i32` 切片中的最大值。

```rust
fn largest_i32(list: &[i32]) -> &i32 {
    let mut largest = &list[0];
    for item in list {
        if item > largest {
            largest = item;
        }
    }
    largest
}
```

如果我们还需要一个找到 `char` 切片中最大值的函数，就必须复制代码并修改类型签名，这违反了 DRY (Don't Repeat Yourself) 原则。

**泛型解决方案**:
通过引入泛型类型参数 `T`，我们可以编写一个通用的 `largest` 函数。

```rust
// 1. 引入泛型参数 `<T>`
// 2. 将具体类型 `i32` 替换为 `T`
// 3. 添加 Trait 约束 `T: PartialOrd`，因为比较大小 (`>`) 的能力不是所有类型都具备的
fn largest<T: PartialOrd>(list: &[T]) -> &T {
    let mut largest = &list[0];
    for item in list {
        if item > largest { // `>` 操作符来自 `PartialOrd` trait
            largest = item;
        }
    }
    largest
}

fn main() {
    let numbers = vec![34, 50, 25, 100, 65];
    let result = largest(&numbers);
    println!("The largest number is {}", result); // 输出 100

    let chars = vec!['y', 'm', 'a', 'q'];
    let result = largest(&chars);
    println!("The largest char is {}", result); // 输出 'y'
}
```

通过泛型，我们用一份代码抽象了"寻找切片中最大元素"这一通用逻辑，并将其安全地应用于任何实现了 `PartialOrd` trait 的类型。

## 1.4. 编译时机制：单态化 (Monomorphization)

Rust 的泛型是**零成本抽象**。这是通过在编译时进行**单态化**实现的。

**定义**: 单态化是编译器在编译期间，将泛型代码替换为使用具体类型的特定代码的过程。编译器会查看所有泛型函数被调用的地方，根据传入的具体类型，为每种类型生成一个非泛型的、定制化的函数实现。

这意味着，虽然我们只写了一份泛型代码，但最终的可执行文件中包含的是多个高度优化的、针对具体类型的函数版本，完全没有运行时的泛型查找或分发开销。

---

**章节导航:**

- **下一章 ->** `02_generic_type_parameters.md`: 深入探讨类型参数。
- **返回目录 ->** `_index.md`

"

---
