﻿# 02. 泛型类型参数 (Generic Type Parameters)

## 目录

- [02. 泛型类型参数 (Generic Type Parameters)](#02-泛型类型参数-generic-type-parameters)
  - [目录](#目录)
  - [2.1. 类型参数的使用场景](#21-类型参数的使用场景)
    - [2.1.1. 在函数定义中](#211-在函数定义中)
    - [2.1.2. 在结构体体体体定义中](#212-在结构体体体体定义中)
    - [2.1.3. 在枚举定义中](#213-在枚举定义中)
    - [2.1.4. 在方法定义中](#214-在方法定义中)
  - [2.2. 编译时机制：单态化 (Monomorphization) 的再探讨](#22-编译时机制单态化-monomorphization-的再探讨)

泛型类型参数是泛型编程的"原子"。
它们是在定义泛型实体时用来代表未知具体类型的占位符。
通过使用这些参数，我们可以定义出适用于多种类型的函数、结构体体体体、枚举和方法。

## 2.1. 类型参数的使用场景

类型参数可以在 Rust 的多个核心构造中使用，通常遵循 `<T>` 的语法进行声明。

### 2.1.1. 在函数定义中

这是最常见的场景，允许函数接受不同类型的参数。

```rust
// `T` 是一个类型参数，使函数可以处理任何类型的单个值
fn wrap_in_vec<T>(value: T) -> Vec<T> {
    vec![value]
}
```

### 2.1.2. 在结构体体体体定义中

这允许我们创建可以持有不同类型数据的容器或结构体体体。

```rust
// `T` 和 `U` 是两个不同的类型参数
// 这使得 `Pair` 可以持有两种不同类型的字段
struct Pair<T, U> {
    first: T,
    second: U,
}
```

### 2.1.3. 在枚举定义中

泛型在枚举中的使用非常普遍，最经典的例子就是标准库的 `Option<T>` 和 `Result<T, E>`。

```rust
enum Result<T, E> {
    Ok(T),  // `T` 代表成功时值的类型
    Err(E), // `E` 代表失败时错误的类型
}
```

### 2.1.4. 在方法定义中

我们可以在 `impl` 块中为泛型类型实现方法。此时，`impl` 后面也需要声明同样的类型参数。

```rust
struct Point<T> {
    x: T,
    y: T,
}

// 为泛型结构体体体体 `Point<T>` 实现方法
impl<T> Point<T> {
    fn x(&self) -> &T {
        &self.x
    }
}
```

值得注意的是，方法本身也可以拥有自己独立的类型参数，这在实现转换或与不同类型交互的方法时很有用。

```rust
impl<T> Point<T> {
    // `mixup` 方法自身引入了新的类型参数 `U`
    fn mixup<U>(self, other: Point<U>) -> Pair<T, U> {
        Pair {
            first: self.x,
            second: other.y,
        }
    }
}
```

## 2.2. 编译时机制：单态化 (Monomorphization) 的再探讨

如导论所述，Rust 通过**单态化**来实现泛型的零成本抽象。理解这一过程对深入掌握泛型至关重要。

**过程详解**:
当编译器遇到一个泛型函数的调用时（例如 `wrap_in_vec(5i32)`），它会执行以下步骤：

1. **类型推断**: 确定泛型参数 `T` 在此次调用中被具体化为 `i32`。
2. **代码生成**: 编译器会生成一份 `wrap_in_vec` 函数的全新副本，其中所有的 `T` 都被替换为 `i32`。这份新生成的代码看起来会像这样：

    ```rust
    // 编译器为 `i32` 类型生成的版本
    fn wrap_in_vec_i32(value: i32) -> Vec<i32> {
        vec![value]
    }
    ```

3. **调用替换**: 原始的泛型调用 `wrap_in_vec(5i32)` 在最终的机器码中会被替换为对这个具体化版本 `wrap_in_vec_i32(5)` 的调用。

如果代码中还有另一次调用 `wrap_in_vec("hello")`，编译器会重复此过程，生成一个 `T` 被替换为 `&'static str` 的新版本。

**影响**:

- **性能**: 由于最终执行的是针对具体类型的、非泛型的代码，所以完全没有运行时的类型检查或动态分派的开销。泛型代码的运行效率与手写具体类型的代码完全相同。
- **二进制文件大小**: 单态化的一个潜在缺点是可能导致最终生成的二进制文件变大，因为同一泛型函数的代码可能会为多个不同的具体类型复制多份。然而，在实践中，由于编译器的各种优化，这个问题通常在可控作用域内。

这种在编译时将抽象"消除"的策略，是 Rust 能够同时提供高级抽象和底层性能的关键所在。

---

**章节导航:**

- **上一章 ->** `01_introduction_to_generics.md`
- **下一章 ->** `03_trait_bounds.md`: 学习如何使用 Trait 来约束类型参数。
- **返回目录 ->** `_index.md`

"

---

<!-- 以下为按标准模板自动补全的占位章节，待后续填充 -->
"
## 概述
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 技术背景
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 核心概念
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 技术实现
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 形式化分析
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 应用案例
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 性能分析
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 最佳实践
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 常见问题
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 未来值值展望
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n


