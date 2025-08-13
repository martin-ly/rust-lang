# Rust 类型系统：基础概念

## 目录

- [Rust 类型系统：基础概念](#rust-类型系统基础概念)
  - [目录](#目录)
    - [1. 类型分类概览](#1-类型分类概览)
    - [2. 原始类型 (Scalar Types)](#2-原始类型-scalar-types)
      - [2.1. 整数、浮点数、布尔与字符](#21-整数浮点数布尔与字符)
      - [2.2. 单元类型 `()`](#22-单元类型-)
    - [3. 复合类型 (Compound Types)——代数数据类型](#3-复合类型-compound-types代数数据类型)
      - [3.1. 结构体体体体 (Structs) - 积类型 (Product Type)](#31-结构体体体体-structs---积类型-product-type)
      - [3.2. 枚举 (Enums) - 和类型 (Sum Type)](#32-枚举-enums---和类型-sum-type)
      - [3.3. 元组 (Tuples) - 匿名的积类型](#33-元组-tuples---匿名的积类型)
    - [4. 序列类型 (Sequence Types)](#4-序列类型-sequence-types)
      - [4.1. 数组 `[T; N]`](#41-数组-t-n)
      - [4.2. 切片 `&[T]`](#42-切片-t)
    - [5. 指针类型 (Pointer Types)](#5-指针类型-pointer-types)
      - [5.1. 引用 `&T` 与 `&mut T`](#51-引用-t-与-mut-t)
      - [5.2. 裸指针 `*const T` 与 `*mut T`](#52-裸指针-const-t-与-mut-t)
      - [5.3. 智能指针 (Smart Pointers)](#53-智能指针-smart-pointers)
    - [6. 函数类型 (Function Types)](#6-函数类型-function-types)
    - [7. 总结](#7-总结)

---

### 1. 类型分类概览

Rust 的类型系统构建在一系列基础类型之上，这些类型可以组合成更复杂的结构体体体。理解这些基础构件是掌握 Rust 的第一步。它们大致可分为：

- **原始类型 (Scalar Types)**：表示单个值，是构成其他所有类型的基础。
- **复合类型 (Compound Types)**：将多个值组合成一个类型，主要体现为代数数据类型 (ADT)。
- **序列类型 (Sequence Types)**：表示一连串相同类型的元素。
- **指针类型 (Pointer Types)**：提供对内存地址的间接访问。
- **函数类型 (Function Types)**：表示函数或闭包的签名。

### 2. 原始类型 (Scalar Types)

#### 2.1. 整数、浮点数、布尔与字符

这些是编程语言中最常见的类型。

| 类型 | 描述 | 示例 |
| :--- | :--- | :--- |
| **整数 (Integer)** | 有符号 (`i8`..`i128`, `isize`) 和无符号 (`u8`..`u128`, `usize`) 整数。`isize`/`usize` 的大小与目标平台的指针大小相同。 | `let x: i32 = -5;` |
| **浮点数 (Float)**| `f32` 和 `f64`，遵循 IEEE-754 标准。| `let y: f64 = 3.14;` |
| **布尔 (Boolean)**| `bool` 类型，只有 `true` 和 `false` 两个值。| `let is_active: bool = true;` |
| **字符 (Character)**| `char` 类型，表示一个单独的 Unicode 标量值，占用 4 个字节。| `let heart: char = '❤';` |

#### 2.2. 单元类型 `()`

单元类型 `()` 是一个特殊的原始类型，它只有一个值，也写作 `()`。它通常用作不返回任何有意义的值的函数的返回类型，或者在元组中作为占位符。在类型理论中，它被称为 **终端对象 (Terminal Object)** 或 **Unit Type**。

```rust
fn do_nothing() { // 隐式返回 ()
    // ...
}

let a = (); // a 的类型是 ()
```

### 3. 复合类型 (Compound Types)——代数数据类型

复合类型将多个不同类型的值组合成一个整体。Rust 的复合类型是 **代数数据类型 (Algebraic Data Types, ADT)** 的直接体现。

#### 3.1. 结构体体体体 (Structs) - 积类型 (Product Type)

结构体体体体允许你将多个相关的值打包成一个有意义的单元。

- **形式化定义**: 结构体体体体是 **积类型** 的实现。一个类型 `struct T { a: A, b: B }` 的所有可能值的集合，是类型 `A` 的值集和类型 `B` 的值集的 **笛卡尔积 (Cartesian Product)**。
  - **构造子**: `T { a, b }`
  - **消除子 (投影)**: `value.a`, `value.b`

```rust
// 经典的 C 风格结构体体体体
struct Point {
    x: f64,
    y: f64,
}

// 元组结构体体体体 (Tuple Struct)
struct Color(u8, u8, u8);

// 单元结构体体体体 (Unit-like Struct)，常用于标记
struct Marker;
```

#### 3.2. 枚举 (Enums) - 和类型 (Sum Type)

枚举允许你定义一个可以是多种不同变体之一的类型。

- **形式化定义**: 枚举是 **和类型 (或余积类型, Coproduct Type)** 的实现。一个类型 `enum E { V1(A), V2(B) }` 的所有可能值的集合，是类型 `A` 的值集和类型 `B` 的值集的 **不交并 (Disjoint Union)**。
  - **构造子 (内射)**: `E::V1(a)`, `E::V2(b)`
  - **消除子 (case分析)**: `match` 表达式

```rust
enum WebEvent {
    PageLoad, // 无关联数据的变体
    KeyPress(char), // 关联一个 `char` 数据的变体
    Click { x: i64, y: i64 }, // 关联一个匿名结构体体体体的变体
}
```

#### 3.3. 元组 (Tuples) - 匿名的积类型

元组是一种简单的复合类型，允许将多个不同类型的值组合成一个固定长度的序列。可以看作是匿名的结构体体体体。

```rust
let person: (String, i32) = ("Alice".to_string(), 30);
let name = person.0; // 通过索引访问
```

### 4. 序列类型 (Sequence Types)

#### 4.1. 数组 `[T; N]`

数组是存储在 **栈上** 的、**固定长度** 的、**同质** (所有元素类型相同) 的集合。其长度 `N` 在编译时确定。

```rust
let numbers: [i32; 5] = [1, 2, 3, 4, 5];
```

#### 4.2. 切片 `&[T]`

切片是对内存中一个连续序列的 **视图 (view)** 或 **引用**。它本身不拥有数据，只是"借用"了数据的一部分。切片是一个"胖指针"，包含了指向序列头部的指针和序列的长度。

```rust
let array = [1, 2, 3, 4, 5];
let slice: &[i32] = &array[1..3]; // 指向 array 中的 [2, 3]
```

### 5. 指针类型 (Pointer Types)

#### 5.1. 引用 `&T` 与 `&mut T`

引用是最常见的指针类型，它们是 **受编译器严格检查的、保证安全的指针**。

- `&T`: 不可变引用，允许多个同时存在，只读。
- `&mut T`: 可变引用，在同一作用域内具有唯一性，可读写。
借用检查器确保引用总是指向有效的内存，从而从根本上消除了悬垂指针。

#### 5.2. 裸指针 `*const T` 与 `*mut T`

裸指针是 Rust 中最接近 C 语言指针的类型。

- 它们不保证指向有效的内存。
- 它们可以有任意别名。
- 解引用裸指针是一个 `unsafe` 操作，必须在 `unsafe` 块中进行。

裸指针主要用于与 C 库交互 (FFI) 或构建底层的、安全的抽象（如 `Vec<T>` 的内部实现）。

#### 5.3. 智能指针 (Smart Pointers)

智能指针是一些表现得像指针，但拥有额外元数据和能力的结构体体体体。它们通过实现 `Deref` 和 `Drop` Trait 来提供这些功能。常见的智能指针包括：

- `Box<T>`: 在堆上分配值。
- `Rc<T>` / `Arc<T>`: 引用计数，用于共享所有权。
- `RefCell<T>` / `Mutex<T>`: 提供内部可变性。

### 6. 函数类型 (Function Types)

在 Rust 中，函数也是一等公民，它们拥有自己的类型。`fn` 关键字用于表示函数指针类型。

```rust
fn add_one(x: i32) -> i32 {
    x + 1
}

let f: fn(i32) -> i32 = add_one; // f 是一个函数指针
```

### 7. 总结

Rust 的基础类型系统通过将来自类型理论的坚实概念（如积类型、和类型）与独特的内存管理模型（所有权、借用）相结合，提供了一套既富有表现力又极其安全的工具集。从简单的原始类型到复杂的复合结构体体体，每一种类型都经过精心设计，以在编译时强制执行不变量，从而将错误扼杀在摇篮中。

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


