# Rust 类型系统：型变 (Variance)

## 目录

- [Rust 类型系统：型变 (Variance)](#rust-类型系统型变-variance)
  - [目录](#目录)
    - [1. 什么是型变？](#1-什么是型变)
    - [2. 协变 (Covariance)：保持子类型关系](#2-协变-covariance保持子类型关系)
    - [3. 逆变 (Contravariance)：反转子类型关系](#3-逆变-contravariance反转子类型关系)
    - [4. 不变 (Invariance)：无子类型关系](#4-不变-invariance无子类型关系)
      - [4.1. `&mut T` 为何必须是不变的？](#41-mut-t-为何必须是不变的)
    - [5. 型变的推导与 `PhantomData`](#5-型变的推导与-phantomdata)
      - [5.1. 编译器如何推导型变](#51-编译器如何推导型变)
      - [5.2. 使用 `PhantomData` 影响型变](#52-使用-phantomdata-影响型变)
    - [6. 哲学批判性分析](#6-哲学批判性分析)
      - [6.1. 安全的必要复杂性](#61-安全的必要复杂性)
      - [6.2. 与其他语言的对比](#62-与其他语言的对比)
    - [7. 总结](#7-总结)

---

### 1. 什么是型变？

型变 (Variance) 是一个类型理论概念，它描述了当类型参数之间存在子类型关系时，包含这些参数的泛型类型之间会形成什么样的子类型关系。

在 Rust 中，型变最常通过 **生命周期 (lifetimes)** 来体现。我们知道，如果生命周期 `'long` 长于 `'short`（写作 `'long: 'short`），那么 `'long` 就是 `'short` 的一个子类型。

核心问题是：给定 `'long: 'short`，泛型类型 `F<'long>` 和 `F<'short>` 之间是什么关系？

- 如果 `F<'long>` 是 `F<'short>` 的子类型，我们称 `F` 对于其生命周期参数是**协变**的。
- 如果 `F<'short>` 是 `F<'long>` 的子类型，我们称 `F` 是**逆变**的。
- 如果两者之间没有子类型关系，我们称 `F` 是**不变**的。

### 2. 协变 (Covariance)：保持子类型关系

**定义**：如果 `T` 是 `U` 的子类型，且 `F<T>` 也是 `F<U>` 的子类型，则 `F` 对参数 `T` 是协变的。

在生命周期中，这意味着如果 `'long: 'short`，那么 `F<'long>` 是 `F<'short>` 的子类型。这非常直观：一个生命周期更长的引用，用在一个需要生命周期更短的引用的地方，总是安全的。

**例子**:

- `&'a T` 对 `'a` 和 `T` 都是协变的。
- `Box<&'a T>` 对 `'a` 是协变的。
- `Vec<&'a T>` 对 `'a` 是协变的。

```rust
fn foo<'long, 'short>(long_ref: &'long str, mut short_ref: &'short str) where 'long: 'short {
    // 合法：可以将一个长生命周期的引用赋给短生命周期的变量
    // 因为 &'long str 是 &'short str 的子类型
    short_ref = long_ref;
}
```

协变是最常见、最符合直觉的型变。

### 3. 逆变 (Contravariance)：反转子类型关系

**定义**：如果 `T` 是 `U` 的子类型，但 `F<U>` 是 `F<T>` 的子类型，则 `F` 对参数 `T` 是逆变的。子类型关系被反转了。

逆变在 Rust 中非常少见，其唯一的主要例子是 **函数参数类型**。

**例子**: `fn(T)` 对 `T` 是逆变的。

- 假设 `'long: 'short`。
- `fn(&'short T)` 是 `fn(&'long T)` 的子类型。

这看起来违反直觉，但可以通过一个例子来理解：
想象一个 API 需要一个“能处理任何长生命周期引用的函数”。如果我们提供一个“能处理任何短生命周期引用的函数”，这是安全的吗？是的，因为短生命周期的函数能力更强——它能处理的输入范围更广（包括了所有长生命周期的引用）。

```rust
// 这个函数接受一个闭包，该闭包可以处理任何 'static 引用
fn process_item(f: fn(&'static str)) {
    f("I am a static string");
}

// 这是一个可以处理任何生命周期引用的函数
fn print_any_str(s: &str) {
    println!("{}", s);
}

fn main() {
    // 合法：可以将一个能力更强（能处理任何 &str）的函数
    // 用在一个要求能力较弱（只需处理 &'static str）的地方。
    // fn(&'a str) 是 fn(&'static str) 的子类型。
    process_item(print_any_str);
}
```

### 4. 不变 (Invariance)：无子类型关系

**定义**：即使 `T` 是 `U` 的子类型，`F<T>` 和 `F<U>` 之间也没有子类型关系。

不变性通常是为了保证内存安全，尤其是在涉及可变性的情况下。

**例子**:

- `&'a mut T` 对 `'a` 和 `T` 都是不变的。
- `Cell<T>`, `RefCell<T>` 等内部可变性类型，对 `T` 都是不变的。

#### 4.1. `&mut T` 为何必须是不变的？

这是理解型变必要性的核心。让我们通过一个例子来证明，如果 `&'a mut T` 是协变的，将会导致类型系统崩溃。

假设我们有两个不同的动物类型：

```rust
struct Animal;
struct Dog;
impl From<Dog> for Animal { fn from(_: Dog) -> Self { Animal } }
```

现在，如果 `&mut T` 是协变的，那么 `&mut Dog` 将是 `&mut Animal` 的子类型。这意味着我们可以将 `&mut Dog` 赋值给一个 `&mut Animal` 类型的变量。

```rust
struct Cat;
impl From<Cat> for Animal { fn from(_: Cat) -> Self { Animal } }

fn evil_covariance() {
    let mut dog = Dog;
    let mut animal_ref: &mut Animal = &mut dog; // 步骤 1: 初始赋值

    // 如果 &mut T 是协变的，那么下面的操作将是合法的：
    // let mut cat = Cat;
    // animal_ref = &mut cat; // 步骤 2: 将一个 &mut Cat 赋给 &mut Animal
                             // 这是协变的核心：子类型可以替代父类型。
    
    // 如果步骤 2 成功，`animal_ref` 现在指向一个 `Cat`。
    // 但是，`dog` 变量的类型仍然是 `Dog`！
    // 我们通过一个类型为 `&mut Animal` 的引用，将一个 `Cat` 写入了一个 `Dog` 类型的位置。
    // 类型系统被破坏了。
}
```

类似地，如果 `&mut T` 是逆变的，也会产生问题。因此，为了同时保证读写的类型安全，`&mut T` 必须是不变的。

### 5. 型变的推导与 `PhantomData`

#### 5.1. 编译器如何推导型变

编译器会检查一个泛型参数 `T` 在结构体的字段中是如何被使用的，来自动推导该结构体对于 `T` 的型变。

- 如果 `T` 只出现在协变的位置（如 `&T`, `Box<T>`），则结构体对 `T` 是协变的。
- 如果 `T` 只出现在逆变的位置（如 `fn(T)`），则结构体对 `T` 是逆变的。
- 如果 `T` 同时出现在协变和逆变位置，或者出现在不变的位置（如 `&mut T`），则结构体对 `T` 是不变的。

#### 5.2. 使用 `PhantomData` 影响型变

有时我们的结构体在逻辑上与某个泛型参数 `T` 有关，但 `T` 并未出现在任何字段中（例如，实现 FFI 时）。这时，我们可以使用 `std::marker::PhantomData<T>` 来“告诉”编译器型变规则。

`PhantomData<T>` 是一个零大小的类型，它本身对 `T` 是协变的。

```rust
use std::marker::PhantomData;

// 这个结构体对 T 是协变的
struct MyCovariant<T> {
    _marker: PhantomData<T>,
}

// 这个结构体对 T 是逆变的
// 因为 fn(T) 对 T 是逆变的
struct MyContravariant<T> {
    _marker: PhantomData<fn(T)>,
}

// 这个结构体对 T 是不变的
// 因为 &mut T 对 T 是不变的
struct MyInvariant<T> {
    _marker: PhantomData<&'static mut T>,
}
```

### 6. 哲学批判性分析

#### 6.1. 安全的必要复杂性

型变是 Rust 中最微妙、最理论化的概念之一。它的存在不是为了理论上的优雅，而是出于对内存安全的绝对承诺。协变、逆变，尤其是不变性的规则，共同构成了一道静态的、在编译时强制执行的防线，从根本上消除了其他系统语言中常见的、因不当的引用赋值而导致的悬垂指针和类型混淆问题。

这种复杂性是 Rust 为其核心价值——“无畏并发”和内存安全——所付出的“必要代价”。

#### 6.2. 与其他语言的对比

- **Java**: Java 的泛型是不变的 (`List<String>` 不是 `List<Object>` 的子类型)。它通过有界通配符 (`? extends T`, `? super T`) 来在需要时引入协变和逆变，这是一种更显式、更局部的控制方式。
- **C#**: C# 的泛型支持在接口和委托上声明协变 (`out T`) 和逆变 (`in T`)。
- **C++**: C++ 的模板是鸭子类型的，不直接涉及型变。其指针和引用的规则允许许多不安全的操作，型变规则需要程序员自己来保证。

Rust 的型变系统是自动推导的，全局性的，且与所有权和生命周期系统深度集成，这在主流语言中是独一无二的。

### 7. 总结

型变是 Rust 类型系统中的一个重要概念，它描述了当类型参数之间存在子类型关系时，包含这些参数的泛型类型之间会形成什么样的子类型关系。
