# 🔷 Rust 泛型编程速查卡

> **快速参考** | [完整文档](../../crates/c04_generic/docs/) | [代码示例](../../crates/c04_generic/examples/)
> **最后更新**: 2025-11-15 | **Rust 版本**: 1.91.1+ | **Edition**: 2024

---

## 📋 目录

- [🔷 Rust 泛型编程速查卡](#-rust-泛型编程速查卡)
  - [📋 目录](#-目录)
  - [🎯 核心概念](#-核心概念)
    - [泛型函数](#泛型函数)
    - [泛型结构体](#泛型结构体)
    - [泛型枚举](#泛型枚举)
  - [📐 Trait 约束](#-trait-约束)
    - [基本约束](#基本约束)
    - [常见 Trait 约束](#常见-trait-约束)
  - [🔧 高级特性](#-高级特性)
    - [关联类型](#关联类型)
    - [泛型关联类型 (GATs)](#泛型关联类型-gats)
    - [const 泛型](#const-泛型)
  - [🎯 常见模式](#-常见模式)
    - [模式 1: 泛型函数](#模式-1-泛型函数)
    - [模式 2: 泛型方法](#模式-2-泛型方法)
    - [模式 3: 泛型 Trait 实现](#模式-3-泛型-trait-实现)
  - [📚 性能考虑](#-性能考虑)
    - [单态化 (Monomorphization)](#单态化-monomorphization)
  - [🔗 相关资源](#-相关资源)
  - [🆕 Rust 1.91.1 泛型改进](#-rust-1911-泛型改进)
    - [const 上下文增强](#const-上下文增强)

---

## 🎯 核心概念

### 泛型函数

```rust
// 基本泛型函数
fn largest<T: PartialOrd>(list: &[T]) -> &T {
    let mut largest = &list[0];
    for item in list {
        if item > largest {
            largest = item;
        }
    }
    largest
}
```

### 泛型结构体

```rust
struct Point<T> {
    x: T,
    y: T,
}

// 使用
let integer = Point { x: 5, y: 10 };
let float = Point { x: 1.0, y: 4.0 };
```

### 泛型枚举

```rust
enum Option<T> {
    Some(T),
    None,
}

enum Result<T, E> {
    Ok(T),
    Err(E),
}
```

---

## 📐 Trait 约束

### 基本约束

```rust
// 使用 where 子句
fn some_function<T, U>(t: T, u: U) -> i32
where
    T: Display + Clone,
    U: Clone + Debug,
{
    // 函数体
}
```

### 常见 Trait 约束

```rust
// 可比较
fn compare<T: PartialOrd>(a: T, b: T) -> bool {
    a > b
}

// 可克隆
fn duplicate<T: Clone>(item: T) -> (T, T) {
    (item.clone(), item.clone())
}

// 可显示
fn print<T: Display>(item: T) {
    println!("{}", item);
}
```

---

## 🔧 高级特性

### 关联类型

```rust
trait Iterator {
    type Item;  // 关联类型

    fn next(&mut self) -> Option<Self::Item>;
}
```

### 泛型关联类型 (GATs)

```rust
trait StreamingIterator {
    type Item<'a> where Self: 'a;

    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>>;
}
```

### const 泛型

```rust
struct Array<T, const N: usize> {
    data: [T; N],
}

// 使用
let arr: Array<i32, 5> = Array { data: [0; 5] };
```

---

## 🎯 常见模式

### 模式 1: 泛型函数

```rust
fn swap<T>(x: &mut T, y: &mut T) {
    std::mem::swap(x, y);
}
```

### 模式 2: 泛型方法

```rust
impl<T> Point<T> {
    fn x(&self) -> &T {
        &self.x
    }
}

// 特定类型的实现
impl Point<f32> {
    fn distance_from_origin(&self) -> f32 {
        (self.x.powi(2) + self.y.powi(2)).sqrt()
    }
}
```

### 模式 3: 泛型 Trait 实现

```rust
impl<T: Display> ToString for T {
    fn to_string(&self) -> String {
        format!("{}", self)
    }
}
```

---

## 📚 性能考虑

### 单态化 (Monomorphization)

```rust
// 编译时生成具体类型
let integer = largest(&[1, 2, 3]);  // 生成 largest_i32
let float = largest(&[1.0, 2.0]);   // 生成 largest_f64
```

**优势**:

- ✅ 零运行时开销
- ✅ 编译器可以内联优化
- ✅ 类型安全保证

---

## 🔗 相关资源

- [泛型编程完整文档](../../crates/c04_generic/docs/)
- [类型系统速查卡](./type_system.md)
- [Rust 官方文档 - 泛型](https://doc.rust-lang.org/book/ch10-00-generics.html)

---

---

## 🆕 Rust 1.91.1 泛型改进

### const 上下文增强

**改进**: 支持对非静态常量的引用，应用于泛型配置

```rust
// Rust 1.91.1 新特性
const fn get_config<T>() -> T
where
    T: Copy + Default,
{
    T::default()
}

const CONFIG: i32 = get_config::<i32>();
const REF: &i32 = &CONFIG;  // ✅ 现在支持
```

**影响**: 更灵活的泛型 const 函数和编译时配置

---

**最后更新**: 2025-11-15
**Rust 版本**: 1.91.1+ (Edition 2024)
