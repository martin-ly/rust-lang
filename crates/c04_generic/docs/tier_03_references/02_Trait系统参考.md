# C04 泛型编程 - Trait 系统完整参考

**文档类型**: Tier 3 完整参考  
**最后更新**: 2025-10-22  
**Rust 版本**: 1.90+  
**参考类型**: 🔍 API 速查

---

## 📋 目录

- [C04 泛型编程 - Trait 系统完整参考](#c04-泛型编程---trait-系统完整参考)
  - [📋 目录](#-目录)
  - [1. Trait 定义语法](#1-trait-定义语法)
    - [1.1 完整 BNF 语法](#11-完整-bnf-语法)
    - [1.2 基础定义](#12-基础定义)
    - [1.3 完整示例](#13-完整示例)
  - [2. Trait 实现语法](#2-trait-实现语法)
    - [2.1 基础实现](#21-基础实现)
    - [2.2 关联类型实现](#22-关联类型实现)
  - [3. 标准库核心 Trait](#3-标准库核心-trait)
    - [3.1 常用 Trait 参考](#31-常用-trait-参考)
    - [3.2 Clone Trait](#32-clone-trait)
    - [3.3 Display 和 Debug](#33-display-和-debug)
    - [3.4 Default Trait](#34-default-trait)
    - [3.5 PartialEq 和 Eq](#35-partialeq-和-eq)
    - [3.6 PartialOrd 和 Ord](#36-partialord-和-ord)
    - [3.7 From 和 Into](#37-from-和-into)
    - [3.8 Iterator Trait](#38-iterator-trait)
  - [4. 对象安全性规则](#4-对象安全性规则)
    - [4.1 对象安全的定义](#41-对象安全的定义)
    - [4.2 对象安全的 Trait](#42-对象安全的-trait)
    - [4.3 不对象安全的 Trait](#43-不对象安全的-trait)
    - [4.4 解决方案](#44-解决方案)
  - [5. Blanket Implementation](#5-blanket-implementation)
    - [5.1 定义](#51-定义)
    - [5.2 常见模式](#52-常见模式)
  - [6. 孤儿规则详解](#6-孤儿规则详解)
    - [6.1 规则定义](#61-规则定义)
    - [6.2 允许的实现](#62-允许的实现)
    - [6.3 不允许的实现](#63-不允许的实现)
    - [6.4 新类型模式绕过](#64-新类型模式绕过)
  - [7. Trait 速查表](#7-trait-速查表)
    - [7.1 派生宏速查](#71-派生宏速查)
    - [7.2 Trait 关系图](#72-trait-关系图)
  - [📚 相关参考](#-相关参考)

---

## 1. Trait 定义语法

### 1.1 完整 BNF 语法

```bnf
Trait ::= 'unsafe'? 'trait' Ident GenericParams? (':' TypeParamBounds?)? WhereClause? '{' InnerAttribute* AssociatedItem* '}'

AssociatedItem ::= OuterAttribute* (TypeAlias | ConstantItem | Function | MacroInvocationSemi)
```

### 1.2 基础定义

```rust
// 最简单的 trait
trait MyTrait {
    fn method(&self);
}

// 带默认实现
trait Logger {
    fn log(&self, message: &str) {
        println!("[LOG] {}", message);
    }
}

// 带关联类型
trait Container {
    type Item;
    fn get(&self, index: usize) -> Option<&Self::Item>;
}

// 带关联常量
trait Numeric {
    const MAX: Self;
    const MIN: Self;
}

// 带泛型参数
trait From<T> {
    fn from(value: T) -> Self;
}
```

### 1.3 完整示例

```rust
trait Processor<Input, Output = Input>
where
    Input: Clone,
    Output: Default,
{
    type Error: std::error::Error;
    const VERSION: u32 = 1;
    
    fn process(&self, input: Input) -> Result<Output, Self::Error>;
    
    fn batch_process(&self, inputs: Vec<Input>) -> Vec<Result<Output, Self::Error>> {
        inputs.into_iter()
            .map(|input| self.process(input))
            .collect()
    }
}
```

---

## 2. Trait 实现语法

### 2.1 基础实现

```bnf
Implementation ::= 'unsafe'? 'impl' GenericParams? Trait 'for' Type WhereClause? '{' InnerAttribute* AssociatedItem* '}'
```

**示例**:

```rust
trait Greet {
    fn greet(&self) -> String;
}

struct Person {
    name: String,
}

impl Greet for Person {
    fn greet(&self) -> String {
        format!("Hello, I'm {}", self.name)
    }
}

// 泛型实现
impl<T: Display> Greet for Option<T> {
    fn greet(&self) -> String {
        match self {
            Some(value) => format!("Hello from {}", value),
            None => String::from("Hello from nowhere"),
        }
    }
}
```

### 2.2 关联类型实现

```rust
trait Iterator {
    type Item;
    fn next(&mut self) -> Option<Self::Item>;
}

struct Counter {
    count: u32,
}

impl Iterator for Counter {
    type Item = u32;
    
    fn next(&mut self) -> Option<u32> {
        self.count += 1;
        Some(self.count)
    }
}
```

---

## 3. 标准库核心 Trait

### 3.1 常用 Trait 参考

| Trait | 用途 | 方法 | 示例 |
|-------|------|------|------|
| `Clone` | 值复制 | `clone(&self) -> Self` | `x.clone()` |
| `Copy` | 位复制 (标记 trait) | 无 | 自动复制 |
| `Debug` | 调试输出 | `fmt(&self, f: &mut Formatter)` | `{:?}` |
| `Display` | 用户输出 | `fmt(&self, f: &mut Formatter)` | `{}` |
| `Default` | 默认值 | `default() -> Self` | `T::default()` |
| `PartialEq` | 相等比较 | `eq(&self, other: &Self) -> bool` | `==`, `!=` |
| `Eq` | 全等 (标记 trait) | 无 | 继承 `PartialEq` |
| `PartialOrd` | 部分排序 | `partial_cmp(&self, other: &Self)` | `<`, `>` |
| `Ord` | 全排序 | `cmp(&self, other: &Self)` | `cmp()` |
| `Hash` | 哈希 | `hash(&self, state: &mut H)` | `HashMap` 键 |

### 3.2 Clone Trait

```rust
pub trait Clone: Sized {
    fn clone(&self) -> Self;
    
    fn clone_from(&mut self, source: &Self) {
        *self = source.clone()
    }
}

// 实现示例
#[derive(Clone)]
struct Point {
    x: i32,
    y: i32,
}

// 手动实现
impl Clone for Point {
    fn clone(&self) -> Self {
        Point {
            x: self.x,
            y: self.y,
        }
    }
}
```

### 3.3 Display 和 Debug

```rust
use std::fmt;

pub trait Debug {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result;
}

pub trait Display {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result;
}

// 实现示例
struct Person {
    name: String,
    age: u32,
}

impl fmt::Debug for Person {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Person")
            .field("name", &self.name)
            .field("age", &self.age)
            .finish()
    }
}

impl fmt::Display for Person {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} ({})", self.name, self.age)
    }
}
```

### 3.4 Default Trait

```rust
pub trait Default: Sized {
    fn default() -> Self;
}

// 实现示例
struct Config {
    host: String,
    port: u16,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            host: String::from("localhost"),
            port: 8080,
        }
    }
}

// 使用
let config = Config::default();
```

### 3.5 PartialEq 和 Eq

```rust
pub trait PartialEq<Rhs = Self>
where
    Rhs: ?Sized,
{
    fn eq(&self, other: &Rhs) -> bool;
    
    fn ne(&self, other: &Rhs) -> bool {
        !self.eq(other)
    }
}

pub trait Eq: PartialEq<Self> {}

// 实现示例
struct Point {
    x: i32,
    y: i32,
}

impl PartialEq for Point {
    fn eq(&self, other: &Self) -> bool {
        self.x == other.x && self.y == other.y
    }
}

impl Eq for Point {}
```

### 3.6 PartialOrd 和 Ord

```rust
pub trait PartialOrd<Rhs = Self>: PartialEq<Rhs>
where
    Rhs: ?Sized,
{
    fn partial_cmp(&self, other: &Rhs) -> Option<Ordering>;
    
    fn lt(&self, other: &Rhs) -> bool { /* ... */ }
    fn le(&self, other: &Rhs) -> bool { /* ... */ }
    fn gt(&self, other: &Rhs) -> bool { /* ... */ }
    fn ge(&self, other: &Rhs) -> bool { /* ... */ }
}

pub trait Ord: Eq + PartialOrd<Self> {
    fn cmp(&self, other: &Self) -> Ordering;
    
    fn max(self, other: Self) -> Self where Self: Sized { /* ... */ }
    fn min(self, other: Self) -> Self where Self: Sized { /* ... */ }
    fn clamp(self, min: Self, max: Self) -> Self where Self: Sized { /* ... */ }
}

// 实现示例
impl PartialOrd for Point {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Point {
    fn cmp(&self, other: &Self) -> Ordering {
        self.x.cmp(&other.x)
            .then(self.y.cmp(&other.y))
    }
}
```

### 3.7 From 和 Into

```rust
pub trait From<T>: Sized {
    fn from(value: T) -> Self;
}

pub trait Into<T>: Sized {
    fn into(self) -> T;
}

// From 自动提供 Into
impl<T, U> Into<U> for T
where
    U: From<T>,
{
    fn into(self) -> U {
        U::from(self)
    }
}

// 实现示例
impl From<i32> for String {
    fn from(value: i32) -> String {
        value.to_string()
    }
}

let s: String = 42.into(); // 使用 Into
let s = String::from(42);  // 使用 From
```

### 3.8 Iterator Trait

```rust
pub trait Iterator {
    type Item;
    
    fn next(&mut self) -> Option<Self::Item>;
    
    // 提供的方法
    fn size_hint(&self) -> (usize, Option<usize>) { (0, None) }
    fn count(self) -> usize where Self: Sized { /* ... */ }
    fn last(self) -> Option<Self::Item> where Self: Sized { /* ... */ }
    fn nth(&mut self, n: usize) -> Option<Self::Item> { /* ... */ }
    fn collect<B: FromIterator<Self::Item>>(self) -> B where Self: Sized { /* ... */ }
    fn map<B, F>(self, f: F) -> Map<Self, F> where Self: Sized, F: FnMut(Self::Item) -> B { /* ... */ }
    fn filter<P>(self, predicate: P) -> Filter<Self, P> where Self: Sized, P: FnMut(&Self::Item) -> bool { /* ... */ }
    // ... 更多方法
}

// 实现示例
struct Counter {
    current: u32,
    max: u32,
}

impl Iterator for Counter {
    type Item = u32;
    
    fn next(&mut self) -> Option<u32> {
        if self.current < self.max {
            self.current += 1;
            Some(self.current - 1)
        } else {
            None
        }
    }
}
```

---

## 4. 对象安全性规则

### 4.1 对象安全的定义

一个 trait 是对象安全的当且仅当：

1. **不要求 `Self: Sized`**
2. **所有方法都是对象安全的**

方法是对象安全的当且仅当：

- 没有泛型类型参数
- 不返回 `Self`
- 不使用 `self` 的值 (除了 `&self` 或 `&mut self`)

### 4.2 对象安全的 Trait

```rust
// ✅ 对象安全
trait Draw {
    fn draw(&self);
    fn area(&self) -> f64;
}

let shapes: Vec<Box<dyn Draw>> = vec![
    Box::new(Circle { radius: 5.0 }),
    Box::new(Rectangle { width: 10.0, height: 5.0 }),
];
```

### 4.3 不对象安全的 Trait

```rust
// ❌ 不对象安全：返回 Self
trait Cloneable {
    fn clone(&self) -> Self;
}

// ❌ 不对象安全：泛型方法
trait Container {
    fn add<T>(&mut self, item: T);
}

// ❌ 不对象安全：Self: Sized 约束
trait Sized {
    fn size() -> usize where Self: Sized;
}
```

### 4.4 解决方案

```rust
// 解决方案 1: 使用关联类型
trait Cloneable {
    fn clone_box(&self) -> Box<dyn Cloneable>;
}

// 解决方案 2: where Self: Sized
trait Printable {
    fn print(&self);
    fn clone(&self) -> Self where Self: Sized;
}
```

---

## 5. Blanket Implementation

### 5.1 定义

为所有满足特定条件的类型实现 trait。

```rust
// 标准库示例
impl<T: Display> ToString for T {
    fn to_string(&self) -> String {
        format!("{}", self)
    }
}

// 所有实现 Display 的类型自动获得 ToString
```

### 5.2 常见模式

```rust
// 模式 1: 基于已有 trait 实现新 trait
trait MyDisplay {
    fn my_display(&self) -> String;
}

impl<T: std::fmt::Display> MyDisplay for T {
    fn my_display(&self) -> String {
        format!("My: {}", self)
    }
}

// 模式 2: 为引用实现
trait Greet {
    fn greet(&self) -> String;
}

impl<T: Greet> Greet for &T {
    fn greet(&self) -> String {
        (**self).greet()
    }
}

// 模式 3: 为 Option 实现
trait Process {
    fn process(&self) -> String;
}

impl<T: Process> Process for Option<T> {
    fn process(&self) -> String {
        match self {
            Some(value) => value.process(),
            None => String::from("None"),
        }
    }
}
```

---

## 6. 孤儿规则详解

### 6.1 规则定义

只能在以下情况实现 trait：

- trait 在当前 crate 中定义，或
- 类型在当前 crate 中定义

### 6.2 允许的实现

```rust
// ✅ 自定义 trait + 自定义类型
trait MyTrait {}
struct MyType;
impl MyTrait for MyType {}

// ✅ 自定义 trait + 外部类型
trait MyTrait {}
impl MyTrait for Vec<i32> {}

// ✅ 外部 trait + 自定义类型
impl Display for MyType {}
```

### 6.3 不允许的实现

```rust
// ❌ 外部 trait + 外部类型
impl Display for Vec<i32> {}  // 编译错误
```

### 6.4 新类型模式绕过

```rust
// ✅ 使用新类型模式
struct MyVec(Vec<i32>);

impl Display for MyVec {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

// 实现 Deref 以便使用 Vec 的方法
impl Deref for MyVec {
    type Target = Vec<i32>;
    
    fn deref(&self) -> &Vec<i32> {
        &self.0
    }
}
```

---

## 7. Trait 速查表

### 7.1 派生宏速查

| Derive | 要求 | 用途 |
|--------|------|------|
| `Clone` | 所有字段实现 `Clone` | 值复制 |
| `Copy` | 所有字段实现 `Copy` | 位复制 |
| `Debug` | 所有字段实现 `Debug` | 调试输出 |
| `Default` | 所有字段实现 `Default` | 默认值 |
| `PartialEq` | 所有字段实现 `PartialEq` | 相等比较 |
| `Eq` | 实现 `PartialEq` | 全等 |
| `PartialOrd` | 实现 `PartialEq` | 部分排序 |
| `Ord` | 实现 `PartialOrd` + `Eq` | 全排序 |
| `Hash` | 所有字段实现 `Hash` | 哈希 |

### 7.2 Trait 关系图

```text
Clone
Copy: Clone
Debug
Display

PartialEq
Eq: PartialEq
PartialOrd: PartialEq
Ord: Eq + PartialOrd

Hash

Default

Iterator
  ├─ IntoIterator
  └─ FromIterator

From<T>
Into<T>: From  (自动实现)

AsRef<T>
AsMut<T>
```

---

## 📚 相关参考

- [01_泛型语法参考.md](./01_泛型语法参考.md) - 泛型语法
- [03_边界约束参考.md](./03_边界约束参考.md) - 约束语法
- [../tier_02_guides/02_Trait系统指南.md](../tier_02_guides/02_Trait系统指南.md) - Trait 实践指南

---

**文档元信息**:

- 创建日期: 2025-10-22
- 作者: Rust-Lang Project
- 许可: MIT OR Apache-2.0
- Rust 版本: 1.90+
