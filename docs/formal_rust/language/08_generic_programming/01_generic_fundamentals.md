# Rust 泛型编程基础理论

**文档编号**: 08.01  
**版本**: 1.0  
**创建日期**: 2025-01-27  

## 目录

1. [泛型编程概述](#1-泛型编程概述)
2. [泛型类型系统](#2-泛型类型系统)
3. [泛型约束与边界](#3-泛型约束与边界)
4. [泛型实现模式](#4-泛型实现模式)
5. [工程实践案例](#5-工程实践案例)

---

## 1. 泛型编程概述

### 1.1 核心概念

泛型编程允许编写可重用的代码，通过类型参数实现类型安全的抽象。

```rust
// 泛型函数示例
fn identity<T>(x: T) -> T {
    x
}

// 泛型结构体示例
struct Container<T> {
    value: T,
}

// 泛型枚举示例
enum Result<T, E> {
    Ok(T),
    Err(E),
}
```

### 1.2 理论基础

泛型编程基于以下理论：

- **多态理论**：参数多态和特设多态
- **类型理论**：类型参数化和类型推断
- **模板理论**：代码生成和实例化
- **约束理论**：类型约束和边界

---

## 2. 泛型类型系统

### 2.1 类型参数

```rust
// 单类型参数
struct Point<T> {
    x: T,
    y: T,
}

// 多类型参数
struct Pair<T, U> {
    first: T,
    second: U,
}

// 生命周期参数
struct Ref<'a, T> {
    value: &'a T,
}

// 常量参数
struct Array<T, const N: usize> {
    data: [T; N],
}
```

### 2.2 泛型函数

```rust
// 泛型函数定义
fn max<T: PartialOrd>(a: T, b: T) -> T {
    if a > b { a } else { b }
}

// 泛型方法
impl<T> Point<T> {
    fn new(x: T, y: T) -> Self {
        Self { x, y }
    }
    
    fn get_x(&self) -> &T {
        &self.x
    }
}

// 泛型关联函数
impl<T> Point<T> {
    fn origin() -> Point<T> 
    where
        T: Default,
    {
        Point {
            x: T::default(),
            y: T::default(),
        }
    }
}
```

---

## 3. 泛型约束与边界

### 3.1 Trait约束

```rust
// 基本trait约束
fn print_debug<T: Debug>(value: T) {
    println!("{:?}", value);
}

// 多个trait约束
fn clone_and_print<T: Clone + Debug>(value: T) {
    let cloned = value.clone();
    println!("{:?}", cloned);
}

// where子句
fn complex_function<T, U>(t: T, u: U) -> T
where
    T: Clone + PartialOrd,
    U: Debug + Clone,
{
    // 函数实现
    t
}
```

### 3.2 生命周期约束

```rust
// 生命周期约束
fn longest<'a, 'b: 'a>(x: &'a str, y: &'b str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}

// 泛型生命周期约束
struct Container<'a, T: 'a> {
    value: &'a T,
}

// 高阶生命周期约束
fn higher_order<'a, F>(f: F) -> impl Fn(&'a i32) -> &'a i32
where
    F: Fn(&'a i32) -> &'a i32,
{
    f
}
```

### 3.3 关联类型约束

```rust
// 关联类型约束
trait Iterator {
    type Item;
    
    fn next(&mut self) -> Option<Self::Item>;
}

// 泛型关联类型
trait Container {
    type Item<T>;
    
    fn get<T>(&self, index: usize) -> Option<&Self::Item<T>>;
}

// 关联类型约束
fn process_iterator<I>(iter: I)
where
    I: Iterator<Item = String>,
{
    for item in iter {
        println!("{}", item);
    }
}
```

---

## 4. 泛型实现模式

### 4.1 泛型实现

```rust
// 泛型trait实现
trait Display {
    fn display(&self);
}

impl<T: Debug> Display for T {
    fn display(&self) {
        println!("{:?}", self);
    }
}

// 条件实现
impl<T> Point<T> {
    fn distance_from_origin(&self) -> f64
    where
        T: Into<f64> + Copy,
    {
        let x: f64 = self.x.into();
        let y: f64 = self.y.into();
        (x * x + y * y).sqrt()
    }
}

// 泛型trait实现
impl<T, U> PartialEq<Point<U>> for Point<T>
where
    T: PartialEq<U>,
{
    fn eq(&self, other: &Point<U>) -> bool {
        self.x == other.x && self.y == other.y
    }
}
```

### 4.2 泛型特化

```rust
// 默认实现
trait Default {
    fn default() -> Self;
}

// 特化实现
impl Default for String {
    fn default() -> Self {
        String::new()
    }
}

impl Default for Vec<T> {
    fn default() -> Self {
        Vec::new()
    }
}

// 条件特化
impl<T> Default for Option<T> {
    fn default() -> Self {
        None
    }
}

impl<T: Default> Default for Option<T> {
    fn default() -> Self {
        Some(T::default())
    }
}
```

---

## 5. 工程实践案例

### 5.1 泛型数据结构

```rust
// 泛型链表
pub struct List<T> {
    head: Option<Box<Node<T>>>,
}

struct Node<T> {
    data: T,
    next: Option<Box<Node<T>>>,
}

impl<T> List<T> {
    pub fn new() -> Self {
        Self { head: None }
    }
    
    pub fn push(&mut self, data: T) {
        let new_node = Box::new(Node {
            data,
            next: self.head.take(),
        });
        self.head = Some(new_node);
    }
    
    pub fn pop(&mut self) -> Option<T> {
        self.head.take().map(|node| {
            self.head = node.next;
            node.data
        })
    }
}

// 泛型迭代器实现
impl<T> Iterator for List<T> {
    type Item = T;
    
    fn next(&mut self) -> Option<Self::Item> {
        self.pop()
    }
}
```

### 5.2 泛型算法

```rust
// 泛型排序算法
pub fn quick_sort<T, F>(arr: &mut [T], compare: F)
where
    T: Clone,
    F: Fn(&T, &T) -> Ordering,
{
    if arr.len() <= 1 {
        return;
    }
    
    let pivot_index = partition(arr, &compare);
    quick_sort(&mut arr[..pivot_index], &compare);
    quick_sort(&mut arr[pivot_index + 1..], &compare);
}

fn partition<T, F>(arr: &mut [T], compare: &F) -> usize
where
    T: Clone,
    F: Fn(&T, &T) -> Ordering,
{
    let pivot = arr[arr.len() - 1].clone();
    let mut i = 0;
    
    for j in 0..arr.len() - 1 {
        if compare(&arr[j], &pivot) == Ordering::Less {
            arr.swap(i, j);
            i += 1;
        }
    }
    
    arr.swap(i, arr.len() - 1);
    i
}

// 使用示例
fn main() {
    let mut numbers = vec![3, 1, 4, 1, 5, 9, 2, 6];
    quick_sort(&mut numbers, |a, b| a.cmp(b));
    println!("{:?}", numbers);
    
    let mut strings = vec!["banana", "apple", "cherry"];
    quick_sort(&mut strings, |a, b| a.cmp(b));
    println!("{:?}", strings);
}
```

### 5.3 泛型序列化

```rust
// 泛型序列化trait
trait Serialize {
    fn serialize(&self) -> String;
}

trait Deserialize: Sized {
    fn deserialize(data: &str) -> Result<Self, String>;
}

// 为基本类型实现序列化
impl Serialize for i32 {
    fn serialize(&self) -> String {
        self.to_string()
    }
}

impl Deserialize for i32 {
    fn deserialize(data: &str) -> Result<Self, String> {
        data.parse().map_err(|e| format!("Parse error: {}", e))
    }
}

// 为泛型容器实现序列化
impl<T: Serialize> Serialize for Vec<T> {
    fn serialize(&self) -> String {
        let items: Vec<String> = self.iter().map(|item| item.serialize()).collect();
        format!("[{}]", items.join(","))
    }
}

impl<T: Deserialize> Deserialize for Vec<T> {
    fn deserialize(data: &str) -> Result<Self, String> {
        let trimmed = data.trim_matches(|c| c == '[' || c == ']');
        if trimmed.is_empty() {
            return Ok(Vec::new());
        }
        
        let items: Result<Vec<T>, _> = trimmed
            .split(',')
            .map(|item| T::deserialize(item.trim()))
            .collect();
        
        items
    }
}
```

---

## 总结

泛型编程是Rust语言的核心特性，提供了类型安全的代码重用机制。通过合理的泛型设计，可以编写既灵活又安全的代码。

### 关键要点

1. **类型参数**：支持类型、生命周期和常量参数
2. **约束系统**：通过trait约束实现类型安全
3. **实现模式**：条件实现和特化机制
4. **工程实践**：泛型数据结构和算法设计

### 学习建议

1. **理解概念**：深入理解泛型的基本概念和原理
2. **实践练习**：通过实际项目掌握泛型编程技巧
3. **设计模式**：学习泛型设计模式和最佳实践
4. **持续学习**：关注泛型编程的最新发展
