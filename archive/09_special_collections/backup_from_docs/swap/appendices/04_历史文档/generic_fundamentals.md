# 泛型编程基础

> **文档定位**: 系统介绍Rust泛型编程的核心概念和基础知识，适合初学者系统学习  
> **先修知识**: Rust基础语法  
> **相关文档**: [实践指南](./PRACTICAL_GENERICS_GUIDE.md) | [主题系列](./01_introduction_to_generics.md) | [主索引](./00_MASTER_INDEX.md)

**最后更新**: 2025-10-19  
**适用版本**: Rust 1.0+  
**难度等级**: ⭐⭐

---

## 📋 本文内容

本文档介绍 Rust 中泛型编程的核心概念，包括类型参数、特征约束、关联类型等。

---

## 目录

- [泛型编程基础](#泛型编程基础)
  - [📋 本文内容](#-本文内容)
  - [目录](#目录)
  - [泛型概述](#泛型概述)
    - [为什么需要泛型？](#为什么需要泛型)
  - [泛型函数](#泛型函数)
    - [基本语法](#基本语法)
    - [多个类型参数](#多个类型参数)
    - [泛型函数与类型推断](#泛型函数与类型推断)
  - [泛型结构体](#泛型结构体)
    - [1基本语法](#1基本语法)
    - [1多个类型参数](#1多个类型参数)
    - [特化实现](#特化实现)
  - [泛型枚举](#泛型枚举)
    - [Option 枚举](#option-枚举)
    - [Result 枚举](#result-枚举)
  - [泛型方法](#泛型方法)
    - [基本泛型方法](#基本泛型方法)
    - [带约束的泛型方法](#带约束的泛型方法)
  - [特征约束](#特征约束)
    - [基本特征约束](#基本特征约束)
    - [多个特征约束](#多个特征约束)
    - [where 子句](#where-子句)
    - [特征对象](#特征对象)
  - [关联类型](#关联类型)
    - [基本关联类型](#基本关联类型)
    - [关联类型 vs 泛型](#关联类型-vs-泛型)
  - [生命周期与泛型](#生命周期与泛型)
    - [生命周期参数](#生命周期参数)
    - [结构体中的生命周期](#结构体中的生命周期)
    - [生命周期省略](#生命周期省略)
  - [高级泛型概念](#高级泛型概念)
    - [泛型特化](#泛型特化)
    - [泛型与闭包](#泛型与闭包)
  - [性能考虑](#性能考虑)
    - [单态化](#单态化)
    - [零成本抽象](#零成本抽象)
  - [最佳实践](#最佳实践)
  - [相关主题](#相关主题)

## 泛型概述

泛型允许我们编写可以处理多种数据类型的代码，而不需要为每种类型重复编写相同的逻辑。

### 为什么需要泛型？

```rust
// 不使用泛型：需要为每种类型编写重复的函数
fn largest_i32(list: &[i32]) -> i32 {
    let mut largest = list[0];
    for &item in list {
        if item > largest {
            largest = item;
        }
    }
    largest
}

fn largest_char(list: &[char]) -> char {
    let mut largest = list[0];
    for &item in list {
        if item > largest {
            largest = item;
        }
    }
    largest
}

// 使用泛型：一个函数处理多种类型
fn largest<T: PartialOrd + Copy>(list: &[T]) -> T {
    let mut largest = list[0];
    for &item in list {
        if item > largest {
            largest = item;
        }
    }
    largest
}
```

## 泛型函数

### 基本语法

```rust
fn identity<T>(x: T) -> T {
    x
}

fn main() {
    let integer = identity(5);
    let float = identity(3.14);
    let string = identity("hello");
    
    println!("{}, {}, {}", integer, float, string);
}
```

### 多个类型参数

```rust
fn swap<T, U>(x: T, y: U) -> (U, T) {
    (y, x)
}

fn main() {
    let pair = swap(5, "hello");
    println!("{:?}", pair);  // ("hello", 5)
}
```

### 泛型函数与类型推断

```rust
fn print_type<T>(_x: T) {
    println!("Type: {}", std::any::type_name::<T>());
}

fn main() {
    print_type(42);        // Type: i32
    print_type(3.14);      // Type: f64
    print_type("hello");   // Type: &str
}
```

## 泛型结构体

### 1基本语法

```rust
struct Point<T> {
    x: T,
    y: T,
}

impl<T> Point<T> {
    fn new(x: T, y: T) -> Point<T> {
        Point { x, y }
    }
    
    fn x(&self) -> &T {
        &self.x
    }
    
    fn y(&self) -> &T {
        &self.y
    }
}

fn main() {
    let integer_point = Point::new(5, 10);
    let float_point = Point::new(1.0, 4.0);
    
    println!("Integer point: ({}, {})", integer_point.x(), integer_point.y());
    println!("Float point: ({}, {})", float_point.x(), float_point.y());
}
```

### 1多个类型参数

```rust
struct Point<T, U> {
    x: T,
    y: U,
}

impl<T, U> Point<T, U> {
    fn mixup<V, W>(self, other: Point<V, W>) -> Point<T, W> {
        Point {
            x: self.x,
            y: other.y,
        }
    }
}

fn main() {
    let p1 = Point { x: 5, y: 10.4 };
    let p2 = Point { x: "Hello", y: 'c' };
    
    let p3 = p1.mixup(p2);
    println!("p3.x = {}, p3.y = {}", p3.x, p3.y);
}
```

### 特化实现

```rust
struct Point<T> {
    x: T,
    y: T,
}

impl<T> Point<T> {
    fn new(x: T, y: T) -> Point<T> {
        Point { x, y }
    }
}

// 只为 f32 类型提供特殊实现
impl Point<f32> {
    fn distance_from_origin(&self) -> f32 {
        (self.x.powi(2) + self.y.powi(2)).sqrt()
    }
}

fn main() {
    let p1 = Point::new(5, 10);
    // p1.distance_from_origin();  // 错误！i32 没有这个方法
    
    let p2 = Point::new(3.0, 4.0);
    println!("Distance: {}", p2.distance_from_origin());  // 5.0
}
```

## 泛型枚举

### Option 枚举

```rust
enum Option<T> {
    Some(T),
    None,
}

fn main() {
    let some_number = Some(5);
    let some_string = Some("hello");
    let absent_number: Option<i32> = None;
    
    match some_number {
        Some(value) => println!("Got: {}", value),
        None => println!("No value"),
    }
}
```

### Result 枚举

```rust
enum Result<T, E> {
    Ok(T),
    Err(E),
}

fn divide(a: i32, b: i32) -> Result<i32, String> {
    if b == 0 {
        Err("Division by zero".to_string())
    } else {
        Ok(a / b)
    }
}

fn main() {
    match divide(10, 2) {
        Ok(result) => println!("Result: {}", result),
        Err(error) => println!("Error: {}", error),
    }
}
```

## 泛型方法

### 基本泛型方法

```rust
struct Container<T> {
    value: T,
}

impl<T> Container<T> {
    fn new(value: T) -> Container<T> {
        Container { value }
    }
    
    fn get(&self) -> &T {
        &self.value
    }
    
    fn set(&mut self, value: T) {
        self.value = value;
    }
}

fn main() {
    let mut container = Container::new(42);
    println!("Value: {}", container.get());
    
    container.set(100);
    println!("New value: {}", container.get());
}
```

### 带约束的泛型方法

```rust
use std::fmt::Display;

struct Pair<T> {
    x: T,
    y: T,
}

impl<T> Pair<T> {
    fn new(x: T, y: T) -> Pair<T> {
        Pair { x, y }
    }
}

impl<T: Display + PartialOrd> Pair<T> {
    fn cmp_display(&self) {
        if self.x >= self.y {
            println!("The largest member is x = {}", self.x);
        } else {
            println!("The largest member is y = {}", self.y);
        }
    }
}

fn main() {
    let pair = Pair::new(5, 10);
    pair.cmp_display();
}
```

## 特征约束

### 基本特征约束

```rust
use std::fmt::Display;

fn print_generic<T: Display>(item: T) {
    println!("{}", item);
}

fn main() {
    print_generic(42);
    print_generic("hello");
    print_generic(3.14);
}
```

### 多个特征约束

```rust
use std::fmt::Display;
use std::fmt::Debug;

fn print_and_debug<T: Display + Debug>(item: T) {
    println!("Display: {}", item);
    println!("Debug: {:?}", item);
}

fn main() {
    print_and_debug(42);
}
```

### where 子句

```rust
use std::fmt::Display;
use std::fmt::Debug;

fn complex_function<T, U>(t: T, u: U) -> i32
where
    T: Display + Clone,
    U: Clone + Debug,
{
    println!("t: {}", t);
    println!("u: {:?}", u);
    42
}

fn main() {
    let result = complex_function("hello", vec![1, 2, 3]);
    println!("Result: {}", result);
}
```

### 特征对象

```rust
trait Drawable {
    fn draw(&self);
}

struct Circle {
    radius: f64,
}

impl Drawable for Circle {
    fn draw(&self) {
        println!("Drawing a circle with radius {}", self.radius);
    }
}

struct Rectangle {
    width: f64,
    height: f64,
}

impl Drawable for Rectangle {
    fn draw(&self) {
        println!("Drawing a rectangle {}x{}", self.width, self.height);
    }
}

fn draw_all(shapes: &[Box<dyn Drawable>]) {
    for shape in shapes {
        shape.draw();
    }
}

fn main() {
    let shapes: Vec<Box<dyn Drawable>> = vec![
        Box::new(Circle { radius: 5.0 }),
        Box::new(Rectangle { width: 10.0, height: 20.0 }),
    ];
    
    draw_all(&shapes);
}
```

## 关联类型

### 基本关联类型

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
    
    fn next(&mut self) -> Option<Self::Item> {
        if self.count < 5 {
            self.count += 1;
            Some(self.count)
        } else {
            None
        }
    }
}

fn main() {
    let mut counter = Counter { count: 0 };
    while let Some(value) = counter.next() {
        println!("{}", value);
    }
}
```

### 关联类型 vs 泛型

```rust
// 使用关联类型
trait Add {
    type Output;
    fn add(self, other: Self) -> Self::Output;
}

impl Add for i32 {
    type Output = i32;
    fn add(self, other: Self) -> Self::Output {
        self + other
    }
}

// 使用泛型
trait AddGeneric<RHS = Self> {
    type Output;
    fn add(self, rhs: RHS) -> Self::Output;
}

impl AddGeneric<i32> for i32 {
    type Output = i32;
    fn add(self, rhs: i32) -> Self::Output {
        self + rhs
    }
}

impl AddGeneric<String> for i32 {
    type Output = String;
    fn add(self, rhs: String) -> Self::Output {
        format!("{}{}", self, rhs)
    }
}
```

## 生命周期与泛型

### 生命周期参数

```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}

fn main() {
    let string1 = String::from("abcd");
    let string2 = "xyz";
    
    let result = longest(string1.as_str(), string2);
    println!("The longest string is {}", result);
}
```

### 结构体中的生命周期

```rust
struct ImportantExcerpt<'a> {
    part: &'a str,
}

impl<'a> ImportantExcerpt<'a> {
    fn level(&self) -> i32 {
        3
    }
    
    fn announce_and_return_part(&self, announcement: &str) -> &str {
        println!("Attention please: {}", announcement);
        self.part
    }
}

fn main() {
    let novel = String::from("Call me Ishmael. Some years ago...");
    let first_sentence = novel.split('.').next().expect("Could not find a '.'");
    let i = ImportantExcerpt {
        part: first_sentence,
    };
    
    println!("Level: {}", i.level());
    println!("Part: {}", i.announce_and_return_part("Hello"));
}
```

### 生命周期省略

```rust
// 编译器可以推断生命周期
fn first_word(s: &str) -> &str {
    let bytes = s.as_bytes();
    
    for (i, &item) in bytes.iter().enumerate() {
        if item == b' ' {
            return &s[0..i];
        }
    }
    
    &s[..]
}

fn main() {
    let my_string = String::from("hello world");
    let word = first_word(&my_string);
    println!("First word: {}", word);
}
```

## 高级泛型概念

### 泛型特化

```rust
trait Default {
    fn default() -> Self;
}

impl Default for i32 {
    fn default() -> Self {
        0
    }
}

impl Default for String {
    fn default() -> Self {
        String::new()
    }
}

fn create_default<T: Default>() -> T {
    T::default()
}

fn main() {
    let int_default: i32 = create_default();
    let string_default: String = create_default();
    
    println!("Default int: {}", int_default);
    println!("Default string: '{}'", string_default);
}
```

### 泛型与闭包

```rust
fn apply_twice<F, T>(f: F, x: T) -> T
where
    F: Fn(T) -> T,
{
    f(f(x))
}

fn main() {
    let add_one = |x: i32| x + 1;
    let result = apply_twice(add_one, 5);
    println!("Result: {}", result);  // 7
}
```

## 性能考虑

### 单态化

```rust
// 编译时，泛型函数会被单态化
fn generic_function<T>(x: T) -> T {
    x
}

// 编译器会生成类似这样的代码：
// fn generic_function_i32(x: i32) -> i32 { x }
// fn generic_function_f64(x: f64) -> f64 { x }
// fn generic_function_string(x: String) -> String { x }

fn main() {
    let int_result = generic_function(42);
    let float_result = generic_function(3.14);
    let string_result = generic_function(String::from("hello"));
    
    println!("{}, {}, {}", int_result, float_result, string_result);
}
```

### 零成本抽象

```rust
// 泛型不会带来运行时开销
fn process_items<T>(items: &[T]) -> usize
where
    T: Clone,
{
    items.len()
}

fn main() {
    let numbers = vec![1, 2, 3, 4, 5];
    let strings = vec!["a", "b", "c"];
    
    println!("Numbers: {}", process_items(&numbers));
    println!("Strings: {}", process_items(&strings));
}
```

## 最佳实践

1. **使用描述性的类型参数名**：`T`、`U`、`V` 对于简单情况，更复杂的用描述性名称
2. **合理使用特征约束**：只添加必要的约束
3. **优先使用关联类型而不是泛型**：当类型参数不需要变化时
4. **利用生命周期省略**：让编译器推断生命周期
5. **考虑性能影响**：泛型在编译时单态化，没有运行时开销

## 相关主题

- [高级泛型特性](./advanced_generics.md)
- [特征系统详解](./trait_system.md)
- [生命周期深入](./lifetimes.md)
- [类型系统理论](./type_theory.md)
