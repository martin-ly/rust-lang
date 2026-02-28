# 🚀 Rust 快速参考 (Quick Reference)

> **创建日期**: 2026-01-26
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已归档
**最后更新**: 2025-10-19
**适用版本**: Rust 1.90+

---

## 📋 目录

- [🚀 Rust 快速参考 (Quick Reference)](#-rust-快速参考-quick-reference)
  - [📋 目录](#-目录)
  - [基础语法](#基础语法)
    - [变量声明](#变量声明)
    - [数据类型](#数据类型)
  - [所有权与借用](#所有权与借用)
    - [所有权规则](#所有权规则)
    - [借用](#借用)
    - [生命周期](#生命周期)
  - [类型系统](#类型系统)
    - [泛型](#泛型)
    - [Trait](#trait)
  - [控制流](#控制流)
    - [条件表达式](#条件表达式)
    - [模式匹配](#模式匹配)
    - [循环](#循环)
  - [函数与闭包](#函数与闭包)
    - [函数](#函数)
    - [闭包](#闭包)
  - [错误处理](#错误处理)
    - [Result 类型](#result-类型)
    - [Option 类型](#option-类型)
    - [panic](#panic)
  - [并发编程](#并发编程)
    - [线程](#线程)
    - [消息传递](#消息传递)
    - [共享状态](#共享状态)
  - [异步编程](#异步编程)
    - [async/await](#asyncawait)
    - [tokio 基础](#tokio-基础)
  - [常用宏](#常用宏)
    - [打印宏](#打印宏)
    - [调试宏](#调试宏)
    - [其他常用宏](#其他常用宏)
  - [常用 Trait](#常用-trait)
    - [基础 Trait](#基础-trait)
    - [转换 Trait](#转换-trait)
    - [运算符 Trait](#运算符-trait)
    - [迭代器 Trait](#迭代器-trait)
  - [🔗 深入学习](#-深入学习)
    - [按主题查找](#按主题查找)
    - [学习资源](#学习资源)

---

## 基础语法

### 变量声明

```rust
// 不可变变量（默认）
let x = 5;

// 可变变量
let mut y = 10;
y += 5;

// 类型标注
let z: i32 = 20;

// 常量（必须标注类型）
const MAX_POINTS: u32 = 100_000;

// 静态变量
static GLOBAL: i32 = 42;
```

### 数据类型

```rust
// 整数类型
let a: i8 = -128;          // 8位有符号
let b: u8 = 255;           // 8位无符号
let c: i32 = -2147483648;  // 32位有符号（默认）
let d: u64 = 18446744073709551615; // 64位无符号

// 浮点类型
let e: f32 = 3.14;         // 32位浮点
let f: f64 = 2.71828;      // 64位浮点（默认）

// 布尔类型
let g: bool = true;

// 字符类型（Unicode）
let h: char = '🦀';

// 元组
let tup: (i32, f64, char) = (500, 6.4, 'y');
let (x, y, z) = tup;       // 解构

// 数组（固定长度）
let arr: [i32; 5] = [1, 2, 3, 4, 5];
let arr2 = [3; 5];         // [3, 3, 3, 3, 3]
```

---

## 所有权与借用

### 所有权规则

```rust
// 规则1: 每个值都有一个所有者
let s1 = String::from("hello");

// 规则2: 值在任意时刻只能有一个所有者
let s2 = s1;  // s1 失效（Move）
// println!("{}", s1);  // 错误

// 规则3: 当所有者离开作用域，值被丢弃
{
    let s = String::from("temp");
}  // s 被丢弃
```

### 借用

```rust
// 不可变借用
let s = String::from("hello");
let len = calculate_length(&s);  // 借用，不取得所有权

// 可变借用
let mut s = String::from("hello");
change(&mut s);  // 可变借用

// 借用规则：
// 1. 多个不可变引用 OR 一个可变引用
// 2. 引用必须总是有效的
```

### 生命周期

```rust
// 函数中的生命周期
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}

// 结构体中的生命周期
struct ImportantExcerpt<'a> {
    part: &'a str,
}

// 'static 生命周期
let s: &'static str = "I have a static lifetime.";
```

---

## 类型系统

### 泛型

```rust
// 泛型函数
fn largest<T: PartialOrd>(list: &[T]) -> &T {
    let mut largest = &list[0];
    for item in list {
        if item > largest {
            largest = item;
        }
    }
    largest
}

// 泛型结构体
struct Point<T> {
    x: T,
    y: T,
}

// 泛型枚举
enum Option<T> {
    Some(T),
    None,
}

enum Result<T, E> {
    Ok(T),
    Err(E),
}
```

### Trait

```rust
// 定义 Trait
trait Summary {
    fn summarize(&self) -> String;

    // 默认实现
    fn summarize_author(&self) -> String {
        String::from("Unknown")
    }
}

// 实现 Trait
impl Summary for Article {
    fn summarize(&self) -> String {
        format!("{}, by {}", self.headline, self.author)
    }
}

// Trait 作为参数
fn notify(item: &impl Summary) {
    println!("{}", item.summarize());
}

// Trait Bound
fn notify<T: Summary>(item: &T) {
    println!("{}", item.summarize());
}

// 多个 Trait Bound
fn some_function<T: Display + Clone, U: Clone + Debug>(t: &T, u: &U) -> i32 {
    // ...
}

// where 子句
fn some_function<T, U>(t: &T, u: &U) -> i32
where
    T: Display + Clone,
    U: Clone + Debug,
{
    // ...
}
```

---

## 控制流

### 条件表达式

```rust
// if 表达式
let number = 6;
if number % 2 == 0 {
    println!("even");
} else {
    println!("odd");
}

// if 作为表达式
let condition = true;
let number = if condition { 5 } else { 6 };

// if let
if let Some(x) = some_option {
    println!("Got: {}", x);
}

// let-else (Rust 1.65+)
let Some(x) = some_option else {
    return;
};
```

### 模式匹配

```rust
// match 表达式
match value {
    1 => println!("one"),
    2 | 3 => println!("two or three"),
    4..=9 => println!("four to nine"),
    _ => println!("anything"),
}

// 解构
match point {
    Point { x: 0, y } => println!("On y-axis at {}", y),
    Point { x, y: 0 } => println!("On x-axis at {}", x),
    Point { x, y } => println!("At ({}, {})", x, y),
}

// 守卫
match num {
    Some(x) if x < 5 => println!("less than five: {}", x),
    Some(x) => println!("{}", x),
    None => (),
}
```

### 循环

```rust
// loop
loop {
    if condition {
        break;
    }
}

// 带返回值的 loop
let result = loop {
    counter += 1;
    if counter == 10 {
        break counter * 2;
    }
};

// while
while number != 0 {
    number -= 1;
}

// while let
while let Some(value) = stack.pop() {
    println!("{}", value);
}

// for
for item in collection {
    println!("{}", item);
}

// 范围
for number in 1..5 {
    println!("{}", number);
}

// 带标签的循环
'outer: loop {
    loop {
        break 'outer;
    }
}
```

---

## 函数与闭包

### 函数

```rust
// 函数定义
fn add(x: i32, y: i32) -> i32 {
    x + y  // 返回表达式（无分号）
}

// 多返回值（元组）
fn swap(x: i32, y: i32) -> (i32, i32) {
    (y, x)
}

// 发散函数
fn forever() -> ! {
    loop {
        // ...
    }
}
```

### 闭包

```rust
// 闭包语法
let add_one = |x| x + 1;
let add = |x: i32, y: i32| -> i32 { x + y };

// 捕获环境
let x = 4;
let equal_to_x = |z| z == x;  // 捕获 x

// move 闭包
let x = vec![1, 2, 3];
let equal_to_x = move |z| z == x;  // 获取所有权

// Fn trait
fn apply<F: Fn(i32) -> i32>(f: F, x: i32) -> i32 {
    f(x)
}

// 返回闭包
fn make_adder(x: i32) -> impl Fn(i32) -> i32 {
    move |y| x + y
}
```

---

## 错误处理

### Result 类型

```rust
// Result 定义
enum Result<T, E> {
    Ok(T),
    Err(E),
}

// 使用 Result
fn read_file(path: &str) -> Result<String, std::io::Error> {
    std::fs::read_to_string(path)
}

// match 处理
match read_file("file.txt") {
    Ok(content) => println!("{}", content),
    Err(e) => eprintln!("Error: {}", e),
}

// unwrap 和 expect
let content = read_file("file.txt").unwrap();
let content = read_file("file.txt").expect("Failed to read file");

// ? 运算符
fn process() -> Result<String, std::io::Error> {
    let content = std::fs::read_to_string("file.txt")?;
    Ok(content)
}
```

### Option 类型

```rust
// Option 定义
enum Option<T> {
    Some(T),
    None,
}

// 使用 Option
let some_number = Some(5);
let no_number: Option<i32> = None;

// 处理 Option
match some_number {
    Some(x) => println!("{}", x),
    None => println!("no value"),
}

// 常用方法
some_number.unwrap();
some_number.unwrap_or(0);
some_number.unwrap_or_else(|| 0);
some_number.map(|x| x * 2);
some_number.and_then(|x| Some(x * 2));
```

### panic

```rust
// 主动 panic
panic!("crash and burn");

// assert 宏
assert!(condition);
assert_eq!(left, right);
assert_ne!(left, right);
```

---

## 并发编程

### 线程

```rust
use std::thread;
use std::time::Duration;

// 创建线程
let handle = thread::spawn(|| {
    for i in 1..10 {
        println!("thread: {}", i);
        thread::sleep(Duration::from_millis(1));
    }
});

// 等待线程完成
handle.join().unwrap();

// move 闭包
let v = vec![1, 2, 3];
let handle = thread::spawn(move || {
    println!("vector: {:?}", v);
});
```

### 消息传递

```rust
use std::sync::mpsc;

// 创建 Channel
let (tx, rx) = mpsc::channel();

// 发送消息
thread::spawn(move || {
    tx.send(String::from("hi")).unwrap();
});

// 接收消息
let received = rx.recv().unwrap();

// 多个发送者
let tx1 = tx.clone();
```

### 共享状态

```rust
use std::sync::{Mutex, Arc};

// Mutex
let m = Mutex::new(5);
{
    let mut num = m.lock().unwrap();
    *num = 6;
}

// Arc + Mutex
let counter = Arc::new(Mutex::new(0));
let counter2 = Arc::clone(&counter);

thread::spawn(move || {
    let mut num = counter2.lock().unwrap();
    *num += 1;
});

// RwLock
use std::sync::RwLock;
let lock = RwLock::new(5);
let r1 = lock.read().unwrap();
let w = lock.write().unwrap();
```

---

## 异步编程

### async/await

```rust
// 异步函数
async fn hello_world() {
    println!("hello, world!");
}

// 异步块
let future = async {
    // 异步代码
};

// await
async fn learn_song() -> Song { /* ... */ }
async fn sing_song(song: Song) { /* ... */ }

async fn learn_and_sing() {
    let song = learn_song().await;
    sing_song(song).await;
}
```

### tokio 基础

```rust
// tokio runtime
#[tokio::main]
async fn main() {
    // 异步代码
}

// 手动创建 runtime
let rt = tokio::runtime::Runtime::new().unwrap();
rt.block_on(async {
    // 异步代码
});

// spawn 任务
tokio::spawn(async {
    // 异步任务
});

// join
let (result1, result2) = tokio::join!(future1, future2);

// select
tokio::select! {
    result1 = future1 => {},
    result2 = future2 => {},
}
```

---

## 常用宏

### 打印宏

```rust
// println!
println!("Hello, {}!", name);
println!("x = {}, y = {}", x, y);
println!("Debug: {:?}", value);
println!("Pretty Debug: {:#?}", value);

// print! (不换行)
print!("Loading");

// eprintln! (标准错误)
eprintln!("Error: {}", error);

// format!
let s = format!("x = {}", x);
```

### 调试宏

```rust
// dbg!
let a = 2;
let b = dbg!(a * 2) + 1;  // 打印并返回值

// assert!
assert!(condition);
assert_eq!(left, right);
assert_ne!(left, right);

// debug_assert! (仅 debug 模式)
debug_assert!(expensive_check());
```

### 其他常用宏

```rust
// vec!
let v = vec![1, 2, 3];

// panic!
panic!("Something went wrong");

// unreachable!
unreachable!("This code should never be reached");

// unimplemented!
unimplemented!("not implemented");

// todo!
todo!("not implemented");

// matches!
if matches!(value, Pattern) {
    // ...
}

// cfg!
if cfg!(target_os = "windows") {
    // Windows 特定代码
}
```

---

## 常用 Trait

### 基础 Trait

```rust
// Clone
let x = value.clone();

// Copy (自动复制)
let x = value;  // value 仍然有效

// Debug
println!("{:?}", value);

// Display
println!("{}", value);

// Default
let x = T::default();

// PartialEq, Eq
if value1 == value2 { }

// PartialOrd, Ord
if value1 < value2 { }

// Hash
use std::collections::HashMap;
let mut map = HashMap::new();
map.insert(key, value);
```

### 转换 Trait

```rust
// From / Into
let s = String::from("hello");
let s: String = "hello".into();

// AsRef / AsMut
fn print_str(s: impl AsRef<str>) {
    println!("{}", s.as_ref());
}

// TryFrom / TryInto
let num: Result<i32, _> = "42".parse();
```

### 运算符 Trait

```rust
// Add, Sub, Mul, Div
impl Add for Point {
    type Output = Point;
    fn add(self, other: Point) -> Point {
        Point { x: self.x + other.x, y: self.y + other.y }
    }
}

// Deref
impl Deref for MyBox<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.0
    }
}

// Drop
impl Drop for MyStruct {
    fn drop(&mut self) {
        println!("Dropping!");
    }
}
```

### 迭代器 Trait

```rust
// Iterator
impl Iterator for Counter {
    type Item = u32;
    fn next(&mut self) -> Option<Self::Item> {
        // ...
    }
}

// IntoIterator
for item in collection {  // 自动调用 into_iter()
    // ...
}
```

---

## 🔗 深入学习

### 按主题查找

- **所有权**: [C01 文档](../../../crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md)
- **类型系统**: [C02 文档](../../../crates/c02_type_system/docs/00_MASTER_INDEX.md)
- **控制流**: [C03 文档](../../../crates/c03_control_fn/docs/00_MASTER_INDEX.md)
- **泛型**: [C04 文档](../../../crates/c04_generic/docs/00_MASTER_INDEX.md)
- **并发**: [C05 文档](../../../crates/c05_threads/docs/00_MASTER_INDEX.md)
- **异步**: [C06 文档](../../../crates/c06_async/docs/00_MASTER_INDEX.md)

### 学习资源

- 📖 [完整学习路径](./README.md#学习路径推荐)
- ✅ [学习检查清单](./LEARNING_CHECKLIST.md)
- 🤝 [贡献指南](./CONTRIBUTING.md)

---

**快速查询完！** 🚀

需要详细学习？查看各模块的完整文档！

**最后更新**: 2025-10-19
**维护团队**: Rust 学习社区
**版本**: v1.0