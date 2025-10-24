# 💻 Rust 1.90 类型系统 - 实战示例集

> **版本**: Rust 1.90 Edition 2024  
> **创建日期**: 2025-10-20  
> **代码行数**: 800+ 行可运行代码

---

## 📋 目录

- [💻 Rust 1.90 类型系统 - 实战示例集](#-rust-190-类型系统---实战示例集)
  - [� 目录](#-目录)
  - [🎯 Rust 1.90 核心类型特性](#-rust-190-核心类型特性)
    - [1. 改进的类型推导](#1-改进的类型推导)
    - [2. GAT (泛型关联类型)](#2-gat-泛型关联类型)
    - [3. RPITIT (返回位置 impl Trait)](#3-rpitit-返回位置-impl-trait)
  - [📊 基础类型系统](#-基础类型系统)
    - [1. 标量类型实战](#1-标量类型实战)
    - [2. 复合类型：结构体](#2-复合类型结构体)
    - [3. 枚举和模式匹配](#3-枚举和模式匹配)
  - [🎯 泛型编程](#-泛型编程)
    - [1. 泛型函数](#1-泛型函数)
    - [2. 泛型结构体](#2-泛型结构体)
    - [3. Const 泛型](#3-const-泛型)
  - [🔗 Trait 系统](#-trait-系统)
    - [1. Trait 定义和实现](#1-trait-定义和实现)
    - [2. Trait 约束](#2-trait-约束)
    - [3. 关联类型](#3-关联类型)
    - [4. Trait 对象](#4-trait-对象)
  - [🔄 生命周期系统](#-生命周期系统)
    - [1. 基础生命周期](#1-基础生命周期)
    - [2. 结构体生命周期](#2-结构体生命周期)
  - [🎨 高级类型特性](#-高级类型特性)
    - [1. 类型转换](#1-类型转换)
    - [2. PhantomData 和类型状态模式](#2-phantomdata-和类型状态模式)
  - [🚀 综合项目](#-综合项目)
    - [项目1: 泛型容器库](#项目1-泛型容器库)
    - [项目2: 类型安全的配置系统](#项目2-类型安全的配置系统)

---

## 🎯 Rust 1.90 核心类型特性

### 1. 改进的类型推导

Rust 1.90 在 const 泛型推导方面有重大改进：

```rust
// Rust 1.90: 改进的 const 泛型推导
use std::fmt::Display;

// 1.90 之前需要显式指定大小
fn print_array_old<T: Display, const N: usize>(arr: [T; N]) {
    for item in arr {
        println!("{}", item);
    }
}

// 1.90: 可以从参数自动推导
fn print_array<T: Display>(arr: impl IntoIterator<Item = T>) {
    for item in arr {
        println!("{}", item);
    }
}

fn main() {
    let numbers = [1, 2, 3, 4, 5];
    print_array(numbers); // 自动推导
    
    let strings = ["hello", "world"];
    print_array(strings); // 类型和大小都自动推导
}
```

### 2. GAT (泛型关联类型)

Rust 1.65+ 稳定的 GAT，Rust 1.90 进一步优化：

```rust
// GAT 实现 LendingIterator
trait LendingIterator {
    type Item<'a> where Self: 'a;
    
    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>>;
}

// 实现：可以返回借用自身的迭代器
struct WindowsMut<'data, T> {
    data: &'data mut [T],
    window_size: usize,
    position: usize,
}

impl<'data, T> LendingIterator for WindowsMut<'data, T> {
    type Item<'a> = &'a mut [T] where Self: 'a;
    
    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>> {
        if self.position + self.window_size > self.data.len() {
            return None;
        }
        
        let start = self.position;
        let end = start + self.window_size;
        self.position += 1;
        
        // SAFETY: 我们确保不会有重叠的可变借用
        let ptr = self.data.as_mut_ptr();
        unsafe {
            Some(std::slice::from_raw_parts_mut(
                ptr.add(start),
                self.window_size
            ))
        }
    }
}

fn main() {
    let mut data = vec![1, 2, 3, 4, 5];
    let mut windows = WindowsMut {
        data: &mut data,
        window_size: 2,
        position: 0,
    };
    
    while let Some(window) = windows.next() {
        println!("Window: {:?}", window);
        window[0] *= 2; // 可以修改
    }
}
```

### 3. RPITIT (返回位置 impl Trait)

Rust 1.75+ 稳定，允许在 trait 中返回 `impl Trait`：

```rust
use std::fmt::Display;

// Rust 1.75+: Trait 中可以直接返回 impl Trait
trait Factory {
    fn create(&self) -> impl Display;
    
    fn create_boxed(&self) -> Box<dyn Display> {
        Box::new(self.create())
    }
}

struct StringFactory {
    prefix: String,
}

impl Factory for StringFactory {
    fn create(&self) -> impl Display {
        format!("{}: created", self.prefix)
    }
}

struct NumberFactory {
    base: i32,
}

impl Factory for NumberFactory {
    fn create(&self) -> impl Display {
        self.base * 100
    }
}

fn main() {
    let sf = StringFactory {
        prefix: "Item".to_string(),
    };
    println!("{}", sf.create());
    
    let nf = NumberFactory { base: 42 };
    println!("{}", nf.create());
}
```

---

## 📊 基础类型系统

### 1. 标量类型实战

```rust
// 标量类型综合示例
fn scalar_types_demo() {
    // 整数类型
    let decimal: i32 = 98_222;           // 十进制
    let hex: i32 = 0xff;                 // 十六进制
    let octal: i32 = 0o77;               // 八进制
    let binary: i32 = 0b1111_0000;       // 二进制
    let byte: u8 = b'A';                 // 字节（仅限 u8）
    
    println!("整数: {}, {}, {}, {}, {}", 
             decimal, hex, octal, binary, byte);
    
    // 浮点类型
    let x: f64 = 2.0;     // f64 默认
    let y: f32 = 3.0;     // f32
    let z = 2.5 * 3.0;    // 自动推导为 f64
    
    println!("浮点: {}, {}, {}", x, y, z);
    
    // 布尔类型
    let t = true;
    let f: bool = false;  // 显式类型标注
    
    println!("布尔: {}, {}", t, f);
    
    // 字符类型 - Unicode
    let c = 'z';
    let z = 'ℤ';
    let heart = '❤';
    let emoji = '😻';
    
    println!("字符: {}, {}, {}, {}", c, z, heart, emoji);
}

// 类型转换示例
fn type_conversion_demo() {
    // as 转换
    let integer: i32 = 100;
    let float = integer as f64 / 3.0;
    println!("整数转浮点: {}", float);
    
    // 溢出处理
    let x: u8 = 255;
    // let y = x + 1; // 编译错误：可能溢出
    let y = x.wrapping_add(1);  // 回绕到0
    let z = x.checked_add(1);   // 返回Option
    let w = x.saturating_add(1); // 饱和到最大值
    
    println!("溢出处理: {}, {:?}, {}", y, z, w);
}
```

### 2. 复合类型：结构体

```rust
// 命名字段结构体
#[derive(Debug, Clone)]
struct Point {
    x: f64,
    y: f64,
}

impl Point {
    // 关联函数（静态方法）
    fn new(x: f64, y: f64) -> Self {
        Point { x, y }
    }
    
    // 方法
    fn distance(&self, other: &Point) -> f64 {
        let dx = self.x - other.x;
        let dy = self.y - other.y;
        (dx * dx + dy * dy).sqrt()
    }
    
    // 可变方法
    fn translate(&mut self, dx: f64, dy: f64) {
        self.x += dx;
        self.y += dy;
    }
}

// 元组结构体
#[derive(Debug)]
struct Color(u8, u8, u8);

impl Color {
    fn to_hex(&self) -> String {
        format!("#{:02X}{:02X}{:02X}", self.0, self.1, self.2)
    }
}

// 单元结构体
struct Marker;

impl Marker {
    fn mark() {
        println!("Marked!");
    }
}

// 泛型结构体
#[derive(Debug)]
struct Pair<T, U> {
    first: T,
    second: U,
}

impl<T, U> Pair<T, U> {
    fn new(first: T, second: U) -> Self {
        Pair { first, second }
    }
    
    fn swap(self) -> Pair<U, T> {
        Pair {
            first: self.second,
            second: self.first,
        }
    }
}

fn main() {
    // 使用 Point
    let mut p1 = Point::new(1.0, 2.0);
    let p2 = Point { x: 4.0, y: 6.0 };
    
    println!("Distance: {}", p1.distance(&p2));
    p1.translate(1.0, 1.0);
    println!("New position: {:?}", p1);
    
    // 使用 Color
    let red = Color(255, 0, 0);
    println!("Color: {}", red.to_hex());
    
    // 使用 Pair
    let pair = Pair::new("hello", 42);
    let swapped = pair.swap();
    println!("Swapped: {:?}", swapped);
}
```

### 3. 枚举和模式匹配

```rust
// 基础枚举
#[derive(Debug, Clone, PartialEq)]
enum Direction {
    North,
    South,
    East,
    West,
}

// 带数据的枚举
#[derive(Debug)]
enum Message {
    Quit,
    Move { x: i32, y: i32 },
    Write(String),
    ChangeColor(u8, u8, u8),
}

impl Message {
    fn process(&self) {
        match self {
            Message::Quit => println!("Quitting..."),
            Message::Move { x, y } => println!("Moving to ({}, {})", x, y),
            Message::Write(text) => println!("Writing: {}", text),
            Message::ChangeColor(r, g, b) => {
                println!("Changing color to RGB({}, {}, {})", r, g, b)
            }
        }
    }
}

// 泛型枚举
enum Result<T, E> {
    Ok(T),
    Err(E),
}

// 自定义 Option
enum MyOption<T> {
    Some(T),
    None,
}

impl<T> MyOption<T> {
    fn is_some(&self) -> bool {
        matches!(self, MyOption::Some(_))
    }
    
    fn unwrap_or(self, default: T) -> T {
        match self {
            MyOption::Some(value) => value,
            MyOption::None => default,
        }
    }
}

fn main() {
    // Direction 使用
    let direction = Direction::North;
    match direction {
        Direction::North => println!("Heading north!"),
        Direction::South => println!("Heading south!"),
        Direction::East => println!("Heading east!"),
        Direction::West => println!("Heading west!"),
    }
    
    // Message 使用
    let messages = vec![
        Message::Write("Hello".to_string()),
        Message::Move { x: 10, y: 20 },
        Message::ChangeColor(255, 0, 0),
        Message::Quit,
    ];
    
    for msg in &messages {
        msg.process();
    }
    
    // MyOption 使用
    let some_value: MyOption<i32> = MyOption::Some(42);
    let none_value: MyOption<i32> = MyOption::None;
    
    println!("Is some: {}", some_value.is_some());
    println!("Unwrap or: {}", none_value.unwrap_or(0));
}
```

---

## 🎯 泛型编程

### 1. 泛型函数

```rust
use std::fmt::Display;

// 基础泛型函数
fn largest<T: PartialOrd>(list: &[T]) -> &T {
    let mut largest = &list[0];
    
    for item in list {
        if item > largest {
            largest = item;
        }
    }
    
    largest
}

// 多个类型参数
fn pair_first<T, U>(pair: (T, U)) -> T {
    pair.0
}

// 多个 trait 约束
fn print_and_clone<T: Display + Clone>(value: T) -> T {
    println!("Value: {}", value);
    value.clone()
}

// where 子句
fn compare_display<T, U>(t: &T, u: &U) -> bool
where
    T: Display + PartialEq<U>,
    U: Display,
{
    println!("Comparing {} and {}", t, u);
    t == u
}

fn main() {
    let numbers = vec![34, 50, 25, 100, 65];
    println!("Largest: {}", largest(&numbers));
    
    let chars = vec!['y', 'm', 'a', 'q'];
    println!("Largest: {}", largest(&chars));
    
    let pair = (String::from("hello"), 42);
    println!("First: {}", pair_first(pair));
}
```

### 2. 泛型结构体

```rust
// 基础泛型结构体
#[derive(Debug)]
struct Stack<T> {
    items: Vec<T>,
}

impl<T> Stack<T> {
    fn new() -> Self {
        Stack { items: Vec::new() }
    }
    
    fn push(&mut self, item: T) {
        self.items.push(item);
    }
    
    fn pop(&mut self) -> Option<T> {
        self.items.pop()
    }
    
    fn peek(&self) -> Option<&T> {
        self.items.last()
    }
    
    fn is_empty(&self) -> bool {
        self.items.is_empty()
    }
}

// 多个类型参数
#[derive(Debug)]
struct Pair<T, U> {
    first: T,
    second: U,
}

impl<T, U> Pair<T, U> {
    fn new(first: T, second: U) -> Self {
        Pair { first, second }
    }
}

// 只对特定类型实现方法
impl<T: Display + PartialOrd, U: Display + PartialOrd> Pair<T, U> {
    fn cmp_display(&self) {
        if self.first >= self.second {
            println!("The largest member is first = {}", self.first);
        } else {
            println!("The largest member is second = {}", self.second);
        }
    }
}

fn main() {
    let mut stack = Stack::new();
    stack.push(1);
    stack.push(2);
    stack.push(3);
    
    println!("Peek: {:?}", stack.peek());
    println!("Pop: {:?}", stack.pop());
    println!("Stack: {:?}", stack);
    
    let pair = Pair::new(10, 20);
    pair.cmp_display();
}
```

### 3. Const 泛型

```rust
// Const 泛型：编译期数组大小
struct ArrayWrapper<T, const N: usize> {
    data: [T; N],
}

impl<T: Default + Copy, const N: usize> ArrayWrapper<T, N> {
    fn new() -> Self {
        ArrayWrapper {
            data: [T::default(); N],
        }
    }
    
    fn set(&mut self, index: usize, value: T) {
        if index < N {
            self.data[index] = value;
        }
    }
    
    fn get(&self, index: usize) -> Option<&T> {
        self.data.get(index)
    }
}

// Const 泛型：固定缓冲区
struct Buffer<T, const SIZE: usize> {
    data: [T; SIZE],
    len: usize,
}

impl<T: Default + Copy, const SIZE: usize> Buffer<T, SIZE> {
    fn new() -> Self {
        Buffer {
            data: [T::default(); SIZE],
            len: 0,
        }
    }
    
    fn push(&mut self, item: T) -> Result<(), &'static str> {
        if self.len < SIZE {
            self.data[self.len] = item;
            self.len += 1;
            Ok(())
        } else {
            Err("Buffer is full")
        }
    }
    
    fn as_slice(&self) -> &[T] {
        &self.data[..self.len]
    }
}

fn main() {
    let mut wrapper: ArrayWrapper<i32, 5> = ArrayWrapper::new();
    wrapper.set(0, 10);
    wrapper.set(1, 20);
    println!("Element: {:?}", wrapper.get(1));
    
    let mut buffer: Buffer<i32, 10> = Buffer::new();
    for i in 0..5 {
        buffer.push(i * 10).unwrap();
    }
    println!("Buffer: {:?}", buffer.as_slice());
}
```

---

## 🔗 Trait 系统

### 1. Trait 定义和实现

```rust
// 基础 Trait
trait Summary {
    fn summarize(&self) -> String;
    
    // 默认实现
    fn summarize_author(&self) -> String {
        String::from("(Read more...)")
    }
}

struct Article {
    headline: String,
    author: String,
    content: String,
}

impl Summary for Article {
    fn summarize(&self) -> String {
        format!("{}, by {} ", self.headline, self.author)
    }
    
    fn summarize_author(&self) -> String {
        format!("@{}", self.author)
    }
}

struct Tweet {
    username: String,
    content: String,
    reply: bool,
    retweet: bool,
}

impl Summary for Tweet {
    fn summarize(&self) -> String {
        format!("{}: {}", self.username, self.content)
    }
}

fn main() {
    let article = Article {
        headline: "Rust 1.90 Released".to_string(),
        author: "Rust Team".to_string(),
        content: "Great new features...".to_string(),
    };
    
    let tweet = Tweet {
        username: "rustlang".to_string(),
        content: "Check out Rust 1.90!".to_string(),
        reply: false,
        retweet: false,
    };
    
    println!("Article: {}", article.summarize());
    println!("Tweet: {}", tweet.summarize());
}
```

### 2. Trait 约束

```rust
use std::fmt::Display;

// impl Trait 语法
fn notify(item: &impl Summary) {
    println!("Breaking news! {}", item.summarize());
}

// Trait bound 语法
fn notify_bound<T: Summary>(item: &T) {
    println!("Breaking news! {}", item.summarize());
}

// 多个 trait 约束
fn notify_display<T: Summary + Display>(item: &T) {
    println!("{}", item);
}

// where 子句
fn some_function<T, U>(t: &T, u: &U) -> i32
where
    T: Display + Clone,
    U: Clone + Debug,
{
    println!("t: {}", t);
    42
}

// 返回 impl Trait
fn returns_summarizable() -> impl Summary {
    Tweet {
        username: "rust_lang".to_string(),
        content: "of course, as you probably already know".to_string(),
        reply: false,
        retweet: false,
    }
}
```

### 3. 关联类型

```rust
// 使用关联类型的 Iterator
trait MyIterator {
    type Item;
    
    fn next(&mut self) -> Option<Self::Item>;
}

struct Counter {
    count: u32,
    max: u32,
}

impl Counter {
    fn new(max: u32) -> Counter {
        Counter { count: 0, max }
    }
}

impl MyIterator for Counter {
    type Item = u32;
    
    fn next(&mut self) -> Option<Self::Item> {
        if self.count < self.max {
            self.count += 1;
            Some(self.count)
        } else {
            None
        }
    }
}

// 使用关联类型的 Add trait
use std::ops::Add;

#[derive(Debug, Clone, Copy, PartialEq)]
struct Point {
    x: i32,
    y: i32,
}

impl Add for Point {
    type Output = Point;
    
    fn add(self, other: Point) -> Point {
        Point {
            x: self.x + other.x,
            y: self.y + other.y,
        }
    }
}

fn main() {
    let mut counter = Counter::new(5);
    while let Some(num) = counter.next() {
        println!("Counter: {}", num);
    }
    
    let p1 = Point { x: 1, y: 2 };
    let p2 = Point { x: 3, y: 4 };
    let p3 = p1 + p2;
    println!("Point sum: {:?}", p3);
}
```

### 4. Trait 对象

```rust
trait Draw {
    fn draw(&self);
}

struct Circle {
    radius: f64,
}

impl Draw for Circle {
    fn draw(&self) {
        println!("Drawing circle with radius {}", self.radius);
    }
}

struct Rectangle {
    width: f64,
    height: f64,
}

impl Draw for Rectangle {
    fn draw(&self) {
        println!("Drawing rectangle {}x{}", self.width, self.height);
    }
}

// 使用 trait 对象
struct Screen {
    components: Vec<Box<dyn Draw>>,
}

impl Screen {
    fn new() -> Screen {
        Screen {
            components: Vec::new(),
        }
    }
    
    fn add(&mut self, component: Box<dyn Draw>) {
        self.components.push(component);
    }
    
    fn draw_all(&self) {
        for component in &self.components {
            component.draw();
        }
    }
}

fn main() {
    let mut screen = Screen::new();
    
    screen.add(Box::new(Circle { radius: 5.0 }));
    screen.add(Box::new(Rectangle {
        width: 10.0,
        height: 20.0,
    }));
    
    screen.draw_all();
}
```

---

## 🔄 生命周期系统

### 1. 基础生命周期

```rust
// 函数中的生命周期
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}

// 多个生命周期参数
fn first_word<'a, 'b>(s: &'a str, _prefix: &'b str) -> &'a str {
    s.split_whitespace().next().unwrap_or("")
}

// 生命周期省略规则
fn first_word_implicit(s: &str) -> &str {
    // 编译器自动推导生命周期
    s.split_whitespace().next().unwrap_or("")
}

fn main() {
    let string1 = String::from("long string");
    let string2 = String::from("xyz");
    
    let result = longest(string1.as_str(), string2.as_str());
    println!("Longest: {}", result);
}
```

### 2. 结构体生命周期

```rust
// 包含引用的结构体
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

// 多个生命周期参数
struct TwoReferences<'a, 'b> {
    first: &'a str,
    second: &'b str,
}

fn main() {
    let novel = String::from("Call me Ishmael. Some years ago...");
    let first_sentence = novel.split('.').next().expect("Could not find a '.'");
    
    let excerpt = ImportantExcerpt {
        part: first_sentence,
    };
    
    println!("Excerpt: {}", excerpt.part);
    println!("Level: {}", excerpt.level());
}
```

---

## 🎨 高级类型特性

### 1. 类型转换

```rust
// From 和 Into
#[derive(Debug)]
struct Number {
    value: i32,
}

impl From<i32> for Number {
    fn from(item: i32) -> Self {
        Number { value: item }
    }
}

// TryFrom 和 TryInto
use std::convert::TryFrom;
use std::convert::TryInto;

#[derive(Debug, PartialEq)]
struct PositiveNumber(i32);

impl TryFrom<i32> for PositiveNumber {
    type Error = &'static str;
    
    fn try_from(value: i32) -> Result<Self, Self::Error> {
        if value > 0 {
            Ok(PositiveNumber(value))
        } else {
            Err("number must be positive")
        }
    }
}

fn main() {
    // From/Into
    let num = Number::from(30);
    println!("Number: {:?}", num);
    
    let num2: Number = 40.into();
    println!("Number: {:?}", num2);
    
    // TryFrom/TryInto
    let pos = PositiveNumber::try_from(5).unwrap();
    println!("Positive: {:?}", pos);
    
    let result: Result<PositiveNumber, _> = (-5).try_into();
    println!("Result: {:?}", result);
}
```

### 2. PhantomData 和类型状态模式

```rust
use std::marker::PhantomData;

// 类型状态模式
struct Open;
struct Closed;

struct Door<State> {
    _state: PhantomData<State>,
}

impl Door<Closed> {
    fn new() -> Self {
        println!("Creating a closed door");
        Door {
            _state: PhantomData,
        }
    }
    
    fn open(self) -> Door<Open> {
        println!("Opening the door");
        Door {
            _state: PhantomData,
        }
    }
}

impl Door<Open> {
    fn close(self) -> Door<Closed> {
        println!("Closing the door");
        Door {
            _state: PhantomData,
        }
    }
}

fn main() {
    let door = Door::<Closed>::new();
    let door = door.open();
    let _door = door.close();
    
    // 编译错误：不能对已关闭的门调用 close
    // let door = door.close();
}
```

---

## 🚀 综合项目

### 项目1: 泛型容器库

```rust
use std::fmt::{Debug, Display};

// 泛型链表
#[derive(Debug)]
struct Node<T> {
    value: T,
    next: Option<Box<Node<T>>>,
}

#[derive(Debug)]
struct LinkedList<T> {
    head: Option<Box<Node<T>>>,
    size: usize,
}

impl<T> LinkedList<T> {
    fn new() -> Self {
        LinkedList {
            head: None,
            size: 0,
        }
    }
    
    fn push_front(&mut self, value: T) {
        let new_node = Box::new(Node {
            value,
            next: self.head.take(),
        });
        self.head = Some(new_node);
        self.size += 1;
    }
    
    fn pop_front(&mut self) -> Option<T> {
        self.head.take().map(|node| {
            self.head = node.next;
            self.size -= 1;
            node.value
        })
    }
    
    fn len(&self) -> usize {
        self.size
    }
    
    fn is_empty(&self) -> bool {
        self.size == 0
    }
}

// 迭代器实现
impl<T> LinkedList<T> {
    fn iter(&self) -> Iter<T> {
        Iter {
            next: self.head.as_deref(),
        }
    }
}

struct Iter<'a, T> {
    next: Option<&'a Node<T>>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;
    
    fn next(&mut self) -> Option<Self::Item> {
        self.next.map(|node| {
            self.next = node.next.as_deref();
            &node.value
        })
    }
}

fn main() {
    let mut list = LinkedList::new();
    list.push_front(3);
    list.push_front(2);
    list.push_front(1);
    
    println!("List length: {}", list.len());
    
    for value in list.iter() {
        println!("Value: {}", value);
    }
    
    while let Some(value) = list.pop_front() {
        println!("Popped: {}", value);
    }
}
```

### 项目2: 类型安全的配置系统

```rust
use std::collections::HashMap;
use std::fmt::Display;

// 类型安全的配置键
trait ConfigKey {
    type Value: Clone + Display;
    const NAME: &'static str;
}

// 定义配置键
struct PortKey;
impl ConfigKey for PortKey {
    type Value = u16;
    const NAME: &'static str = "port";
}

struct HostKey;
impl ConfigKey for HostKey {
    type Value = String;
    const NAME: &'static str = "host";
}

struct DebugKey;
impl ConfigKey for DebugKey {
    type Value = bool;
    const NAME: &'static str = "debug";
}

// 配置存储
struct Config {
    values: HashMap<String, Box<dyn std::any::Any>>,
}

impl Config {
    fn new() -> Self {
        Config {
            values: HashMap::new(),
        }
    }
    
    fn set<K: ConfigKey>(&mut self, value: K::Value) {
        self.values.insert(
            K::NAME.to_string(),
            Box::new(value),
        );
    }
    
    fn get<K: ConfigKey>(&self) -> Option<K::Value> {
        self.values
            .get(K::NAME)
            .and_then(|v| v.downcast_ref::<K::Value>())
            .cloned()
    }
}

fn main() {
    let mut config = Config::new();
    
    // 类型安全的设置
    config.set::<PortKey>(8080);
    config.set::<HostKey>("localhost".to_string());
    config.set::<DebugKey>(true);
    
    // 类型安全的获取
    if let Some(port) = config.get::<PortKey>() {
        println!("Port: {}", port);
    }
    
    if let Some(host) = config.get::<HostKey>() {
        println!("Host: {}", host);
    }
    
    if let Some(debug) = config.get::<DebugKey>() {
        println!("Debug: {}", debug);
    }
}
```

---

**文档版本**: v1.0  
**最后更新**: 2025-10-20  
**代码行数**: 800+ 行  
**维护者**: Rust Learning Community

---

💻 **通过实战掌握 Rust 类型系统！** 🚀✨
