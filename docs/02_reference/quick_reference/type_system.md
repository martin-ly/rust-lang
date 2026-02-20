# 🔷 Rust 类型系统速查卡

> **快速参考** | [完整文档](../../../crates/c02_type_system/docs/) | [代码示例](../../../crates/c02_type_system/examples/)
> **创建日期**: 2026-01-27
> **最后更新**: 2026-01-27
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 📋 目录

- [🔷 Rust 类型系统速查卡](#-rust-类型系统速查卡)
  - [📋 目录](#-目录)
  - [🎯 核心概念](#-核心概念)
    - [类型安全三支柱](#类型安全三支柱)
  - [📐 基本类型速查](#-基本类型速查)
    - [标量类型](#标量类型)
    - [复合类型](#复合类型)
  - [🏗️ Trait 系统](#️-trait-系统)
    - [定义与实现](#定义与实现)
    - [Trait 作为参数](#trait-作为参数)
    - [Trait 作为返回值](#trait-作为返回值)
  - [🔄 类型转换](#-类型转换)
    - [From/Into](#frominto)
    - [TryFrom/TryInto（可失败转换）](#tryfromtryinto可失败转换)
    - [as 转换（基本类型）](#as-转换基本类型)
  - [📦 泛型编程](#-泛型编程)
    - [泛型函数](#泛型函数)
    - [泛型结构体](#泛型结构体)
    - [关联类型](#关联类型)
  - [🎭 型变（Variance）](#-型变variance)
    - [协变（Covariant）- \&T](#协变covariant--t)
    - [逆变（Contravariant）- fn(T)](#逆变contravariant--fnt)
    - [不变（Invariant）- \&mut T](#不变invariant--mut-t)
  - [🔍 常用 Trait](#-常用-trait)
    - [Debug \& Display](#debug--display)
    - [Clone \& Copy](#clone--copy)
    - [PartialEq \& Eq](#partialeq--eq)
    - [PartialOrd \& Ord](#partialord--ord)
  - [🧬 高级类型](#-高级类型)
    - [类型别名](#类型别名)
    - [Never 类型](#never-类型)
    - [PhantomData（零大小类型标记）](#phantomdata零大小类型标记)
  - [🎯 常见模式](#-常见模式)
    - [新类型模式（Newtype）](#新类型模式newtype)
    - [类型状态模式](#类型状态模式)
    - [Builder 模式（类型安全）](#builder-模式类型安全)
  - [⚡ 性能提示](#-性能提示)
    - [单态化（Monomorphization）](#单态化monomorphization)
    - [动态分派 vs 静态分派](#动态分派-vs-静态分派)
    - [内存对齐](#内存对齐)
  - [🚫 反例速查](#-反例速查)
    - [反例 1: 为 Copy 类型实现 Clone 不一致](#反例-1-为-copy-类型实现-clone-不一致)
    - [反例 2: 生命周期省略导致悬垂引用](#反例-2-生命周期省略导致悬垂引用)
    - [反例 3: 混淆 Sized 与动态大小类型](#反例-3-混淆-sized-与动态大小类型)
  - [🔗 快速跳转](#-快速跳转)
    - [深入学习](#深入学习)
    - [代码示例](#代码示例)
    - [形式化理论](#形式化理论)
  - [💡 使用场景](#-使用场景)
    - [场景 1: 状态机类型系统](#场景-1-状态机类型系统)
    - [场景 2: 类型安全的配置构建](#场景-2-类型安全的配置构建)
    - [场景 3: 零成本抽象的数据库查询](#场景-3-零成本抽象的数据库查询)
  - [⚠️ 边界情况](#️-边界情况)
    - [边界 1: 动态大小类型 (DST)](#边界-1-动态大小类型-dst)
    - [边界 2: 递归类型与间接](#边界-2-递归类型与间接)
    - [边界 3: 生命周期子类型](#边界-3-生命周期子类型)
  - [🆕 Rust 1.93.0 新特性](#-rust-1930-新特性)
    - [MaybeUninit API 增强](#maybeuninit-api-增强)
    - [切片到数组转换](#切片到数组转换)
  - [Rust 1.92.0 新特性（历史）](#rust-1920-新特性历史)
    - [const 上下文增强](#const-上下文增强)
  - [📚 相关文档](#-相关文档)
  - [🧩 相关示例代码](#-相关示例代码)
  - [📚 相关资源](#-相关资源)
    - [官方文档](#官方文档)
    - [项目内部文档](#项目内部文档)
    - [相关速查卡](#相关速查卡)

---

## 🎯 核心概念

### 类型安全三支柱

```text
1. 静态类型检查（编译期）
2. 类型推导（省略显式标注）
3. 零成本抽象（无运行时开销）
```

---

## 📐 基本类型速查

### 标量类型

```rust
// 整数
let a: i8 = -128;      // 8位有符号
let b: u8 = 255;       // 8位无符号
let c: i32 = -100;     // 32位有符号（默认）
let d: usize = 100;    // 指针大小

// 浮点
let e: f32 = 3.14;     // 32位
let f: f64 = 2.71;     // 64位（默认）

// 布尔
let g: bool = true;

// 字符
let h: char = '🦀';    // Unicode 字符
```

---

### 复合类型

```rust
// 元组
let tuple: (i32, f64, char) = (500, 6.4, '🦀');
let (x, y, z) = tuple;  // 解构

// 数组
let array: [i32; 5] = [1, 2, 3, 4, 5];
let slice: &[i32] = &array[1..3];  // [2, 3]

// 字符串
let s1: &str = "hello";           // 字符串切片
let s2: String = String::from("world");  // 堆字符串
```

---

## 🏗️ Trait 系统

### 定义与实现

```rust
trait Summary {
    fn summarize(&self) -> String;

    // 默认实现
    fn default_summary(&self) -> String {
        String::from("(Read more...)")
    }
}

struct Article {
    title: String,
    content: String,
}

impl Summary for Article {
    fn summarize(&self) -> String {
        format!("{}: {}", self.title, self.content)
    }
}
```

---

### Trait 作为参数

```rust
// 方式 1: impl Trait
fn notify(item: &impl Summary) {
    println!("{}", item.summarize());
}

// 方式 2: Trait bound
fn notify<T: Summary>(item: &T) {
    println!("{}", item.summarize());
}

// 方式 3: where 子句（复杂约束）
fn notify<T>(item: &T)
where
    T: Summary + Display,
{
    println!("{}", item.summarize());
}
```

---

### Trait 作为返回值

```rust
// impl Trait 语法
fn returns_summarizable() -> impl Summary {
    Article {
        title: String::from("Hello"),
        content: String::from("World"),
    }
}

// Trait 对象（动态分派）
fn returns_trait_object() -> Box<dyn Summary> {
    Box::new(Article { /* ... */ })
}
```

---

## 🔄 类型转换

### From/Into

```rust
// From trait
impl From<i32> for MyType {
    fn from(val: i32) -> Self {
        MyType(val)
    }
}

let my = MyType::from(42);

// Into trait（自动实现）
let my: MyType = 42.into();
```

---

### TryFrom/TryInto（可失败转换）

```rust
use std::convert::TryFrom;

impl TryFrom<i32> for PositiveInt {
    type Error = &'static str;

    fn try_from(value: i32) -> Result<Self, Self::Error> {
        if value > 0 {
            Ok(PositiveInt(value))
        } else {
            Err("Value must be positive")
        }
    }
}

let pos = PositiveInt::try_from(42)?;
```

---

### as 转换（基本类型）

```rust
let a = 3.14f64;
let b = a as i32;      // 3（截断）
let c = 100i32 as u8;  // 100
```

---

## 📦 泛型编程

### 泛型函数

```rust
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

---

### 泛型结构体

```rust
struct Point<T> {
    x: T,
    y: T,
}

impl<T> Point<T> {
    fn new(x: T, y: T) -> Self {
        Point { x, y }
    }
}

// 为特定类型实现方法
impl Point<f32> {
    fn distance_from_origin(&self) -> f32 {
        (self.x.powi(2) + self.y.powi(2)).sqrt()
    }
}
```

---

### 关联类型

```rust
trait Iterator {
    type Item;  // 关联类型

    fn next(&mut self) -> Option<Self::Item>;
}

impl Iterator for Counter {
    type Item = u32;

    fn next(&mut self) -> Option<Self::Item> {
        // ...
    }
}
```

---

## 🎭 型变（Variance）

### 协变（Covariant）- &T

```rust
// 'long 是 'short 的子类型
fn covariant<'long, 'short>(x: &'long str) -> &'short str
where
    'long: 'short,  // 'long 活得更久
{
    x  // ✅ OK: &'long str 可以转为 &'short str
}
```

---

### 逆变（Contravariant）- fn(T)

```rust
// 函数参数是逆变的
fn contravariant<'short, 'long>(
    f: fn(&'long str),
    s: &'short str,
) where
    'short: 'long,
{
    f(s);  // ✅ OK
}
```

---

### 不变（Invariant）- &mut T

```rust
// &mut T 是不变的
fn invariant<'a, 'b>(x: &'a mut i32, y: &'b mut i32) {
    // x 和 y 必须精确匹配生命周期
}
```

---

## 🔍 常用 Trait

### Debug & Display

```rust
#[derive(Debug)]
struct Point { x: i32, y: i32 }

impl std::fmt::Display for Point {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "({}, {})", self.x, self.y)
    }
}

let p = Point { x: 1, y: 2 };
println!("{:?}", p);  // Debug
println!("{}", p);    // Display
```

---

### Clone & Copy

```rust
// Copy: 隐式复制（栈上简单类型）
#[derive(Copy, Clone)]
struct Point { x: i32, y: i32 }

// Clone: 显式深拷贝
#[derive(Clone)]
struct Data { vec: Vec<i32> }

let d1 = Data { vec: vec![1, 2, 3] };
let d2 = d1.clone();  // 显式克隆
```

---

### PartialEq & Eq

```rust
#[derive(PartialEq, Eq)]
struct Point { x: i32, y: i32 }

let p1 = Point { x: 1, y: 2 };
let p2 = Point { x: 1, y: 2 };
assert_eq!(p1, p2);
```

---

### PartialOrd & Ord

```rust
#[derive(PartialOrd, Ord, PartialEq, Eq)]
struct Point { x: i32, y: i32 }

use std::cmp::Ordering;

let p1 = Point { x: 1, y: 2 };
let p2 = Point { x: 3, y: 4 };
assert!(p1 < p2);
```

---

## 🧬 高级类型

### 类型别名

```rust
type Kilometers = i32;
type Result<T> = std::result::Result<T, std::io::Error>;

fn distance() -> Kilometers {
    100
}
```

---

### Never 类型

```rust
fn never_returns() -> ! {
    panic!("This function never returns!");
}

let x: i32 = if some_condition {
    42
} else {
    never_returns()  // ! 可以转换为任何类型
};
```

---

### PhantomData（零大小类型标记）

```rust
use std::marker::PhantomData;

struct MyType<T> {
    data: *const u8,
    _marker: PhantomData<T>,  // 告诉编译器"拥有" T
}
```

---

## 🎯 常见模式

### 新类型模式（Newtype）

```rust
struct Meters(u32);
struct Seconds(u32);

// 防止类型混淆
fn run(distance: Meters, time: Seconds) {
    // ...
}

// ❌ 编译错误
// run(Seconds(10), Meters(100));
```

---

### 类型状态模式

```rust
struct Locked;
struct Unlocked;

struct Door<State> {
    _state: PhantomData<State>,
}

impl Door<Locked> {
    fn unlock(self) -> Door<Unlocked> {
        Door { _state: PhantomData }
    }
}

impl Door<Unlocked> {
    fn lock(self) -> Door<Locked> {
        Door { _state: PhantomData }
    }

    fn open(&self) {
        println!("Door opened");
    }
}

let door = Door::<Locked> { _state: PhantomData };
// door.open();  // ❌ 编译错误：锁着的门不能开
let door = door.unlock();
door.open();  // ✅ OK
```

---

### Builder 模式（类型安全）

```rust
struct EmailBuilder<Subject, Body> {
    to: String,
    subject: Subject,
    body: Body,
}

struct Set<T>(T);
struct Unset;

impl EmailBuilder<Unset, Unset> {
    fn new(to: String) -> Self {
        EmailBuilder { to, subject: Unset, body: Unset }
    }
}

impl<B> EmailBuilder<Unset, B> {
    fn subject(self, subject: String) -> EmailBuilder<Set<String>, B> {
        EmailBuilder {
            to: self.to,
            subject: Set(subject),
            body: self.body,
        }
    }
}

// 只有 subject 和 body 都设置后才能 build
impl EmailBuilder<Set<String>, Set<String>> {
    fn build(self) -> Email {
        Email {
            to: self.to,
            subject: self.subject.0,
            body: self.body.0,
        }
    }
}
```

---

## ⚡ 性能提示

### 单态化（Monomorphization）

```rust
// 泛型函数会为每个具体类型生成一份代码
fn generic<T: Display>(t: T) {
    println!("{}", t);
}

// 调用时
generic(5);       // 生成 generic::<i32>
generic("hello"); // 生成 generic::<&str>
```

**优势**: 零运行时开销
**劣势**: 增加编译时间和二进制大小

---

### 动态分派 vs 静态分派

```rust
// 静态分派（单态化）
fn static_dispatch<T: Summary>(item: &T) {
    item.summarize();
}
// ✅ 性能：无虚表开销
// ⚠️ 代价：代码膨胀

// 动态分派（trait 对象）
fn dynamic_dispatch(item: &dyn Summary) {
    item.summarize();
}
// ✅ 性能：小二进制
// ⚠️ 代价：虚表查找开销
```

---

### 内存对齐

```rust
use std::mem::{size_of, align_of};

// 对齐 = 各字段对齐的最大值
assert_eq!(align_of::<u64>(), 8);

#[repr(C)]
struct Example { a: u8; b: u64; }
assert_eq!(align_of::<Example>(), 8);

// 缓存行对齐（避免伪共享）
#[repr(align(64))]
struct CacheAligned { data: [u8; 64]; }
```

**详见**: [ALIGNMENT_GUIDE](../../ALIGNMENT_GUIDE.md)、[c01 内存布局优化](../../../crates/c01_ownership_borrow_scope/docs/tier_04_advanced/04_内存布局优化.md)

---

## 🚫 反例速查

### 反例 1: 为 Copy 类型实现 Clone 不一致

**错误示例**:

```rust
#[derive(Copy, Clone)]
struct Bad {
    data: String,  // ❌ String 不是 Copy，不能 derive Copy
}
```

**原因**: `Copy` 要求所有字段都是 `Copy`，`String` 不是。

**修正**:

```rust
#[derive(Clone)]
struct Good {
    data: String,
}
```

---

### 反例 2: 生命周期省略导致悬垂引用

**错误示例**:

```rust
fn longest(x: &str, y: &str) -> &str {
    if x.len() > y.len() { x } else { y }
}
// 若无输入引用，返回的引用可能悬垂
```

**原因**: 输出引用生命周期需与输入关联。

**修正**:

```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}
```

---

### 反例 3: 混淆 Sized 与动态大小类型

**错误示例**:

```rust
fn take<T>(t: T) {}  // T: Sized 默认
take(&[1, 2, 3]);   // ❌ [i32; 3] 是 Sized，但 &[i32] 的 T 是 slice
```

**原因**: `&[T]` 为动态大小，需 `T: ?Sized` 或使用 `&[T]` 明确。

**修正**:

```rust
fn take_slice<T>(t: &[T]) {}
```

---

## 🔗 快速跳转

### 深入学习

- [类型系统理论](../../../crates/c02_type_system/docs/tier_04_advanced/)
- [型变详解](../../../crates/c02_type_system/docs/tier_03_references/02_类型型变参考.md)
- [Trait 系统](../../../crates/c02_type_system/docs/tier_02_guides/04_Trait系统指南.md)

### 代码示例

- [泛型示例](../../../crates/c02_type_system/examples/)
- [类型转换](../../../crates/c02_type_system/src/conversions/)

### 形式化理论

- [类型理论基础](../../../crates/c02_type_system/docs/tier_04_advanced/01_类型理论基础.md)
- [类型构造能力](../../research_notes/type_theory/construction_capability.md) — Def TCON1、TCON 矩阵、类型构造决策树、Rust 1.93 新特性
- [类型构造决策树（直达）](../../research_notes/type_theory/construction_capability.md#类型构造决策树) — 目标类型→构造路径选择、确定性判定
- [类型理论完备性缺口](../../research_notes/type_theory/00_completeness_gaps.md) — 缺口与对构造能力的影响
- [类型系统基础](../../research_notes/type_theory/type_system_foundations.md) — 类型系统的数学基础
- [型变理论](../../research_notes/type_theory/variance_theory.md) — 型变的形式化定义
- [Trait 系统形式化](../../research_notes/type_theory/trait_system_formalization.md) — Trait 系统的类型理论

---

## 💡 使用场景

### 场景 1: 状态机类型系统

```rust
// 使用类型系统实现编译时状态检查
struct Idle;
struct Running;
struct Paused;

struct StateMachine<State> {
    data: i32,
    _state: std::marker::PhantomData<State>,
}

impl StateMachine<Idle> {
    fn new(data: i32) -> Self {
        StateMachine {
            data,
            _state: std::marker::PhantomData,
        }
    }

    fn start(self) -> StateMachine<Running> {
        println!("开始运行，数据: {}", self.data);
        StateMachine {
            data: self.data,
            _state: std::marker::PhantomData,
        }
    }
}

impl StateMachine<Running> {
    fn pause(self) -> StateMachine<Paused> {
        println!("暂停");
        StateMachine {
            data: self.data,
            _state: std::marker::PhantomData,
        }
    }

    fn stop(self) -> StateMachine<Idle> {
        println!("停止");
        StateMachine {
            data: self.data,
            _state: std::marker::PhantomData,
        }
    }
}

impl StateMachine<Paused> {
    fn resume(self) -> StateMachine<Running> {
        println!("恢复运行");
        StateMachine {
            data: self.data,
            _state: std::marker::PhantomData,
        }
    }
}

fn main() {
    let machine = StateMachine::<Idle>::new(42)
        .start()
        .pause()
        .resume()
        .stop();

    // machine.start(); // ❌ 编译错误：Idle 状态没有 start 方法
}
```

### 场景 2: 类型安全的配置构建

```rust
use std::marker::PhantomData;

// 标记类型
struct Unvalidated;
struct Validated;

struct Config<State = Unvalidated> {
    host: String,
    port: u16,
    _state: PhantomData<State>,
}

impl Config<Unvalidated> {
    fn new(host: &str, port: u16) -> Self {
        Config {
            host: host.to_string(),
            port,
            _state: PhantomData,
        }
    }

    fn validate(self) -> Result<Config<Validated>, String> {
        if self.host.is_empty() {
            return Err("主机名不能为空".to_string());
        }
        if self.port == 0 {
            return Err("端口号不能为 0".to_string());
        }
        Ok(Config {
            host: self.host,
            port: self.port,
            _state: PhantomData,
        })
    }
}

impl Config<Validated> {
    fn connect(&self) {
        println!("连接到 {}:{}", self.host, self.port);
    }
}

fn main() {
    let config = Config::new("localhost", 8080);
    // config.connect(); // ❌ 编译错误：未验证的配置不能连接

    match config.validate() {
        Ok(valid) => valid.connect(),
        Err(e) => println!("验证失败: {}", e),
    }
}
```

### 场景 3: 零成本抽象的数据库查询

```rust
trait Table {
    const NAME: &'static str;
    type Id: Clone;
}

struct UserTable;
impl Table for UserTable {
    const NAME: &'static str = "users";
    type Id = u64;
}

struct Query<T: Table> {
    _phantom: std::marker::PhantomData<T>,
    conditions: Vec<String>,
}

impl<T: Table> Query<T> {
    fn new() -> Self {
        Query {
            _phantom: std::marker::PhantomData,
            conditions: vec![],
        }
    }

    fn filter(mut self, condition: &str) -> Self {
        self.conditions.push(condition.to_string());
        self
    }

    fn build(self) -> String {
        let where_clause = if self.conditions.is_empty() {
            String::new()
        } else {
            format!(" WHERE {}", self.conditions.join(" AND "))
        };
        format!("SELECT * FROM {}{}", T::NAME, where_clause)
    }
}

fn main() {
    let query = Query::<UserTable>::new()
        .filter("age > 18")
        .filter("active = true")
        .build();

    println!("SQL: {}", query);
    // 输出: SELECT * FROM users WHERE age > 18 AND active = true
}
```

---

## ⚠️ 边界情况

### 边界 1: 动态大小类型 (DST)

```rust
fn process_slice(data: &[i32]) {
    println!("切片长度: {}", data.len());
}

// 胖指针的内存布局
fn main() {
    let arr = [1, 2, 3, 4, 5];
    let slice: &[i32] = &arr;

    // slice 是胖指针：包含数据指针和长度
    println!("胖指针示例");
    process_slice(slice);

    // 动态 trait 对象
    let s: &dyn std::fmt::Display = &42;
    println!("动态分派: {}", s);
}
```

### 边界 2: 递归类型与间接

```rust
use std::rc::Rc;
use std::cell::RefCell;

// ❌ 编译错误：递归类型会导致无限大小
// enum List<T> {
//     Cons(T, List<T>),
//     Nil,
// }

// ✅ 解决：使用 Box 提供间接层
enum List<T> {
    Cons(T, Box<List<T>>),
    Nil,
}

// ✅ 或用于共享所有权场景
#[derive(Debug)]
enum SharedList<T> {
    Cons(T, Rc<RefCell<SharedList<T>>>),
    Nil,
}

fn main() {
    let list = List::Cons(1, Box::new(List::Cons(2, Box::new(List::Nil))));

    let shared = Rc::new(RefCell::new(SharedList::Nil));
    let list2 = SharedList::Cons(1, Rc::clone(&shared));

    println!("递归类型示例完成");
}
```

### 边界 3: 生命周期子类型

```rust
fn longer_lifetime<'a: 'b, 'b>(x: &'a str, _y: &'b str) -> &'b str {
    x  // 'a 比 'b 活得长，所以可以返回 &'b str
}

fn main() {
    let long = String::from("长生命周期");
    let result;
    {
        let short = String::from("短生命周期");
        result = longer_lifetime(&long, &short);
        println!("在作用域内: {}", result);
    }
    // 这里 result 指向的 long 仍然有效
    println!("在作用域外: {}", result);
}
```

---

---

## 🆕 Rust 1.93.0 新特性

### MaybeUninit API 增强

**改进**: 新增多个安全操作方法

```rust
// Rust 1.93.0 新特性
use std::mem::MaybeUninit;

let mut uninit = MaybeUninit::<String>::uninit();

// ✅ 1.93 新增：安全地获取引用
let reference: &String = unsafe { uninit.assume_init_ref() };
let mutable: &mut String = unsafe { uninit.assume_init_mut() };

// ✅ 1.93 新增：安全地调用 drop
unsafe { uninit.assume_init_drop() };
```

### 切片到数组转换

```rust
// ✅ 1.93 新增：切片到数组的安全转换
let slice = &[1, 2, 3, 4];
let array: &[i32; 4] = slice.as_array().unwrap();
```

**影响**: 更安全的未初始化内存操作，更灵活的数组操作

---

## Rust 1.92.0 新特性（历史）

### const 上下文增强

**改进**: 支持对非静态常量的引用

```rust
// Rust 1.92.0 新特性
const fn get_value() -> i32 {
    42
}

const VALUE: i32 = get_value();
const REF: &i32 = &VALUE;  // ✅ 现在支持
```

**影响**: 更灵活的 const 泛型配置和编译时计算

---

## 📚 相关文档

- [类型系统完整文档](../../../crates/c02_type_system/docs/)
- [类型系统 README](../../../crates/c02_type_system/README.md)

## 🧩 相关示例代码

以下示例位于 `crates/c02_type_system/examples/`，可直接运行（例如：`cargo run -p c02_type_system --example type_system_example`）。

- [类型系统基础](../../../crates/c02_type_system/examples/type_system_example.rs)、[类型定义与等价](../../../crates/c02_type_system/examples/type_definition_examples.rs)、[type_equivalence_newtype_examples.rs](../../../crates/c02_type_system/examples/type_equivalence_newtype_examples.rs)
- [Trait 对象与型变](../../../crates/c02_type_system/examples/trait_objects_safety.rs)、[variance_examples.rs](../../../crates/c02_type_system/examples/variance_examples.rs)
- [Pin/自引用、Never 类型、模式匹配](../../../crates/c02_type_system/examples/pin_self_referential_basics.rs)、[never_type_control_flow.rs](../../../crates/c02_type_system/examples/never_type_control_flow.rs)、[pattern_matching_advanced.rs](../../../crates/c02_type_system/examples/pattern_matching_advanced.rs)
- [Rust 1.91/1.92 特性演示](../../../crates/c02_type_system/examples/rust_191_features_demo.rs)、[rust_192_features_demo.rs](../../../crates/c02_type_system/examples/rust_192_features_demo.rs)、[rust_192_comprehensive_demo.rs](../../../crates/c02_type_system/examples/rust_192_comprehensive_demo.rs)

---

## 📚 相关资源

### 官方文档

- [Rust 类型系统文档](https://doc.rust-lang.org/book/ch03-00-common-programming-concepts.html)
- [Rust Reference - Types](https://doc.rust-lang.org/reference/types.html)

### 项目内部文档

- [类型系统完整文档](../../../crates/c02_type_system/docs/)
- [类型系统研究笔记](../../research_notes/type_theory/)

### 相关速查卡

- [所有权系统速查卡](./ownership_cheatsheet.md) - 所有权与类型系统
- [泛型编程速查卡](./generics_cheatsheet.md) - 泛型与类型系统
- [模块系统速查卡](./modules_cheatsheet.md) - 模块中的类型
- [智能指针速查卡](./smart_pointers_cheatsheet.md) - 指针类型
- [错误处理速查卡](./error_handling_cheatsheet.md) - Result 和 Option 类型

---

**最后更新**: 2026-01-27
**Rust 版本**: 1.93.0+ (Edition 2024)

🔷 **Rust 类型系统，安全与表达力的极致！**
