# Trait 与多态（Traits and Polymorphism）

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: ✅ 已完善

---

## 📊 目录

- [Trait 与多态（Traits and Polymorphism）](#trait-与多态traits-and-polymorphism)
  - [📊 目录](#-目录)
  - [概述](#概述)
  - [Trait 基础](#trait-基础)
    - [定义 Trait](#定义-trait)
    - [默认实现](#默认实现)
  - [多态实现](#多态实现)
    - [静态分发（Static Dispatch）](#静态分发static-dispatch)
    - [动态分发（Dynamic Dispatch）](#动态分发dynamic-dispatch)
  - [Trait 对象](#trait-对象)
    - [Trait 对象的限制](#trait-对象的限制)
    - [使用 Trait 对象](#使用-trait-对象)
  - [泛型与 Trait](#泛型与-trait)
    - [Trait Bound](#trait-bound)
    - [多个 Trait Bound](#多个-trait-bound)
    - [where 子句](#where-子句)
  - [组合优于继承](#组合优于继承)
    - [使用组合](#使用组合)
    - [使用 Trait 实现接口](#使用-trait-实现接口)
  - [实践示例](#实践示例)
    - [示例 1：策略模式](#示例-1策略模式)
    - [示例 2：状态模式](#示例-2状态模式)
  - [参考资料](#参考资料)

---

## 概述

Rust 通过 Trait 系统实现面向对象编程中的多态性。虽然 Rust 不支持传统继承，但 Trait 提供了更灵活和类型安全的多态机制。

## Trait 基础

### 定义 Trait

```rust
// 定义 Draw trait
trait Draw {
    fn draw(&self);
}

// 为类型实现 Trait
struct Circle {
    radius: f64,
}

impl Draw for Circle {
    fn draw(&self) {
        println!("绘制圆形，半径: {}", self.radius);
    }
}

struct Rectangle {
    width: f64,
    height: f64,
}

impl Draw for Rectangle {
    fn draw(&self) {
        println!("绘制矩形，宽: {}, 高: {}", self.width, self.height);
    }
}
```

### 默认实现

Trait 可以提供默认实现：

```rust
trait Summary {
    fn summarize(&self) -> String {
        String::from("(阅读更多...)")
    }
}

struct NewsArticle {
    headline: String,
    location: String,
    author: String,
    content: String,
}

impl Summary for NewsArticle {
    // 使用默认实现
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
```

## 多态实现

### 静态分发（Static Dispatch）

使用泛型实现静态分发，编译时确定具体类型：

```rust
fn draw_shape<T: Draw>(shape: &T) {
    shape.draw();
}

// 使用
let circle = Circle { radius: 5.0 };
let rectangle = Rectangle { width: 10.0, height: 20.0 };

draw_shape(&circle);
draw_shape(&rectangle);
```

### 动态分发（Dynamic Dispatch）

使用 Trait 对象实现动态分发，运行时确定具体类型：

```rust
fn draw_shapes(shapes: &[Box<dyn Draw>]) {
    for shape in shapes {
        shape.draw();
    }
}

// 使用
let shapes: Vec<Box<dyn Draw>> = vec![
    Box::new(Circle { radius: 5.0 }),
    Box::new(Rectangle { width: 10.0, height: 20.0 }),
];

draw_shapes(&shapes);
```

## Trait 对象

### Trait 对象的限制

Trait 对象必须是对象安全的（Object Safe）：

```rust
// 对象安全的 Trait
trait Draw {
    fn draw(&self);
}

// 非对象安全的 Trait（包含泛型方法）
trait NotObjectSafe {
    fn method<T>(&self, x: T); // 错误：不能作为 Trait 对象
}
```

### 使用 Trait 对象

```rust
// 函数参数
fn process_drawable(drawable: &dyn Draw) {
    drawable.draw();
}

// 返回值
fn create_shape(shape_type: &str) -> Box<dyn Draw> {
    match shape_type {
        "circle" => Box::new(Circle { radius: 5.0 }),
        "rectangle" => Box::new(Rectangle { width: 10.0, height: 20.0 }),
        _ => panic!("未知形状"),
    }
}

// 集合
let shapes: Vec<Box<dyn Draw>> = vec![
    Box::new(Circle { radius: 5.0 }),
    Box::new(Rectangle { width: 10.0, height: 20.0 }),
];
```

## 泛型与 Trait

### Trait Bound

使用 Trait Bound 约束泛型类型：

```rust
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

### 多个 Trait Bound

```rust
use std::fmt::Display;

fn notify<T: Summary + Display>(item: &T) {
    println!("{}", item);
    println!("{}", item.summarize());
}
```

### where 子句

使用 `where` 子句使函数签名更清晰：

```rust
fn some_function<T, U>(t: &T, u: &U) -> i32
where
    T: Display + Clone,
    U: Clone + Debug,
{
    // 函数体
}
```

## 组合优于继承

### 使用组合

Rust 不支持继承，鼓励使用组合：

```rust
// 基础结构
struct Engine {
    power: u32,
}

impl Engine {
    fn start(&self) {
        println!("引擎启动，功率: {} 马力", self.power);
    }
}

// 组合
struct Car {
    engine: Engine,
    brand: String,
}

impl Car {
    fn new(brand: String, power: u32) -> Self {
        Car {
            engine: Engine { power },
            brand,
        }
    }

    fn drive(&self) {
        self.engine.start();
        println!("{} 汽车行驶中", self.brand);
    }
}
```

### 使用 Trait 实现接口

```rust
trait Vehicle {
    fn start(&self);
    fn stop(&self);
}

struct Bicycle;

impl Vehicle for Bicycle {
    fn start(&self) {
        println!("自行车开始骑行");
    }

    fn stop(&self) {
        println!("自行车停止");
    }
}

struct Motorcycle {
    engine: Engine,
}

impl Vehicle for Motorcycle {
    fn start(&self) {
        self.engine.start();
        println!("摩托车启动");
    }

    fn stop(&self) {
        println!("摩托车停止");
    }
}
```

## 实践示例

### 示例 1：策略模式

```rust
trait PaymentStrategy {
    fn pay(&self, amount: f64) -> bool;
}

struct CreditCard {
    number: String,
}

impl PaymentStrategy for CreditCard {
    fn pay(&self, amount: f64) -> bool {
        println!("使用信用卡 {} 支付 {:.2}", self.number, amount);
        true
    }
}

struct PayPal {
    email: String,
}

impl PaymentStrategy for PayPal {
    fn pay(&self, amount: f64) -> bool {
        println!("使用 PayPal {} 支付 {:.2}", self.email, amount);
        true
    }
}

struct ShoppingCart {
    items: Vec<f64>,
    payment_strategy: Box<dyn PaymentStrategy>,
}

impl ShoppingCart {
    fn checkout(&self) {
        let total: f64 = self.items.iter().sum();
        self.payment_strategy.pay(total);
    }
}
```

### 示例 2：状态模式

```rust
trait State {
    fn handle(&self) -> Box<dyn State>;
}

struct StateA;

impl State for StateA {
    fn handle(&self) -> Box<dyn State> {
        println!("处理状态 A");
        Box::new(StateB)
    }
}

struct StateB;

impl State for StateB {
    fn handle(&self) -> Box<dyn State> {
        println!("处理状态 B");
        Box::new(StateA)
    }
}

struct StateMachine {
    state: Box<dyn State>,
}

impl StateMachine {
    fn new() -> Self {
        StateMachine {
            state: Box::new(StateA),
        }
    }

    fn transition(&mut self) {
        self.state = self.state.handle();
    }
}
```

## 参考资料

- [Rust Trait 文档](https://doc.rust-lang.org/book/ch10-02-traits.html)
- [Trait 对象文档](https://doc.rust-lang.org/book/ch17-02-trait-objects.html)
- [设计模式实现](../../../crates/c09_design_pattern/)

---

**导航**:

- 返回索引: [`00_index.md`](./00_index.md)
- 返回编程范式: [`../00_index.md`](../00_index.md)
