# 🔄 Rust 控制流与函数速查卡 {#-rust-控制流与函数速查卡}

> **快速参考** | [完整文档](../../../crates/c03_control_fn/docs/) | [代码示例](../../../crates/c03_control_fn/examples/)
> **创建日期**: 2026-01-27
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 📋 目录 {#-目录}

- [🔄 Rust 控制流与函数速查卡 {#-rust-控制流与函数速查卡}](#-rust-控制流与函数速查卡--rust-控制流与函数速查卡)
  - [📋 目录 {#-目录}](#-目录--目录)
  - [🎯 条件语句 {#-条件语句}](#-条件语句--条件语句)
    - [if 表达式](#if-表达式)
    - [match 表达式](#match-表达式)
    - [if let 表达式](#if-let-表达式)
    - [let-else 语句 (Rust 1.65+)](#let-else-语句-rust-165)
  - [🔁 循环结构 {#-循环结构}](#-循环结构--循环结构)
    - [loop 循环](#loop-循环)
    - [while 循环](#while-循环)
    - [for 循环](#for-循环)
    - [循环控制](#循环控制)
  - [🎭 模式匹配 {#-模式匹配}](#-模式匹配--模式匹配)
    - [基本模式](#基本模式)
    - [解构模式](#解构模式)
    - [引用模式](#引用模式)
  - [📝 函数定义 {#-函数定义}](#-函数定义--函数定义)
    - [基本函数](#基本函数)
    - [函数参数](#函数参数)
    - [函数返回值](#函数返回值)
    - [函数指针](#函数指针)
  - [🔒 闭包 {#-闭包}](#-闭包--闭包)
    - [基本闭包](#基本闭包)
    - [闭包捕获](#闭包捕获)
    - [闭包类型](#闭包类型)
    - [闭包作为参数](#闭包作为参数)
    - [闭包作为返回值](#闭包作为返回值)
  - [🎯 常用模式 {#-常用模式}](#-常用模式--常用模式)
    - [早期返回](#早期返回)
    - [链式调用](#链式调用)
    - [模式匹配与解构](#模式匹配与解构)
    - [函数式编程](#函数式编程)
    - [递归函数](#递归函数)
  - [🚫 反例速查 {#-反例速查}](#-反例速查--反例速查)
    - [反例 1: match 未覆盖所有分支](#反例-1-match-未覆盖所有分支)
    - [反例 2: 闭包捕获可变引用导致冲突](#反例-2-闭包捕获可变引用导致冲突)
  - [📚 相关文档 {#-相关文档}](#-相关文档--相关文档)
  - [🧩 相关示例代码 {#-相关示例代码}](#-相关示例代码--相关示例代码)
  - [📚 相关资源 {#-相关资源}](#-相关资源--相关资源)
    - [官方文档](#官方文档)
    - [项目内部文档](#项目内部文档)
    - [相关速查卡](#相关速查卡)
  - [💡 使用场景 {#-使用场景}](#-使用场景--使用场景)
    - [场景 1: 命令行参数解析](#场景-1-命令行参数解析)
    - [场景 2: 递归下降解析器](#场景-2-递归下降解析器)
    - [场景 3: 自定义迭代器](#场景-3-自定义迭代器)
  - [⚠️ 边界情况 {#️-边界情况}](#️-边界情况-️-边界情况)
    - [边界 1: 闭包捕获陷阱](#边界-1-闭包捕获陷阱)
    - [边界 2: 递归深度限制](#边界-2-递归深度限制)
    - [边界 3: 模式匹配穷尽性](#边界-3-模式匹配穷尽性)
    - [形式化理论](#形式化理论)

---

## 🎯 条件语句 {#-条件语句}

### if 表达式

```rust
// 基本 if
if condition {
    // 代码块
}

// if-else
if condition {
    // true 分支
} else {
    // false 分支
}

// if-else if-else
if condition1 {
    // 分支1
} else if condition2 {
    // 分支2
} else {
    // 默认分支
}

// if 作为表达式（必须返回相同类型）
let result = if condition {
    "true"
} else {
    "false"
};
```

### match 表达式

```rust
// 基本 match
match value {
    pattern1 => expression1,
    pattern2 => expression2,
    _ => default_expression,
}

// 匹配多个值
match number {
    1 | 2 | 3 => println!("小数字"),
    4..=10 => println!("中等数字"),
    _ => println!("大数字"),
}

// 带守卫的 match
match value {
    x if x > 0 => println!("正数"),
    x if x < 0 => println!("负数"),
    _ => println!("零"),
}

// 绑定变量
match value {
    Some(x) => println!("值: {}", x),
    None => println!("无值"),
}
```

### if let 表达式

```rust
// 基本 if let
if let Some(value) = option {
    println!("有值: {}", value);
}

// if let-else
if let Some(value) = option {
    println!("有值: {}", value);
} else {
    println!("无值");
}

// 链式 if let (Rust 1.93.0+)
if let Some(a) = option1 && let Some(b) = option2 {
    println!("都有值: {} {}", a, b);
}
```

### let-else 语句 (Rust 1.65+)

```rust
// 基本 let-else
let Some(value) = option else {
    return; // 或 panic! 或其他控制流
};

// 使用示例
fn process(value: Option<i32>) -> i32 {
    let Some(x) = value else {
        return 0;
    };
    x * 2
}
```

---

## 🔁 循环结构 {#-循环结构}

### loop 循环

```rust
// 无限循环
loop {
    // 代码
    if condition {
        break; // 退出循环
    }
}

// 返回值
let result = loop {
    counter += 1;
    if counter > 10 {
        break counter * 2; // 返回值
    }
};
```

### while 循环

```rust
// 基本 while
while condition {
    // 代码
}

// while let
while let Some(item) = iterator.next() {
    println!("{}", item);
}
```

### for 循环

```rust
// 遍历范围
for i in 1..=10 {
    println!("{}", i);
}

// 遍历集合
for item in vec {
    println!("{}", item);
}

// 遍历引用
for item in &vec {
    println!("{}", item);
}

// 遍历可变引用
for item in &mut vec {
    *item += 1;
}

// 带索引遍历
for (index, value) in vec.iter().enumerate() {
    println!("{}: {}", index, value);
}
```

### 循环控制

```rust
// break 和 continue
for i in 1..=10 {
    if i == 5 {
        continue; // 跳过本次循环
    }
    if i == 8 {
        break; // 退出循环
    }
    println!("{}", i);
}

// 循环标签
'outer: loop {
    'inner: loop {
        break 'outer; // 退出外层循环
    }
}
```

---

## 🎭 模式匹配 {#-模式匹配}

### 基本模式

```rust
// 字面量模式
match x {
    1 => println!("一"),
    2 => println!("二"),
    _ => println!("其他"),
}

// 变量模式
match x {
    y => println!("值: {}", y),
}

// 通配符模式
match x {
    _ => println!("忽略"),
}

// 范围模式
match x {
    1..=5 => println!("1到5"),
    6..=10 => println!("6到10"),
    _ => println!("其他"),
}
```

### 解构模式

```rust
// 元组解构
let tuple = (1, 2, 3);
match tuple {
    (x, y, z) => println!("{}, {}, {}", x, y, z),
}

// 结构体解构
struct Point { x: i32, y: i32 }
let point = Point { x: 0, y: 0 };
match point {
    Point { x, y } => println!("({}, {})", x, y),
    Point { x: 0, y } => println!("x=0, y={}", y),
}

// 枚举解构
enum Message {
    Quit,
    Move { x: i32, y: i32 },
    Write(String),
}
match msg {
    Message::Quit => println!("退出"),
    Message::Move { x, y } => println!("移动到 ({}, {})", x, y),
    Message::Write(s) => println!("写入: {}", s),
}
```

### 引用模式

```rust
// 引用模式
let value = Some(5);
match &value {
    Some(x) => println!("值: {}", x),
    None => println!("无值"),
}

// ref 和 ref mut
match value {
    ref r => println!("引用: {:p}", r),
}

match mut_value {
    ref mut m => *m = 10,
}
```

---

## 📝 函数定义 {#-函数定义}

### 基本函数

```rust
// 无参数无返回值
fn greet() {
    println!("Hello!");
}

// 有参数
fn add(a: i32, b: i32) {
    println!("{}", a + b);
}

// 有返回值
fn add(a: i32, b: i32) -> i32 {
    a + b  // 最后一行表达式作为返回值
}

// 显式 return
fn add(a: i32, b: i32) -> i32 {
    return a + b;
}
```

### 函数参数

```rust
// 值传递
fn take_ownership(s: String) {
    println!("{}", s);
}

// 引用传递
fn borrow(s: &String) {
    println!("{}", s);
}

// 可变引用
fn modify(s: &mut String) {
    s.push_str(" world");
}

// 多个参数
fn process(x: i32, y: i32, z: i32) -> i32 {
    x + y + z
}
```

### 函数返回值

```rust
// 返回单个值
fn get_value() -> i32 {
    42
}

// 返回元组
fn get_pair() -> (i32, String) {
    (42, "hello".to_string())
}

// 返回 Option
fn find_item() -> Option<i32> {
    Some(42)
}

// 返回 Result
fn parse_number(s: &str) -> Result<i32, std::num::ParseIntError> {
    s.parse()
}
```

### 函数指针

```rust
// 函数指针类型
fn add(a: i32, b: i32) -> i32 {
    a + b
}

let func: fn(i32, i32) -> i32 = add;
let result = func(1, 2);

// 作为参数
fn apply(f: fn(i32, i32) -> i32, x: i32, y: i32) -> i32 {
    f(x, y)
}
```

---

## 🔒 闭包 {#-闭包}

### 基本闭包

```rust
// 基本语法
let add = |x, y| x + y;
let result = add(1, 2);

// 带类型注解
let add = |x: i32, y: i32| -> i32 {
    x + y
};

// 多行闭包
let multiply = |x, y| {
    let result = x * y;
    result
};
```

### 闭包捕获

```rust
// 不可变借用
let x = 5;
let borrow = || println!("{}", x);

// 可变借用
let mut x = 5;
let mut_borrow = || {
    x += 1;
    println!("{}", x);
};

// 移动捕获
let x = vec![1, 2, 3];
let move_closure = move || {
    println!("{:?}", x);
};
// x 不再可用
```

### 闭包类型

```rust
// Fn - 不可变借用
fn call_fn<F: Fn()>(f: F) {
    f();
}

// FnMut - 可变借用
fn call_fn_mut<F: FnMut()>(mut f: F) {
    f();
}

// FnOnce - 获取所有权
fn call_fn_once<F: FnOnce()>(f: F) {
    f();
}
```

### 闭包作为参数

```rust
// 接受闭包
fn apply<F>(f: F) -> i32
where
    F: Fn(i32) -> i32,
{
    f(5)
}

// 使用示例
let double = |x| x * 2;
let result = apply(double);

// 内联闭包
let result = apply(|x| x * 3);
```

### 闭包作为返回值

```rust
// 返回闭包
fn make_adder(x: i32) -> impl Fn(i32) -> i32 {
    move |y| x + y
}

// 使用
let add5 = make_adder(5);
let result = add5(3); // 8
```

---

## 🎯 常用模式 {#-常用模式}

### 早期返回

```rust
fn process(value: Option<i32>) -> i32 {
    let Some(x) = value else {
        return 0;
    };
    x * 2
}
```

### 链式调用

```rust
// Option 链式调用
let result = Some(5)
    .map(|x| x * 2)
    .filter(|&x| x > 5)
    .unwrap_or(0);

// Result 链式调用
let result = "42"
    .parse::<i32>()
    .map(|x| x * 2)
    .map_err(|e| format!("错误: {}", e));
```

### 模式匹配与解构

```rust
// if let 解构
if let Some(x) = option {
    println!("{}", x);
}

// while let 解构
while let Some(item) = stack.pop() {
    process(item);
}

// match 解构
match result {
    Ok(value) => println!("成功: {}", value),
    Err(e) => println!("错误: {}", e),
}
```

### 函数式编程

```rust
// map
let doubled: Vec<i32> = vec![1, 2, 3]
    .iter()
    .map(|x| x * 2)
    .collect();

// filter
let evens: Vec<i32> = vec![1, 2, 3, 4, 5]
    .iter()
    .filter(|&&x| x % 2 == 0)
    .copied()
    .collect();

// fold
let sum: i32 = vec![1, 2, 3, 4, 5]
    .iter()
    .fold(0, |acc, x| acc + x);
```

### 递归函数

```rust
// 基本递归
fn factorial(n: u64) -> u64 {
    if n <= 1 {
        1
    } else {
        n * factorial(n - 1)
    }
}

// 尾递归（Rust 不保证尾递归优化）
fn factorial_tail(n: u64, acc: u64) -> u64 {
    if n <= 1 {
        acc
    } else {
        factorial_tail(n - 1, n * acc)
    }
}
```

---

## 🚫 反例速查 {#-反例速查}

### 反例 1: match 未覆盖所有分支

**错误示例**:

```rust
let x: Option<i32> = Some(1);
let _ = match x {
    Some(v) => v,  // ❌ 未处理 None
};
```

**原因**: match 必须穷尽所有可能。

**修正**:

```rust
let _ = match x {
    Some(v) => v,
    None => 0,
};
```

---

### 反例 2: 闭包捕获可变引用导致冲突

**错误示例**:

```rust
let mut v = vec![1, 2, 3];
let f = || v.push(4);  // ❌ 闭包可变借用 v
// let r = &v;  // 再借用会冲突
```

**原因**: 闭包捕获可变引用后，外部不能再借用。

**修正**:

```rust
let mut v = vec![1, 2, 3];
let mut f = || v.push(4);
f();
let _ = &v;
```

---

## 📚 相关文档 {#-相关文档}

- [控制流与函数完整文档](../../../crates/c03_control_fn/docs/)
- [控制流与函数 README](../../../crates/c03_control_fn/README.md)

## 🧩 相关示例代码 {#-相关示例代码}

以下示例位于 `crates/c03_control_fn/examples/`，可直接运行（例如：`cargo run -p c03_control_fn --example control_flow_example`）。

- [控制流基础与模式匹配](../../../crates/c03_control_fn/examples/control_flow_example.rs)、[control_flow_overview.rs](../../../crates/c03_control_fn/examples/control_flow_overview.rs)、[control_flow_pattern_matching.rs](../../../crates/c03_control_fn/examples/control_flow_pattern_matching.rs)
- [闭包与 let-else、循环](../../../crates/c03_control_fn/examples/closures_and_fn_traits.rs)、[let_else_patterns_handbook.rs](../../../crates/c03_control_fn/examples/let_else_patterns_handbook.rs)、[loops_and_iterators_control.rs](../../../crates/c03_control_fn/examples/loops_and_iterators_control.rs)
- [Rust 1.91/1.92 特性演示](../../../crates/c03_control_fn/examples/rust_191_features_demo.rs)、[rust_192_features_demo.rs](../../../crates/c03_control_fn/examples/rust_192_features_demo.rs)

---

## 📚 相关资源 {#-相关资源}

### 官方文档

- [Rust 控制流文档](https://doc.rust-lang.org/book/ch03-05-control-flow.html)
- [Rust 函数文档](https://doc.rust-lang.org/book/ch03-03-how-functions-work.html)
- [Rust 闭包文档](https://doc.rust-lang.org/book/ch13-01-closures.html)

### 项目内部文档

- [完整控制流文档](../../../crates/c03_control_fn/docs/)
- [控制流研究笔记](../../research_notes/)

### 相关速查卡

- [错误处理速查卡](./error_handling_cheatsheet.md) - 错误处理模式
- [类型系统速查卡](./type_system.md) - 类型与函数
- [集合与迭代器速查卡](./collections_iterators_cheatsheet.md) - 迭代器与循环
- [所有权系统速查卡](./ownership_cheatsheet.md) - 所有权与闭包

---

## 💡 使用场景 {#-使用场景}

### 场景 1: 命令行参数解析

```rust
fn parse_args(args: &[String]) -> Result<Config, &'static str> {
    // 使用 let-else 进行早期返回
    let Some(command) = args.get(1) else {
        return Err("缺少命令参数");
    };

    match command.as_str() {
        "add" => {
            let Some(name) = args.get(2) else {
                return Err("add 命令需要名称参数");
            };
            Ok(Config::Add(name.clone()))
        }
        "remove" => {
            let Some(id_str) = args.get(2) else {
                return Err("remove 命令需要 ID 参数");
            };
            let Ok(id) = id_str.parse::<u32>() else {
                return Err("ID 必须是数字");
            };
            Ok(Config::Remove(id))
        }
        _ => Err("未知命令"),
    }
}

#[derive(Debug)]
enum Config {
    Add(String),
    Remove(u32),
}

fn main() {
    let args: Vec<String> = vec![
        "program".to_string(),
        "add".to_string(),
        "task1".to_string(),
    ];

    match parse_args(&args) {
        Ok(config) => println!("配置: {:?}", config),
        Err(e) => println!("错误: {}", e),
    }
}
```

### 场景 2: 递归下降解析器

```rust
#[derive(Debug)]
enum Expr {
    Number(i32),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
}

fn parse_number(input: &str) -> Option<(Expr, &str)> {
    let end = input.find(|c: char| !c.is_ascii_digit()).unwrap_or(input.len());
    if end == 0 {
        return None;
    }
    let (num_str, rest) = input.split_at(end);
    let num = num_str.parse().ok()?;
    Some((Expr::Number(num), rest.trim_start()))
}

fn parse_expr(input: &str) -> Option<Expr> {
    let (mut left, mut rest) = parse_number(input)?;

    loop {
        rest = rest.trim_start();
        if rest.is_empty() {
            break;
        }

        let op = rest.chars().next()?;
        rest = &rest[1..];

        let (right, new_rest) = parse_number(rest.trim_start())?;

        left = match op {
            '+' => Expr::Add(Box::new(left), Box::new(right)),
            '-' => Expr::Sub(Box::new(left), Box::new(right)),
            _ => break,
        };
        rest = new_rest;
    }

    Some(left)
}

fn eval(expr: &Expr) -> i32 {
    match expr {
        Expr::Number(n) => *n,
        Expr::Add(a, b) => eval(a) + eval(b),
        Expr::Sub(a, b) => eval(a) - eval(b),
    }
}

fn main() {
    let input = "10 + 20 - 5";
    if let Some(expr) = parse_expr(input) {
        println!("表达式: {:?}", expr);
        println!("结果: {}", eval(&expr));
    }
}
```

### 场景 3: 自定义迭代器

```rust
struct Fibonacci {
    curr: u64,
    next: u64,
    max: u64,
}

impl Fibonacci {
    fn new(max: u64) -> Self {
        Fibonacci { curr: 0, next: 1, max }
    }
}

impl Iterator for Fibonacci {
    type Item = u64;

    fn next(&mut self) -> Option<Self::Item> {
        if self.curr > self.max {
            return None;
        }

        let current = self.curr;
        self.curr = self.next;
        self.next = current + self.next;

        Some(current)
    }
}

fn main() {
    let fib = Fibonacci::new(100);

    println!("斐波那契数列 (< 100):");
    for num in fib {
        print!("{} ", num);
    }
    println!();
}
```

---

## ⚠️ 边界情况 {#️-边界情况}

### 边界 1: 闭包捕获陷阱

```rust
fn main() {
    let mut count = 0;

    // 闭包捕获可变引用
    let mut increment = || {
        count += 1;
        count
    };

    // ❌ 编译错误：不能同时使用 count 和 increment
    // println!("{}", count);

    println!("{}", increment()); // 1
    println!("{}", increment()); // 2

    // 闭包不再使用，count 恢复可用
    drop(increment);
    println!("最终计数: {}", count); // 2
}
```

### 边界 2: 递归深度限制

```rust
fn recursive_sum(n: u64) -> u64 {
    if n == 0 {
        0
    } else {
        n + recursive_sum(n - 1) // 可能栈溢出
    }
}

// 尾递归优化（Rust 不保证）
fn tail_recursive_sum(n: u64, acc: u64) -> u64 {
    if n == 0 {
        acc
    } else {
        tail_recursive_sum(n - 1, acc + n)
    }
}

fn main() {
    // 小数字 OK
    println!("递归求和 100: {}", recursive_sum(100));

    // 大数字使用迭代
    let sum: u64 = (1..=100000).sum();
    println!("迭代求和 100000: {}", sum);
}
```

### 边界 3: 模式匹配穷尽性

```rust
enum Shape {
    Circle { radius: f64 },
    Rectangle { width: f64, height: f64 },
    Triangle { base: f64, height: f64 },
}

fn area(shape: &Shape) -> f64 {
    match shape {
        Shape::Circle { radius } => std::f64::consts::PI * radius * radius,
        Shape::Rectangle { width, height } => width * height,
        Shape::Triangle { base, height } => 0.5 * base * height,
    }  // 编译器确保穷尽所有变体
}

fn main() {
    let shapes = vec![
        Shape::Circle { radius: 5.0 },
        Shape::Rectangle { width: 4.0, height: 6.0 },
        Shape::Triangle { base: 3.0, height: 4.0 },
    ];

    for shape in &shapes {
        println!("面积: {:.2}", area(shape));
    }
}
```

### 形式化理论

- [借用检查器证明](../../research_notes/formal_methods/borrow_checker_proof.md) — 控制流相关的借用规则证明
- [Send/Sync 形式化](../../research_notes/formal_methods/send_sync_formalization.md) — 闭包在多线程环境下的安全性

---

**最后更新**: 2026-01-27
**维护者**: 文档团队
**状态**: ✅ **Rust 1.93.0 更新完成**

🎯 **掌握控制流，编写清晰代码！**
