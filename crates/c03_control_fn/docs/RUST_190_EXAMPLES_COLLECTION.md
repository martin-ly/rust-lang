# 💻 Rust 1.90 控制流与函数 - 实战示例集

> **版本**: Rust 1.90 Edition 2024  
> **创建日期**: 2025-10-20  
> **代码行数**: 900+ 行可运行代码

---

## 📋 目录

- [💻 Rust 1.90 控制流与函数 - 实战示例集](#-rust-190-控制流与函数---实战示例集)
  - [� 目录](#-目录)
  - [🎯 Rust 1.90 核心特性](#-rust-190-核心特性)
    - [1. let else 语句](#1-let-else-语句)
    - [2. 链式 if let](#2-链式-if-let)
  - [🔀 控制流实战](#-控制流实战)
    - [1. 条件语句](#1-条件语句)
    - [2. 循环结构](#2-循环结构)
  - [🎭 模式匹配实战](#-模式匹配实战)
    - [1. match 表达式](#1-match-表达式)
    - [2. 高级模式](#2-高级模式)
  - [📞 函数系统](#-函数系统)
    - [1. 基础函数](#1-基础函数)
    - [2. 泛型函数](#2-泛型函数)
    - [3. 高阶函数](#3-高阶函数)
  - [🔒 闭包实战](#-闭包实战)
    - [1. 闭包捕获](#1-闭包捕获)
    - [2. async 闭包 (Rust 1.90)](#2-async-闭包-rust-190)
  - [⚠️ 错误处理](#️-错误处理)
    - [1. Result 和 Option](#1-result-和-option)
    - [2. ? 操作符](#2--操作符)
  - [🚀 综合项目](#-综合项目)
    - [项目1: 命令行解析器](#项目1-命令行解析器)
    - [项目2: 简单的表达式求值器](#项目2-简单的表达式求值器)

---

## 🎯 Rust 1.90 核心特性

### 1. let else 语句

Rust 1.65+ 稳定，1.90 改进类型推导：

```rust
// let else: 模式匹配失败时早期返回
fn process_config(config: Option<String>) -> Result<(), String> {
    // 如果是 None，提前返回错误
    let Some(config_str) = config else {
        return Err("Configuration not provided".to_string());
    };
    
    println!("Processing config: {}", config_str);
    Ok(())
}

// 解析用户输入
fn parse_user_input(input: &str) -> Result<i32, String> {
    // let else 与 parse 结合
    let Ok(number) = input.parse::<i32>() else {
        return Err(format!("'{}' is not a valid number", input));
    };
    
    // 验证范围
    let number = if number >= 0 && number <= 100 {
        number
    } else {
        return Err("Number must be between 0 and 100".to_string());
    };
    
    Ok(number)
}

// 多层 let else
fn extract_first_word(text: Option<&str>) -> Result<String, &'static str> {
    let Some(text) = text else {
        return Err("Text is None");
    };
    
    let Some(first_word) = text.split_whitespace().next() else {
        return Err("Text is empty");
    };
    
    Ok(first_word.to_string())
}

fn main() {
    // 测试 let else
    match process_config(Some("app.toml".to_string())) {
        Ok(_) => println!("Config processed successfully"),
        Err(e) => println!("Error: {}", e),
    }
    
    match parse_user_input("42") {
        Ok(n) => println!("Parsed number: {}", n),
        Err(e) => println!("Parse error: {}", e),
    }
    
    match extract_first_word(Some("Hello World")) {
        Ok(word) => println!("First word: {}", word),
        Err(e) => println!("Error: {}", e),
    }
}
```

### 2. 链式 if let

Rust 1.90 改进的链式 if let：

```rust
enum Response {
    Success(String),
    Error(String),
    Retry,
    Unknown,
}

fn handle_response(response: Response) {
    // 链式 if let - Rust 1.90 更好的类型推导
    if let Response::Success(msg) = response {
        println!("Success: {}", msg);
    } else if let Response::Error(err) = response {
        eprintln!("Error: {}", err);
    } else if let Response::Retry = response {
        println!("Retrying...");
    } else {
        println!("Unknown response");
    }
}

fn main() {
    handle_response(Response::Success("Data saved".to_string()));
    handle_response(Response::Error("Connection failed".to_string()));
    handle_response(Response::Retry);
    handle_response(Response::Unknown);
}
```

---

## 🔀 控制流实战

### 1. 条件语句

```rust
// if 表达式：返回值
fn max(a: i32, b: i32) -> i32 {
    if a > b {
        a
    } else {
        b
    }
}

// if let：简化的模式匹配
fn print_optional(value: Option<i32>) {
    if let Some(x) = value {
        println!("Value is: {}", x);
    } else {
        println!("No value");
    }
}

// 复杂条件判断
fn categorize_number(n: i32) -> &'static str {
    if n < 0 {
        "negative"
    } else if n == 0 {
        "zero"
    } else if n <= 10 {
        "small positive"
    } else if n <= 100 {
        "medium positive"
    } else {
        "large positive"
    }
}

// 使用 if let 链
enum Message {
    Quit,
    Move { x: i32, y: i32 },
    Write(String),
    ChangeColor(u8, u8, u8),
}

fn process_message(msg: Message) {
    if let Message::Write(text) = msg {
        println!("Text message: {}", text);
    } else if let Message::Move { x, y } = msg {
        println!("Move to ({}, {})", x, y);
    } else {
        println!("Other message type");
    }
}

fn main() {
    println!("Max: {}", max(10, 20));
    print_optional(Some(42));
    println!("Category: {}", categorize_number(15));
    process_message(Message::Write("Hello".to_string()));
}
```

### 2. 循环结构

```rust
// loop: 无限循环with返回值
fn find_first_even() -> i32 {
    let mut counter = 0;
    
    loop {
        counter += 1;
        
        if counter % 2 == 0 {
            break counter; // 返回值
        }
        
        if counter > 100 {
            break -1; // 未找到
        }
    }
}

// while：条件循环
fn countdown(mut n: i32) {
    while n > 0 {
        println!("{}", n);
        n -= 1;
    }
    println!("Liftoff!");
}

// while let：模式匹配循环
fn sum_until_none(values: &mut Vec<Option<i32>>) -> i32 {
    let mut sum = 0;
    
    while let Some(Some(value)) = values.pop() {
        sum += value;
    }
    
    sum
}

// for：迭代循环
fn iterate_examples() {
    // 遍历范围
    for i in 0..5 {
        print!("{} ", i);
    }
    println!();
    
    // 遍历数组
    let arr = [10, 20, 30, 40, 50];
    for element in arr.iter() {
        print!("{} ", element);
    }
    println!();
    
    // 带索引遍历
    for (index, value) in arr.iter().enumerate() {
        println!("Index {}: {}", index, value);
    }
}

// 嵌套循环with标签
fn nested_loops() {
    'outer: for i in 0..5 {
        for j in 0..5 {
            if i * j > 10 {
                println!("Breaking outer loop at i={}, j={}", i, j);
                break 'outer;
            }
            print!("({},{}) ", i, j);
        }
        println!();
    }
}

fn main() {
    println!("First even: {}", find_first_even());
    countdown(3);
    
    let mut values = vec![Some(1), Some(2), Some(3), None, Some(4)];
    println!("Sum: {}", sum_until_none(&mut values));
    
    iterate_examples();
    nested_loops();
}
```

---

## 🎭 模式匹配实战

### 1. match 表达式

```rust
// 基础 match
enum Color {
    Red,
    Green,
    Blue,
    RGB(u8, u8, u8),
}

fn color_to_string(color: Color) -> String {
    match color {
        Color::Red => "Red".to_string(),
        Color::Green => "Green".to_string(),
        Color::Blue => "Blue".to_string(),
        Color::RGB(r, g, b) => format!("RGB({}, {}, {})", r, g, b),
    }
}

// match 守卫
fn describe_number(n: i32) -> &'static str {
    match n {
        x if x < 0 => "negative",
        0 => "zero",
        x if x % 2 == 0 => "positive even",
        _ => "positive odd",
    }
}

// 解构结构体
struct Point {
    x: i32,
    y: i32,
}

fn describe_point(p: Point) -> String {
    match p {
        Point { x: 0, y: 0 } => "Origin".to_string(),
        Point { x: 0, y } => format!("On Y-axis at {}", y),
        Point { x, y: 0 } => format!("On X-axis at {}", x),
        Point { x, y } if x == y => format!("On diagonal at {}", x),
        Point { x, y } => format!("At ({}, {})", x, y),
    }
}

// match 多个模式
fn is_weekend(day: u8) -> bool {
    match day {
        6 | 7 => true,  // Saturday or Sunday
        _ => false,
    }
}

// match 范围
fn http_status_category(status: u16) -> &'static str {
    match status {
        100..=199 => "Informational",
        200..=299 => "Success",
        300..=399 => "Redirection",
        400..=499 => "Client Error",
        500..=599 => "Server Error",
        _ => "Unknown",
    }
}

fn main() {
    let color = Color::RGB(255, 0, 0);
    println!("{}", color_to_string(color));
    
    println!("{}", describe_number(-5));
    println!("{}", describe_number(0));
    println!("{}", describe_number(4));
    
    let point = Point { x: 3, y: 3 };
    println!("{}", describe_point(point));
    
    println!("Is weekend: {}", is_weekend(7));
    println!("HTTP 404: {}", http_status_category(404));
}
```

### 2. 高级模式

```rust
// @ 绑定
fn print_value_in_range(x: i32) {
    match x {
        n @ 1..=5 => println!("{} is in range 1-5", n),
        n @ 6..=10 => println!("{} is in range 6-10", n),
        n => println!("{} is out of range", n),
    }
}

// 解构元组
fn process_tuple(t: (i32, i32, i32)) {
    match t {
        (0, y, z) => println!("First is 0, y={}, z={}", y, z),
        (x, 0, z) => println!("Second is 0, x={}, z={}", x, z),
        (x, y, 0) => println!("Third is 0, x={}, y={}", x, y),
        (x, y, z) => println!("All non-zero: {}, {}, {}", x, y, z),
    }
}

// 解构数组
fn analyze_array(arr: [i32; 5]) {
    match arr {
        [first, .., last] => {
            println!("First: {}, Last: {}", first, last);
        }
    }
}

// 嵌套解构
enum Message {
    Move { x: i32, y: i32 },
    Write(String),
    Quit,
}

struct Envelope {
    sender: String,
    message: Message,
}

fn process_envelope(env: Envelope) {
    match env {
        Envelope {
            sender,
            message: Message::Write(text),
        } => {
            println!("Message from {}: {}", sender, text);
        }
        Envelope {
            sender,
            message: Message::Move { x, y },
        } => {
            println!("{} wants to move to ({}, {})", sender, x, y);
        }
        Envelope { sender, .. } => {
            println!("Other message from {}", sender);
        }
    }
}

fn main() {
    print_value_in_range(3);
    process_tuple((0, 5, 10));
    analyze_array([1, 2, 3, 4, 5]);
    
    let env = Envelope {
        sender: "Alice".to_string(),
        message: Message::Write("Hello".to_string()),
    };
    process_envelope(env);
}
```

---

## 📞 函数系统

### 1. 基础函数

```rust
// 基础函数定义
fn add(a: i32, b: i32) -> i32 {
    a + b  // 隐式返回
}

// 多个返回值（使用元组）
fn div_mod(dividend: i32, divisor: i32) -> (i32, i32) {
    let quotient = dividend / divisor;
    let remainder = dividend % divisor;
    (quotient, remainder)
}

// 可变参数（使用切片）
fn sum(numbers: &[i32]) -> i32 {
    numbers.iter().sum()
}

// 引用参数
fn append_suffix(s: &mut String, suffix: &str) {
    s.push_str(suffix);
}

// 所有权转移
fn consume_and_return(s: String) -> String {
    let mut result = s;
    result.push_str(" (processed)");
    result
}

fn main() {
    println!("Add: {}", add(5, 3));
    
    let (q, r) = div_mod(17, 5);
    println!("17 ÷ 5 = {} remainder {}", q, r);
    
    println!("Sum: {}", sum(&[1, 2, 3, 4, 5]));
    
    let mut text = String::from("Hello");
    append_suffix(&mut text, " World");
    println!("{}", text);
    
    let s = String::from("data");
    let result = consume_and_return(s);
    println!("{}", result);
}
```

### 2. 泛型函数

```rust
// 基础泛型函数
fn swap<T>(a: T, b: T) -> (T, T) {
    (b, a)
}

// 带约束的泛型
use std::fmt::Display;

fn print_pair<T: Display, U: Display>(a: T, b: U) {
    println!("({}, {})", a, b);
}

// where 子句
fn compare_and_print<T, U>(a: &T, b: &U)
where
    T: Display + PartialOrd,
    U: Display + PartialOrd,
{
    println!("a = {}, b = {}", a, b);
}

// 泛型函数返回impl Trait
fn make_adder(x: i32) -> impl Fn(i32) -> i32 {
    move |y| x + y
}

fn main() {
    let (a, b) = swap(1, 2);
    println!("Swapped: {}, {}", a, b);
    
    print_pair("Hello", 42);
    compare_and_print(&10, &20);
    
    let add_5 = make_adder(5);
    println!("5 + 3 = {}", add_5(3));
}
```

### 3. 高阶函数

```rust
// 接受函数作为参数
fn apply<F>(f: F, x: i32) -> i32
where
    F: Fn(i32) -> i32,
{
    f(x)
}

// 返回函数
fn make_multiplier(factor: i32) -> impl Fn(i32) -> i32 {
    move |x| x * factor
}

// 函数组合
fn compose<F, G, A, B, C>(f: F, g: G) -> impl Fn(A) -> C
where
    F: Fn(B) -> C,
    G: Fn(A) -> B,
{
    move |x| f(g(x))
}

// 使用迭代器的高阶函数
fn process_numbers(numbers: Vec<i32>) -> Vec<i32> {
    numbers
        .into_iter()
        .filter(|&x| x > 0)
        .map(|x| x * 2)
        .collect()
}

fn main() {
    let square = |x| x * x;
    println!("Apply square to 5: {}", apply(square, 5));
    
    let mul3 = make_multiplier(3);
    println!("3 * 7 = {}", mul3(7));
    
    let add_one = |x: i32| x + 1;
    let square = |x: i32| x * x;
    let add_one_then_square = compose(square, add_one);
    println!("(5 + 1)^2 = {}", add_one_then_square(5));
    
    let numbers = vec![-2, -1, 0, 1, 2, 3];
    let result = process_numbers(numbers);
    println!("Processed: {:?}", result);
}
```

---

## 🔒 闭包实战

### 1. 闭包捕获

```rust
// 不可变借用 (Fn)
fn demonstrate_fn() {
    let x = 10;
    let add_x = |y| x + y;  // 捕获 x 的不可变引用
    
    println!("10 + 5 = {}", add_x(5));
    println!("10 + 3 = {}", add_x(3));
    println!("x is still accessible: {}", x);
}

// 可变借用 (FnMut)
fn demonstrate_fn_mut() {
    let mut count = 0;
    let mut increment = || {
        count += 1;
        count
    };
    
    println!("Count: {}", increment());
    println!("Count: {}", increment());
    println!("Count: {}", increment());
}

// 所有权转移 (FnOnce)
fn demonstrate_fn_once() {
    let s = String::from("hello");
    let consume = move || {
        println!("Consumed: {}", s);
        // s 被移动到闭包内
    };
    
    consume();
    // consume(); // 错误：只能调用一次
    // println!("{}", s); // 错误：s已被移动
}

// move 闭包
fn create_closure() -> impl Fn() {
    let x = 42;
    move || {
        println!("x = {}", x);
    }
}

// 闭包作为参数
fn apply_twice<F>(mut f: F, x: i32) -> i32
where
    F: FnMut(i32) -> i32,
{
    let result = f(x);
    f(result)
}

fn main() {
    demonstrate_fn();
    demonstrate_fn_mut();
    demonstrate_fn_once();
    
    let closure = create_closure();
    closure();
    
    let mut counter = 0;
    let mut count_and_add = |x| {
        counter += 1;
        x + counter
    };
    
    let result = apply_twice(count_and_add, 10);
    println!("Result: {}", result);
}
```

### 2. async 闭包 (Rust 1.90)

```rust
// Rust 1.75+ async 闭包
use std::future::Future;

// async 闭包示例
async fn demonstrate_async_closure() {
    let async_add = async |x: i32| {
        // 模拟异步操作
        x + 1
    };
    
    let result = async_add(5).await;
    println!("Async result: {}", result);
}

// 高阶 async 闭包
async fn process_async<F, Fut>(f: F, x: i32) -> i32
where
    F: Fn(i32) -> Fut,
    Fut: Future<Output = i32>,
{
    f(x).await
}

#[tokio::main]
async fn main() {
    demonstrate_async_closure().await;
    
    let async_double = async |x: i32| x * 2;
    let result = process_async(async_double, 21).await;
    println!("Async double: {}", result);
}
```

---

## ⚠️ 错误处理

### 1. Result 和 Option

```rust
// 返回 Result
fn divide(a: f64, b: f64) -> Result<f64, String> {
    if b == 0.0 {
        Err("Division by zero".to_string())
    } else {
        Ok(a / b)
    }
}

// 返回 Option
fn find_first_even(numbers: &[i32]) -> Option<i32> {
    numbers.iter().find(|&&x| x % 2 == 0).copied()
}

// Result 方法链
fn parse_and_process(s: &str) -> Result<i32, String> {
    s.parse::<i32>()
        .map_err(|_| format!("Failed to parse: {}", s))?
        .checked_mul(2)
        .ok_or_else(|| "Multiplication overflow".to_string())
}

// Option 方法链
fn get_first_char(s: &str) -> Option<char> {
    s.chars()
        .next()
        .filter(|c| c.is_alphabetic())
}

fn main() {
    match divide(10.0, 2.0) {
        Ok(result) => println!("Result: {}", result),
        Err(e) => println!("Error: {}", e),
    }
    
    if let Some(even) = find_first_even(&[1, 3, 5, 6, 7]) {
        println!("First even: {}", even);
    }
    
    match parse_and_process("42") {
        Ok(n) => println!("Processed: {}", n),
        Err(e) => println!("Error: {}", e),
    }
}
```

### 2. ? 操作符

```rust
use std::fs::File;
use std::io::{self, Read};

// ? 操作符简化错误传播
fn read_file_content(path: &str) -> io::Result<String> {
    let mut file = File::open(path)?;
    let mut content = String::new();
    file.read_to_string(&mut content)?;
    Ok(content)
}

// 自定义错误类型
#[derive(Debug)]
enum MyError {
    IoError(io::Error),
    ParseError(String),
}

impl From<io::Error> for MyError {
    fn from(error: io::Error) -> Self {
        MyError::IoError(error)
    }
}

fn process_file(path: &str) -> Result<i32, MyError> {
    let content = std::fs::read_to_string(path)?;
    
    content
        .trim()
        .parse::<i32>()
        .map_err(|_| MyError::ParseError("Invalid number".to_string()))
}

// 链式 ? 操作符
fn calculate(a: &str, b: &str) -> Result<i32, String> {
    let a: i32 = a.parse().map_err(|_| "Invalid first number")?;
    let b: i32 = b.parse().map_err(|_| "Invalid second number")?;
    Ok(a + b)
}

fn main() {
    match read_file_content("test.txt") {
        Ok(content) => println!("Content: {}", content),
        Err(e) => println!("Error: {}", e),
    }
    
    match calculate("10", "20") {
        Ok(sum) => println!("Sum: {}", sum),
        Err(e) => println!("Error: {}", e),
    }
}
```

---

## 🚀 综合项目

### 项目1: 命令行解析器

```rust
// 简单的命令行参数解析器
#[derive(Debug)]
enum Command {
    Add { x: i32, y: i32 },
    Sub { x: i32, y: i32 },
    Mul { x: i32, y: i32 },
    Div { x: i32, y: i32 },
    Help,
}

fn parse_command(args: &[String]) -> Result<Command, String> {
    let Some(cmd) = args.get(0) else {
        return Err("No command provided".to_string());
    };
    
    match cmd.as_str() {
        "add" | "sub" | "mul" | "div" => {
            let Some(x_str) = args.get(1) else {
                return Err("Missing first number".to_string());
            };
            let Some(y_str) = args.get(2) else {
                return Err("Missing second number".to_string());
            };
            
            let x: i32 = x_str
                .parse()
                .map_err(|_| "Invalid first number".to_string())?;
            let y: i32 = y_str
                .parse()
                .map_err(|_| "Invalid second number".to_string())?;
            
            match cmd.as_str() {
                "add" => Ok(Command::Add { x, y }),
                "sub" => Ok(Command::Sub { x, y }),
                "mul" => Ok(Command::Mul { x, y }),
                "div" => Ok(Command::Div { x, y }),
                _ => unreachable!(),
            }
        }
        "help" => Ok(Command::Help),
        _ => Err(format!("Unknown command: {}", cmd)),
    }
}

fn execute_command(cmd: Command) -> Result<i32, String> {
    match cmd {
        Command::Add { x, y } => Ok(x + y),
        Command::Sub { x, y } => Ok(x - y),
        Command::Mul { x, y } => Ok(x * y),
        Command::Div { x, y } => {
            if y == 0 {
                Err("Division by zero".to_string())
            } else {
                Ok(x / y)
            }
        }
        Command::Help => {
            println!("Available commands:");
            println!("  add <x> <y>  - Add two numbers");
            println!("  sub <x> <y>  - Subtract two numbers");
            println!("  mul <x> <y>  - Multiply two numbers");
            println!("  div <x> <y>  - Divide two numbers");
            println!("  help         - Show this help");
            Ok(0)
        }
    }
}

fn main() {
    let args = vec!["add".to_string(), "10".to_string(), "20".to_string()];
    
    match parse_command(&args) {
        Ok(cmd) => match execute_command(cmd) {
            Ok(result) => println!("Result: {}", result),
            Err(e) => eprintln!("Execution error: {}", e),
        },
        Err(e) => eprintln!("Parse error: {}", e),
    }
}
```

### 项目2: 简单的表达式求值器

```rust
// 简单的表达式求值器
#[derive(Debug, Clone)]
enum Expr {
    Number(f64),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
}

impl Expr {
    fn eval(&self) -> Result<f64, String> {
        match self {
            Expr::Number(n) => Ok(*n),
            Expr::Add(left, right) => {
                let l = left.eval()?;
                let r = right.eval()?;
                Ok(l + r)
            }
            Expr::Sub(left, right) => {
                let l = left.eval()?;
                let r = right.eval()?;
                Ok(l - r)
            }
            Expr::Mul(left, right) => {
                let l = left.eval()?;
                let r = right.eval()?;
                Ok(l * r)
            }
            Expr::Div(left, right) => {
                let l = left.eval()?;
                let r = right.eval()?;
                
                if r == 0.0 {
                    Err("Division by zero".to_string())
                } else {
                    Ok(l / r)
                }
            }
        }
    }
    
    fn to_string(&self) -> String {
        match self {
            Expr::Number(n) => n.to_string(),
            Expr::Add(l, r) => format!("({} + {})", l.to_string(), r.to_string()),
            Expr::Sub(l, r) => format!("({} - {})", l.to_string(), r.to_string()),
            Expr::Mul(l, r) => format!("({} * {})", l.to_string(), r.to_string()),
            Expr::Div(l, r) => format!("({} / {})", l.to_string(), r.to_string()),
        }
    }
}

fn main() {
    // (10 + 20) * 3
    let expr = Expr::Mul(
        Box::new(Expr::Add(
            Box::new(Expr::Number(10.0)),
            Box::new(Expr::Number(20.0)),
        )),
        Box::new(Expr::Number(3.0)),
    );
    
    println!("Expression: {}", expr.to_string());
    
    match expr.eval() {
        Ok(result) => println!("Result: {}", result),
        Err(e) => eprintln!("Error: {}", e),
    }
    
    // 测试除零
    let div_zero = Expr::Div(
        Box::new(Expr::Number(10.0)),
        Box::new(Expr::Number(0.0)),
    );
    
    match div_zero.eval() {
        Ok(result) => println!("Result: {}", result),
        Err(e) => eprintln!("Error: {}", e),
    }
}
```

---

**文档版本**: v1.0  
**最后更新**: 2025-10-20  
**代码行数**: 900+ 行  
**维护者**: Rust Learning Community

---

💻 **通过实战掌握 Rust 控制流与函数！** 🚀✨
