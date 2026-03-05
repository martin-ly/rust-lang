# 惯用Rust模式

> **Rust版本**: 1.93.1
> **主题**: 编写地道Rust代码的模式与技巧
> **目标**: 掌握Rust特有的编程范式，写出符合社区习惯的代码

---

## 目录

- [惯用Rust模式](#惯用rust模式)
  - [目录](#目录)
  - [1. 引言](#1-引言)
    - [什么是惯用Rust](#什么是惯用rust)
    - [与其他语言的差异](#与其他语言的差异)
  - [2. Option组合子模式](#2-option组合子模式)
    - [2.1 map](#21-map)
    - [2.2 and\_then](#22-and_then)
    - [2.3 unwrap\_or / unwrap\_or\_else](#23-unwrap_or--unwrap_or_else)
    - [2.4 ok\_or / ok\_or\_else](#24-ok_or--ok_or_else)
    - [2.5 filter / map\_or](#25-filter--map_or)
    - [2.6 组合子链式调用](#26-组合子链式调用)
  - [3. Result传播模式](#3-result传播模式)
    - [3.1 ?操作符](#31-操作符)
    - [3.2 try\_trait与自定义类型](#32-try_trait与自定义类型)
    - [3.3 map\_err错误转换](#33-map_err错误转换)
    - [3.4 错误上下文](#34-错误上下文)
  - [4. 借用与转换模式](#4-借用与转换模式)
    - [4.1 AsRef模式](#41-asref模式)
    - [4.2 Borrow模式](#42-borrow模式)
    - [4.3 ToOwned模式](#43-toowned模式)
    - [4.4 泛型参数设计](#44-泛型参数设计)
  - [5. 类型转换模式](#5-类型转换模式)
    - [5.1 From/Into](#51-frominto)
    - [5.2 TryFrom/TryInto](#52-tryfromtryinto)
    - [5.3 AsRef/AsMut](#53-asrefasmut)
  - [6. 迭代器模式](#6-迭代器模式)
    - [6.1 惰性求值](#61-惰性求值)
    - [6.2 消费器与适配器](#62-消费器与适配器)
    - [6.3 collect策略](#63-collect策略)
    - [6.4 fold与reduce](#64-fold与reduce)
    - [6.5 自定义迭代器](#65-自定义迭代器)
  - [7. 闭包与函数式模式](#7-闭包与函数式模式)
    - [7.1 Fn/FnMut/FnOnce](#71-fnfnmutfnonce)
    - [7.2 高阶函数](#72-高阶函数)
    - [7.3 闭包捕获](#73-闭包捕获)
  - [8. 智能指针模式](#8-智能指针模式)
    - [8.1 Box](#81-box)
    - [8.2 Rc/Arc](#82-rcarc)
    - [8.3 RefCell/Mutex/RwLock](#83-refcellmutexrwlock)
    - [8.4 Cow](#84-cow)
  - [9. 生命周期模式](#9-生命周期模式)
    - [9.1 生命周期省略](#91-生命周期省略)
    - [9.2 生命周期约束](#92-生命周期约束)
    - [9.3 'static](#93-static)
  - [10. 最佳实践总结](#10-最佳实践总结)
    - [错误处理检查清单](#错误处理检查清单)
    - [Option使用检查清单](#option使用检查清单)
    - [类型设计检查清单](#类型设计检查清单)
    - [迭代器检查清单](#迭代器检查清单)
    - [性能检查清单](#性能检查清单)
  - [参考资源](#参考资源)

---

## 1. 引言

### 什么是惯用Rust

惯用Rust（Idiomatic Rust）是指符合Rust语言哲学和社区实践的编程方式。它不仅仅是"能运行的代码"，而是：

- 充分利用Rust的类型系统
- 遵循所有权和借用规则
- 使用标准库提供的抽象
- 零成本抽象原则
- 显式优于隐式

```rust
// 非惯用方式
fn process(input: Option<String>) -> String {
    match input {
        Some(s) => s.to_uppercase(),
        None => String::new(),
    }
}

// 惯用方式
fn process(input: Option<String>) -> String {
    input.map(|s| s.to_uppercase()).unwrap_or_default()
}
```

### 与其他语言的差异

| 概念 | 其他语言 | Rust惯用方式 |
|------|---------|-------------|
| 空值 | null | `Option<T>` |
| 异常 | try-catch | Result<T, E> + ? |
| 继承 | class extends | Trait + 组合 |
| 泛型约束 | where T extends X | where T: X |
| 资源释放 | finally/手动 | RAII/Drop |

---

## 2. Option组合子模式

Option是Rust处理可能缺失值的惯用方式。
组合子（combinators）提供了声明式的操作方式。

### 2.1 map

`map`将`Option<T>`转换为`Option<U>`，在Some时应用函数，None时保持None。

```rust
fn parse_number(s: &str) -> Option<i32> {
    s.parse().ok()
}

fn double_if_positive(n: i32) -> Option<i32> {
    if n > 0 { Some(n * 2) } else { None }
}

// 链式使用
let result: Option<i32> = Some("42")
    .and_then(|s| s.parse().ok())
    .and_then(double_if_positive)
    .map(|n| n + 1);

assert_eq!(result, Some(85));
```

**与match对比**:

```rust
// 命令式
fn imperative(input: Option<String>) -> Option<usize> {
    match input {
        Some(s) => {
            if s.is_empty() {
                None
            } else {
                Some(s.len())
            }
        }
        None => None,
    }
}

// 声明式
fn declarative(input: Option<String>) -> Option<usize> {
    input.filter(|s| !s.is_empty()).map(|s| s.len())
}
```

### 2.2 and_then

`and_then`（也叫`flat_map`）用于当转换函数本身返回Option时，避免嵌套Option。

```rust
struct User {
    id: u64,
    email: Option<String>,
}

struct Database;

impl Database {
    fn find_user(&self, id: u64) -> Option<User> {
        // 模拟查询
        Some(User {
            id,
            email: Some("user@example.com".to_string()),
        })
    }
}

fn get_user_email(db: &Database, user_id: u64) -> Option<String> {
    // 错误：会返回Option<Option<String>>
    // db.find_user(user_id).map(|u| u.email)

    // 正确：使用and_then展平
    db.find_user(user_id).and_then(|u| u.email)
}
```

### 2.3 unwrap_or / unwrap_or_else

提供默认值，但不panic。

```rust
let config_timeout: Option<u64> = None;

// 使用固定默认值
let timeout = config_timeout.unwrap_or(30);

// 使用惰性计算（当默认值创建成本高时）
let timeout = config_timeout.unwrap_or_else(|| {
    println!("Loading default from config file...");
    load_default_timeout()
});

// 使用Default trait
let timeout: u64 = config_timeout.unwrap_or_default();
```

### 2.4 ok_or / ok_or_else

将Option转换为Result，为None时提供错误。

```rust
fn find_user(db: &Database, id: u64) -> Result<User, String> {
    db.get_user(id).ok_or_else(|| format!("User {} not found", id))
}

// 对比
let result1: Result<i32, &str> = Some(42).ok_or("was None");        // Ok(42)
let result2: Result<i32, &str> = None.ok_or("was None");            // Err("was None")
```

### 2.5 filter / map_or

```rust
// filter: 仅当满足条件时保持Some
let maybe_positive = Some(5)
    .filter(|&n| n > 0);  // Some(5)

let maybe_positive = Some(-5)
    .filter(|&n| n > 0);  // None

// map_or: 提供默认值并转换
let len = Some("hello")
    .map_or(0, |s| s.len());  // 5

let len = None
    .map_or(0, |s: &str| s.len());  // 0
```

### 2.6 组合子链式调用

```rust
fn process_user_input(input: &str) -> Result<String, String> {
    input
        .trim()                                   // &str
        .is_empty()                               // bool
        .then(|| None)                            // Option<Option<_>>
        .flatten()                                // Option<_>
        .unwrap_or_else(|| {
            input
                .parse::<i32>()                   // Result<i32, _>
                .ok()                             // Option<i32>
                .filter(|&n| n >= 0 && n <= 100)  // Option<i32>
                .map(|n| format!("Score: {}", n)) // Option<String>
        })
        .ok_or_else(|| "Invalid input".to_string()) // Result<String, _>
}
```

---

## 3. Result传播模式

### 3.1 ?操作符

`?`操作符是Rust错误处理的核心，在Err时提前返回，Ok时解包。

```rust
use std::fs::File;
use std::io::{self, Read};

// 不使用?
fn read_file_contents_v1(path: &str) -> Result<String, io::Error> {
    match File::open(path) {
        Ok(mut file) => {
            let mut contents = String::new();
            match file.read_to_string(&mut contents) {
                Ok(_) => Ok(contents),
                Err(e) => Err(e),
            }
        }
        Err(e) => Err(e),
    }
}

// 使用?
fn read_file_contents_v2(path: &str) -> Result<String, io::Error> {
    let mut file = File::open(path)?;
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;
    Ok(contents)
}

// 链式
fn read_file_contents_v3(path: &str) -> Result<String, io::Error> {
    let mut contents = String::new();
    File::open(path)?.read_to_string(&mut contents)?;
    Ok(contents)
}
```

**?与Option**:

```rust
fn parse_then_divide(a: &str, b: &str) -> Option<i32> {
    let a: i32 = a.parse().ok()?;
    let b: i32 = b.parse().ok()?;
    a.checked_div(b)
}
```

### 3.2 try_trait与自定义类型

```rust
use std::ops::ControlFlow;

// 自定义Result类型
#[derive(Debug)]
struct MyError {
    code: u32,
    message: String,
}

type MyResult<T> = Result<T, MyError>;

impl MyError {
    fn new(code: u32, message: &str) -> Self {
        Self {
            code,
            message: message.to_string(),
        }
    }
}

// 使用
fn operation1() -> MyResult<i32> {
    Ok(42)
}

fn operation2() -> MyResult<String> {
    let val = operation1()?;
    Ok(val.to_string())
}
```

### 3.3 map_err错误转换

```rust
use std::num::ParseIntError;
use std::str::Utf8Error;

#[derive(Debug)]
enum AppError {
    ParseError(String),
    IoError(std::io::Error),
    Utf8Error(Utf8Error),
}

impl From<std::io::Error> for AppError {
    fn from(e: std::io::Error) -> Self {
        AppError::IoError(e)
    }
}

fn parse_config(input: &str) -> Result<Vec<i32>, AppError> {
    input
        .lines()
        .map(|line| {
            line.parse()
                .map_err(|e: ParseIntError| {
                    AppError::ParseError(format!("Failed to parse '{}': {}", line, e))
                })
        })
        .collect()
}
```

### 3.4 错误上下文

```rust
use std::fmt;

#[derive(Debug)]
struct ContextualError {
    context: String,
    source: Box<dyn std::error::Error>,
}

impl fmt::Display for ContextualError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.context, self.source)
    }
}

impl std::error::Error for ContextualError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&*self.source)
    }
}

trait ResultExt<T, E> {
    fn with_context<F>(self, f: F) -> Result<T, ContextualError>
    where
        F: FnOnce() -> String;
}

impl<T, E: std::error::Error + 'static> ResultExt<T, E> for Result<T, E> {
    fn with_context<F>(self, f: F) -> Result<T, ContextualError>
    where
        F: FnOnce() -> String,
    {
        self.map_err(|e| ContextualError {
            context: f(),
            source: Box::new(e),
        })
    }
}

// 使用
fn read_config(path: &str) -> Result<String, ContextualError> {
    std::fs::read_to_string(path)
        .with_context(|| format!("Failed to read config from {}", path))
}
```

---

## 4. 借用与转换模式

### 4.1 AsRef模式

`AsRef<T>`用于泛化地接受借用。

```rust
use std::path::Path;
use std::fs::File;

// 接受任何可以转换为&Path的类型
fn open_file<P: AsRef<Path>>(path: P) -> Result<File, std::io::Error> {
    File::open(path)
}

// 以下调用都有效
open_file("/etc/passwd");                       // &str
open_file(String::from("/etc/passwd"));         // String
open_file(std::path::Path::new("/etc/passwd")); // &Path
open_file(std::path::PathBuf::from("/etc/passwd")); // PathBuf
```

### 4.2 Borrow模式

`Borrow<T>`强调语义等价性，常用于HashMap键。

```rust
use std::borrow::Borrow;
use std::collections::HashMap;

fn get_value<K, Q, V>(map: &HashMap<K, V>, key: &Q) -> Option<&V>
where
    K: Borrow<Q> + Eq + std::hash::Hash,
    Q: Eq + std::hash::Hash + ?Sized,
{
    map.get(key)
}

// 使用
let mut map: HashMap<String, i32> = HashMap::new();
map.insert("key".to_string(), 42);

// 可以用&str查询String键
let value = get_value(&map, "key");
```

### 4.3 ToOwned模式

`ToOwned`从借用创建拥有值。

```rust
use std::borrow::ToOwned;

fn ensure_owned<T: ToOwned + ?Sized>(borrowed: &T) -> T::Owned {
    borrowed.to_owned()
}

// 使用
let s: String = ensure_owned("hello");
let v: Vec<i32> = ensure_owned(&[1, 2, 3]);
```

### 4.4 泛型参数设计

```rust
// 灵活的字符串参数
fn process_text<S>(input: S) -> String
where
    S: AsRef<str> + Into<String>,
{
    // AsRef<str>用于读取
    let lower = input.as_ref().to_lowercase();

    // Into<String>用于获取所有权
    let owned: String = input.into();

    format!("{} -> {}", lower, owned)
}
```

---

## 5. 类型转换模式

### 5.1 From/Into

`From<T>`和`Into<T>`是Rust类型转换的基础。

```rust
// 实现From自动获得Into
#[derive(Debug)]
struct Port(u16);

impl From<u16> for Port {
    fn from(value: u16) -> Self {
        Port(value)
    }
}

impl From<Port> for u16 {
    fn from(port: Port) -> Self {
        port.0
    }
}

// 使用
let port: Port = 8080.into();
let num: u16 = port.into();

// 函数参数中使用
fn connect(port: impl Into<Port>) {
    let port: Port = port.into();
    println!("Connecting to port {:?}", port);
}

connect(8080u16);  // 自动转换
connect(Port(8080)); // 已经是Port
```

### 5.2 TryFrom/TryInto

当转换可能失败时使用。

```rust
use std::convert::TryFrom;

#[derive(Debug)]
struct NonZeroU32(u32);

#[derive(Debug)]
struct ZeroError;

impl TryFrom<u32> for NonZeroU32 {
    type Error = ZeroError;

    fn try_from(value: u32) -> Result<Self, Self::Error> {
        if value == 0 {
            Err(ZeroError)
        } else {
            Ok(NonZeroU32(value))
        }
    }
}

// 使用
let result: Result<NonZeroU32, _> = 5u32.try_into();  // Ok
let result: Result<NonZeroU32, _> = 0u32.try_into();  // Err
```

### 5.3 AsRef/AsMut

用于廉价引用转换。

```rust
// 为自定义类型实现AsRef
struct Buffer {
    data: Vec<u8>,
}

impl AsRef<[u8]> for Buffer {
    fn as_ref(&self) -> &[u8] {
        &self.data
    }
}

impl AsMut<[u8]> for Buffer {
    fn as_mut(&mut self) -> &mut [u8] {
        &mut self.data
    }
}

// 泛化函数
fn process_bytes<B: AsRef<[u8]>>(buffer: B) -> usize {
    buffer.as_ref().len()
}
```

---

## 6. 迭代器模式

### 6.1 惰性求值

Rust迭代器是惰性的，只有在消费时才执行。

```rust
let result: Vec<i32> = (0..100)
    .map(|x| {
        println!("Processing {}", x);
        x * 2
    })
    .filter(|&x| x > 50)
    .take(5)
    .collect();

// 只处理到足够产生5个元素为止
```

### 6.2 消费器与适配器

```rust
// 消费器（产生最终结果）
let sum: i32 = (1..=10).sum();
let product: i32 = (1..=5).product();
let max: Option<i32> = [3, 1, 4, 1, 5].iter().max();
let min: Option<i32> = [3, 1, 4, 1, 5].iter().min();
let count: usize = [1, 2, 3].iter().count();
let found: bool = [1, 2, 3].iter().any(|&x| x > 2);
let all_match: bool = [2, 4, 6].iter().all(|&x| x % 2 == 0);

// 适配器（返回新迭代器）
let doubled: Vec<i32> = [1, 2, 3].iter().map(|&x| x * 2).collect();
let evens: Vec<i32> = [1, 2, 3, 4].iter().copied().filter(|&x| x % 2 == 0).collect();
let first_three: Vec<i32> = (1..100).take(3).collect();
let skip_first: Vec<i32> = [1, 2, 3, 4].iter().copied().skip(2).collect();
let enumerated: Vec<(usize, i32)> = [10, 20, 30].iter().copied().enumerate().collect();
let chained: Vec<i32> = [1, 2].iter().chain([3, 4].iter()).copied().collect();
let zipped: Vec<(i32, i32)> = [1, 2].iter().zip([10, 20].iter()).map(|(&a, &b)| (a, b)).collect();
```

### 6.3 collect策略

```rust
use std::collections::{HashSet, HashMap, BTreeMap};

let data = vec![1, 2, 3, 2, 1];

// 收集到不同容器
let vec: Vec<i32> = data.iter().copied().collect();
let set: HashSet<i32> = data.iter().copied().collect();

// 收集到Map
let map: HashMap<i32, i32> = data
    .iter()
    .enumerate()
    .map(|(i, &v)| (v, i as i32))
    .collect();

// 使用collect_with（需要itertools）
// let grouped: HashMap<i32, Vec<i32>> = data
//     .iter()
//     .copied()
//     .into_group_map_by(|&x| x % 2);
```

### 6.4 fold与reduce

```rust
// fold（有初始值）
let sum = [1, 2, 3, 4].iter().fold(0, |acc, &x| acc + x);

// 自定义数据结构
let words = vec!["hello", "world", "rust"];
let sentence = words.iter().fold(
    String::new(),
    |mut acc, &word| {
        if !acc.is_empty() {
            acc.push(' ');
        }
        acc.push_str(word);
        acc
    }
);

// reduce（无初始值，返回Option）
let max = [3, 1, 4, 1, 5].iter().reduce(|acc, &x| if x > *acc { &x } else { acc });

// try_fold（提前返回）
let result: Result<i32, &str> = [1, 2, 3, 4].iter().try_fold(0, |acc, &x| {
    if x == 3 {
        Err("Found 3!")
    } else {
        Ok(acc + x)
    }
});
```

### 6.5 自定义迭代器

```rust
struct Fibonacci {
    curr: u64,
    next: u64,
}

impl Fibonacci {
    fn new() -> Self {
        Self { curr: 0, next: 1 }
    }
}

impl Iterator for Fibonacci {
    type Item = u64;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.curr;
        self.curr = self.next;
        self.next = current + self.next;
        Some(current)
    }
}

// 使用
let fib: Vec<u64> = Fibonacci::new().take(10).collect();
println!("{:?}", fib); // [0, 1, 1, 2, 3, 5, 8, 13, 21, 34]
```

---

## 7. 闭包与函数式模式

### 7.1 Fn/FnMut/FnOnce

```rust
fn apply_fn<F>(f: F, x: i32) -> i32
where
    F: Fn(i32) -> i32,
{
    f(x)
}

fn apply_fn_mut<F>(mut f: F, x: i32) -> i32
where
    F: FnMut(i32) -> i32,
{
    f(x)
}

fn apply_fn_once<F>(f: F, x: i32) -> i32
where
    F: FnOnce(i32) -> i32,
{
    f(x)
}

// 使用示例
let n = 5;

// Fn: 只读捕获
let add_n = |x| x + n;
apply_fn(add_n, 10);
apply_fn(add_n, 20);  // 可以多次调用

// FnMut: 可变捕获
let mut count = 0;
let mut increment = |x| {
    count += 1;
    x + count
};
apply_fn_mut(&mut increment, 10);
apply_fn_mut(&mut increment, 20);

// FnOnce: 消费捕获
let s = String::from("hello");
let consume = |x| x + s.len() as i32;
apply_fn_once(consume, 10);
// consume(20);  // 错误：已被消费
```

### 7.2 高阶函数

```rust
// 返回闭包
fn make_multiplier(factor: i32) -> impl Fn(i32) -> i32 {
    move |x| x * factor
}

// 条件选择函数
fn choose_operation(use_add: bool) -> Box<dyn Fn(i32, i32) -> i32> {
    if use_add {
        Box::new(|a, b| a + b)
    } else {
        Box::new(|a, b| a - b)
    }
}

// 函数组合
fn compose<F, G, T, U, V>(f: F, g: G) -> impl Fn(T) -> V
where
    F: Fn(U) -> V,
    G: Fn(T) -> U,
{
    move |x| f(g(x))
}

// 使用
let add_one = |x| x + 1;
let double = |x| x * 2;
let add_one_then_double = compose(double, add_one);
assert_eq!(add_one_then_double(5), 12);
```

### 7.3 闭包捕获

```rust
// 移动语义
let s = String::from("hello");
let closure = move || println!("{}", s);
// s被移动，后续不能使用s
closure();

// 借用语义
let data = vec![1, 2, 3];
let sum = || data.iter().sum::<i32>();
println!("Sum: {}", sum());
println!("Data still available: {:?}", data);

// 在并发中使用move
use std::thread;

let data = vec![1, 2, 3];
let handle = thread::spawn(move || {
    data.iter().sum::<i32>()
});
let result = handle.join().unwrap();
```

---

## 8. 智能指针模式

### 8.1 Box

```rust
// 递归类型
enum List<T> {
    Cons(T, Box<List<T>>),
    Nil,
}

// 大对象转移
fn process_large_data() -> Box<[u8; 1024 * 1024]> {
    Box::new([0u8; 1024 * 1024])
}

// trait对象
trait Drawable {
    fn draw(&self);
}

fn create_drawable(kind: &str) -> Box<dyn Drawable> {
    match kind {
        "circle" => Box::new(Circle),
        "rect" => Box::new(Rectangle),
        _ => panic!("Unknown kind"),
    }
}

struct Circle;
struct Rectangle;

impl Drawable for Circle {
    fn draw(&self) { println!("Drawing circle"); }
}

impl Drawable for Rectangle {
    fn draw(&self) { println!("Drawing rectangle"); }
}
```

### 8.2 Rc/Arc

```rust
use std::rc::Rc;
use std::sync::Arc;
use std::thread;

// 单线程引用计数
let data = Rc::new(vec![1, 2, 3]);
let data2 = Rc::clone(&data);
let data3 = Rc::clone(&data);

println!("Reference count: {}", Rc::strong_count(&data));  // 3

// 多线程原子引用计数
let data = Arc::new(vec![1, 2, 3]);
let handles: Vec<_> = (0..3)
    .map(|i| {
        let data = Arc::clone(&data);
        thread::spawn(move || {
            println!("Thread {}: {:?}", i, data);
        })
    })
    .collect();

for handle in handles {
    handle.join().unwrap();
}
```

### 8.3 RefCell/Mutex/RwLock

```rust
use std::cell::RefCell;
use std::sync::{Mutex, RwLock};

// 单线程内部可变性
let cell = RefCell::new(5);
{
    let mut val = cell.borrow_mut();
    *val += 1;
}
println!("{}", cell.borrow());  // 6

// 多线程互斥
let counter = Mutex::new(0);
{
    let mut num = counter.lock().unwrap();
    *num += 1;
}
println!("{}", *counter.lock().unwrap());  // 1

// 读写锁
let data = RwLock::new(vec![1, 2, 3]);
{
    let mut write = data.write().unwrap();
    write.push(4);
}
{
    let read = data.read().unwrap();
    println!("{:?}", *read);  // [1, 2, 3, 4]
}
```

### 8.4 Cow

```rust
use std::borrow::Cow;

// 写时克隆
fn process_string(input: &str) -> Cow<str> {
    if input.contains(' ') {
        // 需要修改，执行分配
        Cow::Owned(input.replace(' ', "_"))
    } else {
        // 不需要修改，借用即可
        Cow::Borrowed(input)
    }
}

// 使用
let borrowed = process_string("hello");  // 无分配
let owned = process_string("hello world");  // 需要分配

// 通用参数
fn process_bytes<B: AsRef<[u8]>>(input: B) -> Cow<'static, [u8]> {
    let bytes = input.as_ref();
    if bytes.is_empty() {
        Cow::Borrowed(b"default")
    } else {
        Cow::Owned(bytes.to_vec())
    }
}
```

---

## 9. 生命周期模式

### 9.1 生命周期省略

```rust
// 编译器可以自动推导的生命周期
fn first_word(s: &str) -> &str {  // 输入和输出生命周期相同
    &s[0..s.find(' ').unwrap_or(s.len())]
}

// 展开后
fn first_word_explicit<'a>(s: &'a str) -> &'a str {
    &s[0..s.find(' ').unwrap_or(s.len())]
}

// 多条输入时不能省略
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}
```

### 9.2 生命周期约束

```rust
// 结构体生命周期
struct Parser<'a> {
    input: &'a str,
    position: usize,
}

impl<'a> Parser<'a> {
    fn new(input: &'a str) -> Self {
        Self { input, position: 0 }
    }

    fn remaining(&self) -> &'a str {
        &self.input[self.position..]
    }
}

// 生命周期约束
struct Ref<'a, T: 'a>(&'a T);  // T必须至少存活'a

// 多重约束
fn longest_with_an_announcement<'a, T>(
    x: &'a str,
    y: &'a str,
    ann: T,
) -> &'a str
where
    T: std::fmt::Display,
{
    println!("Announcement! {}", ann);
    if x.len() > y.len() { x } else { y }
}
```

### 9.3 'static

```rust
// 'static表示整个程序生命周期

// 字符串字面量是'static
let s: &'static str = "hello";

// Box<T> where T: 'static 拥有数据
let owned: Box<dyn std::any::Any + 'static> = Box::new(5);

// 线程边界需要'static
use std::thread;
let data = String::from("hello");
thread::spawn(move || {
    println!("{}", data);  // move使data变为'static
}).join().unwrap();

// 错误：借用不能进入线程
// let data = String::from("hello");
// thread::spawn(|| {
//     println!("{}", data);
// });
```

---

## 10. 最佳实践总结

### 错误处理检查清单

- [ ] 使用`?`传播错误，而非显式match
- [ ] 使用`map_err`添加错误上下文
- [ ] 实现`From` trait进行错误转换
- [ ] 使用`thiserror`或`anyhow`简化错误处理

### Option使用检查清单

- [ ] 优先使用组合子而非match
- [ ] 使用`unwrap_or`/`unwrap_or_else`提供默认值
- [ ] 使用`ok_or`将Option转为Result
- [ ] 避免在库代码中使用`unwrap()`

### 类型设计检查清单

- [ ] 为自定义类型实现`Default`
- [ ] 为有意义转换实现`From`/`Into`
- [ ] 为可能失败转换实现`TryFrom`/`TryInto`
- [ ] 为泛型接口实现`AsRef`/`AsMut`

### 迭代器检查清单

- [ ] 利用惰性求值，避免中间集合
- [ ] 使用`collect`指定目标类型
- [ ] 对于大数据考虑使用`rayon`并行化
- [ ] 实现自定义`Iterator`时考虑`DoubleEndedIterator`和`ExactSizeIterator`

### 性能检查清单

- [ ] 使用`Cow`避免不必要克隆
- [ ] 使用`&str`/`&[T]`而非`String`/`Vec`
- [ ] 优先栈分配，必要时使用`Box`
- [ ] 减少`Rc<RefCell<T>>`使用

---

## 参考资源

- [The Rust Programming Language - 迭代器](https://doc.rust-lang.org/book/ch13-02-iterators.html)
- [The Rust Programming Language - 闭包](https://doc.rust-lang.org/book/ch13-01-closures.html)
- [Rust By Example - 错误处理](https://doc.rust-lang.org/rust-by-example/error.html)
- [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)
- [This Week in Rust - 惯用Rust](https://this-week-in-rust.org/)
