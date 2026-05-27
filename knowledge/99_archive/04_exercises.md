# Rust 编程练习集
>
> **相关概念**: [Rc](../../concept/02_intermediate/03_memory_management.md)

> **Bloom 层级**: 理解

本练习集包含从入门到专家级的 Rust 编程练习题，涵盖所有权、生命周期、泛型、特质、异步编程等核心概念。建议按顺序完成，逐步提升 Rust 编程能力。

---

## 入门练习 ⭐
>
> **[来源: Rust Official Docs]**

掌握 Rust 的所有权系统和基础语法。

### 练习 1: 所有权转移
>
> **[来源: Rust Official Docs]**

**描述**: 理解 Rust 的所有权转移机制。

**要求**: 修复以下代码，使其能够编译通过。

```rust,compile_fail
fn main() {
    let s = String::from("hello");
    take_ownership(s);
    println!("{}", s); // 这里会报错，如何修复？
}

fn take_ownership(s: String) {
    println!("{}", s);
}
```

<details>
<summary>💡 解答</summary>

```rust
fn main() {
    let s = String::from("hello");
    take_ownership(s.clone()); // 方案1: 克隆
    println!("{}", s);

    // 方案2: 使用引用
    let s2 = String::from("world");
    borrow_string(&s2);
    println!("{}", s2);
}

fn take_ownership(s: String) {
    println!("{}", s);
}

fn borrow_string(s: &String) {
    println!("{}", s);
}
```

</details>

---

### 练习 2: 可变引用
>
> **[来源: Rust Official Docs]**

**描述**: 掌握可变引用的使用规则。

**要求**: 实现一个函数，接收字符串的可变引用并将其内容转换为大写。

```rust
fn to_uppercase(s: &mut String) {
    // 实现这里
}

fn main() {
    let mut s = String::from("hello");
    to_uppercase(&mut s);
    assert_eq!(s, "HELLO");
}
```

<details>
<summary>💡 解答</summary>

```rust
fn to_uppercase(s: &mut String) {
    *s = s.to_uppercase();
}

fn main() {
    let mut s = String::from("hello");
    to_uppercase(&mut s);
    assert_eq!(s, "HELLO");
    println!("✓ 测试通过!");
}
```

</details>

---

### 练习 3: 生命周期基础
>
> **[来源: Rust Official Docs]**

**描述**: 理解生命周期的基本概念。

**要求**: 为函数添加正确的生命周期标注。

```rust,compile_fail
fn longest(x: &str, y: &str) -> &str {
    if x.len() > y.len() { x } else { y }
}

fn main() {
    let s1 = String::from("abc");
    let s2 = "xy";
    println!("最长的字符串是: {}", longest(&s1, s2));
}
```

<details>
<summary>💡 解答</summary>

```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}

fn main() {
    let s1 = String::from("abc");
    let s2 = "xy";
    println!("最长的字符串是: {}", longest(&s1, s2));
}
```

</details>

---

### 练习 4: 结构体与所有权
>
> **[来源: Rust Official Docs]**

**描述**: 在结构体中管理所有权。

**要求**: 实现一个 `Person` 结构体，包含姓名和年龄字段。

```rust,compile_fail
struct Person {
    // 实现这里
}

impl Person {
    fn new(name: &str, age: u32) -> Self {
        // 实现这里
    }

    fn greet(&self) -> String {
        // 实现这里
    }
}

fn main() {
    let p = Person::new("张三", 25);
    assert_eq!(p.greet(), "你好，我是张三，今年25岁");
}
```

<details>
<summary>💡 解答</summary>

```rust
struct Person {
    name: String,
    age: u32,
}

impl Person {
    fn new(name: &str, age: u32) -> Self {
        Self {
            name: name.to_string(),
            age,
        }
    }

    fn greet(&self) -> String {
        format!("你好，我是{}，今年{}岁", self.name, self.age)
    }
}

fn main() {
    let p = Person::new("张三", 25);
    assert_eq!(p.greet(), "你好，我是张三，今年25岁");
    println!("✓ 测试通过!");
}
```

</details>

---

### 练习 5: Slice 类型

**描述**: 掌握字符串 slice 和数组 slice 的使用。

**要求**: 实现一个函数，返回字符串的第一个单词。

```rust,compile_fail
fn first_word(s: &str) -> &str {
    // 实现这里
}

fn main() {
    let s = String::from("hello world");
    assert_eq!(first_word(&s), "hello");

    let s2 = "rust programming";
    assert_eq!(first_word(s2), "rust");
}
```

<details>
<summary>💡 解答</summary>

```rust
fn first_word(s: &str) -> &str {
    match s.find(' ') {
        Some(idx) => &s[..idx],
        None => s,
    }
}

fn main() {
    let s = String::from("hello world");
    assert_eq!(first_word(&s), "hello");

    let s2 = "rust programming";
    assert_eq!(first_word(s2), "rust");

    println!("✓ 测试通过!");
}
```

</details>

---

## 基础练习 ⭐⭐

深入理解迭代器和集合类型。

### 练习 6: 迭代器适配器

**描述**: 使用迭代器适配器处理集合数据。

**要求**: 使用迭代器计算一组数字中所有偶数的平方和。

```rust,compile_fail
fn sum_of_even_squares(numbers: &[i32]) -> i32 {
    // 实现这里，使用迭代器方法链
}

fn main() {
    let nums = vec![1, 2, 3, 4, 5, 6];
    assert_eq!(sum_of_even_squares(&nums), 56); // 4 + 16 + 36 = 56
}
```

<details>
<summary>💡 解答</summary>

```rust
fn sum_of_even_squares(numbers: &[i32]) -> i32 {
    numbers
        .iter()
        .filter(|&&x| x % 2 == 0)
        .map(|&x| x * x)
        .sum()
}

fn main() {
    let nums = vec![1, 2, 3, 4, 5, 6];
    assert_eq!(sum_of_even_squares(&nums), 56);
    println!("✓ 测试通过!");
}
```

</details>

---

### 练习 7: HashMap 统计

**描述**: 使用 HashMap 进行数据统计。

**要求**: 统计一段文本中每个单词出现的次数。

```rust,compile_fail
use std::collections::HashMap;

fn word_count(text: &str) -> HashMap<String, u32> {
    // 实现这里
}

fn main() {
    let text = "hello world hello rust";
    let counts = word_count(text);
    assert_eq!(counts.get("hello"), Some(&2));
    assert_eq!(counts.get("world"), Some(&1));
}
```

<details>
<summary>💡 解答</summary>

```rust
use std::collections::HashMap;

fn word_count(text: &str) -> HashMap<String, u32> {
    let mut map = HashMap::new();
    for word in text.split_whitespace() {
        *map.entry(word.to_string()).or_insert(0) += 1;
    }
    map
}

fn main() {
    let text = "hello world hello rust";
    let counts = word_count(text);
    assert_eq!(counts.get("hello"), Some(&2));
    assert_eq!(counts.get("world"), Some(&1));
    println!("✓ 测试通过!");
}
```

</details>

---

### 练习 8: 自定义迭代器

**描述**: 实现一个简单的斐波那契数列迭代器。

**要求**: 创建一个可以生成前 N 个斐波那契数的迭代器。

```rust,compile_fail
struct Fibonacci {
    // 实现这里
}

impl Fibonacci {
    fn new() -> Self {
        // 实现这里
    }
}

impl Iterator for Fibonacci {
    type Item = u64;

    fn next(&mut self) -> Option<Self::Item> {
        // 实现这里
    }
}

fn main() {
    let fib: Vec<u64> = Fibonacci::new().take(10).collect();
    assert_eq!(fib, vec![0, 1, 1, 2, 3, 5, 8, 13, 21, 34]);
}
```

<details>
<summary>💡 解答</summary>

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

fn main() {
    let fib: Vec<u64> = Fibonacci::new().take(10).collect();
    assert_eq!(fib, vec![0, 1, 1, 2, 3, 5, 8, 13, 21, 34]);
    println!("✓ 测试通过!");
}
```

</details>

---

### 练习 9: Vec 排序与去重

**描述**: 对 Vec 进行排序并移除重复元素。

**要求**: 实现一个函数，接收整数向量，返回有序且不包含重复元素的向量。

```rust,compile_fail
fn sort_and_deduplicate(nums: Vec<i32>) -> Vec<i32> {
    // 实现这里
}

fn main() {
    let nums = vec![3, 1, 4, 1, 5, 9, 2, 6, 5, 3];
    assert_eq!(sort_and_deduplicate(nums), vec![1, 2, 3, 4, 5, 6, 9]);
}
```

<details>
<summary>💡 解答</summary>

```rust
fn sort_and_deduplicate(nums: Vec<i32>) -> Vec<i32> {
    let mut nums = nums;
    nums.sort();
    nums.dedup();
    nums
}

fn main() {
    let nums = vec![3, 1, 4, 1, 5, 9, 2, 6, 5, 3];
    assert_eq!(sort_and_deduplicate(nums), vec![1, 2, 3, 4, 5, 6, 9]);
    println!("✓ 测试通过!");
}
```

</details>

---

### 练习 10: BTreeMap 范围查询

**描述**: 使用 BTreeMap 进行高效的范围查询。

**要求**: 创建一个存储学生成绩的系统，支持按分数范围查询学生。

```rust,compile_fail
use std::collections::BTreeMap;

struct GradeBook {
    grades: BTreeMap<String, u32>,
}

impl GradeBook {
    fn new() -> Self {
        Self { grades: BTreeMap::new() }
    }

    fn add(&mut self, name: &str, grade: u32) {
        // 实现这里
    }

    fn students_with_grade_between(&self, low: u32, high: u32) -> Vec<&String> {
        // 实现这里
    }
}

fn main() {
    let mut book = GradeBook::new();
    book.add("Alice", 85);
    book.add("Bob", 92);
    book.add("Carol", 78);
    book.add("David", 88);

    let good_students = book.students_with_grade_between(80, 90);
    assert!(good_students.contains(&&"Alice".to_string()));
    assert!(good_students.contains(&&"David".to_string()));
}
```

<details>
<summary>💡 解答</summary>

```rust,compile_fail
use std::collections::BTreeMap;

struct GradeBook {
    grades: BTreeMap<String, u32>,
}

impl GradeBook {
    fn new() -> Self {
        Self { grades: BTreeMap::new() }
    }

    fn add(&mut self, name: &str, grade: u32) {
        self.grades.insert(name.to_string(), grade);
    }

    fn students_with_grade_between(&self, low: u32, high: u32) -> Vec<&String> {
        self.grades
            .iter()
            .filter(|(_, &grade)| grade >= low && grade <= high)
            .map(|(name, _)| name)
            .collect()
    }
}

fn main() {
    let mut book = GradeBook::new();
    book.add("Alice", 85);
    book.add("Bob", 92);
    book.add("Carol", 78);
    book.add("David", 88);

    let good_students = book.students_with_grade_between(80, 90);
    assert!(good_students.contains(&&"Alice".to_string()));
    assert!(good_students.contains(&&"David".to_string()));
    println!("✓ 测试通过!");
}
```

</details>

---

## 进阶练习 ⭐⭐⭐

掌握泛型、特质和错误处理。

### 练习 11: 泛型函数

**描述**: 实现一个泛型的二分查找函数。

**要求**: 函数应适用于任何有序类型。

```rust,compile_fail
fn binary_search<T: Ord>(arr: &[T], target: &T) -> Option<usize> {
    // 实现这里
}

fn main() {
    let nums = vec![1, 3, 5, 7, 9, 11, 13];
    assert_eq!(binary_search(&nums, &7), Some(3));
    assert_eq!(binary_search(&nums, &4), None);

    let words = vec!["apple", "banana", "cherry", "date"];
    assert_eq!(binary_search(&words, &"cherry"), Some(2));
}
```

<details>
<summary>💡 解答</summary>

```rust
fn binary_search<T: Ord>(arr: &[T], target: &T) -> Option<usize> {
    let mut left = 0;
    let mut right = arr.len();

    while left < right {
        let mid = left + (right - left) / 2;
        match arr[mid].cmp(target) {
            std::cmp::Ordering::Equal => return Some(mid),
            std::cmp::Ordering::Less => left = mid + 1,
            std::cmp::Ordering::Greater => right = mid,
        }
    }
    None
}

fn main() {
    let nums = vec![1, 3, 5, 7, 9, 11, 13];
    assert_eq!(binary_search(&nums, &7), Some(3));
    assert_eq!(binary_search(&nums, &4), None);

    let words = vec!["apple", "banana", "cherry", "date"];
    assert_eq!(binary_search(&words, &"cherry"), Some(2));

    println!("✓ 测试通过!");
}
```

</details>

---

### 练习 12: 自定义错误类型

**描述**: 实现一个自定义错误类型用于文件解析。

**要求**: 创建一个可以表示不同错误情况的枚举，并实现 Error 特质。

```rust,compile_fail
use std::error::Error;
use std::fmt;

#[derive(Debug)]
enum ParseError {
    // 实现这里
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // 实现这里
    }
}

impl Error for ParseError {}

fn parse_number(s: &str) -> Result<i32, ParseError> {
    // 实现这里
}

fn main() {
    assert!(parse_number("42").is_ok());
    assert!(parse_number("abc").is_err());
}
```

<details>
<summary>💡 解答</summary>

```rust
use std::error::Error;
use std::fmt;

#[derive(Debug)]
enum ParseError {
    EmptyInput,
    InvalidFormat(String),
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ParseError::EmptyInput => write!(f, "输入为空"),
            ParseError::InvalidFormat(s) => write!(f, "无效格式: {}", s),
        }
    }
}

impl Error for ParseError {}

fn parse_number(s: &str) -> Result<i32, ParseError> {
    if s.is_empty() {
        return Err(ParseError::EmptyInput);
    }
    s.parse()
        .map_err(|_| ParseError::InvalidFormat(s.to_string()))
}

fn main() {
    assert!(parse_number("42").is_ok());
    assert!(parse_number("abc").is_err());
    println!("✓ 测试通过!");
}
```

</details>

---

### 练习 13: 特质对象与动态分发

**描述**: 使用特质对象实现简单的图形渲染系统。

**要求**: 定义 Drawable 特质，创建多个图形类型，统一渲染。

```rust
trait Drawable {
    fn draw(&self);
    fn area(&self) -> f64;
}

struct Circle { radius: f64 }
struct Rectangle { width: f64, height: f64 }

// 为 Circle 和 Rectangle 实现 Drawable

fn render_all(shapes: &[Box<dyn Drawable>]) {
    for shape in shapes {
        shape.draw();
        println!("面积: {:.2}", shape.area());
    }
}

fn main() {
    let shapes: Vec<Box<dyn Drawable>> = vec![
        // 创建 Circle 和 Rectangle
    ];
    render_all(&shapes);
}
```

<details>
<summary>💡 解答</summary>

```rust
trait Drawable {
    fn draw(&self);
    fn area(&self) -> f64;
}

struct Circle { radius: f64 }
struct Rectangle { width: f64, height: f64 }

impl Drawable for Circle {
    fn draw(&self) {
        println!("绘制圆形，半径: {}", self.radius);
    }

    fn area(&self) -> f64 {
        std::f64::consts::PI * self.radius * self.radius
    }
}

impl Drawable for Rectangle {
    fn draw(&self) {
        println!("绘制矩形，{} x {}", self.width, self.height);
    }

    fn area(&self) -> f64 {
        self.width * self.height
    }
}

fn render_all(shapes: &[Box<dyn Drawable>]) {
    for shape in shapes {
        shape.draw();
        println!("面积: {:.2}", shape.area());
    }
}

fn main() {
    let shapes: Vec<Box<dyn Drawable>> = vec![
        Box::new(Circle { radius: 5.0 }),
        Box::new(Rectangle { width: 4.0, height: 6.0 }),
    ];
    render_all(&shapes);
}
```

</details>

---

### 练习 14: 关联类型

**描述**: 使用关联类型实现图遍历器。

**要求**: 定义 Graph 特质，使用关联类型表示节点和边。

```rust,compile_fail
trait Graph {
    type Node;
    type Edge;

    fn nodes(&self) -> Vec<Self::Node>;
    fn edges(&self) -> Vec<Self::Edge>;
}

struct SimpleGraph {
    adjacency_list: Vec<Vec<usize>>,
}

impl Graph for SimpleGraph {
    // 实现这里
}

fn main() {
    let graph = SimpleGraph {
        adjacency_list: vec![vec![1, 2], vec![0], vec![0]],
    };
    println!("节点数: {}", graph.nodes().len());
}
```

<details>
<summary>💡 解答</summary>

```rust
trait Graph {
    type Node;
    type Edge;

    fn nodes(&self) -> Vec<Self::Node>;
    fn edges(&self) -> Vec<Self::Edge>;
}

struct SimpleGraph {
    adjacency_list: Vec<Vec<usize>>,
}

impl Graph for SimpleGraph {
    type Node = usize;
    type Edge = (usize, usize);

    fn nodes(&self) -> Vec<Self::Node> {
        (0..self.adjacency_list.len()).collect()
    }

    fn edges(&self) -> Vec<Self::Edge> {
        let mut edges = Vec::new();
        for (from, neighbors) in self.adjacency_list.iter().enumerate() {
            for &to in neighbors {
                edges.push((from, to));
            }
        }
        edges
    }
}

fn main() {
    let graph = SimpleGraph {
        adjacency_list: vec![vec![1, 2], vec![0], vec![0]],
    };
    println!("节点数: {}", graph.nodes().len());
    println!("边数: {}", graph.edges().len());
}
```

</details>

---

### 练习 15: 运算符重载

**描述**: 为自定义复数类型实现运算符重载。

**要求**: 实现 Add、Sub、Mul 等运算符。

```rust,compile_fail
use std::ops::{Add, Sub, Mul};

#[derive(Debug, Clone, Copy, PartialEq)]
struct Complex {
    real: f64,
    imag: f64,
}

impl Complex {
    fn new(real: f64, imag: f64) -> Self {
        Self { real, imag }
    }
}

// 实现 Add、Sub、Mul

fn main() {
    let a = Complex::new(1.0, 2.0);
    let b = Complex::new(3.0, 4.0);

    assert_eq!(a + b, Complex::new(4.0, 6.0));
    assert_eq!(a * b, Complex::new(-5.0, 10.0));
}
```

<details>
<summary>💡 解答</summary>

```rust
use std::ops::{Add, Sub, Mul};

#[derive(Debug, Clone, Copy, PartialEq)]
struct Complex {
    real: f64,
    imag: f64,
}

impl Complex {
    fn new(real: f64, imag: f64) -> Self {
        Self { real, imag }
    }
}

impl Add for Complex {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        Self::new(self.real + other.real, self.imag + other.imag)
    }
}

impl Sub for Complex {
    type Output = Self;
    fn sub(self, other: Self) -> Self {
        Self::new(self.real - other.real, self.imag - other.imag)
    }
}

impl Mul for Complex {
    type Output = Self;
    fn mul(self, other: Self) -> Self {
        Self::new(
            self.real * other.real - self.imag * other.imag,
            self.real * other.imag + self.imag * other.real,
        )
    }
}

fn main() {
    let a = Complex::new(1.0, 2.0);
    let b = Complex::new(3.0, 4.0);

    assert_eq!(a + b, Complex::new(4.0, 6.0));
    assert_eq!(a * b, Complex::new(-5.0, 10.0));
    println!("✓ 测试通过!");
}
```

</details>

---

## 高级练习 ⭐⭐⭐⭐

探索异步编程和并发处理。

### 练习 16: 多线程计数器

**描述**: 使用 Arc 和 Mutex 实现线程安全的计数器。

**要求**: 多个线程同时递增计数器，最终值正确。

```rust,compile_fail
use std::sync::{Arc, Mutex};
use std::thread;

fn main() {
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        // 创建线程并递增计数器
    }

    for handle in handles {
        handle.join().unwrap();
    }

    assert_eq!(*counter.lock().unwrap(), 1000);
}
```

<details>
<summary>💡 解答</summary>

```rust
use std::sync::{Arc, Mutex};
use std::thread;

fn main() {
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            for _ in 0..100 {
                let mut num = counter.lock().unwrap();
                *num += 1;
            }
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    assert_eq!(*counter.lock().unwrap(), 1000);
    println!("✓ 测试通过!");
}
```

</details>

---

### 练习 17: 异步 HTTP 客户端

**描述**: 使用 async/await 发起并发 HTTP 请求。

**要求**: 同时请求多个 URL，收集所有响应。

```rust,compile_fail
use reqwest;

async fn fetch_urls(urls: &[&str]) -> Vec<Result<String, reqwest::Error>> {
    // 使用 futures 并发获取
}

#[tokio::main]
async fn main() {
    let urls = vec![
        "https://api.github.com/users/rust-lang",
        "https://api.github.com/users/torvalds",
    ];
    let results = fetch_urls(&urls).await;
    println!("获取了 {} 个响应", results.len());
}
```

<details>
<summary>💡 解答</summary>

```rust,compile_fail
use futures::future::join_all;

async fn fetch_urls(urls: &[&str]) -> Vec<Result<String, reqwest::Error>> {
    let futures = urls.iter().map(|url| async move {
        reqwest::get(*url).await?.text().await
    });
    join_all(futures).await
}

#[tokio::main]
async fn main() {
    let urls = vec![
        "https://api.github.com/users/rust-lang",
        "https://api.github.com/users/torvalds",
    ];
    let results = fetch_urls(&urls).await;
    println!("获取了 {} 个响应", results.len());
    for (i, result) in results.iter().enumerate() {
        match result {
            Ok(_) => println!("URL {}: 成功", i),
            Err(e) => println!("URL {}: 失败 - {}", i, e),
        }
    }
}
```

</details>

---

### 练习 18: 通道通信

**描述**: 使用 mpsc 通道实现生产者-消费者模式。

**要求**: 多个生产者向单个消费者发送消息。

```rust,compile_fail
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

fn main() {
    let (tx, rx) = mpsc::channel();

    // 创建多个生产者线程

    // 消费者接收所有消息

    println!("共接收 {} 条消息", received_count);
}
```

<details>
<summary>💡 解答</summary>

```rust
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

fn main() {
    let (tx, rx) = mpsc::channel();

    // 创建3个生产者
    for i in 0..3 {
        let tx = tx.clone();
        thread::spawn(move || {
            for j in 0..5 {
                tx.send(format!("生产者{}的消息{}", i, j)).unwrap();
                thread::sleep(Duration::from_millis(10));
            }
        });
    }

    // 丢弃原始发送者，否则接收者会无限等待
    drop(tx);

    // 消费者接收所有消息
    let mut received_count = 0;
    for msg in rx {
        println!("收到: {}", msg);
        received_count += 1;
    }

    println!("共接收 {} 条消息", received_count);
    assert_eq!(received_count, 15);
}
```

</details>

---

### 练习 19: RwLock 读写锁

**描述**: 使用 RwLock 实现高效的读多写少场景。

**要求**: 实现一个缓存，支持并发读取和独占写入。

```rust,compile_fail
use std::sync::RwLock;
use std::collections::HashMap;
use std::sync::Arc;
use std::thread;

struct Cache {
    data: RwLock<HashMap<String, String>>,
}

impl Cache {
    fn new() -> Self {
        Self { data: RwLock::new(HashMap::new()) }
    }

    fn get(&self, key: &str) -> Option<String> {
        // 实现这里
    }

    fn set(&self, key: String, value: String) {
        // 实现这里
    }
}

fn main() {
    let cache = Arc::new(Cache::new());

    // 创建读取和写入线程

    println!("缓存测试完成");
}
```

<details>
<summary>💡 解答</summary>

```rust
use std::sync::RwLock;
use std::collections::HashMap;
use std::sync::Arc;
use std::thread;

struct Cache {
    data: RwLock<HashMap<String, String>>,
}

impl Cache {
    fn new() -> Self {
        Self { data: RwLock::new(HashMap::new()) }
    }

    fn get(&self, key: &str) -> Option<String> {
        self.data.read().unwrap().get(key).cloned()
    }

    fn set(&self, key: String, value: String) {
        self.data.write().unwrap().insert(key, value);
    }
}

fn main() {
    let cache = Arc::new(Cache::new());

    // 写入线程
    let cache_write = Arc::clone(&cache);
    let write_handle = thread::spawn(move || {
        for i in 0..10 {
            cache_write.set(format!("key{}", i), format!("value{}", i));
        }
    });

    // 读取线程
    let cache_read = Arc::clone(&cache);
    let read_handle = thread::spawn(move || {
        for _ in 0..20 {
            let _ = cache_read.get("key1");
        }
    });

    write_handle.join().unwrap();
    read_handle.join().unwrap();

    println!("缓存测试完成");
}
```

</details>

---

### 练习 20: 条件变量

**描述**: 使用 Condvar 实现线程同步。

**要求**: 实现一个工作队列，线程等待任务可用。

```rust,compile_fail
use std::sync::{Mutex, Condvar, Arc};
use std::thread;
use std::collections::VecDeque;

struct TaskQueue {
    queue: Mutex<VecDeque<i32>>,
    cond: Condvar,
}

impl TaskQueue {
    fn new() -> Self {
        Self {
            queue: Mutex::new(VecDeque::new()),
            cond: Condvar::new(),
        }
    }

    fn push(&self, task: i32) {
        // 实现这里
    }

    fn pop(&self) -> i32 {
        // 实现这里
    }
}

fn main() {
    let queue = Arc::new(TaskQueue::new());

    // 创建生产者和消费者线程

    println!("任务队列测试完成");
}
```

<details>
<summary>💡 解答</summary>

```rust
use std::sync::{Mutex, Condvar, Arc};
use std::thread;
use std::collections::VecDeque;

struct TaskQueue {
    queue: Mutex<VecDeque<i32>>,
    cond: Condvar,
}

impl TaskQueue {
    fn new() -> Self {
        Self {
            queue: Mutex::new(VecDeque::new()),
            cond: Condvar::new(),
        }
    }

    fn push(&self, task: i32) {
        let mut queue = self.queue.lock().unwrap();
        queue.push_back(task);
        self.cond.notify_one();
    }

    fn pop(&self) -> i32 {
        let mut queue = self.queue.lock().unwrap();
        while queue.is_empty() {
            queue = self.cond.wait(queue).unwrap();
        }
        queue.pop_front().unwrap()
    }
}

fn main() {
    let queue = Arc::new(TaskQueue::new());

    // 消费者
    let consumer_queue = Arc::clone(&queue);
    let consumer = thread::spawn(move || {
        for _ in 0..5 {
            let task = consumer_queue.pop();
            println!("处理任务: {}", task);
        }
    });

    // 生产者
    let producer_queue = Arc::clone(&queue);
    let producer = thread::spawn(move || {
        for i in 0..5 {
            thread::sleep(std::time::Duration::from_millis(10));
            println!("添加任务: {}", i);
            producer_queue.push(i);
        }
    });

    producer.join().unwrap();
    consumer.join().unwrap();

    println!("任务队列测试完成");
}
```

</details>

---

## 专家挑战 ⭐⭐⭐⭐⭐

设计复杂系统，掌握 Rust 的高级特性。

### 练习 21: 实现自己的 Vec

**描述**: 从头实现一个简化版的动态数组 MyVec。

**要求**: 实现 new、push、pop、get、len 等基本操作。

```rust,compile_fail
use std::alloc::{self, Layout};
use std::ptr::{self, NonNull};

struct MyVec<T> {
    ptr: NonNull<T>,
    len: usize,
    cap: usize,
}

impl<T> MyVec<T> {
    fn new() -> Self {
        // 实现这里
    }

    fn push(&mut self, item: T) {
        // 实现这里
    }

    fn pop(&mut self) -> Option<T> {
        // 实现这里
    }

    fn get(&self, index: usize) -> Option<&T> {
        // 实现这里
    }

    fn len(&self) -> usize {
        self.len
    }
}

fn main() {
    let mut vec = MyVec::new();
    vec.push(1);
    vec.push(2);
    assert_eq!(vec.pop(), Some(2));
    assert_eq!(vec.get(0), Some(&1));
}
```

<details>
<summary>💡 解答</summary>

```rust
use std::alloc::{self, Layout};
use std::ptr::{self, NonNull};

struct MyVec<T> {
    ptr: NonNull<T>,
    len: usize,
    cap: usize,
}

impl<T> MyVec<T> {
    fn new() -> Self {
        Self {
            ptr: NonNull::dangling(),
            len: 0,
            cap: 0,
        }
    }

    fn push(&mut self, item: T) {
        if self.len == self.cap {
            self.grow();
        }
        unsafe {
            ptr::write(self.ptr.as_ptr().add(self.len), item);
        }
        self.len += 1;
    }

    fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            return None;
        }
        self.len -= 1;
        unsafe {
            Some(ptr::read(self.ptr.as_ptr().add(self.len)))
        }
    }

    fn get(&self, index: usize) -> Option<&T> {
        if index >= self.len {
            return None;
        }
        unsafe {
            Some(&*self.ptr.as_ptr().add(index))
        }
    }

    fn grow(&mut self) {
        let new_cap = if self.cap == 0 { 1 } else { self.cap * 2 };
        let new_layout = Layout::array::<T>(new_cap).unwrap();
        let new_ptr = if self.cap == 0 {
            unsafe { alloc::alloc(new_layout) as *mut T }
        } else {
            let old_layout = Layout::array::<T>(self.cap).unwrap();
            unsafe {
                alloc::realloc(self.ptr.as_ptr() as *mut u8, old_layout, new_layout.size()) as *mut T
            }
        };
        self.ptr = NonNull::new(new_ptr).unwrap();
        self.cap = new_cap;
    }
}

fn main() {
    let mut vec = MyVec::new();
    vec.push(1);
    vec.push(2);
    assert_eq!(vec.pop(), Some(2));
    assert_eq!(vec.get(0), Some(&1));
    println!("✓ MyVec 测试通过!");
}
```

</details>

---

### 练习 22: 线程安全的 HashMap

**描述**: 实现一个分片锁的并发 HashMap。

**要求**: 使用多个 Mutex 分片，提高并发性能。

```rust,compile_fail
use std::sync::Mutex;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

const SHARD_COUNT: usize = 16;

struct ConcurrentHashMap<K, V> {
    shards: [Mutex<std::collections::HashMap<K, V>>; SHARD_COUNT],
}

impl<K: Hash + Eq, V> ConcurrentHashMap<K, V> {
    fn new() -> Self {
        // 实现这里
    }

    fn insert(&self, key: K, value: V) -> Option<V> {
        // 实现这里
    }

    fn get(&self, key: &K) -> Option<V>
    where V: Clone {
        // 实现这里
    }
}

fn main() {
    let map = ConcurrentHashMap::new();
    map.insert("key1", 100);
    assert_eq!(map.get(&"key1"), Some(100));
}
```

<details>
<summary>💡 解答</summary>

```rust
use std::sync::Mutex;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

const SHARD_COUNT: usize = 16;

struct ConcurrentHashMap<K, V> {
    shards: Vec<Mutex<std::collections::HashMap<K, V>>>,
}

impl<K: Hash + Eq, V> ConcurrentHashMap<K, V> {
    fn new() -> Self {
        let mut shards = Vec::with_capacity(SHARD_COUNT);
        for _ in 0..SHARD_COUNT {
            shards.push(Mutex::new(std::collections::HashMap::new()));
        }
        Self { shards }
    }

    fn shard_index(&self, key: &K) -> usize {
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        (hasher.finish() as usize) % SHARD_COUNT
    }

    fn insert(&self, key: K, value: V) -> Option<V> {
        let idx = self.shard_index(&key);
        self.shards[idx].lock().unwrap().insert(key, value)
    }

    fn get(&self, key: &K) -> Option<V>
    where V: Clone {
        let idx = self.shard_index(key);
        self.shards[idx].lock().unwrap().get(key).cloned()
    }
}

fn main() {
    let map = ConcurrentHashMap::new();
    map.insert("key1", 100);
    assert_eq!(map.get(&"key1"), Some(100));
    println!("✓ 并发 HashMap 测试通过!");
}
```

</details>

---

### 练习 23: 异步运行时骨架

**描述**: 实现一个简化版的异步任务调度器。

**要求**: 支持 spawn 任务和基本的 waker 机制。

```rust,compile_fail
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll, Waker, RawWaker, RawWakerVTable};
use std::sync::mpsc::{channel, Sender, Receiver};
use std::sync::Arc;
use std::cell::RefCell;

struct Task {
    future: RefCell<Pin<Box<dyn Future<Output = ()>>>>,
}

struct Runtime {
    task_queue: Receiver<Arc<Task>>,
    task_sender: Sender<Arc<Task>>,
}

impl Runtime {
    fn new() -> Self {
        // 实现这里
    }

    fn spawn<F>(&self, future: F)
    where F: Future<Output = ()> + 'static {
        // 实现这里
    }

    fn run(&self) {
        // 实现这里
    }
}

fn main() {
    let rt = Runtime::new();
    rt.spawn(async {
        println!("Hello from async task!");
    });
    rt.run();
}
```

<details>
<summary>💡 解答</summary>

```rust,compile_fail
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll, Waker, RawWaker, RawWakerVTable};
use std::sync::mpsc::{channel, Sender, Receiver};
use std::sync::Arc;
use std::cell::RefCell;

struct Task {
    future: RefCell<Pin<Box<dyn Future<Output = ()>>>>,
}

struct Runtime {
    task_queue: Receiver<Arc<Task>>,
    task_sender: Sender<Arc<Task>>,
}

fn dummy_raw_waker() -> RawWaker {
    fn no_op(_: *const ()) {}
    fn clone(_: *const ()) -> RawWaker {
        dummy_raw_waker()
    }
    let vtable = &RawWakerVTable::new(clone, no_op, no_op, no_op);
    RawWaker::new(std::ptr::null(), vtable)
}

fn dummy_waker() -> Waker {
    unsafe { Waker::from_raw(dummy_raw_waker()) }
}

impl Runtime {
    fn new() -> Self {
        let (task_sender, task_queue) = channel();
        Self { task_queue, task_sender }
    }

    fn spawn<F>(&self, future: F)
    where F: Future<Output = ()> + 'static {
        let task = Arc::new(Task {
            future: RefCell::new(Box::pin(future)),
        });
        self.task_sender.send(task).unwrap();
    }

    fn run(&self) {
        while let Ok(task) = self.task_queue.recv() {
            let waker = dummy_waker();
            let mut context = Context::from_waker(&waker);

            match task.future.borrow_mut().as_mut().poll(&mut context) {
                Poll::Pending => {
                    // 简化版：重新入队
                    self.task_sender.send(task).unwrap();
                }
                Poll::Ready(()) => {}
            }
        }
    }
}

fn main() {
    let rt = Runtime::new();
    rt.spawn(async {
        println!("Hello from async task!");
    });
    rt.run();
}
```

</details>

---

## 总结

完成本练习集后，你应该掌握了：

1. **所有权与借用** - Rust 最核心的内存管理概念
2. **集合与迭代器** - 高效处理数据的工具
3. **泛型与特质** - 抽象和代码复用的基础
4. **错误处理** - 健壮的程序设计
5. **并发与异步** - 现代编程必备技能
6. **unsafe 与底层** - 理解 Rust 的运行时机制

建议在学习过程中多思考、多实践，并尝试为练习添加更多边界情况测试。

---

*本练习集持续更新中，欢迎提出改进建议！*
---

> **权威来源**: [来源: Rust 官方文档](https://doc.rust-lang.org/)

---

## 相关概念

- [Rust 生产案例研究](03_case_studies.md)
- [Rust 知识库建设完成报告](01_completion_report_2026_03_1_94.md)

### 边界测试：递归深度与栈溢出（运行时 panic）

```rust,ignore
fn factorial(n: u64) -> u64 {
    if n == 0 { 1 } else { n * factorial(n - 1) }
}

fn main() {
    // ❌ 运行时栈溢出: 递归深度过大
    let _ = factorial(100000);
}
```

> **修正**: Rust 不优化尾递归，`factorial(100000)` 创建 10 万层栈帧，超出栈大小（通常 1-8MB），触发 `thread '<main>' has overflowed its stack` panic。解决方案：1) **循环替代**：`let mut result = 1; for i in 1..=n { result *= i; }`；2) **显式栈**：用 `Vec` 模拟递归栈；3) **尾递归优化 crate**：`trampolin` 模式（返回闭包而非调用）。`std::thread::Builder::stack_size()` 可增加单个线程的栈大小，但非根本解决。这与 Scheme/Erlang 的尾递归优化（语言保证不增长栈）或 C 的递归（同样栈溢出风险）不同——Rust 偏向命令式循环，递归仅用于算法清晰表达。[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/ch03-05-control-flow.html)] · [来源: [Rust Reference — Functions](https://doc.rust-lang.org/reference/items/functions.html)]

### 边界测试：迭代器消费后的重复使用（编译错误）

```rust,ignore
fn main() {
    let v = vec![1, 2, 3];
    let iter = v.into_iter();
    let sum: i32 = iter.sum();
    println!("{}", sum);

    // ❌ 编译错误: into_iter 消耗了 v，iter 也已被消费（sum 是 consuming adaptor）
    // let product: i32 = iter.product();
}
```

> **修正**: Rust 的迭代器是**单次消费**的：`sum()`、`product()`、`collect()` 等终止操作（consuming adaptor）消费迭代器，之后不能再使用。某些迭代器可通过 `clone()` 复制（若底层数据 `Clone`），但通常需重新创建。`into_iter()` 消费集合本身（`Vec` 被 move），之后 `v` 不可用；`iter()` 借用集合，`v` 仍可用但受借用规则限制；`iter_mut()` 可变借用。这与 C++ 的迭代器（可多次遍历同一容器，但失效规则复杂）或 Python 的迭代器（同样单次消费，但 `list` 可多次 `iter()`）类似——Rust 的迭代器模型明确区分消费和借用。[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/ch13-02-iterators.html)] · [来源: [Rust Standard Library](https://doc.rust-lang.org/std/iter/trait.Iterator.html)]

### 边界测试：模式匹配中的绑定与守卫的变量遮蔽（逻辑错误）

```rust,ignore
fn main() {
    let x = Some(5);
    match x {
        Some(n) if n > 3 => println!("big: {}", n),
        Some(n) => println!("small: {}", n),
        None => println!("none"),
    }

    let y = Some(5);
    match y {
        Some(n) => {
            let n = n + 1; // 遮蔽
            println!("{}", n); // 6
        }
        None => {},
    }
    // ❌ 逻辑问题: 模式绑定中的变量可能被意外遮蔽，导致困惑
}
```

> **修正**: 模式匹配中的**绑定**（binding）：`Some(n)` 将内部值绑定到 `n`，`n` 的生命周期限于该匹配臂。`match` 守卫（`if` 条件）中可使用绑定变量：`Some(n) if n > 3`。变量遮蔽在 match 臂内允许：`let n = n + 1` 创建新 `n`，不影响外部的 `n`。这与 Haskell 的 `case`（类似绑定，但无守卫的变量遮蔽问题）或 Scala 的 `match`（类似，但可用 `@` 绑定整个模式）类似——Rust 的模式匹配提供强大的解构能力，但需注意变量作用域和遮蔽。[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/ch18-03-pattern-syntax.html)] · [来源: [Rust Reference — Patterns](https://doc.rust-lang.org/reference/patterns.html)]

### 边界测试：`std::mem::swap` 与 `take` 的惯用选择（逻辑错误）

```rust,ignore
use std::mem;

fn main() {
    let mut s1 = String::from("hello");
    let mut s2 = String::from("world");
    mem::swap(&mut s1, &mut s2);
    println!("s1 = {}, s2 = {}", s1, s2); // s1 = world, s2 = hello

    let mut opt = Some(String::from("hello"));
    // ❌ 逻辑问题: 若只想取走值并留 None，swap 不如 take 惯用
    // let mut temp = None;
    // mem::swap(&mut opt, &mut temp);
    // let value = temp.unwrap();

    // 正确:
    let value = opt.take().unwrap();
    println!("value = {}, opt = {:?}", value, opt); // value = hello, opt = None
}
```

> **修正**: `std::mem::take` 是 `replace(&mut t, T::default())` 的便捷方法：取走值并留默认值。`Option::take` 特别常用：取走 `Some`，留 `None`。`swap` 用于交换两个同类型值，`take` 用于获取值并替换为默认。选择：1) 需要交换两个变量 → `swap`；2) 需要从变量获取值并留默认 → `take`；3) 需要从变量获取值并替换为新值 → `replace`。这与 C++ 的 `std::swap`（类似）或 Python 的 `a, b = b, a`（元组解包交换）不同——Rust 的 `take` 是获取所有权并留默认值的惯用模式。[来源: [Rust Standard Library](https://doc.rust-lang.org/std/mem/fn.take.html)] · [来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]

### 边界测试：`?` 运算符在 `Option` 与 `Result` 混用时的类型不匹配（编译错误）

```rust,ignore
fn may_fail() -> Result<i32, String> {
    Ok(42)
}

fn may_be_none() -> Option<i32> {
    Some(42)
}

fn combine() -> Result<i32, String> {
    let x = may_fail()?;
    // ❌ 编译错误: Option 不能直接用 ? 在返回 Result 的函数中
    // let y = may_be_none()?;

    // 正确: 显式转换
    let y = may_be_none().ok_or("missing value")?;
    Ok(x + y)
}

fn main() {
    println!("{:?}", combine());
}
```

> **修正**: `?` 运算符要求错误类型可转换：`Result<T, E>` 中的 `E` 必须实现 `From<InnerE>`，`Option<T>` 在返回 `Result` 的函数中不能直接用 `?`（无错误类型可转换）。转换方法：1) `opt.ok_or(err)?` — `Option` → `Result`；2) `res.ok()?` — `Result` → `Option`（忽略错误）；3) `opt.ok_or_else(|| make_err())?` — 延迟错误构造。Rust 1.70+ 中 `?` 在 `Option` 和 `Result` 之间有更灵活的转换，但类型不匹配仍需显式处理。这与 Haskell 的 `Maybe` 和 `Either`（需显式 `maybeToEither` 转换）或 Swift 的 `try?` / `try!`（类似但语义不同）不同——Rust 的 `?` 是语法糖，但类型系统严格检查转换可行性。[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/ch09-02-recoverable-errors-with-result.html)] · [来源: [Rust Reference — The Question Mark Operator](https://doc.rust-lang.org/reference/expressions/operator-expr.html#the-question-mark-operator)]

### 边界测试：trait object 的 `downcast_ref` 与类型安全（运行时 panic）

```rust,ignore
use std::any::Any;

fn main() {
    let value: Box<dyn Any> = Box::new(42i32);

    // ❌ 运行时 panic: downcast_ref 到错误类型返回 None，unwrap 时 panic
    let s = value.downcast_ref::<String>().unwrap();
    println!("{}", s);

    // 正确:
    // if let Some(n) = value.downcast_ref::<i32>() {
    //     println!("{}", n);
    // }
}
```

> **修正**: `Any` trait 提供**运行时类型反射**：`downcast_ref::<T>()` 将 `&dyn Any` 转为 `Option<&T>`。类型安全：1) 类型匹配 → `Some(&T)`；2) 类型不匹配 → `None`；3) 无 UB（运行时检查）。`Any` 的局限：1) 要求 `'static` 边界（因类型标识符是全局静态）；2) 不能用于含借用引用的类型（非 `'static`）；3) 性能开销（vtable 查找 + 类型 ID 比较）。使用场景：1) 错误处理（`Box<dyn Any>` 传递 panic payload）；2) 插件系统（动态类型注册）；3) 序列化框架（类型擦除后恢复）。这与 Java 的 `instanceof` / `cast`（类似运行时检查）或 C++ 的 `dynamic_cast`（类似，但需 RTTI）不同——Rust 的 `Any` 是 opt-in 的，无全局 RTTI 开销。[来源: [Rust Standard Library](https://doc.rust-lang.org/std/any/trait.Any.html)] · [来源: [The Rust Programming Language](https://doc.rust-lang.org/book/ch17-02-trait-objects.html)]

### 边界测试：`std::thread::spawn` 与闭包生命周期（编译错误）

```rust,ignore
fn main() {
    let v = vec![1, 2, 3];
    // ❌ 编译错误: 闭包捕获 &v，但线程可能活得更长
    // let handle = std::thread::spawn(|| {
    //     println!("{:?}", v);
    // });

    // 正确: move 闭包转移所有权
    let handle = std::thread::spawn(move || {
        println!("{:?}", v);
    });
    handle.join().unwrap();
}
```

> **修正**: `std::thread::spawn` 要求闭包实现 `'static`：捕获的数据必须拥有 `'static` 生命周期（或转移所有权）。`move || { ... }` 强制按值捕获变量，将所有权转移到新线程。非 `move` 闭包捕获引用：`|| { println!("{:?}", v); }` 捕获 `&v`，但 `v` 在主线程栈上，新线程可能在其 drop 后访问 → 悬垂引用。编译器拒绝：`closure may outlive the current function, but it borrows v`。这与 Go 的 goroutine（闭包捕获变量是引用，但 goroutine 通常在函数返回前完成，且 GC 管理生命周期）或 C++ 的 `std::thread`（类似 `move`，但可用 `std::ref` 传递引用，需手动保证生命周期）不同——Rust 的编译期检查强制线程闭包的生命周期安全。[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/ch16-01-threads.html)] · [来源: [Rust Reference — Threads](https://doc.rust-lang.org/reference/runtime.html#threads)]

### 边界测试：`std::sync::mpsc` 的通道关闭检测（运行时逻辑错误）

```rust,ignore
use std::sync::mpsc;
use std::thread;

fn main() {
    let (tx, rx) = mpsc::channel::<i32>();

    thread::spawn(move || {
        tx.send(1).unwrap();
        tx.send(2).unwrap();
        // tx 在作用域结束时 drop，通道关闭
    });

    // ❌ 逻辑错误: recv 返回 Err(RecvError) 时未处理，unwrap 会 panic
    // 若发送端 panic 或被 drop 前未发送完消息
    loop {
        let msg = rx.recv().unwrap();
        println!("{}", msg);
    }
}
```

> **修正**: `mpsc::channel` 的关闭语义：1) 所有 `Sender` drop → `Receiver::recv()` 返回 `Err(RecvError)`（Disconnected）；2) `try_recv()` 在无消息时立即返回 `Err(TryRecvError::Empty)`；3) `iter()` 在 channel 关闭且所有消息消费完后终止。安全模式：1) `while let Ok(msg) = rx.recv()` — 优雅处理关闭；2) `for msg in rx` — 使用迭代器接口；3) 多生产者场景确保所有 `Sender` 正确 drop。`mpsc` 是标准库的同步通道，async 场景用 `tokio::sync::mpsc`。这与 Go 的 channel（`range` 迭代自动检测关闭，`close()` 显式关闭）或 Erlang 的消息传递（无显式关闭，进程退出即终止）不同——Rust 的 channel 关闭通过 drop 隐式触发。[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/ch16-02-message-passing.html)] · [来源: [Rust Standard Library](https://doc.rust-lang.org/std/sync/mpsc/)]
