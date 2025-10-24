# 高级借用模式 - Advanced Borrowing Patterns

## 📊 目录

- [高级借用模式 - Advanced Borrowing Patterns](#高级借用模式---advanced-borrowing-patterns)
  - [📊 目录](#-目录)
  - [📋 目录](#-目录-1)
  - [1. 借用分割](#1-借用分割)
    - [1.1 切片借用分割](#11-切片借用分割)
    - [1.2 结构体字段借用分割](#12-结构体字段借用分割)
  - [2. 内部可变性](#2-内部可变性)
    - [2.1 Cell 和 RefCell](#21-cell-和-refcell)
    - [2.2 Mutex 和 RwLock](#22-mutex-和-rwlock)
  - [3. 生命周期省略](#3-生命周期省略)
    - [3.1 函数生命周期省略](#31-函数生命周期省略)
    - [3.2 impl块生命周期省略](#32-impl块生命周期省略)
  - [4. 高阶生命周期绑定](#4-高阶生命周期绑定)
    - [4.1 HRTB 基础](#41-hrtb-基础)
    - [4.2 HRTB 高级应用](#42-hrtb-高级应用)
  - [5. 借用检查器的高级技巧](#5-借用检查器的高级技巧)
    - [5.1 非词汇生命周期（NLL）](#51-非词汇生命周期nll)
    - [5.2 Polonius 借用检查器](#52-polonius-借用检查器)
  - [6. 智能指针与借用](#6-智能指针与借用)
    - [6.1 Rc 和 Arc](#61-rc-和-arc)
    - [6.2 Cow (Clone-on-Write)](#62-cow-clone-on-write)
  - [7. 借用模式最佳实践](#7-借用模式最佳实践)
    - [7.1 避免借用冲突](#71-避免借用冲突)
    - [7.2 优化借用性能](#72-优化借用性能)
  - [📚 总结](#-总结)

**版本**: 1.0  
**最后更新**: 2025-01-27  
**状态**: 完整版  

## 📋 目录

- [高级借用模式 - Advanced Borrowing Patterns](#高级借用模式---advanced-borrowing-patterns)
  - [📊 目录](#-目录)
  - [📋 目录](#-目录-1)
  - [1. 借用分割](#1-借用分割)
    - [1.1 切片借用分割](#11-切片借用分割)
    - [1.2 结构体字段借用分割](#12-结构体字段借用分割)
  - [2. 内部可变性](#2-内部可变性)
    - [2.1 Cell 和 RefCell](#21-cell-和-refcell)
    - [2.2 Mutex 和 RwLock](#22-mutex-和-rwlock)
  - [3. 生命周期省略](#3-生命周期省略)
    - [3.1 函数生命周期省略](#31-函数生命周期省略)
    - [3.2 impl块生命周期省略](#32-impl块生命周期省略)
  - [4. 高阶生命周期绑定](#4-高阶生命周期绑定)
    - [4.1 HRTB 基础](#41-hrtb-基础)
    - [4.2 HRTB 高级应用](#42-hrtb-高级应用)
  - [5. 借用检查器的高级技巧](#5-借用检查器的高级技巧)
    - [5.1 非词汇生命周期（NLL）](#51-非词汇生命周期nll)
    - [5.2 Polonius 借用检查器](#52-polonius-借用检查器)
  - [6. 智能指针与借用](#6-智能指针与借用)
    - [6.1 Rc 和 Arc](#61-rc-和-arc)
    - [6.2 Cow (Clone-on-Write)](#62-cow-clone-on-write)
  - [7. 借用模式最佳实践](#7-借用模式最佳实践)
    - [7.1 避免借用冲突](#71-避免借用冲突)
    - [7.2 优化借用性能](#72-优化借用性能)
  - [📚 总结](#-总结)

## 1. 借用分割

### 1.1 切片借用分割

切片借用分割允许同时可变借用数组的不同部分：

```rust
// 基本的切片分割
fn split_at_mut_example() {
    let mut data = [1, 2, 3, 4, 5, 6];
    let (left, right) = data.split_at_mut(3);
    
    // 可以同时修改不同部分
    left[0] = 10;
    right[0] = 20;
    
    println!("Data: {:?}", data); // [10, 2, 3, 20, 5, 6]
}

// 高级分割模式
fn advanced_split_pattern<T>(slice: &mut [T]) -> (&mut T, &mut [T], &mut T) {
    let len = slice.len();
    assert!(len >= 2);
    
    let (first, rest) = slice.split_first_mut().unwrap();
    let (rest, last) = rest.split_last_mut().unwrap();
    
    (first, rest, last)
}

// 使用示例
fn use_advanced_split() {
    let mut numbers = vec![1, 2, 3, 4, 5];
    let (first, middle, last) = advanced_split_pattern(&mut numbers);
    
    *first = 10;
    *last = 50;
    for num in middle {
        *num *= 2;
    }
    
    println!("{:?}", numbers); // [10, 4, 6, 8, 50]
}
```

### 1.2 结构体字段借用分割

Rust 允许同时可变借用结构体的不同字段：

```rust
struct Point {
    x: i32,
    y: i32,
}

impl Point {
    // 同时借用不同字段
    fn adjust(&mut self) {
        let x_ref = &mut self.x;
        let y_ref = &mut self.y;
        
        *x_ref += *y_ref;
        *y_ref *= 2;
    }
}

// 更复杂的字段分割
struct ComplexData {
    values: Vec<i32>,
    metadata: String,
    counter: usize,
}

impl ComplexData {
    fn process(&mut self) {
        // 可以同时借用不同字段
        let values = &mut self.values;
        let counter = &mut self.counter;
        
        for value in values.iter_mut() {
            *value += 1;
            *counter += 1;
        }
    }
    
    // 返回多个字段的借用
    fn split_mut(&mut self) -> (&mut Vec<i32>, &mut String, &mut usize) {
        (&mut self.values, &mut self.metadata, &mut self.counter)
    }
}
```

## 2. 内部可变性

### 2.1 Cell 和 RefCell

`Cell` 和 `RefCell` 提供内部可变性：

```rust
use std::cell::{Cell, RefCell};

// Cell: 用于Copy类型
struct Sensor {
    reading: Cell<f64>,
    name: String,
}

impl Sensor {
    fn new(name: String) -> Self {
        Self {
            reading: Cell::new(0.0),
            name,
        }
    }
    
    // 即使 &self 是不可变借用，也可以修改 Cell
    fn update_reading(&self, new_reading: f64) {
        self.reading.set(new_reading);
    }
    
    fn get_reading(&self) -> f64 {
        self.reading.get()
    }
}

// RefCell: 用于非Copy类型
struct Graph {
    nodes: RefCell<Vec<String>>,
}

impl Graph {
    fn new() -> Self {
        Self {
            nodes: RefCell::new(Vec::new()),
        }
    }
    
    // 通过 &self 修改内部数据
    fn add_node(&self, node: String) {
        self.nodes.borrow_mut().push(node);
    }
    
    fn get_nodes(&self) -> Vec<String> {
        self.nodes.borrow().clone()
    }
    
    // 演示动态借用检查
    fn demonstrate_borrow_checking(&self) {
        let borrow1 = self.nodes.borrow(); // 不可变借用
        let borrow2 = self.nodes.borrow(); // 可以有多个不可变借用
        
        println!("Nodes: {:?}", *borrow1);
        println!("Nodes: {:?}", *borrow2);
        
        // let mut_borrow = self.nodes.borrow_mut(); // 会panic！
        // 因为已经有不可变借用
    }
}
```

### 2.2 Mutex 和 RwLock

在并发场景中的内部可变性：

```rust
use std::sync::{Mutex, RwLock, Arc};
use std::thread;

// Mutex: 互斥锁
struct SharedCounter {
    count: Mutex<i32>,
}

impl SharedCounter {
    fn new() -> Self {
        Self {
            count: Mutex::new(0),
        }
    }
    
    fn increment(&self) {
        let mut count = self.count.lock().unwrap();
        *count += 1;
    }
    
    fn get(&self) -> i32 {
        *self.count.lock().unwrap()
    }
}

// RwLock: 读写锁
struct SharedData {
    data: RwLock<Vec<String>>,
}

impl SharedData {
    fn new() -> Self {
        Self {
            data: RwLock::new(Vec::new()),
        }
    }
    
    // 多个线程可以同时读
    fn read(&self) -> Vec<String> {
        self.data.read().unwrap().clone()
    }
    
    // 写操作是独占的
    fn write(&self, item: String) {
        self.data.write().unwrap().push(item);
    }
}

// 使用示例
fn concurrent_example() {
    let counter = Arc::new(SharedCounter::new());
    let mut handles = vec![];
    
    for _ in 0..10 {
        let counter_clone = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            for _ in 0..100 {
                counter_clone.increment();
            }
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("Final count: {}", counter.get()); // 1000
}
```

## 3. 生命周期省略

### 3.1 函数生命周期省略

Rust 有三条生命周期省略规则：

```rust
// 规则1：每个引用参数都有自己的生命周期
// 编译器推断为: fn foo<'a, 'b>(x: &'a str, y: &'b str)
fn foo(x: &str, y: &str) {
    println!("{} {}", x, y);
}

// 规则2：如果只有一个输入生命周期，它被赋给所有输出生命周期
// 编译器推断为: fn first_word<'a>(s: &'a str) -> &'a str
fn first_word(s: &str) -> &str {
    let bytes = s.as_bytes();
    for (i, &item) in bytes.iter().enumerate() {
        if item == b' ' {
            return &s[0..i];
        }
    }
    &s[..]
}

// 规则3：如果有 &self 或 &mut self，它的生命周期被赋给所有输出
struct StringHolder {
    data: String,
}

impl StringHolder {
    // 编译器推断为: fn get_data<'a>(&'a self) -> &'a str
    fn get_data(&self) -> &str {
        &self.data
    }
    
    // 多个引用参数时，需要显式标注
    fn longest<'a>(&'a self, other: &'a str) -> &'a str {
        if self.data.len() > other.len() {
            &self.data
        } else {
            other
        }
    }
}
```

### 3.2 impl块生命周期省略

```rust
// impl 块中的生命周期省略
struct ImportantExcerpt<'a> {
    part: &'a str,
}

impl<'a> ImportantExcerpt<'a> {
    // 返回值生命周期与 self 相同
    fn get_part(&self) -> &str {
        self.part
    }
    
    // 多个生命周期参数
    fn announce_and_return_part(&self, announcement: &str) -> &str {
        println!("Attention: {}", announcement);
        self.part
    }
}

// 泛型和生命周期结合
struct Wrapper<'a, T> 
where
    T: 'a,
{
    value: &'a T,
}

impl<'a, T> Wrapper<'a, T> 
where
    T: 'a,
{
    fn new(value: &'a T) -> Self {
        Self { value }
    }
    
    fn get(&self) -> &T {
        self.value
    }
}
```

## 4. 高阶生命周期绑定

### 4.1 HRTB 基础

高阶生命周期绑定（Higher-Ranked Trait Bounds）：

```rust
// for<'a> 语法表示对所有可能的生命周期 'a
trait Processor {
    fn process<F>(&self, f: F)
    where
        F: for<'a> Fn(&'a str) -> &'a str;
}

struct TextProcessor;

impl Processor for TextProcessor {
    fn process<F>(&self, f: F)
    where
        F: for<'a> Fn(&'a str) -> &'a str,
    {
        let text = String::from("Hello, world!");
        let result = f(&text);
        println!("Processed: {}", result);
    }
}

// 使用示例
fn hrtb_example() {
    let processor = TextProcessor;
    processor.process(|s| {
        if s.len() > 5 {
            &s[..5]
        } else {
            s
        }
    });
}
```

### 4.2 HRTB 高级应用

```rust
// 高阶闭包trait
trait ClosureProcessor {
    fn apply<F>(&self, f: F) -> String
    where
        F: for<'a> Fn(&'a str) -> &'a str;
}

struct DataProcessor {
    data: Vec<String>,
}

impl ClosureProcessor for DataProcessor {
    fn apply<F>(&self, f: F) -> String
    where
        F: for<'a> Fn(&'a str) -> &'a str,
    {
        self.data
            .iter()
            .map(|s| f(s))
            .collect::<Vec<_>>()
            .join(", ")
    }
}

// 组合多个HRTB
trait MultiProcessor {
    fn process_multi<F, G>(&self, f: F, g: G) -> String
    where
        F: for<'a> Fn(&'a str) -> &'a str,
        G: for<'b> Fn(&'b str) -> bool;
}

impl MultiProcessor for DataProcessor {
    fn process_multi<F, G>(&self, f: F, g: G) -> String
    where
        F: for<'a> Fn(&'a str) -> &'a str,
        G: for<'b> Fn(&'b str) -> bool,
    {
        self.data
            .iter()
            .filter(|s| g(s))
            .map(|s| f(s))
            .collect::<Vec<_>>()
            .join(", ")
    }
}
```

## 5. 借用检查器的高级技巧

### 5.1 非词汇生命周期（NLL）

NLL 让借用检查器更加智能：

```rust
// NLL 之前需要的写法
fn nll_before() {
    let mut data = vec![1, 2, 3];
    {
        let borrow = &data;
        println!("{:?}", borrow);
    } // borrow 在这里结束
    data.push(4); // 现在可以修改
}

// NLL 之后的写法
fn nll_after() {
    let mut data = vec![1, 2, 3];
    let borrow = &data;
    println!("{:?}", borrow);
    // borrow 的生命周期在最后一次使用后就结束了
    data.push(4); // 直接可以修改
}

// NLL 处理条件分支
fn nll_conditional(condition: bool) {
    let mut data = vec![1, 2, 3];
    
    let borrow = if condition {
        &data[0]
    } else {
        &data[1]
    };
    
    println!("Value: {}", borrow);
    // borrow 在这里结束
    
    data.push(4); // 可以修改
}

// NLL 处理返回值
fn nll_return(data: &mut Vec<i32>) -> Option<&i32> {
    if data.is_empty() {
        data.push(0);
        return None;
    }
    Some(&data[0])
}
```

### 5.2 Polonius 借用检查器

Polonius 是新一代借用检查器：

```rust
// Polonius 可以处理更复杂的借用模式
fn polonius_example() {
    let mut data = vec![1, 2, 3];
    let mut iter = data.iter_mut();
    
    // 可以在迭代中修改
    while let Some(value) = iter.next() {
        *value += 1;
    }
    
    // 迭代器在这里结束，可以再次借用
    data.push(4);
}

// Polonius 处理嵌套借用
struct Node {
    value: i32,
    next: Option<Box<Node>>,
}

impl Node {
    fn process_chain(&mut self) {
        let mut current = self;
        loop {
            current.value += 1;
            
            match &mut current.next {
                Some(next) => current = next,
                None => break,
            }
        }
    }
}
```

## 6. 智能指针与借用

### 6.1 Rc 和 Arc

引用计数智能指针：

```rust
use std::rc::Rc;
use std::sync::Arc;
use std::thread;

// Rc: 单线程引用计数
fn rc_example() {
    let data = Rc::new(vec![1, 2, 3]);
    
    let data1 = Rc::clone(&data);
    let data2 = Rc::clone(&data);
    
    println!("Count: {}", Rc::strong_count(&data)); // 3
    println!("Data: {:?}", data1);
    println!("Data: {:?}", data2);
}

// Arc: 多线程引用计数
fn arc_example() {
    let data = Arc::new(vec![1, 2, 3]);
    let mut handles = vec![];
    
    for i in 0..3 {
        let data_clone = Arc::clone(&data);
        let handle = thread::spawn(move || {
            println!("Thread {}: {:?}", i, data_clone);
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
}

// Rc 与 RefCell 结合
use std::cell::RefCell;

type SharedData = Rc<RefCell<Vec<i32>>>;

fn rc_refcell_example() {
    let data: SharedData = Rc::new(RefCell::new(vec![1, 2, 3]));
    
    let data1 = Rc::clone(&data);
    let data2 = Rc::clone(&data);
    
    // 可以通过不同的 Rc 修改同一数据
    data1.borrow_mut().push(4);
    data2.borrow_mut().push(5);
    
    println!("{:?}", data.borrow()); // [1, 2, 3, 4, 5]
}
```

### 6.2 Cow (Clone-on-Write)

写时复制智能指针：

```rust
use std::borrow::Cow;

// Cow 基础使用
fn cow_example() {
    let s = "Hello";
    let cow: Cow<str> = Cow::Borrowed(s);
    
    println!("{}", cow); // Hello
    
    // 需要修改时才会复制
    let cow_owned: Cow<str> = Cow::Owned(s.to_string() + " World");
    println!("{}", cow_owned); // Hello World
}

// Cow 高级应用
fn process_string(s: &str) -> Cow<str> {
    if s.contains("placeholder") {
        // 需要修改，创建owned版本
        Cow::Owned(s.replace("placeholder", "value"))
    } else {
        // 不需要修改，借用原始字符串
        Cow::Borrowed(s)
    }
}

// 使用示例
fn use_cow() {
    let text1 = "This is a placeholder";
    let text2 = "This is normal text";
    
    let result1 = process_string(text1);
    let result2 = process_string(text2);
    
    println!("Result 1: {}", result1); // 会复制
    println!("Result 2: {}", result2); // 不会复制
}

// Cow 用于配置
#[derive(Debug)]
struct Config<'a> {
    name: Cow<'a, str>,
    value: Cow<'a, str>,
}

impl<'a> Config<'a> {
    fn new(name: &'a str, value: &'a str) -> Self {
        Self {
            name: Cow::Borrowed(name),
            value: Cow::Borrowed(value),
        }
    }
    
    fn with_modified_value(mut self, new_value: String) -> Self {
        self.value = Cow::Owned(new_value);
        self
    }
}
```

## 7. 借用模式最佳实践

### 7.1 避免借用冲突

```rust
// 技巧1：使用作用域限制借用
fn scope_limiting() {
    let mut data = vec![1, 2, 3];
    
    {
        let borrow = &data;
        println!("{:?}", borrow);
    } // borrow 在这里结束
    
    data.push(4); // 可以修改
}

// 技巧2：重构函数避免借用冲突
struct DataProcessor {
    data: Vec<i32>,
    config: String,
}

impl DataProcessor {
    // 不好的设计
    fn process_bad(&mut self) {
        let config = &self.config; // 借用 self
        // self.data.push(1); // 错误：不能在借用 self 时修改
    }
    
    // 好的设计：分离借用
    fn process_good(&mut self) {
        let config = self.config.clone(); // 复制配置
        self.process_with_config(&config); // 现在可以修改 self
    }
    
    fn process_with_config(&mut self, config: &str) {
        self.data.push(config.len() as i32);
    }
}

// 技巧3：使用辅助函数
impl DataProcessor {
    fn helper_get_config(&self) -> &str {
        &self.config
    }
    
    fn process_with_helper(&mut self) {
        let config = self.helper_get_config().to_string();
        self.data.push(config.len() as i32);
    }
}
```

### 7.2 优化借用性能

```rust
// 优化1：避免不必要的克隆
fn avoid_clone_bad(data: Vec<String>) -> Vec<String> {
    let mut result = data.clone(); // 不必要的克隆
    result.push("new".to_string());
    result
}

fn avoid_clone_good(mut data: Vec<String>) -> Vec<String> {
    data.push("new".to_string()); // 直接修改
    data
}

// 优化2：使用借用而不是所有权
fn use_borrow_bad(data: Vec<i32>) -> i32 {
    data.iter().sum() // data 被移动
}

fn use_borrow_good(data: &[i32]) -> i32 {
    data.iter().sum() // 只借用，不移动
}

// 优化3：返回借用而不是克隆
struct DataHolder {
    data: Vec<String>,
}

impl DataHolder {
    fn get_data_bad(&self) -> Vec<String> {
        self.data.clone() // 昂贵的克隆
    }
    
    fn get_data_good(&self) -> &[String] {
        &self.data // 返回借用
    }
}

// 优化4：使用迭代器避免借用
fn iterator_optimization(data: &[i32]) -> Vec<i32> {
    // 使用迭代器链，避免中间借用
    data.iter()
        .filter(|&&x| x > 0)
        .map(|&x| x * 2)
        .collect()
}
```

## 📚 总结

高级借用模式是 Rust 编程的核心技能，掌握这些模式可以：

1. **借用分割**：同时借用数据的不同部分
2. **内部可变性**：在不可变引用下修改数据
3. **生命周期省略**：简化代码，让编译器推断生命周期
4. **HRTB**：处理泛型生命周期约束
5. **智能指针**：灵活管理所有权和借用
6. **最佳实践**：写出高效且安全的代码

通过深入理解这些高级借用模式，开发者可以：

- 编写更灵活的API
- 避免不必要的数据复制
- 构建复杂的数据结构
- 实现零成本抽象

---

**相关文档**：

- [借用理论](../01_theory/02_borrowing_theory.md)
- [生命周期注解](../02_core/03_lifetime_annotations.md)
- [智能指针系统](./04_smart_pointers.md)
- [内存安全保证](../04_safety/01_memory_safety.md)

**最后更新**: 2025年1月27日  
**维护状态**: 活跃维护中  
**质量等级**: 完整版
