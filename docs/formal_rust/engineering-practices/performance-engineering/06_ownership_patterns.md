# 所有权设计模式


## 📊 目录

- [概述](#概述)
- [1. 所有权模式理论基础](#1-所有权模式理论基础)
  - [1.1 所有权规则](#11-所有权规则)
  - [1.2 形式化语义](#12-形式化语义)
- [2. 所有权转移模式](#2-所有权转移模式)
  - [2.1 Move语义](#21-move语义)
  - [2.2 Clone语义](#22-clone语义)
- [3. 借用模式](#3-借用模式)
  - [3.1 不可变借用](#31-不可变借用)
  - [3.2 可变借用](#32-可变借用)
- [4. 生命周期模式](#4-生命周期模式)
  - [4.1 生命周期注解](#41-生命周期注解)
  - [4.2 生命周期省略](#42-生命周期省略)
- [5. 智能指针模式](#5-智能指针模式)
  - [5.1 `Box<T>` - 堆分配](#51-boxt-堆分配)
  - [5.2 `Rc<T>` - 共享所有权](#52-rct-共享所有权)
  - [5.3 `Arc<T>` - 线程安全共享](#53-arct-线程安全共享)
- [6. 内部可变性模式](#6-内部可变性模式)
  - [6.1 `RefCell<T>` - 运行时借用检查](#61-refcellt-运行时借用检查)
  - [6.2 `Mutex<T>` - 线程安全内部可变性](#62-mutext-线程安全内部可变性)
- [7. 形式化证明](#7-形式化证明)
  - [7.1 内存安全定理](#71-内存安全定理)
  - [7.2 数据竞争自由定理](#72-数据竞争自由定理)
- [8. 工程实践](#8-工程实践)
  - [8.1 最佳实践](#81-最佳实践)
  - [8.2 常见陷阱](#82-常见陷阱)
- [9. 交叉引用](#9-交叉引用)
- [10. 参考文献](#10-参考文献)


## 概述

本文档详细分析Rust所有权系统的设计模式，包括所有权转移、借用管理和生命周期设计。

## 1. 所有权模式理论基础

### 1.1 所有权规则

Rust的所有权系统基于三个核心规则：

```rust
// 规则1: 每个值都有一个所有者
let s1 = String::from("hello");

// 规则2: 同一时间只能有一个所有者
let s2 = s1; // s1的所有权移动到s2
// println!("{}", s1); // 编译错误：s1已被移动

// 规则3: 当所有者离开作用域时，值被丢弃
{
    let s3 = String::from("world");
    // s3在这里被自动释放
}
```

### 1.2 形式化语义

所有权可以形式化为线性类型系统：

$$
\text{Ownership}(T) = \text{Linear}(T) \times \text{Lifetime}(T)
$$

其中Linear(T)表示线性类型，Lifetime(T)表示生命周期约束。

## 2. 所有权转移模式

### 2.1 Move语义

```rust
struct Data {
    value: i32,
}

fn take_ownership(data: Data) -> i32 {
    data.value // 所有权转移，返回后data被释放
}

fn main() {
    let data = Data { value: 42 };
    let result = take_ownership(data);
    // data在这里已经不可用
}
```

### 2.2 Clone语义

```rust
#[derive(Clone)]
struct CloneableData {
    value: i32,
}

fn borrow_and_clone(data: &CloneableData) -> CloneableData {
    data.clone() // 创建副本，原数据保持不变
}
```

## 3. 借用模式

### 3.1 不可变借用

```rust
fn calculate_sum(data: &[i32]) -> i32 {
    data.iter().sum()
}

fn main() {
    let numbers = vec![1, 2, 3, 4, 5];
    let sum = calculate_sum(&numbers);
    // numbers仍然可用
}
```

### 3.2 可变借用

```rust
fn modify_data(data: &mut [i32]) {
    for item in data.iter_mut() {
        *item *= 2;
    }
}

fn main() {
    let mut numbers = vec![1, 2, 3, 4, 5];
    modify_data(&mut numbers);
    // numbers被修改
}
```

## 4. 生命周期模式

### 4.1 生命周期注解

```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}

struct ImportantExcerpt<'a> {
    part: &'a str,
}
```

### 4.2 生命周期省略

```rust
// 生命周期省略规则
fn first_word(s: &str) -> &str {
    // 编译器自动推断生命周期
    s.split_whitespace().next().unwrap_or("")
}
```

## 5. 智能指针模式

### 5.1 `Box<T>` - 堆分配

```rust
struct TreeNode {
    value: i32,
    left: Option<Box<TreeNode>>,
    right: Option<Box<TreeNode>>,
}

impl TreeNode {
    fn new(value: i32) -> Self {
        TreeNode {
            value,
            left: None,
            right: None,
        }
    }
}
```

### 5.2 `Rc<T>` - 共享所有权

```rust
use std::rc::Rc;

struct SharedData {
    value: i32,
}

fn main() {
    let data = Rc::new(SharedData { value: 42 });
    let data1 = Rc::clone(&data);
    let data2 = Rc::clone(&data);
    // 多个所有者共享数据
}
```

### 5.3 `Arc<T>` - 线程安全共享

```rust
use std::sync::Arc;
use std::thread;

fn main() {
    let data = Arc::new(vec![1, 2, 3, 4, 5]);
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
```

## 6. 内部可变性模式

### 6.1 `RefCell<T>` - 运行时借用检查

```rust
use std::cell::RefCell;

struct MockMessenger {
    sent_messages: RefCell<Vec<String>>,
}

impl MockMessenger {
    fn new() -> MockMessenger {
        MockMessenger {
            sent_messages: RefCell::new(vec![]),
        }
    }
    
    fn send_message(&self, msg: &str) {
        self.sent_messages.borrow_mut().push(String::from(msg));
    }
}
```

### 6.2 `Mutex<T>` - 线程安全内部可变性

```rust
use std::sync::Mutex;

struct SharedCounter {
    count: Mutex<i32>,
}

impl SharedCounter {
    fn new() -> Self {
        SharedCounter {
            count: Mutex::new(0),
        }
    }
    
    fn increment(&self) {
        let mut count = self.count.lock().unwrap();
        *count += 1;
    }
}
```

## 7. 形式化证明

### 7.1 内存安全定理

**定理**: Rust的所有权系统保证内存安全。

**证明**: 通过线性类型系统和生命周期分析证明无悬垂指针和数据竞争。

### 7.2 数据竞争自由定理

**定理**: Rust的借用检查器保证数据竞争自由。

**证明**: 通过借用规则证明同一时间不能有多个可变引用。

## 8. 工程实践

### 8.1 最佳实践

1. 优先使用借用而不是克隆
2. 合理使用智能指针
3. 避免不必要的所有权转移
4. 正确使用生命周期注解

### 8.2 常见陷阱

1. 循环引用导致内存泄漏
2. 生命周期注解错误
3. 过度使用克隆影响性能

## 9. 交叉引用

- [资源管理模型](./01_resource_management.md) - 资源管理理论基础
- [并发安全性保证](./07_concurrency_safety.md) - 并发安全保证机制
- [并发编程模式](./08_parallel_patterns.md) - 并发编程模式设计

## 10. 参考文献

1. Rust Ownership System
2. Linear Type Theory
3. Smart Pointer Patterns
4. Lifetime Management
