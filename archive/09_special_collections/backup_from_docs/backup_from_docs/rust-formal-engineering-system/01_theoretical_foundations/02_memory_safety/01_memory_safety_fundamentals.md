# 内存安全基础（Memory Safety Fundamentals）

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: ✅ 已完善

---

## 📊 目录

- [内存安全基础（Memory Safety Fundamentals）](#内存安全基础memory-safety-fundamentals)
  - [📊 目录](#-目录)
  - [概述](#概述)
  - [所有权系统](#所有权系统)
    - [所有权规则](#所有权规则)
    - [移动语义](#移动语义)
    - [克隆](#克隆)
  - [借用检查器](#借用检查器)
    - [不可变借用](#不可变借用)
    - [可变借用](#可变借用)
    - [借用规则](#借用规则)
  - [生命周期](#生命周期)
    - [生命周期注解](#生命周期注解)
    - [结构体中的生命周期](#结构体中的生命周期)
  - [实践示例](#实践示例)
    - [示例 1：避免悬垂指针](#示例-1避免悬垂指针)
    - [示例 2：切片](#示例-2切片)
    - [示例 3：数据竞争防护](#示例-3数据竞争防护)
  - [最佳实践](#最佳实践)
    - [1. 优先使用引用](#1-优先使用引用)
    - [2. 使用切片](#2-使用切片)
    - [3. 生命周期省略](#3-生命周期省略)
  - [参考资料](#参考资料)

---

## 概述

Rust 的内存安全系统通过所有权、借用和生命周期机制，在编译时防止常见的内存安全问题，如空指针解引用、数据竞争、内存泄漏等。

## 所有权系统

### 所有权规则

```rust
// 所有权规则：
// 1. 每个值都有一个所有者
// 2. 同一时间只能有一个所有者
// 3. 当所有者离开作用域时，值会被丢弃

fn ownership_example() {
    let s = String::from("hello");  // s 拥有字符串
    takes_ownership(s);              // s 的所有权被移动
    // println!("{}", s);            // 错误：s 不再有效
}

fn takes_ownership(some_string: String) {
    println!("{}", some_string);
}  // some_string 离开作用域，内存被释放
```

### 移动语义

```rust
fn move_semantics() {
    let s1 = String::from("hello");
    let s2 = s1;  // s1 的所有权移动到 s2
    // println!("{}", s1);  // 错误：s1 不再有效
    println!("{}", s2);  // 正确：s2 拥有字符串
}
```

### 克隆

```rust
fn clone_example() {
    let s1 = String::from("hello");
    let s2 = s1.clone();  // 深拷贝，s1 和 s2 都有效
    println!("{}", s1);   // 正确
    println!("{}", s2);   // 正确
}
```

## 借用检查器

### 不可变借用

```rust
fn borrowing_example() {
    let s = String::from("hello");
    let len = calculate_length(&s);  // 不可变借用
    println!("'{}' 的长度是 {}", s, len);  // s 仍然有效
}

fn calculate_length(s: &String) -> usize {
    s.len()
}  // s 离开作用域，但因为它只是借用，所以不会释放内存
```

### 可变借用

```rust
fn mutable_borrowing() {
    let mut s = String::from("hello");
    change(&mut s);  // 可变借用
    println!("{}", s);
}

fn change(some_string: &mut String) {
    some_string.push_str(", world");
}
```

### 借用规则

```rust
// 借用规则：
// 1. 同一时间，只能有一个可变借用，或者多个不可变借用
// 2. 借用必须始终有效

fn borrowing_rules() {
    let mut s = String::from("hello");

    let r1 = &s;      // 不可变借用
    let r2 = &s;      // 不可变借用，可以
    // let r3 = &mut s;  // 错误：不能同时有可变和不可变借用
    println!("{} 和 {}", r1, r2);

    let r3 = &mut s;  // 现在可以了，r1 和 r2 已经不再使用
    println!("{}", r3);
}
```

## 生命周期

### 生命周期注解

```rust
// 生命周期注解确保引用有效
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}

fn lifetime_example() {
    let string1 = String::from("long string is long");
    {
        let string2 = String::from("xyz");
        let result = longest(string1.as_str(), string2.as_str());
        println!("最长的字符串是 {}", result);
    }
}
```

### 结构体中的生命周期

```rust
struct ImportantExcerpt<'a> {
    part: &'a str,
}

impl<'a> ImportantExcerpt<'a> {
    fn level(&self) -> i32 {
        3
    }

    fn announce_and_return_part(&self, announcement: &str) -> &str {
        println!("注意！{}", announcement);
        self.part
    }
}
```

## 实践示例

### 示例 1：避免悬垂指针

```rust
// ❌ 错误：返回悬垂指针
// fn dangle() -> &String {
//     let s = String::from("hello");
//     &s  // 错误：s 离开作用域后，引用无效
// }

// ✅ 正确：返回所有权
fn no_dangle() -> String {
    let s = String::from("hello");
    s  // 返回所有权
}
```

### 示例 2：切片

```rust
fn slice_example() {
    let s = String::from("hello world");
    let word = first_word(&s);
    println!("第一个单词: {}", word);
}

fn first_word(s: &str) -> &str {
    let bytes = s.as_bytes();

    for (i, &item) in bytes.iter().enumerate() {
        if item == b' ' {
            return &s[0..i];
        }
    }

    &s[..]
}
```

### 示例 3：数据竞争防护

```rust
use std::sync::{Arc, Mutex};
use std::thread;

fn data_race_prevention() {
    let data = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let data = Arc::clone(&data);
        let handle = thread::spawn(move || {
            let mut num = data.lock().unwrap();
            *num += 1;
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("结果: {}", *data.lock().unwrap());
}
```

## 最佳实践

### 1. 优先使用引用

```rust
// ✅ 正确：使用引用避免移动
fn process_string(s: &String) {
    // 处理字符串
}

// ❌ 错误：不必要地移动所有权
fn process_string(s: String) {
    // 处理字符串
}
```

### 2. 使用切片

```rust
// ✅ 正确：使用 &str 更灵活
fn process_text(s: &str) {
    // 处理文本
}

// ❌ 错误：限制性太强
fn process_text(s: &String) {
    // 处理文本
}
```

### 3. 生命周期省略

```rust
// Rust 编译器可以自动推断生命周期
fn first_word(s: &str) -> &str {
    // 编译器自动添加生命周期注解
    let bytes = s.as_bytes();
    for (i, &item) in bytes.iter().enumerate() {
        if item == b' ' {
            return &s[0..i];
        }
    }
    &s[..]
}
```

## 参考资料

- [内存安全索引](./00_index.md)
- [理论基础索引](../00_index.md)
- [所有权和借用](../../08_practical_examples/01_basic_examples/01_ownership_and_borrowing.md)

---

**导航**:

- 返回索引: [`00_index.md`](./00_index.md)
- 返回理论基础: [`../00_index.md`](../00_index.md)
