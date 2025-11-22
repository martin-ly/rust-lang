# 所有权与借用基础示例（Ownership and Borrowing Basics）

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: ✅ 已完善

---

## 📊 目录

- [所有权与借用基础示例（Ownership and Borrowing Basics）](#所有权与借用基础示例ownership-and-borrowing-basics)
  - [📊 目录](#-目录)
  - [概述](#概述)
  - [所有权基础](#所有权基础)
    - [移动语义](#移动语义)
    - [克隆](#克隆)
    - [Copy 类型](#copy-类型)
  - [借用基础](#借用基础)
    - [不可变借用](#不可变借用)
    - [借用规则](#借用规则)
  - [可变借用](#可变借用)
    - [基本用法](#基本用法)
  - [实践示例](#实践示例)
    - [示例 1：字符串处理](#示例-1字符串处理)
    - [示例 2：结构体所有权](#示例-2结构体所有权)
    - [示例 3：向量所有权](#示例-3向量所有权)
  - [常见错误](#常见错误)
    - [错误 1：使用已移动的值](#错误-1使用已移动的值)
    - [错误 2：悬垂引用](#错误-2悬垂引用)
    - [错误 3：同时有可变和不可变借用](#错误-3同时有可变和不可变借用)
  - [参考资料](#参考资料)

---

## 概述

所有权（Ownership）是 Rust 的核心特性，它确保内存安全而无需垃圾回收。本示例展示所有权和借用的基本用法。

## 所有权基础

### 移动语义

```rust
// 示例 1：值的移动
fn main() {
    let s1 = String::from("hello");
    let s2 = s1;  // s1 被移动到 s2
    // println!("{}", s1);  // ❌ 错误：s1 不再有效
    println!("{}", s2);  // ✅ 正确
}

// 示例 2：函数参数移动
fn take_ownership(s: String) {
    println!("{}", s);
}  // s 在这里被丢弃

fn main() {
    let s = String::from("hello");
    take_ownership(s);
    // println!("{}", s);  // ❌ 错误：s 已被移动
}
```

### 克隆

```rust
// 示例：使用 clone 创建深拷贝
fn main() {
    let s1 = String::from("hello");
    let s2 = s1.clone();  // 创建深拷贝
    println!("{}", s1);   // ✅ 正确：s1 仍然有效
    println!("{}", s2);   // ✅ 正确
}
```

### Copy 类型

```rust
// 示例：Copy 类型自动复制
fn main() {
    let x = 5;
    let y = x;  // x 被复制（不是移动）
    println!("{}", x);  // ✅ 正确：x 仍然有效
    println!("{}", y);
}

// Copy 类型包括：
// - 整数类型（i32, u32, 等）
// - 布尔类型（bool）
// - 字符类型（char）
// - 浮点类型（f64, f32）
// - 包含 Copy 类型的元组
```

## 借用基础

### 不可变借用

```rust
// 示例：不可变借用
fn calculate_length(s: &String) -> usize {
    s.len()
}  // s 离开作用域，但因为它只是引用，不会丢弃值

fn main() {
    let s1 = String::from("hello");
    let len = calculate_length(&s1);
    println!("'{}' 的长度是 {}", s1, len);  // ✅ s1 仍然有效
}

// 示例：多个不可变借用
fn main() {
    let s = String::from("hello");
    let r1 = &s;
    let r2 = &s;
    println!("{}, {}", r1, r2);  // ✅ 可以有多个不可变借用
}
```

### 借用规则

```rust
// 规则 1：任意时刻，只能有一个可变引用，或者任意数量的不可变引用
fn main() {
    let mut s = String::from("hello");

    let r1 = &s;      // ✅ 不可变借用
    let r2 = &s;      // ✅ 不可变借用
    // let r3 = &mut s;  // ❌ 错误：不能同时有可变和不可变借用
    println!("{}, {}", r1, r2);

    // r1 和 r2 离开作用域后
    let r3 = &mut s;  // ✅ 现在可以可变借用
    r3.push_str(" world");
}
```

## 可变借用

### 基本用法

```rust
// 示例：可变借用
fn change(s: &mut String) {
    s.push_str(", world");
}

fn main() {
    let mut s = String::from("hello");
    change(&mut s);
    println!("{}", s);  // 输出：hello, world
}

// 示例：可变借用限制
fn main() {
    let mut s = String::from("hello");

    let r1 = &mut s;
    // let r2 = &mut s;  // ❌ 错误：不能同时有两个可变借用
    r1.push_str(", world");

    // r1 离开作用域后
    let r2 = &mut s;  // ✅ 现在可以
    r2.push_str("!");
}
```

## 实践示例

### 示例 1：字符串处理

```rust
// 示例：字符串切片
fn first_word(s: &str) -> &str {
    let bytes = s.as_bytes();

    for (i, &item) in bytes.iter().enumerate() {
        if item == b' ' {
            return &s[0..i];
        }
    }

    &s[..]
}

fn main() {
    let s = String::from("hello world");
    let word = first_word(&s);
    println!("第一个单词: {}", word);
}

// 示例：字符串切片和所有权
fn main() {
    let s = String::from("hello world");
    let word = first_word(&s);
    // s.clear();  // ❌ 错误：不能清空 s，因为 word 是不可变借用
    println!("第一个单词: {}", word);
}
```

### 示例 2：结构体所有权

```rust
// 示例：结构体包含字符串
struct User {
    username: String,
    email: String,
    sign_in_count: u64,
    active: bool,
}

fn build_user(email: String, username: String) -> User {
    User {
        email,      // 字段初始化简写
        username,
        active: true,
        sign_in_count: 1,
    }
}

fn main() {
    let user1 = build_user(
        String::from("someone@example.com"),
        String::from("someusername123"),
    );

    println!("用户: {}", user1.username);
}

// 示例：结构体更新语法
fn main() {
    let user1 = build_user(
        String::from("someone@example.com"),
        String::from("someusername123"),
    );

    let user2 = User {
        email: String::from("another@example.com"),
        ..user1  // 移动 user1 的其他字段
    };

    // println!("{}", user1.email);  // ❌ 错误：user1.email 已被移动
    println!("{}", user2.email);
}
```

### 示例 3：向量所有权

```rust
// 示例：向量的所有权
fn main() {
    let v = vec![1, 2, 3, 4, 5];

    // 移动
    let v2 = v;
    // println!("{:?}", v);  // ❌ 错误：v 已被移动

    // 借用
    let v3 = vec![1, 2, 3, 4, 5];
    let v4 = &v3;
    println!("{:?}", v3);  // ✅ 正确
    println!("{:?}", v4);
}

// 示例：向量元素的所有权
fn main() {
    let mut v = vec![1, 2, 3, 4, 5];

    // 不可变借用
    let first = &v[0];
    // v.push(6);  // ❌ 错误：不能同时有可变和不可变借用
    println!("第一个元素: {}", first);

    // 可变借用
    let first_mut = &mut v[0];
    *first_mut = 10;
    println!("{:?}", v);
}
```

## 常见错误

### 错误 1：使用已移动的值

```rust
// ❌ 错误示例
fn main() {
    let s = String::from("hello");
    let s2 = s;
    println!("{}", s);  // 错误：s 已被移动
}

// ✅ 正确示例
fn main() {
    let s = String::from("hello");
    let s2 = s.clone();
    println!("{}", s);   // 正确
    println!("{}", s2);
}
```

### 错误 2：悬垂引用

```rust
// ❌ 错误示例
fn dangle() -> &String {
    let s = String::from("hello");
    &s  // 错误：返回局部变量的引用
}

// ✅ 正确示例
fn no_dangle() -> String {
    let s = String::from("hello");
    s  // 返回所有权
}
```

### 错误 3：同时有可变和不可变借用

```rust
// ❌ 错误示例
fn main() {
    let mut s = String::from("hello");
    let r1 = &s;
    let r2 = &mut s;  // 错误：不能同时有可变和不可变借用
    println!("{}", r1);
}

// ✅ 正确示例
fn main() {
    let mut s = String::from("hello");
    let r1 = &s;
    println!("{}", r1);  // r1 离开作用域
    let r2 = &mut s;     // 现在可以可变借用
    r2.push_str(" world");
}
```

## 参考资料

- [所有权与借用理论](../../01_theoretical_foundations/03_ownership_borrowing/00_index.md)
- [C01 所有权模块](../../../../crates/c01_ownership_borrow_scope/)
- [Rust 所有权文档](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)

---

**导航**:

- 返回索引: [`00_index.md`](./00_index.md)
- 返回实践示例: [`../00_index.md`](../00_index.md)
