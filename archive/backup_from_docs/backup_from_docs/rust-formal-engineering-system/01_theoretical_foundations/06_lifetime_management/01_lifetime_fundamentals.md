# 生命周期基础（Lifetime Fundamentals）

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: ✅ 已完善

---

## 📊 目录

- [生命周期基础](#生命周期基础lifetime-fundamentals)
  - [概述](#概述)
  - [生命周期注解](#生命周期注解)
  - [生命周期省略规则](#生命周期省略规则)
  - [生命周期约束](#生命周期约束)
  - [实践示例](#实践示例)
  - [常见问题](#常见问题)
  - [参考资料](#参考资料)

---

## 概述

生命周期（Lifetime）是 Rust 类型系统的重要组成部分，用于确保引用在使用期间始终有效。生命周期注解帮助编译器理解引用的有效范围。

## 生命周期注解

### 基本语法

```rust
// 函数中的生命周期注解
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}
```

### 结构体中的生命周期

```rust
// 结构体包含引用时需要生命周期注解
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

### 方法中的生命周期

```rust
impl<'a> ImportantExcerpt<'a> {
    // 第一个生命周期省略规则适用
    fn first_word(&self) -> &str {
        self.part.split_whitespace().next().unwrap()
    }

    // 需要显式生命周期注解
    fn longest_part<'b>(&self, other: &'b str) -> &'a str
    where
        'b: 'a,  // 'b 必须至少和 'a 一样长
    {
        if self.part.len() > other.len() {
            self.part
        } else {
            self.part  // 返回 self.part，生命周期为 'a
        }
    }
}
```

## 生命周期省略规则

Rust 编译器有三条生命周期省略规则：

### 规则 1：每个引用参数都有自己的生命周期

```rust
// 编译器自动添加生命周期
fn first_word(s: &str) -> &str {
    // 等价于：
    // fn first_word<'a>(s: &'a str) -> &'a str
}
```

### 规则 2：如果只有一个输入生命周期参数，它被赋予所有输出生命周期参数

```rust
// 编译器自动推断
fn longest(x: &str, y: &str) -> &str {
    // 等价于：
    // fn longest<'a>(x: &'a str, y: &'a str) -> &'a str
    // 但这样会有问题，因为 x 和 y 可能有不同的生命周期
}
```

### 规则 3：如果方法有 `&self` 或 `&mut self`，`self` 的生命周期被赋予所有输出生命周期参数

```rust
impl ImportantExcerpt<'_> {
    // 编译器自动推断
    fn announce_and_return_part(&self, announcement: &str) -> &str {
        // 等价于：
        // fn announce_and_return_part<'a, 'b>(&'a self, announcement: &'b str) -> &'a str
        self.part
    }
}
```

## 生命周期约束

### 生命周期子类型

```rust
// 'b 必须至少和 'a 一样长
fn longest_with_an_announcement<'a, 'b>(
    x: &'a str,
    y: &'a str,
    ann: &'b str,
) -> &'a str
where
    'b: 'a,  // 'b 必须至少和 'a 一样长
{
    println!("公告！{}", ann);
    if x.len() > y.len() {
        x
    } else {
        y
    }
}
```

### 静态生命周期

```rust
// 'static 生命周期表示整个程序运行期间都有效
let s: &'static str = "我拥有静态生命周期";

// 字符串字面量有 'static 生命周期
fn get_static_str() -> &'static str {
    "静态字符串"
}
```

## 实践示例

### 示例 1：返回引用

```rust
struct TextProcessor<'a> {
    text: &'a str,
}

impl<'a> TextProcessor<'a> {
    fn new(text: &'a str) -> Self {
        TextProcessor { text }
    }

    fn first_sentence(&self) -> &'a str {
        self.text
            .split('.')
            .next()
            .unwrap_or(self.text)
    }

    fn longest_word(&self) -> &'a str {
        self.text
            .split_whitespace()
            .max_by_key(|word| word.len())
            .unwrap_or("")
    }
}
```

### 示例 2：多个生命周期参数

```rust
struct MultiLifetime<'a, 'b> {
    first: &'a str,
    second: &'b str,
}

impl<'a, 'b> MultiLifetime<'a, 'b> {
    fn new(first: &'a str, second: &'b str) -> Self {
        MultiLifetime { first, second }
    }

    // 返回 'a 生命周期的引用
    fn get_first(&self) -> &'a str {
        self.first
    }

    // 返回 'b 生命周期的引用
    fn get_second(&self) -> &'b str {
        self.second
    }

    // 返回较短生命周期的引用
    fn get_shorter(&self) -> &'a str
    where
        'b: 'a,
    {
        if self.first.len() < self.second.len() {
            self.first
        } else {
            self.first  // 必须返回 'a 生命周期的引用
        }
    }
}
```

### 示例 3：生命周期与泛型结合

```rust
use std::fmt::Display;

fn longest_with_an_announcement<'a, T>(
    x: &'a str,
    y: &'a str,
    ann: T,
) -> &'a str
where
    T: Display,
{
    println!("公告！{}", ann);
    if x.len() > y.len() {
        x
    } else {
        y
    }
}
```

## 常见问题

### 问题 1：返回局部变量的引用

```rust
// ❌ 错误：不能返回局部变量的引用
fn invalid_function() -> &str {
    let s = String::from("hello");
    &s  // s 在函数结束时被丢弃
}

// ✅ 正确：返回参数中的引用
fn valid_function(s: &str) -> &str {
    s
}
```

### 问题 2：生命周期不匹配

```rust
// ❌ 错误：生命周期不匹配
fn problematic() {
    let string1 = String::from("long string is long");
    let result;
    {
        let string2 = String::from("xyz");
        result = longest(string1.as_str(), string2.as_str());
        // string2 在这里被丢弃
    }
    println!("最长的字符串是 {}", result);  // result 引用了已丢弃的 string2
}

// ✅ 正确：确保引用的生命周期足够长
fn correct() {
    let string1 = String::from("long string is long");
    let string2 = String::from("xyz");
    let result = longest(string1.as_str(), string2.as_str());
    println!("最长的字符串是 {}", result);
}
```

### 问题 3：结构体生命周期

```rust
// ❌ 错误：结构体包含的引用生命周期不够长
fn invalid_struct() {
    let r;
    {
        let x = 5;
        r = &x;  // x 在这里被丢弃
    }
    println!("r: {}", r);  // r 引用了已丢弃的 x
}

// ✅ 正确：确保引用的生命周期足够长
fn valid_struct() {
    let x = 5;
    let r = &x;
    println!("r: {}", r);
}
```

## 参考资料

- [生命周期管理索引](./00_index.md)
- [所有权与借用理论](../../03_ownership_borrowing/00_index.md)
- [Rust 生命周期文档](https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html)

---

**导航**:

- 返回索引: [`00_index.md`](./00_index.md)
- 返回理论基础: [`../00_index.md`](../00_index.md)
