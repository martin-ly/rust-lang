# 所有权基础练习

> **难度**: 🟢 简单
> **目标**: 掌握 Rust 所有权系统基础

---

## 练习 1: 移动语义

### 题目

```rust
fn main() {
    let s1 = String::from("hello");
    let s2 = s1;

    println!("{}", s1);  // 这里会报错，为什么？
}
```

### 答案

```rust
fn main() {
    let s1 = String::from("hello");
    let s2 = s1;  // s1 被移动到 s2

    // println!("{}", s1);  // 错误：s1 不再有效
    println!("{}", s2);     // 正确：s2 拥有数据
}
```

**解释**: String 不实现 Copy trait，赋值时发生所有权移动。

---

## 练习 2: 借用规则

### 题目

修复以下代码：

```rust
fn main() {
    let mut s = String::from("hello");

    let r1 = &s;
    let r2 = &mut s;

    println!("{} {}", r1, r2);
}
```

### 答案

```rust
fn main() {
    let mut s = String::from("hello");

    let r1 = &s;
    println!("{}", r1);  // 在 r2 之前使用 r1

    let r2 = &mut s;      // 现在可以创建可变借用
    println!("{}", r2);
}
```

**解释**: 不能同时拥有不可变和可变借用。

---

## 练习 3: 生命周期

### 题目

实现一个函数，返回两个字符串切片中较长的一个。

```rust
fn longest(x: &str, y: &str) -> &str {
    // 实现这里
}
```

### 答案

```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}

fn main() {
    let string1 = String::from("long string is long");
    {
        let string2 = String::from("xyz");
        let result = longest(&string1, &string2);
        println!("The longest string is {}", result);
    }
}
```

---

## 练习 4: 实现自定义智能指针

### 题目

实现一个简单的 Box。

### 答案

```rust
use std::ops::Deref;

struct MyBox<T>(T);

impl<T> MyBox<T> {
    fn new(x: T) -> MyBox<T> {
        MyBox(x)
    }
}

impl<T> Deref for MyBox<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.0
    }
}

impl<T> Drop for MyBox<T> {
    fn drop(&mut self) {
        println!("Dropping MyBox!");
    }
}
```

---

*更多练习持续添加中...*
