# 2.1 所有权系统 - 完整指南

> **文档类型**: Tier 2 - 实践指南 (完整版)
> **难度**: ⭐⭐ 初级
> **预计学习时间**: 2-3 小时
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+

---

## 📋 目录

- [2.1 所有权系统 - 完整指南](#21-所有权系统---完整指南)
  - [📋 目录](#-目录)
  - [🎯 学习目标](#-学习目标)
  - [1. 所有权三大规则](#1-所有权三大规则)
    - [1.1 规则详解](#11-规则详解)
    - [1.2 为什么需要所有权](#12-为什么需要所有权)
    - [1.3 所有权与内存安全](#13-所有权与内存安全)
  - [2. 变量的所有权](#2-变量的所有权)
    - [2.1 基本示例](#21-基本示例)
    - [2.2 所有权转移 (Move)](#22-所有权转移-move)
    - [2.3 复制语义 (Copy)](#23-复制语义-copy)
  - [3. 函数与所有权](#3-函数与所有权)
  - [4. 返回值与所有权](#4-返回值与所有权)
  - [5. 实战练习](#5-实战练习)
    - [练习 1: 修复所有权错误](#练习-1-修复所有权错误)
    - [练习 2: 实现一个简单的字符串交换函数](#练习-2-实现一个简单的字符串交换函数)
    - [练习 3: 计算字符串长度后不丢失所有权](#练习-3-计算字符串长度后不丢失所有权)
  - [6. 常见错误与解决](#6-常见错误与解决)
    - [错误 1: use of moved value](#错误-1-use-of-moved-value)
    - [错误 2: value used after move](#错误-2-value-used-after-move)
  - [7. 最佳实践](#7-最佳实践)
    - [7.1 何时使用 Move](#71-何时使用-move)
    - [7.2 何时使用 Copy](#72-何时使用-copy)
    - [7.3 何时使用 Clone](#73-何时使用-clone)
  - [✅ 完成检查](#-完成检查)
  - [**版本**: v2.0 (完整版)](#版本-v20-完整版)

---

## 🎯 学习目标

完成本文档后，你将能够：

- ✅ 理解所有权的**三大规则**及其实现原理
- ✅ 区分 **Move** 和 **Copy** 语义
- ✅ 预测代码中的所有权转移
- ✅ 设计合理的所有权策略
- ✅ 解决基本的所有权错误

---

## 1. 所有权三大规则

### 1.1 规则详解

**规则 1: 每个值都有一个所有者**:

```rust
fn rule1() {
    let s = String::from("hello");  // s 是 "hello" 的所有者
    // 每个资源在任意时刻都有唯一的所有者
}
```

**规则 2: 同一时间只能有一个所有者**:

```rust
fn rule2() {
    let s1 = String::from("hello");
    let s2 = s1;  // 所有权从 s1 转移到 s2

    // println!("{}", s1);  // ❌ 错误！s1 不再拥有该值
    println!("{}", s2);     // ✅ 正确！s2 现在是所有者
}
```

**规则 3: 所有者离开作用域时，值被自动释放**:

```rust
fn rule3() {
    {
        let s = String::from("hello");  // s 进入作用域
        // 使用 s
    }  // s 离开作用域，内存自动释放（调用 drop）

    // s 在这里不可用
}
```

### 1.2 为什么需要所有权

**对比其他语言：**

| 语言 | 内存管理方式 | 问题 |
|------|-------------|------|
| C/C++ | 手动管理 | 容易忘记释放（内存泄漏）或重复释放（use-after-free） |
| Java/Python | 垃圾回收 (GC) | 运行时开销，不可预测的暂停 |
| Rust | 所有权系统 | 编译期检查，零运行时开销 |

**Rust 的解决方案：**

- 在编译期跟踪所有权
- 无运行时垃圾回收器
- 保证内存安全且无数据竞争

### 1.3 所有权与内存安全

```rust
fn memory_safety() {
    let s = String::from("hello");

    // Rust 保证以下不会发生：
    // 1. use-after-free（使用已释放内存）
    // 2. double-free（重复释放）
    // 3. 内存泄漏（除非故意使用 Rc/Arc 循环）

    takes_ownership(s);  // s 的所有权转移给函数
    // println!("{}", s);  // ❌ 编译错误！s 已被移动
} // s 不会在这里被释放（已在 takes_ownership 中释放）

fn takes_ownership(s: String) {
    println!("{}", s);
} // s 在这里被释放
```

---

## 2. 变量的所有权

### 2.1 基本示例

```rust
fn main() {
    // 整数是 Copy 类型
    let x = 5;
    let y = x;  // x 被复制到 y，x 仍然有效
    println!("x = {}, y = {}", x, y);  // ✅ 两者都可用

    // String 不是 Copy 类型
    let s1 = String::from("hello");
    let s2 = s1;  // s1 被移动到 s2，s1 不再有效
    // println!("{}", s1);  // ❌ 编译错误！
    println!("{}", s2);     // ✅ s2 有效
}
```

### 2.2 所有权转移 (Move)

**什么情况下发生 Move？**

```rust
fn move_examples() {
    // 1. 赋值给另一个变量
    let s1 = String::from("hello");
    let s2 = s1;  // Move！

    // 2. 传递给函数
    let s3 = String::from("world");
    takes_ownership(s3);  // Move！
    // s3 在这里不可用

    // 3. 从函数返回
    let s4 = gives_ownership();  // Move 返回值
}

fn takes_ownership(s: String) {
    println!("{}", s);
} // s 在这里 drop

fn gives_ownership() -> String {
    String::from("yours")
} // 返回值的所有权转移给调用者
```

### 2.3 复制语义 (Copy)

**哪些类型实现了 Copy？**

```rust
fn copy_types() {
    // 所有标量类型都是 Copy
    let a: i32 = 5;
    let b = a;  // Copy，不是 Move
    println!("a = {}, b = {}", a, b);  // ✅ 两者都可用

    // 布尔类型
    let flag = true;
    let flag2 = flag;  // Copy

    // 字符类型
    let c = 'z';
    let c2 = c;  // Copy

    // 元组（如果所有元素都是 Copy）
    let tup = (1, 2.0, false);
    let tup2 = tup;  // Copy

    // 数组（如果元素是 Copy）
    let arr = [1, 2, 3];
    let arr2 = arr;  // Copy
}

// 自定义类型可以通过 derive 实现 Copy
#[derive(Copy, Clone)]
struct Point {
    x: i32,
    y: i32,
}

fn use_point() {
    let p1 = Point { x: 1, y: 2 };
    let p2 = p1;  // Copy！
    println!("p1.x = {}, p2.x = {}", p1.x, p2.x);  // ✅ 两者都可用
}
```

**什么类型不能实现 Copy？**

```rust
// ❌ String 不能是 Copy（管理堆内存）
// ❌ Vec 不能是 Copy
// ❌ HashMap 不能是 Copy
// ❌ 任何包含非 Copy 类型的结构体不能是 Copy

struct Container {
    data: String,  // String 不是 Copy
}
// 不能 #[derive(Copy, Clone)]
```

---

## 3. 函数与所有权

```rust
fn main() {
    let s = String::from("hello");

    // 情况 1: 传入并返回（转移出去再回来）
    let s = takes_and_gives_back(s);

    // 情况 2: 使用引用（不转移所有权）- 下一章内容
    let len = calculate_length(&s);

    println!("'{}' 的长度是 {}", s, len);  // ✅ s 仍然有效
}

fn takes_and_gives_back(s: String) -> String {
    println!("{}", s);
    s  // 返回所有权
}

fn calculate_length(s: &String) -> usize {
    s.len()
} // s 在这里不会被 drop（因为只是借用）
```

**所有权转移总结图：**

```text
传入函数参数: 值 ──Move──→ 函数参数 ──函数结束──→ drop (除非返回)
返回函数值: 函数内部 ──Move──→ 返回值 ──Move──→ 调用者
```

---

## 4. 返回值与所有权

```rust
fn return_ownership() {
    // 函数可以返回所有权
    let s1 = gives_ownership();

    let s2 = String::from("hello");
    let s3 = takes_and_gives_back(s2);

    // s2 不可用（已移动给函数）
    // s1 和 s3 可用
}

fn gives_ownership() -> String {
    String::from("yours")
}

fn takes_and_gives_back(s: String) -> String {
    s  // 返回传入的值
}
```

---

## 5. 实战练习

### 练习 1: 修复所有权错误

```rust
// 这段代码有错误，请修复
fn exercise1() {
    let s = String::from("hello");
    let s2 = s;
    println!("{}", s);  // ❌ 错误！如何修复？
}

// 答案 1: 使用 s2 而不是 s
fn answer1() {
    let s = String::from("hello");
    let s2 = s;
    println!("{}", s2);  // ✅
}

// 答案 2: 克隆数据
fn answer2() {
    let s = String::from("hello");
    let s2 = s.clone();  // 深拷贝
    println!("{} {}", s, s2);  // ✅ 两者都可用
}
```

### 练习 2: 实现一个简单的字符串交换函数

```rust
fn swap_strings() {
    let mut s1 = String::from("hello");
    let mut s2 = String::from("world");

    // 如何交换 s1 和 s2 的值？
    std::mem::swap(&mut s1, &mut s2);

    println!("s1 = {}, s2 = {}", s1, s2);  // s1 = world, s2 = hello
}
```

### 练习 3: 计算字符串长度后不丢失所有权

```rust
fn exercise3() {
    let s = String::from("hello");

    // 方法 1: 使用引用（推荐）
    let len = get_length(&s);
    println!("{} 的长度是 {}", s, len);  // ✅ s 仍然有效

    // 方法 2: 传入并返回（繁琐）
    let (s, len) = get_length_return(s);
    println!("{} 的长度是 {}", s, len);  // ✅ s 仍然有效
}

fn get_length(s: &String) -> usize {
    s.len()
}

fn get_length_return(s: String) -> (String, usize) {
    let len = s.len();
    (s, len)
}
```

---

## 6. 常见错误与解决

### 错误 1: use of moved value

```rust
fn error1() {
    let s = String::from("hello");
    let s2 = s;
    println!("{}", s);  // ❌ error[E0382]: borrow of moved value: `s`
}

// 解决：使用引用或 clone
fn fix1() {
    let s = String::from("hello");
    let s2 = s.clone();
    println!("{}", s);  // ✅
}
```

### 错误 2: value used after move

```rust
fn error2() {
    let s = String::from("hello");
    takes_ownership(s);
    println!("{}", s);  // ❌ error[E0382]: borrow of moved value
}

fn takes_ownership(s: String) {
    println!("{}", s);
}

// 解决：使用引用
fn fix2() {
    let s = String::from("hello");
    borrow_value(&s);
    println!("{}", s);  // ✅
}

fn borrow_value(s: &String) {
    println!("{}", s);
}
```

---

## 7. 最佳实践

### 7.1 何时使用 Move

```rust
// ✅ 当调用者不再需要该值时
fn consume_data(data: Vec<u8>) {
    // 处理并消耗数据
}

// ✅ 当需要转移所有权到新的作用域
fn transfer_to_thread(data: String) {
    std::thread::spawn(move || {
        println!("{}", data);
    });
}
```

### 7.2 何时使用 Copy

```rust
// ✅ 小型、固定的值
#[derive(Copy, Clone)]
struct Config {
    max_size: usize,
    timeout: u64,
}

// ❌ 不要为大型结构体实现 Copy
#[derive(Clone)]  // 只实现 Clone，不实现 Copy
struct LargeData {
    buffer: [u8; 1024],
}
```

### 7.3 何时使用 Clone

```rust
// 当确实需要两个独立的副本时
fn duplicate_data() {
    let original = String::from("important");
    let backup = original.clone();

    // 现在可以独立修改两者
    process(&mut original.clone());
    store(&backup);
}
```

---

## ✅ 完成检查

你能回答以下问题吗？

- [ ] 什么是所有权的三大规则？
- [ ] Move 和 Copy 有什么区别？
- [ ] 什么时候会发生所有权转移？
- [ ] 为什么 String 不是 Copy 类型？
- [ ] 如何在函数调用后保留所有权？

如果都能回答，你已经掌握了所有权的基础！下一步学习**借用（Borrowing）**。

---

**文档维护**: Rust 学习项目团队
**最后更新**: 2026-02-28
**版本**: v2.0 (完整版)
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
