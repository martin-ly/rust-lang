# 🚀 C01: Ownership & Borrow - 实战项目集

> **创建日期**: 2025-10-25
> **文档版本**: v1.0
> **适用模块**: C01 所有权、借用和作用域
> **目标**: 通过实战项目深入理解 Rust 的所有权和借用机制

---

## 目录

- [🚀 C01: Ownership \& Borrow - 实战项目集](#-c01-ownership--borrow---实战项目集)
  - [目录](#目录)
  - [📋 项目概览](#-项目概览)
  - [项目1: 简单的智能指针](#项目1-简单的智能指针)
    - [📖 项目说明](#-项目说明)
    - [学习目标](#学习目标)
    - [功能需求](#功能需求)
      - [基础功能](#基础功能)
      - [进阶功能（可选）](#进阶功能可选)
    - [项目结构](#项目结构)
    - [核心代码实现](#核心代码实现)
      - [`simple_box.rs`](#simple_boxrs)
      - [`main.rs`](#mainrs)
    - [测试方式](#测试方式)
    - [预期输出](#预期输出)
    - [关键知识点](#关键知识点)
    - [扩展方向](#扩展方向)
  - [项目2: 字符串处理工具](#项目2-字符串处理工具)
    - [📖 项目说明2](#-项目说明2)
    - [学习目标2](#学习目标2)
    - [功能需求2](#功能需求2)
      - [基础功能2](#基础功能2)
      - [进阶功能2](#进阶功能2)
    - [项目结构2](#项目结构2)
    - [核心代码实现2](#核心代码实现2)
      - [`lib.rs`](#librs)
      - [`main.rs`-](#mainrs-)
    - [测试方式-](#测试方式-)
    - [预期输出-](#预期输出-)
    - [关键知识点-](#关键知识点-)
    - [扩展方向-](#扩展方向-)
  - [项目3: 引用计数容器](#项目3-引用计数容器)
    - [📖 项目说明3](#-项目说明3)
    - [学习目标3](#学习目标3)
    - [功能需求3](#功能需求3)
      - [基础功能3](#基础功能3)
      - [进阶功能3](#进阶功能3)
    - [项目结构3](#项目结构3)
    - [核心代码实现3](#核心代码实现3)
      - [`container.rs`](#containerrs)
      - [`main.rs`--](#mainrs--)
    - [测试方式3](#测试方式3)
    - [预期输出3](#预期输出3)
    - [关键知识点3](#关键知识点3)
    - [扩展方向3](#扩展方向3)
  - [📝 总结](#-总结)
    - [项目难度递进](#项目难度递进)
    - [核心概念对应](#核心概念对应)
    - [学习建议](#学习建议)
    - [相关文档](#相关文档)

## 📋 项目概览

本文档提供了 **3个精心设计的实战项目**，从入门到进阶，帮助你在实践中掌握 Rust 的核心概念。

| #   | 项目名称                                | 难度   | 预计时间 | 核心概念             |
| :--- | :--- | :--- | :--- | :--- |
| 1   | [简单的智能指针](#项目1-简单的智能指针) | ⭐     | 1-2小时  | 所有权转移、Drop     |
| 2   | [字符串处理工具](#项目2-字符串处理工具) | ⭐⭐   | 2-3小时  | 借用、切片、生命周期 |
| 3   | [引用计数容器](#项目3-引用计数容器)     | ⭐⭐⭐ | 3-4小时  | RefCell、内部可变性  |

---

## 项目1: 简单的智能指针

### 📖 项目说明

**难度**: ⭐
**预计时间**: 1-2小时
**目标**: 理解所有权转移和 Drop trait

### 学习目标

1. 理解所有权的移动语义
2. 实现自定义 Drop trait
3. 掌握堆内存分配
4. 理解 RAII 模式

### 功能需求

#### 基础功能

1. 创建一个简单的 `Box` 封装
2. 支持创建、访问数据
3. 自动释放内存
4. 追踪内存分配和释放

#### 进阶功能（可选）

1. 实现 `Deref` trait
2. 实现 `DerefMut` trait
3. 添加统计功能

### 项目结构

```text
simple_box/
├── Cargo.toml
└── src/
    ├── main.rs
    └── simple_box.rs
```

### 核心代码实现

#### `simple_box.rs`

```rust
use std::fmt;

/// 简单的智能指针实现
pub struct SimpleBox<T> {
    data: *mut T,  // 原始指针
}

impl<T> SimpleBox<T> {
    /// 创建新的 SimpleBox
    pub fn new(value: T) -> Self {
        // 分配堆内存
        let ptr = Box::into_raw(Box::new(value));
        println!("📦 SimpleBox 创建: 分配内存 {:p}", ptr);

        SimpleBox { data: ptr }
    }

    /// 获取不可变引用
    pub fn get(&self) -> &T {
        unsafe { &*self.data }
    }

    /// 获取可变引用
    pub fn get_mut(&mut self) -> &mut T {
        unsafe { &mut *self.data }
    }

    /// 解构并返回内部值
    pub fn into_inner(self) -> T {
        let value = unsafe { Box::from_raw(self.data) };
        std::mem::forget(self);  // 防止 Drop
        *value
    }
}

// 实现 Drop trait - RAII 模式
impl<T> Drop for SimpleBox<T> {
    fn drop(&mut self) {
        println!("🗑️  SimpleBox 销毁: 释放内存 {:p}", self.data);
        unsafe {
            // 从原始指针恢复 Box，然后自动 drop
            let _ = Box::from_raw(self.data);
        }
    }
}

// 实现 Debug trait
impl<T: fmt::Debug> fmt::Debug for SimpleBox<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SimpleBox({:?})", self.get())
    }
}

// 实现 Deref trait (进阶)
use std::ops::Deref;

impl<T> Deref for SimpleBox<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.get()
    }
}

// 实现 DerefMut trait (进阶)
use std::ops::DerefMut;

impl<T> DerefMut for SimpleBox<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.get_mut()
    }
}
```

#### `main.rs`

```rust
mod simple_box;
use simple_box::SimpleBox;

fn main() {
    println!("===== SimpleBox 测试 =====\n");

    // 测试1: 基础创建和访问
    {
        println!("测试1: 基础创建和访问");
        let boxed = SimpleBox::new(42);
        println!("值: {}", boxed.get());
        println!("Debug: {:?}\n", boxed);
    } // boxed 在这里被 drop

    // 测试2: 可变访问
    {
        println!("测试2: 可变访问");
        let mut boxed = SimpleBox::new(String::from("Hello"));
        println!("原始值: {}", boxed.get());

        boxed.get_mut().push_str(", World!");
        println!("修改后: {}\n", boxed.get());
    }

    // 测试3: 所有权转移
    {
        println!("测试3: 所有权转移");
        let boxed = SimpleBox::new(vec![1, 2, 3]);

        // 转移所有权
        let moved = take_ownership(boxed);
        println!("返回的值: {:?}\n", moved);
    }

    // 测试4: Deref trait
    {
        println!("测试4: Deref 自动解引用");
        let boxed = SimpleBox::new(String::from("Rust"));

        // 通过 Deref 自动解引用
        println!("长度: {}", boxed.len());  // String::len()
        println!("大写: {}\n", boxed.to_uppercase());
    }

    // 测试5: into_inner
    {
        println!("测试5: 解构");
        let boxed = SimpleBox::new(100);
        let value = boxed.into_inner();
        println!("提取的值: {}\n", value);
        // boxed 不会被 drop，因为使用了 mem::forget
    }

    println!("===== 程序结束 =====");
}

fn take_ownership(boxed: SimpleBox<Vec<i32>>) -> Vec<i32> {
    boxed.into_inner()
}
```

### 测试方式

```bash
cargo new simple_box
cd simple_box
# 复制上述代码
cargo run
```

### 预期输出

```text
===== SimpleBox 测试 =====

测试1: 基础创建和访问
📦 SimpleBox 创建: 分配内存 0x...
值: 42
Debug: SimpleBox(42)
🗑️  SimpleBox 销毁: 释放内存 0x...

测试2: 可变访问
📦 SimpleBox 创建: 分配内存 0x...
原始值: Hello
修改后: Hello, World!
🗑️  SimpleBox 销毁: 释放内存 0x...

测试3: 所有权转移
📦 SimpleBox 创建: 分配内存 0x...
返回的值: [1, 2, 3]

测试4: Deref 自动解引用
📦 SimpleBox 创建: 分配内存 0x...
长度: 4
大写: RUST
🗑️  SimpleBox 销毁: 释放内存 0x...

测试5: 解构
📦 SimpleBox 创建: 分配内存 0x...
提取的值: 100

===== 程序结束 =====
```

### 关键知识点

1. **所有权转移**: `SimpleBox` 拥有堆上数据的所有权
2. **RAII**: 通过 `Drop` trait 自动释放资源
3. **原始指针**: 使用 `*mut T` 存储数据
4. **Deref**: 实现自动解引用，更方便使用
5. **内存安全**: 防止双重释放和内存泄漏

### 扩展方向

1. 添加引用计数（类似 `Rc`）
2. 实现 `Clone` trait
3. 添加内存统计功能
4. 实现弱引用（类似 `Weak`）

---

## 项目2: 字符串处理工具

### 📖 项目说明2

**难度**: ⭐⭐
**预计时间**: 2-3小时
**目标**: 掌握借用、切片和生命周期

### 学习目标2

1. 理解 `&str` 和 `String` 的区别
2. 掌握切片的使用
3. 理解生命周期标注
4. 处理 UTF-8 编码

### 功能需求2

#### 基础功能2

1. 字符串切割（split）
2. 字符串查找（find）
3. 字符串替换（replace）
4. 去除空白字符（trim）

#### 进阶功能2

1. 多种分隔符支持
2. 正则表达式匹配（可选）
3. Unicode 字符处理

### 项目结构2

```text
string_utils/
├── Cargo.toml
└── src/
    ├── main.rs
    └── lib.rs
```

### 核心代码实现2

#### `lib.rs`

```rust
/// 字符串工具模块

/// 按分隔符分割字符串
pub fn split_str<'a>(text: &'a str, delimiter: &str) -> Vec<&'a str> {
    text.split(delimiter).collect()
}

/// 查找子字符串的位置
pub fn find_substring(text: &str, pattern: &str) -> Option<usize> {
    text.find(pattern)
}

/// 查找所有匹配位置
pub fn find_all(text: &str, pattern: &str) -> Vec<usize> {
    let mut positions = Vec::new();
    let mut start = 0;

    while let Some(pos) = text[start..].find(pattern) {
        positions.push(start + pos);
        start += pos + pattern.len();
    }

    positions
}

/// 替换所有匹配的字符串
pub fn replace_all(text: &str, from: &str, to: &str) -> String {
    text.replace(from, to)
}

/// 去除首尾空白字符
pub fn trim_whitespace(text: &str) -> &str {
    text.trim()
}

/// 按字符数量切割字符串
pub fn slice_chars(text: &str, start: usize, len: usize) -> Option<String> {
    let chars: Vec<char> = text.chars().collect();

    if start + len > chars.len() {
        return None;
    }

    Some(chars[start..start + len].iter().collect())
}

/// 字符串反转（支持 Unicode）
pub fn reverse_string(text: &str) -> String {
    text.chars().rev().collect()
}

/// 统计单词数量
pub fn count_words(text: &str) -> usize {
    text.split_whitespace().count()
}

/// 提取最长的单词
pub fn longest_word<'a>(text: &'a str) -> Option<&'a str> {
    text.split_whitespace()
        .max_by_key(|word| word.len())
}

/// 检查是否为回文
pub fn is_palindrome(text: &str) -> bool {
    let cleaned: String = text.chars()
        .filter(|c| c.is_alphanumeric())
        .map(|c| c.to_lowercase().next().unwrap())
        .collect();

    let reversed: String = cleaned.chars().rev().collect();
    cleaned == reversed
}

/// 首字母大写
pub fn capitalize(text: &str) -> String {
    let mut chars = text.chars();
    match chars.next() {
        None => String::new(),
        Some(first) => {
            first.to_uppercase().collect::<String>() + chars.as_str()
        }
    }
}

/// 按行分割并处理
pub struct LineIterator<'a> {
    remaining: &'a str,
}

impl<'a> LineIterator<'a> {
    pub fn new(text: &'a str) -> Self {
        LineIterator { remaining: text }
    }
}

impl<'a> Iterator for LineIterator<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining.is_empty() {
            return None;
        }

        match self.remaining.find('\n') {
            Some(pos) => {
                let line = &self.remaining[..pos];
                self.remaining = &self.remaining[pos + 1..];
                Some(line)
            }
            None => {
                let line = self.remaining;
                self.remaining = "";
                Some(line)
            }
        }
    }
}
```

#### `main.rs`-

```rust
mod lib;
use lib::*;

fn main() {
    println!("===== 字符串处理工具测试 =====\n");

    // 测试1: 字符串分割
    {
        println!("测试1: 字符串分割");
        let text = "apple,banana,cherry";
        let parts = split_str(text, ",");
        println!("原始: {}", text);
        println!("分割: {:?}\n", parts);
    }

    // 测试2: 查找子字符串
    {
        println!("测试2: 查找子字符串");
        let text = "Hello, Rust! Rust is great!";

        if let Some(pos) = find_substring(text, "Rust") {
            println!("找到 'Rust' 在位置: {}", pos);
        }

        let all_positions = find_all(text, "Rust");
        println!("所有 'Rust' 的位置: {:?}\n", all_positions);
    }

    // 测试3: 字符串替换
    {
        println!("测试3: 字符串替换");
        let text = "I like Python. Python is easy.";
        let replaced = replace_all(text, "Python", "Rust");
        println!("原始: {}", text);
        println!("替换: {}\n", replaced);
    }

    // 测试4: Unicode 处理
    {
        println!("测试4: Unicode 处理");
        let text = "Hello 世界 🦀";
        println!("原始: {}", text);
        println!("反转: {}", reverse_string(text));

        if let Some(slice) = slice_chars(text, 6, 2) {
            println!("切片 [6..8]: {}\n", slice);
        }
    }

    // 测试5: 单词统计
    {
        println!("测试5: 单词统计");
        let text = "Rust is a systems programming language";
        println!("文本: {}", text);
        println!("单词数: {}", count_words(text));

        if let Some(longest) = longest_word(text) {
            println!("最长单词: {}\n", longest);
        }
    }

    // 测试6: 回文检查
    {
        println!("测试6: 回文检查");
        let test_cases = vec![
            "A man a plan a canal Panama",
            "race car",
            "Hello",
        ];

        for text in test_cases {
            println!("{:?} 是回文: {}", text, is_palindrome(text));
        }
        println!();
    }

    // 测试7: 首字母大写
    {
        println!("测试7: 首字母大写");
        let words = vec!["hello", "rust", "world"];
        let capitalized: Vec<String> = words.iter()
            .map(|&w| capitalize(w))
            .collect();
        println!("原始: {:?}", words);
        println!("大写: {:?}\n", capitalized);
    }

    // 测试8: 行迭代器
    {
        println!("测试8: 行迭代器");
        let text = "Line 1\nLine 2\nLine 3";
        println!("原始文本:\n{}\n", text);

        println!("逐行处理:");
        for (i, line) in LineIterator::new(text).enumerate() {
            println!("  第{}行: {}", i + 1, line);
        }
    }
}
```

### 测试方式-

```bash
cargo new string_utils
cd string_utils
# 复制上述代码
cargo run
```

### 预期输出-

```text
===== 字符串处理工具测试 =====

测试1: 字符串分割
原始: apple,banana,cherry
分割: ["apple", "banana", "cherry"]

测试2: 查找子字符串
找到 'Rust' 在位置: 7
所有 'Rust' 的位置: [7, 13]

测试3: 字符串替换
原始: I like Python. Python is easy.
替换: I like Rust. Rust is easy.

测试4: Unicode 处理
原始: Hello 世界 🦀
反转: 🦀界世 olleH
切片 [6..8]: 世界

测试5: 单词统计
文本: Rust is a systems programming language
单词数: 6
最长单词: programming

测试6: 回文检查
"A man a plan a canal Panama" 是回文: true
"race car" 是回文: true
"Hello" 是回文: false

测试7: 首字母大写
原始: ["hello", "rust", "world"]
大写: ["Hello", "Rust", "World"]

测试8: 行迭代器
原始文本:
Line 1
Line 2
Line 3

逐行处理:
  第1行: Line 1
  第2行: Line 2
  第3行: Line 3
```

### 关键知识点-

1. **生命周期**: 返回的切片与输入有相同的生命周期
2. **借用**: 多个函数可以同时借用同一个字符串
3. **切片**: `&str` 是字符串切片，不拥有数据
4. **UTF-8**: 正确处理多字节字符
5. **迭代器**: 自定义迭代器处理文本

### 扩展方向-

1. 添加正则表达式支持（使用 `regex` crate）
2. 实现更多的字符串算法（KMP、Boyer-Moore）
3. 添加性能基准测试
4. 支持流式处理大文件

---

## 项目3: 引用计数容器

### 📖 项目说明3

**难度**: ⭐⭐⭐
**预计时间**: 3-4小时
**目标**: 掌握 `RefCell` 和内部可变性

### 学习目标3

1. 理解内部可变性模式
2. 掌握 `RefCell` 和 `Rc` 的使用
3. 实现共享可变状态
4. 理解运行时借用检查

### 功能需求3

#### 基础功能3

1. 创建引用计数容器
2. 支持共享访问
3. 支持内部可变性
4. 追踪引用计数

#### 进阶功能3

1. 实现观察者模式
2. 循环引用检测
3. 弱引用支持

### 项目结构3

```text
shared_container/
├── Cargo.toml
└── src/
    ├── main.rs
    └── container.rs
```

### 核心代码实现3

#### `container.rs`

```rust
use std::cell::RefCell;
use std::rc::Rc;

/// 共享容器，支持内部可变性
#[derive(Debug)]
pub struct SharedContainer<T> {
    data: Rc<RefCell<T>>,
}

impl<T> SharedContainer<T> {
    /// 创建新的共享容器
    pub fn new(value: T) -> Self {
        SharedContainer {
            data: Rc::new(RefCell::new(value)),
        }
    }

    /// 获取引用计数
    pub fn ref_count(&self) -> usize {
        Rc::strong_count(&self.data)
    }

    /// 借用内部数据（不可变）
    pub fn borrow(&self) -> std::cell::Ref<'_, T> {
        self.data.borrow()
    }

    /// 借用内部数据（可变）
    pub fn borrow_mut(&self) -> std::cell::RefMut<'_, T> {
        self.data.borrow_mut()
    }

    /// 尝试借用（可变），如果已被借用则返回 None
    pub fn try_borrow_mut(&self) -> Option<std::cell::RefMut<'_, T>> {
        self.data.try_borrow_mut().ok()
    }
}

impl<T> Clone for SharedContainer<T> {
    fn clone(&self) -> Self {
        SharedContainer {
            data: Rc::clone(&self.data),
        }
    }
}

/// 计数器示例
pub struct Counter {
    count: i32,
    observers: Vec<Rc<RefCell<dyn Observer>>>,
}

impl Counter {
    pub fn new() -> Self {
        Counter {
            count: 0,
            observers: Vec::new(),
        }
    }

    pub fn increment(&mut self) {
        self.count += 1;
        self.notify();
    }

    pub fn decrement(&mut self) {
        self.count -= 1;
        self.notify();
    }

    pub fn get(&self) -> i32 {
        self.count
    }

    pub fn add_observer(&mut self, observer: Rc<RefCell<dyn Observer>>) {
        self.observers.push(observer);
    }

    fn notify(&self) {
        for observer in &self.observers {
            observer.borrow_mut().update(self.count);
        }
    }
}

/// 观察者 trait
pub trait Observer {
    fn update(&mut self, value: i32);
}

/// 日志观察者
pub struct LogObserver {
    name: String,
}

impl LogObserver {
    pub fn new(name: &str) -> Self {
        LogObserver {
            name: name.to_string(),
        }
    }
}

impl Observer for LogObserver {
    fn update(&mut self, value: i32) {
        println!("📢 [{}] 收到更新: {}", self.name, value);
    }
}

/// 统计观察者
pub struct StatsObserver {
    min: i32,
    max: i32,
    updates: usize,
}

impl StatsObserver {
    pub fn new() -> Self {
        StatsObserver {
            min: i32::MAX,
            max: i32::MIN,
            updates: 0,
        }
    }

    pub fn report(&self) {
        println!("📊 统计: min={}, max={}, updates={}",
                 self.min, self.max, self.updates);
    }
}

impl Observer for StatsObserver {
    fn update(&mut self, value: i32) {
        self.min = self.min.min(value);
        self.max = self.max.max(value);
        self.updates += 1;
    }
}
```

#### `main.rs`--

```rust
mod container;
use container::*;
use std::rc::Rc;
use std::cell::RefCell;

fn main() {
    println!("===== 引用计数容器测试 =====\n");

    // 测试1: 基础共享容器
    {
        println!("测试1: 基础共享容器");
        let container = SharedContainer::new(vec![1, 2, 3]);
        println!("引用计数: {}", container.ref_count());

        // 克隆容器（增加引用计数）
        let container2 = container.clone();
        println!("克隆后引用计数: {}", container.ref_count());

        // 不可变借用
        {
            let data = container.borrow();
            println!("数据: {:?}", *data);
        }

        // 可变借用
        {
            let mut data = container.borrow_mut();
            data.push(4);
            println!("修改后: {:?}", *data);
        }

        // 通过第二个引用访问
        {
            let data = container2.borrow();
            println!("通过 container2 访问: {:?}\n", *data);
        }
    }

    // 测试2: 多个可变引用（运行时检查）
    {
        println!("测试2: 借用检查");
        let container = SharedContainer::new(100);

        // 第一个可变借用
        let mut ref1 = container.borrow_mut();
        *ref1 += 10;
        println!("第一次修改: {}", *ref1);

        // 尝试第二个可变借用（会失败）
        match container.try_borrow_mut() {
            Some(_) => println!("获取第二个可变引用成功"),
            None => println!("❌ 无法获取第二个可变引用（已被借用）"),
        }

        drop(ref1);  // 释放第一个借用

        // 现在可以借用了
        match container.try_borrow_mut() {
            Some(mut ref2) => {
                *ref2 += 20;
                println!("✅ 释放后获取可变引用成功: {}\n", *ref2);
            }
            None => println!("失败"),
        }
    }

    // 测试3: 观察者模式
    {
        println!("测试3: 观察者模式");

        let counter = SharedContainer::new(Counter::new());

        // 创建观察者
        let log_observer = Rc::new(RefCell::new(
            LogObserver::new("Logger")
        ));
        let stats_observer = Rc::new(RefCell::new(
            StatsObserver::new()
        ));

        // 注册观察者
        counter.borrow_mut().add_observer(Rc::clone(&log_observer));
        counter.borrow_mut().add_observer(Rc::clone(&stats_observer));

        // 执行操作
        println!("开始计数:");
        counter.borrow_mut().increment();
        counter.borrow_mut().increment();
        counter.borrow_mut().increment();
        counter.borrow_mut().decrement();

        println!("\n当前计数: {}", counter.borrow().get());

        // 显示统计
        stats_observer.borrow().report();
        println!();
    }

    // 测试4: 共享可变状态
    {
        println!("测试4: 共享可变状态");

        struct Node {
            value: i32,
            next: Option<Rc<RefCell<Node>>>,
        }

        let node1 = Rc::new(RefCell::new(Node {
            value: 1,
            next: None,
        }));

        let node2 = Rc::new(RefCell::new(Node {
            value: 2,
            next: Some(Rc::clone(&node1)),
        }));

        let node3 = Rc::new(RefCell::new(Node {
            value: 3,
            next: Some(Rc::clone(&node2)),
        }));

        // 遍历链表
        let mut current = Some(Rc::clone(&node3));
        print!("链表: ");
        while let Some(node) = current {
            let node_ref = node.borrow();
            print!("{} ", node_ref.value);
            current = node_ref.next.as_ref().map(Rc::clone);
        }
        println!();

        // 修改节点
        node2.borrow_mut().value = 20;

        // 再次遍历
        let mut current = Some(Rc::clone(&node3));
        print!("修改后: ");
        while let Some(node) = current {
            let node_ref = node.borrow();
            print!("{} ", node_ref.value);
            current = node_ref.next.as_ref().map(Rc::clone);
        }
        println!();
    }
}
```

### 测试方式3

```bash
cargo new shared_container
cd shared_container
# 复制上述代码
cargo run
```

### 预期输出3

```text
===== 引用计数容器测试 =====

测试1: 基础共享容器
引用计数: 1
克隆后引用计数: 2
数据: [1, 2, 3]
修改后: [1, 2, 3, 4]
通过 container2 访问: [1, 2, 3, 4]

测试2: 借用检查
第一次修改: 110
❌ 无法获取第二个可变引用（已被借用）
✅ 释放后获取可变引用成功: 130

测试3: 观察者模式
开始计数:
📢 [Logger] 收到更新: 1
📢 [Logger] 收到更新: 2
📢 [Logger] 收到更新: 3
📢 [Logger] 收到更新: 2

当前计数: 2
📊 统计: min=1, max=3, updates=4

测试4: 共享可变状态
链表: 3 2 1
修改后: 3 20 1
```

### 关键知识点3

1. **内部可变性**: `RefCell` 允许在不可变引用下修改数据
2. **引用计数**: `Rc` 实现共享所有权
3. **运行时检查**: `RefCell` 在运行时检查借用规则
4. **观察者模式**: 使用 `Rc<RefCell<T>>` 实现共享可变状态
5. **借用规则**: 同时只能有一个可变借用或多个不可变借用

### 扩展方向3

1. 实现 `Weak` 弱引用，防止循环引用
2. 添加线程安全版本（使用 `Arc` 和 `Mutex`）
3. 实现图数据结构
4. 添加循环引用检测

---

## 📝 总结

### 项目难度递进

1. **项目1**: 理解所有权的基础 - 单一所有者
2. **项目2**: 理解借用的实践 - 多个借用者
3. **项目3**: 理解共享的高级 - 共享所有权

### 核心概念对应

| 项目  | 所有权 | 借用   | 生命周期 | 内部可变性 |
| :--- | :--- | :--- | :--- | :--- |
| 项目1 | ✅✅✅ | ✅     | ✅       | ❌         |
| 项目2 | ✅     | ✅✅✅ | ✅✅✅   | ❌         |
| 项目3 | ✅✅   | ✅✅   | ✅       | ✅✅✅     |

### 学习建议

1. **循序渐进**: 按项目1 → 2 → 3 的顺序学习
2. **动手实践**: 自己实现并运行代码
3. **理解原理**: 思考为什么需要这些规则
4. **尝试扩展**: 实现建议的扩展功能

### 相关文档

- 📖 [代码示例集合](06_code_examples.md)
- 📖 [所有权基础](../tier_01_foundations/01_所有权基础.md)
- 📖 [借用与引用](../tier_01_foundations/02_借用与引用.md)
- 📖 [生命周期](../tier_01_foundations/03_生命周期基础.md)

---

**文档版本**: v1.0
**创建日期**: 2025-10-25
**维护状态**: 活跃维护

**🎯 通过实战项目，真正掌握 Rust 的所有权系统！🦀**-

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
