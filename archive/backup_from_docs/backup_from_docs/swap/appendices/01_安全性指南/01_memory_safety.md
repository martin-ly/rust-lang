# Rust 内存安全系统完整指南

**文档版本**: 2.0  
**创建日期**: 2025-01-27  
**Rust版本**: 1.90+  
**难度等级**: 中级到高级  

## 📋 目录

- [Rust 内存安全系统完整指南](#rust-内存安全系统完整指南)
  - [� 目录](#-目录)
  - [1. 内存安全基础](#1-内存安全基础)
    - [1.1 什么是内存安全](#11-什么是内存安全)
    - [1.2 内存安全问题](#12-内存安全问题)
    - [1.3 Rust 的内存安全保证](#13-rust-的内存安全保证)
  - [2. 所有权系统](#2-所有权系统)
    - [2.1 所有权规则](#21-所有权规则)
    - [2.2 移动语义](#22-移动语义)
    - [2.3 复制语义](#23-复制语义)
    - [2.4 所有权转移](#24-所有权转移)
  - [3. 借用系统](#3-借用系统)
    - [3.1 不可变借用](#31-不可变借用)
    - [3.2 可变借用](#32-可变借用)
    - [3.3 借用规则](#33-借用规则)
    - [3.4 借用检查器](#34-借用检查器)
  - [4. 生命周期系统](#4-生命周期系统)
    - [4.1 生命周期基础](#41-生命周期基础)
    - [4.2 生命周期注解](#42-生命周期注解)
    - [4.3 生命周期推断](#43-生命周期推断)
    - [4.4 生命周期约束](#44-生命周期约束)
  - [5. 内部可变性](#5-内部可变性)
    - [5.1 UnsafeCell 基础](#51-unsafecell-基础)
    - [5.2 Cell 类型](#52-cell-类型)
    - [5.3 RefCell 类型](#53-refcell-类型)
    - [5.4 原子类型](#54-原子类型)
  - [6. 内存布局](#6-内存布局)
    - [6.1 结构体内存布局](#61-结构体内存布局)
    - [6.2 枚举内存布局](#62-枚举内存布局)
    - [6.3 对齐和填充](#63-对齐和填充)
    - [6.4 零大小类型](#64-零大小类型)
  - [7. 不安全代码](#7-不安全代码)
    - [7.1 unsafe 关键字](#71-unsafe-关键字)
    - [7.2 原始指针](#72-原始指针)
    - [7.3 内存操作](#73-内存操作)
    - [7.4 FFI 安全](#74-ffi-安全)
  - [8. 内存管理](#8-内存管理)
    - [8.1 栈内存管理](#81-栈内存管理)
    - [8.2 堆内存管理](#82-堆内存管理)
    - [8.3 内存分配器](#83-内存分配器)
    - [8.4 内存泄漏](#84-内存泄漏)
  - [9. 性能优化](#9-性能优化)
    - [9.1 内存布局优化](#91-内存布局优化)
    - [9.2 零拷贝技术](#92-零拷贝技术)
    - [9.3 内存池](#93-内存池)
    - [9.4 缓存友好性](#94-缓存友好性)
  - [10. 调试和诊断](#10-调试和诊断)
    - [10.1 内存错误诊断](#101-内存错误诊断)
    - [10.2 工具支持](#102-工具支持)
    - [10.3 最佳实践](#103-最佳实践)
  - [11. 总结](#11-总结)
    - [关键要点](#关键要点)
    - [进一步学习](#进一步学习)

## 1. 内存安全基础

### 1.1 什么是内存安全

内存安全是指程序在运行时不会出现以下内存相关错误：

1. **缓冲区溢出**: 访问数组或缓冲区边界外的内存
2. **悬垂指针**: 访问已被释放的内存
3. **双重释放**: 多次释放同一块内存
4. **内存泄漏**: 分配的内存无法被释放
5. **数据竞争**: 多个线程同时访问同一内存位置

```rust
// Rust 内存安全示例
fn memory_safe_example() {
    let vec = vec![1, 2, 3, 4, 5];
    
    // 安全的数组访问
    if let Some(value) = vec.get(2) {
        println!("Value: {}", value);
    }
    
    // 安全的迭代
    for item in &vec {
        println!("Item: {}", item);
    }
    
    // 自动内存管理
    // vec 在这里自动被释放
}
```

### 1.2 内存安全问题

传统系统编程语言（如 C/C++）中的常见内存安全问题：

```c
// C 语言中的内存安全问题示例
void unsafe_example() {
    int* ptr = malloc(sizeof(int));
    *ptr = 42;
    
    // 问题1：可能忘记释放内存
    // free(ptr);
    
    // 问题2：悬垂指针
    free(ptr);
    *ptr = 100;  // 未定义行为
    
    // 问题3：缓冲区溢出
    char buffer[10];
    strcpy(buffer, "This is a very long string");  // 缓冲区溢出
}
```

### 1.3 Rust 的内存安全保证

Rust 通过以下机制保证内存安全：

1. **所有权系统**: 确保每个值有唯一的所有者
2. **借用检查器**: 编译时检查引用的有效性
3. **生命周期系统**: 确保引用不会悬垂
4. **类型系统**: 防止类型相关的内存错误

```rust
// Rust 的内存安全保证
fn rust_memory_safety() {
    let s = String::from("hello");
    
    // 所有权转移
    let s2 = s;  // s 的所有权转移给 s2
    // println!("{}", s);  // 编译错误：s 不再有效
    
    // 借用检查
    let s3 = &s2;
    let s4 = &s2;  // 多个不可变借用是安全的
    // let s5 = &mut s2;  // 编译错误：不能同时有可变和不可变借用
    
    println!("{}", s3);
    println!("{}", s4);
}
```

## 2. 所有权系统

### 2.1 所有权规则

Rust 的所有权系统遵循三条基本规则：

1. **每个值都有一个所有者**
2. **同时只能有一个所有者**
3. **当所有者离开作用域时，值被丢弃**

```rust
// 所有权规则示例
fn ownership_rules() {
    // 规则1：每个值都有一个所有者
    let s = String::from("hello");  // s 是 "hello" 的所有者
    
    // 规则2：同时只能有一个所有者
    let s2 = s;  // 所有权转移给 s2
    // println!("{}", s);  // 错误：s 不再是所有者
    
    // 规则3：当所有者离开作用域时，值被丢弃
    {
        let s3 = String::from("world");
        // s3 在这里被丢弃
    }
    // println!("{}", s3);  // 错误：s3 已经不存在
}
```

### 2.2 移动语义

移动语义是 Rust 所有权系统的核心，确保值的唯一所有权：

```rust
// 移动语义示例
fn move_semantics() {
    let s1 = String::from("hello");
    let s2 = s1;  // s1 的值被移动到 s2
    
    // s1 不再有效
    // println!("{}", s1);  // 编译错误
    
    println!("{}", s2);  // 正确：s2 拥有值
}

// 函数参数中的移动
fn take_ownership(s: String) {
    println!("{}", s);
    // s 在这里被丢弃
}

fn move_to_function() {
    let s = String::from("hello");
    take_ownership(s);  // s 的所有权转移给函数
    // println!("{}", s);  // 错误：s 不再有效
}
```

### 2.3 复制语义

实现了 `Copy` 特征的类型具有复制语义，不会发生所有权转移：

```rust
// 复制语义示例
fn copy_semantics() {
    let x = 5;
    let y = x;  // x 的值被复制给 y
    
    println!("{}", x);  // 正确：x 仍然有效
    println!("{}", y);  // 正确：y 有自己的副本
}

// Copy 类型示例
#[derive(Copy, Clone, Debug)]
struct Point {
    x: i32,
    y: i32,
}

fn copy_struct() {
    let p1 = Point { x: 1, y: 2 };
    let p2 = p1;  // 复制，不是移动
    
    println!("{:?}", p1);  // 正确：p1 仍然有效
    println!("{:?}", p2);  // 正确：p2 有自己的副本
}
```

### 2.4 所有权转移

所有权可以在函数调用、赋值等操作中转移：

```rust
// 所有权转移示例
fn ownership_transfer() {
    let s1 = String::from("hello");
    
    // 转移给函数
    let s2 = return_ownership(s1);
    
    // 转移给变量
    let s3 = s2;
    
    println!("{}", s3);
}

fn return_ownership(s: String) -> String {
    println!("Received: {}", s);
    s  // 所有权转移回调用者
}

// 避免所有权转移的方法
fn avoid_transfer() {
    let s = String::from("hello");
    
    // 方法1：借用
    print_string(&s);
    println!("{}", s);  // 正确：s 仍然有效
    
    // 方法2：克隆
    let s2 = s.clone();
    take_ownership(s2);
    println!("{}", s);  // 正确：s 仍然有效
}

fn print_string(s: &String) {
    println!("{}", s);
}
```

## 3. 借用系统

### 3.1 不可变借用

不可变借用允许在不获取所有权的情况下访问数据：

```rust
// 不可变借用示例
fn immutable_borrowing() {
    let s = String::from("hello");
    
    // 创建不可变借用
    let s1 = &s;
    let s2 = &s;
    let s3 = &s;
    
    // 多个不可变借用是安全的
    println!("{}", s1);
    println!("{}", s2);
    println!("{}", s3);
    
    // 原始值仍然有效
    println!("{}", s);
}

// 函数中的不可变借用
fn calculate_length(s: &String) -> usize {
    s.len()
}

fn use_immutable_borrow() {
    let s = String::from("hello");
    let len = calculate_length(&s);
    
    println!("The length of '{}' is {}.", s, len);
    // s 仍然有效，因为只是借用了它
}
```

### 3.2 可变借用

可变借用允许修改数据，但有严格的限制：

```rust
// 可变借用示例
fn mutable_borrowing() {
    let mut s = String::from("hello");
    
    // 创建可变借用
    let s1 = &mut s;
    s1.push_str(", world");
    
    println!("{}", s1);
    
    // 可变借用结束后，可以再次借用
    let s2 = &mut s;
    s2.push_str("!");
    
    println!("{}", s2);
}

// 可变借用的限制
fn mutable_borrow_restrictions() {
    let mut s = String::from("hello");
    
    let r1 = &mut s;
    // let r2 = &mut s;  // 错误：不能同时有多个可变借用
    // let r3 = &s;      // 错误：不能同时有可变和不可变借用
    
    println!("{}", r1);
    
    // 借用结束后，可以创建新的借用
    let r2 = &s;  // 正确：r1 已经不再使用
    println!("{}", r2);
}
```

### 3.3 借用规则

Rust 的借用规则确保内存安全：

1. **任意时刻，只能有一个可变引用或多个不可变引用**
2. **引用必须始终有效**

```rust
// 借用规则示例
fn borrowing_rules() {
    let mut s = String::from("hello");
    
    // 规则1：多个不可变引用
    let r1 = &s;
    let r2 = &s;
    println!("{} and {}", r1, r2);
    
    // 规则1：可变引用
    let r3 = &mut s;
    r3.push_str(", world");
    println!("{}", r3);
    
    // 规则2：引用必须有效
    let reference = {
        let s = String::from("hello");
        &s  // 错误：s 在作用域结束时被丢弃
    };
    // println!("{}", reference);  // 错误：悬垂引用
}
```

### 3.4 借用检查器

借用检查器在编译时验证借用的安全性：

```rust
// 借用检查器示例
fn borrow_checker_example() {
    let mut vec = vec![1, 2, 3, 4, 5];
    
    // 不可变借用
    let first = &vec[0];
    
    // 尝试可变借用
    // vec.push(6);  // 错误：不能在有不可变借用时进行可变借用
    
    println!("First element: {}", first);
    
    // 不可变借用结束后，可以进行可变借用
    vec.push(6);
    println!("Vector: {:?}", vec);
}

// 借用检查器的智能分析
fn smart_borrow_checker() {
    let mut s = String::from("hello");
    
    let r1 = &s;
    let r2 = &s;
    println!("{} and {}", r1, r2);
    // r1 和 r2 在这里不再使用
    
    let r3 = &mut s;  // 正确：r1 和 r2 已经不再使用
    r3.push_str(", world");
    println!("{}", r3);
}
```

## 4. 生命周期系统

### 4.1 生命周期基础

生命周期确保引用在有效期间内保持有效：

```rust
// 生命周期基础示例
fn lifetime_basics() {
    let x = 5;
    let r = &x;  // r 的生命周期不能超过 x
    
    println!("r: {}", r);
}

// 生命周期注解
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}

fn use_longest() {
    let string1 = String::from("long string is long");
    
    {
        let string2 = String::from("xyz");
        let result = longest(string1.as_str(), string2.as_str());
        println!("The longest string is {}", result);
    }
}
```

### 4.2 生命周期注解

生命周期注解用于明确引用的生命周期关系：

```rust
// 结构体中的生命周期
struct ImportantExcerpt<'a> {
    part: &'a str,
}

fn use_excerpt() {
    let novel = String::from("Call me Ishmael. Some years ago...");
    let first_sentence = novel.split('.').next().expect("Could not find a '.'");
    let i = ImportantExcerpt {
        part: first_sentence,
    };
    
    println!("{}", i.part);
}

// 方法中的生命周期
impl<'a> ImportantExcerpt<'a> {
    fn level(&self) -> i32 {
        3
    }
    
    fn announce_and_return_part(&self, announcement: &str) -> &str {
        println!("Attention please: {}", announcement);
        self.part
    }
}
```

### 4.3 生命周期推断

编译器可以自动推断大部分生命周期：

```rust
// 生命周期推断示例
fn lifetime_elision() {
    // 编译器自动推断生命周期
    let s = String::from("hello");
    let first_word = get_first_word(&s);
    println!("First word: {}", first_word);
}

// 生命周期省略规则
fn get_first_word(s: &str) -> &str {
    let bytes = s.as_bytes();
    
    for (i, &item) in bytes.iter().enumerate() {
        if item == b' ' {
            return &s[0..i];
        }
    }
    
    &s[..]
}
```

### 4.4 生命周期约束

生命周期约束确保引用的有效性：

```rust
// 生命周期约束示例
fn lifetime_constraints<'a, 'b>(x: &'a str, y: &'b str) -> &'a str
where
    'b: 'a,  // 'b 必须至少和 'a 一样长
{
    if x.len() > y.len() {
        x
    } else {
        y
    }
}

// 复杂生命周期约束
struct ComplexLifetime<'a, 'b> {
    short: &'a str,
    long: &'b str,
}

impl<'a, 'b> ComplexLifetime<'a, 'b>
where
    'b: 'a,
{
    fn new(short: &'a str, long: &'b str) -> Self {
        ComplexLifetime { short, long }
    }
    
    fn get_short(&self) -> &'a str {
        self.short
    }
    
    fn get_long(&self) -> &'b str {
        self.long
    }
}
```

## 5. 内部可变性

### 5.1 UnsafeCell 基础

`UnsafeCell` 是内部可变性的底层原语：

```rust
use std::cell::UnsafeCell;

// UnsafeCell 基础
fn unsafecell_basics() {
    let cell = UnsafeCell::new(42);
    
    // 获取可变引用
    let value = unsafe { &mut *cell.get() };
    *value = 100;
    
    // 获取不可变引用
    let value = unsafe { &*cell.get() };
    println!("Value: {}", value);
}

// 自定义内部可变类型
struct MyCell<T> {
    value: UnsafeCell<T>,
}

impl<T> MyCell<T> {
    fn new(value: T) -> Self {
        MyCell {
            value: UnsafeCell::new(value),
        }
    }
    
    fn get(&self) -> T
    where
        T: Copy,
    {
        unsafe { *self.value.get() }
    }
    
    fn set(&self, value: T) {
        unsafe {
            *self.value.get() = value;
        }
    }
}
```

### 5.2 Cell 类型

`Cell` 提供内部可变性，适用于 `Copy` 类型：

```rust
use std::cell::Cell;

// Cell 类型示例
fn cell_example() {
    let cell = Cell::new(42);
    
    // 获取值
    let value = cell.get();
    println!("Value: {}", value);
    
    // 设置值
    cell.set(100);
    let new_value = cell.get();
    println!("New value: {}", new_value);
    
    // 交换值
    let old_value = cell.replace(200);
    println!("Old value: {}, New value: {}", old_value, cell.get());
}

// Cell 的限制
fn cell_limitations() {
    let cell = Cell::new(String::from("hello"));
    
    // Cell 不适用于非 Copy 类型
    // let value = cell.get();  // 错误：String 不是 Copy 类型
    
    // 只能整体替换
    let old_string = cell.replace(String::from("world"));
    println!("Old: {}, New: {}", old_string, cell.into_inner());
}
```

### 5.3 RefCell 类型

`RefCell` 提供运行时借用检查的内部可变性：

```rust
use std::cell::RefCell;

// RefCell 类型示例
fn refcell_example() {
    let cell = RefCell::new(42);
    
    // 不可变借用
    let value = cell.borrow();
    println!("Value: {}", *value);
    
    // 可变借用
    let mut value = cell.borrow_mut();
    *value = 100;
    println!("New value: {}", *value);
}

// RefCell 的运行时检查
fn refcell_runtime_check() {
    let cell = RefCell::new(42);
    
    let _borrow1 = cell.borrow();
    let _borrow2 = cell.borrow();
    
    // 尝试可变借用会导致 panic
    // let _mut_borrow = cell.borrow_mut();  // panic!
    
    // 借用结束后可以可变借用
    drop(_borrow1);
    drop(_borrow2);
    
    let _mut_borrow = cell.borrow_mut();  // 正确
}

// RefCell 的实际应用
struct Counter {
    value: RefCell<i32>,
}

impl Counter {
    fn new() -> Self {
        Counter {
            value: RefCell::new(0),
        }
    }
    
    fn increment(&self) {
        let mut value = self.value.borrow_mut();
        *value += 1;
    }
    
    fn get(&self) -> i32 {
        *self.value.borrow()
    }
}

fn use_counter() {
    let counter = Counter::new();
    
    counter.increment();
    counter.increment();
    
    println!("Counter value: {}", counter.get());
}
```

### 5.4 原子类型

原子类型提供线程安全的内部可变性：

```rust
use std::sync::atomic::{AtomicI32, Ordering};

// 原子类型示例
fn atomic_example() {
    let atomic = AtomicI32::new(42);
    
    // 加载值
    let value = atomic.load(Ordering::SeqCst);
    println!("Value: {}", value);
    
    // 存储值
    atomic.store(100, Ordering::SeqCst);
    
    // 交换值
    let old_value = atomic.swap(200, Ordering::SeqCst);
    println!("Old: {}, New: {}", old_value, atomic.load(Ordering::SeqCst));
    
    // 比较并交换
    let result = atomic.compare_exchange(200, 300, Ordering::SeqCst, Ordering::SeqCst);
    match result {
        Ok(old) => println!("CAS successful, old value: {}", old),
        Err(current) => println!("CAS failed, current value: {}", current),
    }
}

// 原子操作的内存序
fn memory_ordering_example() {
    let atomic = AtomicI32::new(0);
    
    // 不同的内存序
    atomic.store(1, Ordering::Relaxed);    // 最弱的内存序
    atomic.store(2, Ordering::Release);    // 释放语义
    let value = atomic.load(Ordering::Acquire);  // 获取语义
    let value = atomic.load(Ordering::SeqCst);   // 顺序一致性
    
    println!("Value: {}", value);
}
```

## 6. 内存布局

### 6.1 结构体内存布局

```rust
// 结构体内存布局示例
#[repr(C)]
struct CStruct {
    a: u8,
    b: u32,
    c: u16,
}

#[repr(Rust)]
struct RustStruct {
    a: u8,
    b: u32,
    c: u16,
}

fn struct_layout() {
    println!("C struct size: {}", std::mem::size_of::<CStruct>());
    println!("Rust struct size: {}", std::mem::size_of::<RustStruct>());
    
    // 字段偏移
    println!("C struct field offsets:");
    println!("  a: {}", 0);
    println!("  b: {}", 4);  // 对齐到 4 字节边界
    println!("  c: {}", 8);
    
    println!("Rust struct field offsets:");
    println!("  a: {}", 0);
    println!("  b: {}", 4);
    println!("  c: {}", 8);
}

// 内存对齐
#[repr(align(8))]
struct AlignedStruct {
    value: u32,
}

fn alignment_example() {
    println!("Aligned struct size: {}", std::mem::size_of::<AlignedStruct>());
    println!("Aligned struct alignment: {}", std::mem::align_of::<AlignedStruct>());
}
```

### 6.2 枚举内存布局

```rust
// 枚举内存布局示例
enum SimpleEnum {
    A,
    B,
    C,
}

enum DataEnum {
    A,
    B(i32),
    C { x: i32, y: i32 },
}

fn enum_layout() {
    println!("Simple enum size: {}", std::mem::size_of::<SimpleEnum>());
    println!("Data enum size: {}", std::mem::size_of::<DataEnum>());
    
    // 判别值
    println!("Simple enum A discriminant: {:?}", std::mem::discriminant(&SimpleEnum::A));
    println!("Simple enum B discriminant: {:?}", std::mem::discriminant(&SimpleEnum::B));
}

// 零大小枚举
enum ZeroSizeEnum {
    A,
    B,
}

fn zero_size_enum() {
    println!("Zero size enum size: {}", std::mem::size_of::<ZeroSizeEnum>());
}
```

### 6.3 对齐和填充

```rust
// 对齐和填充示例
struct PaddingExample {
    a: u8,   // 1 字节
    b: u32,  // 4 字节，需要对齐到 4 字节边界
    c: u16,  // 2 字节
}

fn padding_example() {
    println!("Struct size: {}", std::mem::size_of::<PaddingExample>());
    println!("Struct alignment: {}", std::mem::align_of::<PaddingExample>());
    
    // 字段大小和对齐
    println!("Field sizes:");
    println!("  a: {} bytes", std::mem::size_of_val(&PaddingExample { a: 0, b: 0, c: 0 }.a));
    println!("  b: {} bytes", std::mem::size_of_val(&PaddingExample { a: 0, b: 0, c: 0 }.b));
    println!("  c: {} bytes", std::mem::size_of_val(&PaddingExample { a: 0, b: 0, c: 0 }.c));
}

// 紧凑布局
#[repr(packed)]
struct PackedStruct {
    a: u8,
    b: u32,
    c: u16,
}

fn packed_example() {
    println!("Packed struct size: {}", std::mem::size_of::<PackedStruct>());
    println!("Packed struct alignment: {}", std::mem::align_of::<PackedStruct>());
}
```

### 6.4 零大小类型

```rust
// 零大小类型示例
struct ZeroSizedType;

fn zero_sized_types() {
    println!("ZeroSizedType size: {}", std::mem::size_of::<ZeroSizedType>());
    println!("ZeroSizedType alignment: {}", std::mem::align_of::<ZeroSizedType>());
    
    // 零大小类型的数组
    let array: [ZeroSizedType; 1000] = [ZeroSizedType; 1000];
    println!("Array of 1000 zero-sized types: {} bytes", std::mem::size_of_val(&array));
}

// 单元类型
fn unit_type() {
    let unit = ();
    println!("Unit type size: {}", std::mem::size_of_val(&unit));
    
    // 单元类型的函数
    fn unit_function() -> () {
        println!("This function returns unit");
    }
    
    let result = unit_function();
    println!("Unit function result size: {}", std::mem::size_of_val(&result));
}
```

## 7. 不安全代码

### 7.1 unsafe 关键字

```rust
// unsafe 关键字的使用
unsafe fn unsafe_function() {
    // 不安全操作
    let raw_ptr = 0x1000 as *const i32;
    // let value = *raw_ptr;  // 不安全：可能访问无效内存
}

// unsafe 块
fn safe_function() {
    unsafe {
        // 在 unsafe 块中进行不安全操作
        let raw_ptr = std::ptr::null();
        // 使用原始指针
    }
}

// unsafe 特征
unsafe trait UnsafeTrait {
    unsafe fn unsafe_method(&self);
}

unsafe impl UnsafeTrait for i32 {
    unsafe fn unsafe_method(&self) {
        // 不安全实现
    }
}
```

### 7.2 原始指针

```rust
// 原始指针示例
fn raw_pointers() {
    let x = 42;
    let raw_ptr = &x as *const i32;
    
    unsafe {
        let value = *raw_ptr;
        println!("Value through raw pointer: {}", value);
    }
    
    // 可变原始指针
    let mut y = 100;
    let mut_raw_ptr = &mut y as *mut i32;
    
    unsafe {
        *mut_raw_ptr = 200;
        println!("Modified value: {}", y);
    }
}

// 原始指针的算术运算
fn pointer_arithmetic() {
    let array = [1, 2, 3, 4, 5];
    let ptr = array.as_ptr();
    
    unsafe {
        for i in 0..array.len() {
            let value = *ptr.add(i);
            println!("Array[{}] = {}", i, value);
        }
    }
}
```

### 7.3 内存操作

```rust
// 内存操作示例
use std::ptr;

fn memory_operations() {
    // 分配内存
    let layout = std::alloc::Layout::new::<i32>();
    let ptr = unsafe {
        std::alloc::alloc(layout) as *mut i32
    };
    
    if !ptr.is_null() {
        // 写入值
        unsafe {
            ptr::write(ptr, 42);
        }
        
        // 读取值
        let value = unsafe {
            ptr::read(ptr)
        };
        
        println!("Allocated value: {}", value);
        
        // 释放内存
        unsafe {
            std::alloc::dealloc(ptr as *mut u8, layout);
        }
    }
}

// 内存复制
fn memory_copy() {
    let src = [1, 2, 3, 4, 5];
    let mut dst = [0; 5];
    
    unsafe {
        ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), src.len());
    }
    
    println!("Copied array: {:?}", dst);
}
```

### 7.4 FFI 安全

```rust
// FFI 安全示例
extern "C" {
    fn strlen(s: *const i8) -> usize;
}

fn ffi_safety() {
    let c_string = b"hello\0";
    let len = unsafe {
        strlen(c_string.as_ptr() as *const i8)
    };
    
    println!("C string length: {}", len);
}

// 安全的 FFI 包装
fn safe_strlen(s: &str) -> Option<usize> {
    let c_string = std::ffi::CString::new(s).ok()?;
    let len = unsafe {
        strlen(c_string.as_ptr())
    };
    Some(len)
}

fn use_safe_ffi() {
    if let Some(len) = safe_strlen("hello") {
        println!("Safe string length: {}", len);
    }
}
```

## 8. 内存管理

### 8.1 栈内存管理

```rust
// 栈内存管理示例
fn stack_memory() {
    let x = 42;  // 在栈上分配
    let y = x;   // 复制到栈上的新位置
    
    println!("x: {}, y: {}", x, y);
    
    // 当函数结束时，栈上的变量自动被释放
}

// 栈上的结构体
#[derive(Debug)]
struct StackStruct {
    value: i32,
}

fn stack_struct() {
    let s = StackStruct { value: 42 };
    println!("Stack struct: {:?}", s);
    
    // s 在函数结束时自动被释放
}
```

### 8.2 堆内存管理

```rust
// 堆内存管理示例
fn heap_memory() {
    let boxed = Box::new(42);  // 在堆上分配
    println!("Boxed value: {}", *boxed);
    
    // Box 在离开作用域时自动释放堆内存
}

// 堆上的结构体
fn heap_struct() {
    let boxed_struct = Box::new(StackStruct { value: 100 });
    println!("Boxed struct: {:?}", boxed_struct);
    
    // 堆内存自动释放
}

// 自定义堆分配
use std::alloc::{alloc, dealloc, Layout};

fn custom_heap_allocation() {
    let layout = Layout::new::<i32>();
    let ptr = unsafe {
        alloc(layout) as *mut i32
    };
    
    if !ptr.is_null() {
        unsafe {
            *ptr = 42;
            println!("Custom allocated value: {}", *ptr);
            dealloc(ptr as *mut u8, layout);
        }
    }
}
```

### 8.3 内存分配器

```rust
// 内存分配器示例
use std::alloc::GlobalAlloc;
use std::alloc::Layout;

struct MyAllocator;

unsafe impl GlobalAlloc for MyAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // 自定义分配逻辑
        std::alloc::System.alloc(layout)
    }
    
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // 自定义释放逻辑
        std::alloc::System.dealloc(ptr, layout);
    }
}

// 使用自定义分配器
#[global_allocator]
static GLOBAL: MyAllocator = MyAllocator;

fn use_custom_allocator() {
    let vec = vec![1, 2, 3, 4, 5];
    println!("Vector with custom allocator: {:?}", vec);
}
```

### 8.4 内存泄漏

```rust
// 内存泄漏示例
use std::rc::Rc;
use std::cell::RefCell;

// 循环引用导致的内存泄漏
struct Node {
    value: i32,
    children: RefCell<Vec<Rc<Node>>>,
    parent: RefCell<Option<Rc<Node>>>,
}

fn memory_leak_example() {
    let node1 = Rc::new(Node {
        value: 1,
        children: RefCell::new(Vec::new()),
        parent: RefCell::new(None),
    });
    
    let node2 = Rc::new(Node {
        value: 2,
        children: RefCell::new(Vec::new()),
        parent: RefCell::new(Some(Rc::clone(&node1))),
    });
    
    // 创建循环引用
    node1.children.borrow_mut().push(Rc::clone(&node2));
    
    // 即使离开作用域，内存也不会被释放
    println!("Created circular reference");
}

// 使用 Weak 引用避免循环引用
use std::rc::Weak;

struct SafeNode {
    value: i32,
    children: RefCell<Vec<Rc<SafeNode>>>,
    parent: RefCell<Option<Weak<SafeNode>>>,
}

fn safe_node_example() {
    let node1 = Rc::new(SafeNode {
        value: 1,
        children: RefCell::new(Vec::new()),
        parent: RefCell::new(None),
    });
    
    let node2 = Rc::new(SafeNode {
        value: 2,
        children: RefCell::new(Vec::new()),
        parent: RefCell::new(Some(Rc::downgrade(&node1))),
    });
    
    node1.children.borrow_mut().push(Rc::clone(&node2));
    
    // 使用 Weak 引用，内存可以正常释放
    println!("Created safe reference");
}
```

## 9. 性能优化

### 9.1 内存布局优化

```rust
// 内存布局优化示例
#[repr(C)]
struct OptimizedStruct {
    large_field: u64,  // 8 字节，放在前面
    medium_field: u32, // 4 字节
    small_field: u16,  // 2 字节
    tiny_field: u8,    // 1 字节
}

fn layout_optimization() {
    println!("Optimized struct size: {}", std::mem::size_of::<OptimizedStruct>());
    println!("Optimized struct alignment: {}", std::mem::align_of::<OptimizedStruct>());
}

// 缓存友好的数据结构
struct CacheFriendlyStruct {
    data: [f64; 64],  // 连续的内存布局
}

fn cache_friendly_example() {
    let mut structs = Vec::new();
    for i in 0..1000 {
        structs.push(CacheFriendlyStruct {
            data: [i as f64; 64],
        });
    }
    
    // 顺序访问，缓存友好
    let sum: f64 = structs.iter()
        .flat_map(|s| s.data.iter())
        .sum();
    
    println!("Sum: {}", sum);
}
```

### 9.2 零拷贝技术

```rust
// 零拷贝技术示例
use std::borrow::Cow;

fn zero_copy_example() {
    let data = "hello world";
    
    // 使用 Cow 避免不必要的克隆
    let cow: Cow<str> = Cow::Borrowed(data);
    println!("Cow: {}", cow);
    
    // 只有在需要修改时才进行克隆
    let mut cow: Cow<str> = Cow::Borrowed(data);
    cow.to_mut().make_ascii_uppercase();
    println!("Modified cow: {}", cow);
}

// 使用切片避免数据复制
fn slice_example() {
    let data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    
    // 使用切片，不复制数据
    let slice = &data[2..8];
    println!("Slice: {:?}", slice);
    
    // 处理切片
    let sum: i32 = slice.iter().sum();
    println!("Sum: {}", sum);
}
```

### 9.3 内存池

```rust
// 简单内存池实现
use std::collections::VecDeque;

struct MemoryPool<T> {
    available: VecDeque<T>,
    capacity: usize,
}

impl<T> MemoryPool<T> {
    fn new(capacity: usize) -> Self {
        MemoryPool {
            available: VecDeque::new(),
            capacity,
        }
    }
    
    fn get(&mut self) -> Option<T> {
        self.available.pop_front()
    }
    
    fn return_item(&mut self, item: T) {
        if self.available.len() < self.capacity {
            self.available.push_back(item);
        }
    }
}

fn memory_pool_example() {
    let mut pool = MemoryPool::new(10);
    
    // 从池中获取对象
    if let Some(item) = pool.get() {
        // 使用对象
        println!("Got item from pool");
        
        // 归还对象
        pool.return_item(item);
    }
}
```

### 9.4 缓存友好性

```rust
// 缓存友好的数据结构
struct CacheFriendlyArray {
    data: Vec<f64>,
}

impl CacheFriendlyArray {
    fn new(size: usize) -> Self {
        CacheFriendlyArray {
            data: vec![0.0; size],
        }
    }
    
    fn sum(&self) -> f64 {
        // 顺序访问，缓存友好
        self.data.iter().sum()
    }
    
    fn random_access(&self, indices: &[usize]) -> f64 {
        // 随机访问，可能缓存不友好
        indices.iter().map(|&i| self.data[i]).sum()
    }
}

fn cache_friendly_benchmark() {
    let array = CacheFriendlyArray::new(1000000);
    
    // 顺序访问
    let start = std::time::Instant::now();
    let _sum = array.sum();
    let sequential_time = start.elapsed();
    
    // 随机访问
    let indices: Vec<usize> = (0..1000000).map(|i| i * 7 % 1000000).collect();
    let start = std::time::Instant::now();
    let _sum = array.random_access(&indices);
    let random_time = start.elapsed();
    
    println!("Sequential access: {:?}", sequential_time);
    println!("Random access: {:?}", random_time);
}
```

## 10. 调试和诊断

### 10.1 内存错误诊断

```rust
// 内存错误诊断示例
fn memory_error_diagnosis() {
    // 使用 AddressSanitizer 检测内存错误
    // 编译时使用: RUSTFLAGS="-Z sanitizer=address" cargo run
    
    let mut vec = vec![1, 2, 3, 4, 5];
    
    // 安全的访问
    if let Some(value) = vec.get(2) {
        println!("Safe access: {}", value);
    }
    
    // 不安全的访问（在调试模式下会 panic）
    // let value = vec[10];  // 索引越界
}

// 使用调试工具
fn debug_tools() {
    let data = vec![1, 2, 3, 4, 5];
    
    // 使用 dbg! 宏调试
    dbg!(&data);
    
    // 使用 println! 调试内存布局
    println!("Data pointer: {:p}", data.as_ptr());
    println!("Data length: {}", data.len());
    println!("Data capacity: {}", data.capacity());
}
```

### 10.2 工具支持

```rust
// 使用内存分析工具
fn memory_analysis_tools() {
    // 使用 valgrind 检测内存错误
    // valgrind --tool=memcheck --leak-check=full ./target/debug/program
    
    // 使用 perf 分析内存访问模式
    // perf record -e cache-misses ./target/debug/program
    
    let data = vec![1, 2, 3, 4, 5];
    println!("Memory analysis data: {:?}", data);
}

// 使用 Rust 的内存分析工具
fn rust_memory_tools() {
    // 使用 heaptrack 分析堆内存使用
    // heaptrack ./target/debug/program
    
    // 使用 massif 分析内存使用
    // valgrind --tool=massif ./target/debug/program
    
    let mut vec = Vec::new();
    for i in 0..1000 {
        vec.push(i);
    }
    
    println!("Allocated {} elements", vec.len());
}
```

### 10.3 最佳实践

```rust
// 内存安全最佳实践
fn memory_safety_best_practices() {
    // 1. 优先使用安全的 API
    let vec = vec![1, 2, 3, 4, 5];
    if let Some(value) = vec.get(2) {
        println!("Safe access: {}", value);
    }
    
    // 2. 使用 RAII 管理资源
    {
        let _file = std::fs::File::open("test.txt").unwrap();
        // 文件在作用域结束时自动关闭
    }
    
    // 3. 避免不必要的 unsafe 代码
    let data = vec![1, 2, 3, 4, 5];
    let slice = &data[1..4];  // 安全的方式
    println!("Slice: {:?}", slice);
    
    // 4. 使用适当的容器类型
    use std::collections::HashMap;
    let mut map = HashMap::new();
    map.insert("key", "value");
    println!("Map: {:?}", map);
}

// 性能优化最佳实践
fn performance_best_practices() {
    // 1. 使用适当的数据结构
    let vec = vec![1, 2, 3, 4, 5];  // 连续内存，缓存友好
    let sum: i32 = vec.iter().sum();
    println!("Sum: {}", sum);
    
    // 2. 避免不必要的克隆
    let data = vec![1, 2, 3, 4, 5];
    let slice = &data[1..4];  // 借用，不克隆
    println!("Slice: {:?}", slice);
    
    // 3. 使用迭代器链
    let result: Vec<i32> = (0..1000)
        .filter(|&x| x % 2 == 0)
        .map(|x| x * x)
        .collect();
    println!("Result length: {}", result.len());
}
```

## 11. 总结

Rust 的内存安全系统通过以下机制保证了内存安全：

1. **所有权系统**: 确保每个值有唯一的所有者
2. **借用检查器**: 编译时检查引用的有效性
3. **生命周期系统**: 防止悬垂引用
4. **类型系统**: 防止类型相关的内存错误

### 关键要点

- 内存安全是 Rust 的核心特性
- 所有权、借用和生命周期系统协同工作
- 内部可变性提供了灵活的内存管理选项
- 不安全代码需要谨慎使用
- 性能优化需要考虑内存布局和缓存友好性

### 进一步学习

- 学习更多内存管理技术
- 研究 Rust 编译器的内存安全实现
- 了解其他语言的内存管理机制
- 实践编写内存安全的代码

---

**示例与测试**: 见 `examples/memory_safety_examples.rs` 与 `tests/memory_safety_tests.rs`。
