# Rust 所有权系统基础语法详解

## 目录

- [Rust 所有权系统基础语法详解](#rust-所有权系统基础语法详解)
  - [目录](#目录)
  - [概述](#概述)
  - [1. 所有权基础概念](#1-所有权基础概念)
    - [1.1 所有权规则](#11-所有权规则)
    - [1.2 移动语义 (Move Semantics)](#12-移动语义-move-semantics)
    - [1.3 引用和借用 (References and Borrowing)](#13-引用和借用-references-and-borrowing)
  - [2. 生命周期基础](#2-生命周期基础)
    - [2.1 生命周期注解](#21-生命周期注解)
    - [2.2 生命周期省略规则](#22-生命周期省略规则)
  - [3. 智能指针系统](#3-智能指针系统)
    - [3.1 `Box<T>` - 堆分配](#31-boxt---堆分配)
    - [3.2 `Rc<T>` - 引用计数](#32-rct---引用计数)
    - [3.3 `RefCell<T>` - 内部可变性](#33-refcellt---内部可变性)
  - [4. 内存安全保证](#4-内存安全保证)
    - [4.1 编译时安全检查](#41-编译时安全检查)
    - [4.2 运行时安全检查](#42-运行时安全检查)
  - [5. 高级所有权模式](#5-高级所有权模式)
    - [5.1 所有权转移模式](#51-所有权转移模式)
    - [5.2 借用模式](#52-借用模式)
    - [5.3 生命周期模式](#53-生命周期模式)
  - [6. 性能优化技巧](#6-性能优化技巧)
    - [6.1 避免不必要的克隆](#61-避免不必要的克隆)
    - [6.2 使用 Copy 类型](#62-使用-copy-类型)
    - [6.3 智能指针性能优化](#63-智能指针性能优化)
  - [7. 常见错误和解决方案](#7-常见错误和解决方案)
    - [7.1 所有权错误](#71-所有权错误)
    - [7.2 借用错误](#72-借用错误)
    - [7.3 生命周期错误](#73-生命周期错误)
  - [8. 最佳实践总结](#8-最佳实践总结)
    - [8.1 所有权最佳实践](#81-所有权最佳实践)
    - [8.2 性能优化最佳实践](#82-性能优化最佳实践)
  - [总结](#总结)

## 概述

本文档深入解析 Rust 所有权系统的基础语法，包括详细的中英文注释、规范的语言使用、全面的解释和丰富的示例，充分挖掘 Rust 1.89 版本的语言特性。

## 1. 所有权基础概念

### 1.1 所有权规则

Rust 的所有权系统基于三个核心规则：

```rust
//! 所有权规则 / Ownership Rules
//! 
//! 1. Rust 中的每个值都有一个所有者 / Each value in Rust has an owner
//! 2. 值在任意时刻只能有一个所有者 / There can only be one owner at a time
//! 3. 当所有者离开作用域时，值将被丢弃 / When the owner goes out of scope, the value will be dropped

/// 所有权基础示例 / Basic Ownership Example
fn ownership_basics() {
    // 变量 s 拥有字符串的所有权 / Variable s owns the string
    let s = String::from("hello");
    
    // 所有权转移给函数 / Ownership is transferred to the function
    takes_ownership(s);
    
    // 这里不能再使用 s，因为所有权已经转移 / s can no longer be used here because ownership has been transferred
    // println!("{}", s); // 这会导致编译错误 / This would cause a compilation error
    
    // 基本类型实现了 Copy trait，所以不会转移所有权 / Primitive types implement Copy trait, so ownership is not transferred
    let x = 5;
    makes_copy(x);
    println!("x is still valid: {}", x); // x 仍然有效 / x is still valid
}

/// 获取所有权的函数 / Function that takes ownership
fn takes_ownership(some_string: String) {
    println!("{}", some_string);
} // some_string 在这里离开作用域并被丢弃 / some_string goes out of scope and is dropped

/// 复制值的函数 / Function that copies the value
fn makes_copy(some_integer: i32) {
    println!("{}", some_integer);
} // some_integer 在这里离开作用域，但因为是 Copy 类型，所以没有特殊操作 / some_integer goes out of scope, but since it's a Copy type, no special action is taken
```

### 1.2 移动语义 (Move Semantics)

```rust
/// 移动语义详解 / Move Semantics Explained
fn move_semantics_detailed() {
    // 创建字符串 / Create a string
    let s1 = String::from("hello");
    
    // 移动语义：s1 的所有权转移给 s2 / Move semantics: ownership of s1 is transferred to s2
    let s2 = s1;
    
    // s1 不再有效，因为所有权已经转移 / s1 is no longer valid because ownership has been transferred
    // println!("{}", s1); // 编译错误 / Compilation error
    
    // s2 现在拥有字符串的所有权 / s2 now owns the string
    println!("s2: {}", s2);
    
    // 深度复制：创建新的字符串 / Deep copy: create a new string
    let s3 = s2.clone();
    
    // 现在 s2 和 s3 都有效 / Now both s2 and s3 are valid
    println!("s2: {}, s3: {}", s2, s3);
}

/// 移动语义在函数中的应用 / Application of Move Semantics in Functions
fn move_semantics_in_functions() {
    let s = String::from("hello");
    
    // 所有权转移给函数 / Ownership is transferred to the function
    let s2 = takes_and_gives_back(s);
    
    // s 不再有效，但 s2 有效 / s is no longer valid, but s2 is valid
    println!("s2: {}", s2);
}

/// 获取所有权并返回所有权的函数 / Function that takes ownership and returns ownership
fn takes_and_gives_back(a_string: String) -> String {
    a_string // 返回所有权 / Return ownership
}
```

### 1.3 引用和借用 (References and Borrowing)

```rust
/// 引用和借用详解 / References and Borrowing Explained
fn references_and_borrowing() {
    let s1 = String::from("hello");
    
    // 使用引用而不是转移所有权 / Use reference instead of transferring ownership
    let len = calculate_length(&s1);
    
    // s1 仍然有效，因为我们只借用了它 / s1 is still valid because we only borrowed it
    println!("The length of '{}' is {}.", s1, len);
}

/// 计算字符串长度的函数，使用引用 / Function to calculate string length using reference
fn calculate_length(s: &String) -> usize {
    s.len()
} // s 离开作用域，但因为它不拥有所有权，所以不会丢弃任何内容 / s goes out of scope, but since it doesn't own the value, nothing is dropped

/// 可变引用 / Mutable References
fn mutable_references() {
    let mut s = String::from("hello");
    
    // 可变引用 / Mutable reference
    change(&mut s);
    
    println!("Changed string: {}", s);
}

/// 修改字符串的函数 / Function that modifies the string
fn change(some_string: &mut String) {
    some_string.push_str(", world");
}

/// 借用规则示例 / Borrowing Rules Example
fn borrowing_rules() {
    let mut s = String::from("hello");
    
    // 可以有多个不可变引用 / Can have multiple immutable references
    let r1 = &s;
    let r2 = &s;
    println!("r1: {}, r2: {}", r1, r2);
    
    // 可变引用和不可变引用不能同时存在 / Mutable and immutable references cannot coexist
    let r3 = &mut s;
    // println!("r1: {}", r1); // 编译错误 / Compilation error
    println!("r3: {}", r3);
    
    // 可变引用不能同时存在 / Mutable references cannot coexist
    // let r4 = &mut s; // 编译错误 / Compilation error
}
```

## 2. 生命周期基础

### 2.1 生命周期注解

```rust
/// 生命周期注解基础 / Lifetime Annotation Basics
fn lifetime_annotations_basic() {
    let string1 = String::from("abcd");
    let string2 = "xyz";
    
    let result = longest(string1.as_str(), string2);
    println!("The longest string is {}", result);
}

/// 带生命周期注解的函数 / Function with lifetime annotations
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}

/// 生命周期注解在结构体中的应用 / Application of Lifetime Annotations in Structs
struct ImportantExcerpt<'a> {
    part: &'a str,
}

impl<'a> ImportantExcerpt<'a> {
    /// 方法中的生命周期注解 / Lifetime annotations in methods
    fn level(&self) -> i32 {
        3
    }
    
    /// 方法中的生命周期省略 / Lifetime elision in methods
    fn announce_and_return_part(&self, announcement: &str) -> &str {
        println!("Attention please: {}", announcement);
        self.part
    }
}

/// 生命周期注解示例 / Lifetime Annotation Example
fn lifetime_example() {
    let novel = String::from("Call me Ishmael. Some years ago...");
    let first_sentence = novel.split('.').next().expect("Could not find a '.'");
    let i = ImportantExcerpt {
        part: first_sentence,
    };
    
    println!("Part: {}", i.part);
    println!("Level: {}", i.level());
    println!("Announcement: {}", i.announce_and_return_part("Hello"));
}
```

### 2.2 生命周期省略规则

```rust
/// 生命周期省略规则 / Lifetime Elision Rules
fn lifetime_elision_rules() {
    let s1 = String::from("hello");
    let s2 = String::from("world");
    
    // 编译器可以推断生命周期 / The compiler can infer lifetimes
    let result = first_word(&s1);
    println!("First word: {}", result);
    
    // 多个参数的生命周期推断 / Lifetime inference for multiple parameters
    let result2 = longest_word(&s1, &s2);
    println!("Longest word: {}", result2);
}

/// 生命周期省略示例 1：单参数 / Lifetime Elision Example 1: Single Parameter
fn first_word(s: &str) -> &str {
    let bytes = s.as_bytes();
    
    for (i, &item) in bytes.iter().enumerate() {
        if item == b' ' {
            return &s[0..i];
        }
    }
    
    &s[..]
}

/// 生命周期省略示例 2：多参数 / Lifetime Elision Example 2: Multiple Parameters
fn longest_word(x: &str, y: &str) -> &str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}
```

## 3. 智能指针系统

### 3.1 `Box<T>` - 堆分配

```rust
/// Box<T> 智能指针详解 / Box<T> Smart Pointer Explained
use std::boxed::Box;

fn box_smart_pointer() {
    // 在堆上分配数据 / Allocate data on the heap
    let b = Box::new(5);
    println!("b = {}", b);
    
    // Box 在离开作用域时自动释放内存 / Box automatically frees memory when it goes out of scope
    
    // 递归数据结构示例 / Recursive data structure example
    let list = Cons(1, Box::new(Cons(2, Box::new(Cons(3, Box::new(Nil))))));
    println!("List: {:?}", list);
}

/// 递归枚举 / Recursive Enum
#[derive(Debug)]
enum List {
    Cons(i32, Box<List>),
    Nil,
}

use List::{Cons, Nil};
```

### 3.2 `Rc<T>` - 引用计数

```rust
/// Rc<T> 引用计数智能指针 / Rc<T> Reference Counting Smart Pointer
use std::rc::Rc;

fn rc_smart_pointer() {
    let a = Rc::new(Cons(5, Rc::new(Cons(10, Rc::new(Nil)))));
    println!("count after creating a = {}", Rc::strong_count(&a));
    
    let b = Cons(3, Rc::clone(&a));
    println!("count after creating b = {}", Rc::strong_count(&a));
    
    {
        let c = Cons(4, Rc::clone(&a));
        println!("count after creating c = {}", Rc::strong_count(&a));
    }
    
    println!("count after c goes out of scope = {}", Rc::strong_count(&a));
}

/// 使用 Rc 的递归列表 / Recursive List using Rc
#[derive(Debug)]
enum RcList {
    Cons(i32, Rc<RcList>),
    Nil,
}

use RcList::{Cons as RcCons, Nil as RcNil};
```

### 3.3 `RefCell<T>` - 内部可变性

```rust
/// RefCell<T> 内部可变性 / RefCell<T> Interior Mutability
use std::cell::RefCell;

fn refcell_interior_mutability() {
    let data = RefCell::new(5);
    
    // 不可变借用 / Immutable borrow
    {
        let r1 = data.borrow();
        println!("r1: {}", r1);
    }
    
    // 可变借用 / Mutable borrow
    {
        let mut r2 = data.borrow_mut();
        *r2 += 1;
    }
    
    // 不可变借用 / Immutable borrow
    let r3 = data.borrow();
    println!("r3: {}", r3);
}

/// 结合 Rc 和 RefCell / Combining Rc and RefCell
fn rc_refcell_combination() {
    let value = Rc::new(RefCell::new(5));
    
    let a = Rc::new(Cons(Rc::clone(&value), Rc::new(Nil)));
    let b = Cons(Rc::new(RefCell::new(3)), Rc::clone(&a));
    let c = Cons(Rc::new(RefCell::new(4)), Rc::clone(&a));
    
    *value.borrow_mut() += 10;
    
    println!("a after = {:?}", a);
    println!("b after = {:?}", b);
    println!("c after = {:?}", c);
}

/// 使用 Rc<RefCell<T>> 的递归列表 / Recursive List using Rc<RefCell<T>>
#[derive(Debug)]
enum RcRefCellList {
    Cons(Rc<RefCell<i32>>, Rc<RcRefCellList>),
    Nil,
}

use RcRefCellList::{Cons as RcRefCellCons, Nil as RcRefCellNil};
```

## 4. 内存安全保证

### 4.1 编译时安全检查

```rust
/// 编译时内存安全检查 / Compile-time Memory Safety Checks
fn compile_time_safety_checks() {
    // 1. 悬垂引用检测 / Dangling Reference Detection
    // let reference_to_nothing = dangle(); // 编译错误 / Compilation error
    
    // 2. 数据竞争检测 / Data Race Detection
    let mut data = vec![1, 2, 3];
    let reference = &data[0];
    // data.push(4); // 编译错误：不能同时有可变和不可变借用 / Compilation error: cannot have mutable and immutable borrows at the same time
    println!("Reference: {}", reference);
    
    // 3. 双重释放检测 / Double Free Detection
    let s = String::from("hello");
    // drop(s); // 手动释放 / Manual drop
    // drop(s); // 编译错误：值已经被移动 / Compilation error: value has already been moved
}

/// 悬垂引用示例（编译错误）/ Dangling Reference Example (Compilation Error)
// fn dangle() -> &String {
//     let s = String::from("hello");
//     &s // 编译错误：返回对局部变量的引用 / Compilation error: returning reference to local variable
// }

/// 正确的引用返回 / Correct Reference Return
fn no_dangle() -> String {
    let s = String::from("hello");
    s // 返回所有权而不是引用 / Return ownership instead of reference
}
```

### 4.2 运行时安全检查

```rust
/// 运行时内存安全检查 / Runtime Memory Safety Checks
use std::cell::RefCell;
use std::rc::Rc;

fn runtime_safety_checks() {
    // RefCell 的运行时借用检查 / Runtime borrow checking for RefCell
    let data = RefCell::new(5);
    
    // 正确的借用 / Correct borrowing
    {
        let r1 = data.borrow();
        println!("r1: {}", r1);
    }
    
    {
        let mut r2 = data.borrow_mut();
        *r2 += 1;
    }
    
    // 错误的借用（运行时 panic）/ Incorrect borrowing (runtime panic)
    // let r1 = data.borrow();
    // let mut r2 = data.borrow_mut(); // panic: already borrowed
    
    println!("Final value: {}", data.borrow());
}
```

## 5. 高级所有权模式

### 5.1 所有权转移模式

```rust
/// 所有权转移模式 / Ownership Transfer Patterns
fn ownership_transfer_patterns() {
    // 1. 函数参数所有权转移 / Function parameter ownership transfer
    let s = String::from("hello");
    takes_ownership(s);
    // s 不再有效 / s is no longer valid
    
    // 2. 返回值所有权转移 / Return value ownership transfer
    let s1 = gives_ownership();
    let s2 = String::from("hello");
    let s3 = takes_and_gives_back(s2);
    
    println!("s1: {}, s3: {}", s1, s3);
    
    // 3. 结构体字段所有权 / Struct field ownership
    let user = User {
        name: String::from("Alice"),
        email: String::from("alice@example.com"),
    };
    
    println!("User: {} <{}>", user.name, user.email);
}

/// 返回所有权的函数 / Function that returns ownership
fn gives_ownership() -> String {
    let some_string = String::from("yours");
    some_string // 返回所有权 / Return ownership
}

/// 获取并返回所有权的函数 / Function that takes and returns ownership
fn takes_and_gives_back(a_string: String) -> String {
    a_string // 返回所有权 / Return ownership
}

/// 用户结构体 / User Struct
struct User {
    name: String,
    email: String,
}
```

### 5.2 借用模式

```rust
/// 借用模式详解 / Borrowing Patterns Explained
fn borrowing_patterns() {
    let mut data = vec![1, 2, 3, 4, 5];
    
    // 1. 不可变借用 / Immutable borrowing
    let reference = &data[0];
    println!("Reference: {}", reference);
    
    // 2. 可变借用 / Mutable borrowing
    let mutable_reference = &mut data[1];
    *mutable_reference = 10;
    println!("Modified: {}", mutable_reference);
    
    // 3. 切片借用 / Slice borrowing
    let slice = &data[1..4];
    println!("Slice: {:?}", slice);
    
    // 4. 结构体字段借用 / Struct field borrowing
    let mut user = User {
        name: String::from("Bob"),
        email: String::from("bob@example.com"),
    };
    
    let name_ref = &user.name;
    let email_ref = &user.email;
    println!("Name: {}, Email: {}", name_ref, email_ref);
    
    // 5. 可变结构体字段借用 / Mutable struct field borrowing
    let name_mut_ref = &mut user.name;
    name_mut_ref.push_str(" Smith");
    println!("Modified name: {}", name_mut_ref);
}
```

### 5.3 生命周期模式

```rust
/// 生命周期模式详解 / Lifetime Patterns Explained
fn lifetime_patterns() {
    let string1 = String::from("abcd");
    let string2 = "xyz";
    
    // 1. 显式生命周期注解 / Explicit lifetime annotations
    let result = longest_with_an_announcement(&string1, string2, "Today is someone's birthday!");
    println!("The longest string is {}", result);
    
    // 2. 结构体生命周期 / Struct lifetimes
    let novel = String::from("Call me Ishmael. Some years ago...");
    let first_sentence = novel.split('.').next().expect("Could not find a '.'");
    let i = ImportantExcerpt {
        part: first_sentence,
    };
    
    // 3. 方法生命周期 / Method lifetimes
    let announcement = "Attention please";
    let part = i.announce_and_return_part(announcement);
    println!("Part: {}", part);
}

/// 带生命周期注解和额外参数的函数 / Function with lifetime annotations and additional parameters
fn longest_with_an_announcement<'a>(x: &'a str, y: &'a str, ann: &str) -> &'a str {
    println!("Announcement! {}", ann);
    if x.len() > y.len() {
        x
    } else {
        y
    }
}
```

## 6. 性能优化技巧

### 6.1 避免不必要的克隆

```rust
/// 避免不必要的克隆 / Avoiding Unnecessary Clones
fn avoid_unnecessary_clones() {
    let data = String::from("hello world");
    
    // 错误：不必要的克隆 / Wrong: unnecessary clone
    // let processed = process_string(data.clone());
    
    // 正确：使用引用 / Correct: use reference
    let processed = process_string(&data);
    
    println!("Original: {}", data);
    println!("Processed: {}", processed);
}

/// 处理字符串的函数 / Function that processes a string
fn process_string(s: &str) -> String {
    s.to_uppercase()
}
```

### 6.2 使用 Copy 类型

```rust
/// 使用 Copy 类型优化性能 / Using Copy Types for Performance
fn use_copy_types() {
    // 基本类型实现了 Copy trait / Primitive types implement Copy trait
    let x = 5;
    let y = x; // 复制，不是移动 / Copy, not move
    println!("x: {}, y: {}", x, y);
    
    // 自定义 Copy 类型 / Custom Copy type
    let point1 = Point { x: 0, y: 0 };
    let point2 = point1; // 复制 / Copy
    println!("Point1: {:?}, Point2: {:?}", point1, point2);
}

/// 实现 Copy trait 的结构体 / Struct that implements Copy trait
#[derive(Debug, Copy, Clone)]
struct Point {
    x: i32,
    y: i32,
}
```

### 6.3 智能指针性能优化

```rust
/// 智能指针性能优化 / Smart Pointer Performance Optimization
use std::rc::Rc;
use std::cell::RefCell;

fn smart_pointer_optimization() {
    // 使用 Rc 避免克隆 / Use Rc to avoid cloning
    let data = Rc::new(vec![1, 2, 3, 4, 5]);
    let data_clone1 = Rc::clone(&data);
    let data_clone2 = Rc::clone(&data);
    
    // 所有引用指向同一个数据 / All references point to the same data
    println!("Data: {:?}", data);
    println!("Clone1: {:?}", data_clone1);
    println!("Clone2: {:?}", data_clone2);
    
    // 使用 RefCell 实现内部可变性 / Use RefCell for interior mutability
    let counter = Rc::new(RefCell::new(0));
    let counter_clone = Rc::clone(&counter);
    
    *counter.borrow_mut() += 1;
    *counter_clone.borrow_mut() += 1;
    
    println!("Counter: {}", counter.borrow());
}
```

## 7. 常见错误和解决方案

### 7.1 所有权错误

```rust
/// 常见所有权错误和解决方案 / Common Ownership Errors and Solutions
fn common_ownership_errors() {
    // 错误 1：使用已移动的值 / Error 1: Using moved value
    let s1 = String::from("hello");
    let s2 = s1; // s1 被移动 / s1 is moved
    // println!("{}", s1); // 编译错误 / Compilation error
    
    // 解决方案：使用引用 / Solution: use reference
    let s3 = String::from("hello");
    let s4 = &s3; // 借用 / borrow
    println!("s3: {}, s4: {}", s3, s4);
    
    // 错误 2：悬垂引用 / Error 2: Dangling reference
    // let reference_to_nothing = dangle(); // 编译错误 / Compilation error
    
    // 解决方案：返回所有权 / Solution: return ownership
    let valid_string = no_dangle();
    println!("Valid string: {}", valid_string);
}
```

### 7.2 借用错误

```rust
/// 常见借用错误和解决方案 / Common Borrowing Errors and Solutions
fn common_borrowing_errors() {
    let mut data = vec![1, 2, 3];
    
    // 错误 1：可变和不可变借用冲突 / Error 1: Mutable and immutable borrow conflict
    let reference = &data[0];
    // data.push(4); // 编译错误 / Compilation error
    
    // 解决方案：限制借用作用域 / Solution: limit borrow scope
    {
        let reference = &data[0];
        println!("Reference: {}", reference);
    } // 借用在这里结束 / Borrow ends here
    
    data.push(4); // 现在可以修改 / Now we can modify
    
    // 错误 2：多个可变借用 / Error 2: Multiple mutable borrows
    // let r1 = &mut data;
    // let r2 = &mut data; // 编译错误 / Compilation error
    
    // 解决方案：限制可变借用作用域 / Solution: limit mutable borrow scope
    {
        let r1 = &mut data;
        r1.push(5);
    }
    
    {
        let r2 = &mut data;
        r2.push(6);
    }
    
    println!("Data: {:?}", data);
}
```

### 7.3 生命周期错误

```rust
/// 常见生命周期错误和解决方案 / Common Lifetime Errors and Solutions
fn common_lifetime_errors() {
    // 错误 1：生命周期不匹配 / Error 1: Lifetime mismatch
    let string1 = String::from("abcd");
    let result;
    {
        let string2 = String::from("xyz");
        // result = longest(&string1, &string2); // 编译错误 / Compilation error
    }
    // println!("The longest string is {}", result);
    
    // 解决方案：确保生命周期匹配 / Solution: ensure lifetime matching
    let string1 = String::from("abcd");
    let string2 = String::from("xyz");
    let result = longest(&string1, &string2);
    println!("The longest string is {}", result);
}
```

## 8. 最佳实践总结

### 8.1 所有权最佳实践

```rust
/// 所有权最佳实践 / Ownership Best Practices
fn ownership_best_practices() {
    // 1. 优先使用引用而不是所有权转移 / 1. Prefer references over ownership transfer
    let data = String::from("hello");
    let length = calculate_length(&data);
    println!("Length: {}, Data: {}", length, data);
    
    // 2. 使用智能指针管理复杂所有权 / 2. Use smart pointers for complex ownership
    let shared_data = Rc::new(RefCell::new(vec![1, 2, 3]));
    let shared_clone = Rc::clone(&shared_data);
    
    // 3. 合理使用生命周期注解 / 3. Use lifetime annotations appropriately
    let string1 = String::from("abcd");
    let string2 = "xyz";
    let result = longest(&string1, string2);
    println!("Longest: {}", result);
    
    // 4. 避免不必要的克隆 / 4. Avoid unnecessary clones
    let processed = process_string(&data);
    println!("Processed: {}", processed);
}
```

### 8.2 性能优化最佳实践

```rust
/// 性能优化最佳实践 / Performance Optimization Best Practices
fn performance_best_practices() {
    // 1. 使用 Copy 类型避免移动开销 / 1. Use Copy types to avoid move overhead
    let x = 5;
    let y = x; // 复制，不是移动 / Copy, not move
    
    // 2. 使用引用避免克隆开销 / 2. Use references to avoid clone overhead
    let data = vec![1, 2, 3, 4, 5];
    let sum = calculate_sum(&data);
    println!("Sum: {}", sum);
    
    // 3. 使用智能指针共享数据 / 3. Use smart pointers to share data
    let shared_data = Rc::new(data);
    let shared_clone = Rc::clone(&shared_data);
    
    // 4. 最小化借用作用域 / 4. Minimize borrow scopes
    {
        let reference = &shared_data[0];
        println!("Reference: {}", reference);
    } // 借用在这里结束 / Borrow ends here
    
    // 现在可以安全地修改数据 / Now we can safely modify the data
}
```

/// 计算和的函数 / Function to calculate sum
fn calculate_sum(data: &[i32]) -> i32 {
    data.iter().sum()
}

## 总结

Rust 的所有权系统是语言的核心特性，它通过编译时检查确保内存安全，同时提供零成本抽象。通过深入理解所有权、借用和生命周期概念，开发者可以编写安全、高效的 Rust 代码。

关键要点：

1. **所有权规则**：每个值有一个所有者，值在任意时刻只能有一个所有者，当所有者离开作用域时值被丢弃
2. **借用规则**：可以有多个不可变借用，或者一个可变借用，但不能同时有可变和不可变借用
3. **生命周期**：确保引用在有效期内使用，防止悬垂引用
4. **智能指针**：提供不同的所有权语义，如共享所有权（Rc）和内部可变性（RefCell）
5. **性能优化**：使用引用避免克隆，使用 Copy 类型避免移动开销，最小化借用作用域

通过遵循这些原则和最佳实践，开发者可以充分利用 Rust 的所有权系统，编写出既安全又高效的代码。
