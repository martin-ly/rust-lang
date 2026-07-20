# 03 可变性与内部可变性


## 📊 目录

- [03 可变性与内部可变性](#03-可变性与内部可变性)
  - [📊 目录](#-目录)
  - [概述](#概述)
  - [理论基础](#理论基础)
  - [核心机制](#核心机制)
    - [1. 可变变量与可变借用](#1-可变变量与可变借用)
    - [2. 不可变变量与只读借用](#2-不可变变量与只读借用)
    - [3. 内部可变性（Cell/RefCell）](#3-内部可变性cellrefcell)
    - [4. 多线程下的可变性（Mutex/Arc）](#4-多线程下的可变性mutexarc)
  - [批判性分析](#批判性分析)
  - [FAQ](#faq)
  - [交叉借用](#交叉借用)
  - [总结](#总结)


## 概述

本章系统梳理Rust的可变性（Mutability）与内部可变性（Interior Mutability）机制，分析其对内存安全、并发和灵活性的影响。通过理论分析与代码示例，帮助读者理解Rust如何在类型安全下实现灵活的数据修改。

## 理论基础

- 变量可变性与不可变性
- 可变借用与独占性原则
- 内部可变性设计模式
- 并发与多线程下的可变性约束

## 核心机制

### 1. 可变变量与可变借用

```rust
let mut x = 10;
x = 20;

let mut s = String::from("hello");
let r = &mut s;
r.push_str(", world");
```

### 2. 不可变变量与只读借用

```rust
let y = 5;
let r = &y;
println!("{}", r);
```

### 3. 内部可变性（Cell/RefCell）

```rust
use std::cell::RefCell;

let data = RefCell::new(42);
*data.borrow_mut() = 100;
println!("{}", data.borrow());
```

### 4. 多线程下的可变性（Mutex/Arc）

```rust
use std::sync::{Arc, Mutex};
use std::thread;

let data = Arc::new(Mutex::new(0));
let mut handles = vec![];
for _ in 0..10 {
    let data = Arc::clone(&data);
    handles.push(thread::spawn(move || {
        let mut num = data.lock().unwrap();
        *num += 1;
    }));
}
for handle in handles { handle.join().unwrap(); }
println!("result: {}", *data.lock().unwrap());
```

## 批判性分析

- Rust默认不可变性提升了线程安全，但部分场景下需灵活变通
- 内部可变性打破了借用规则，需谨慎使用，避免运行时借用冲突
- 多线程可变性需结合Arc/Mutex等原语，保证数据一致性

## FAQ

- 为什么Rust变量默认不可变？
  - 保证数据一致性和线程安全，减少意外修改。
- 什么是内部可变性？
  - 允许即使在不可变借用下也能修改数据，常用Cell/RefCell实现。
- RefCell和Mutex有何区别？
  - RefCell用于单线程内部可变性，Mutex用于多线程并发场景。

## 交叉借用

- [所有权与变量系统](./01_variable_and_ownership.md)
- [生命周期与作用域分析](./02_lifetime_and_scope.md)
- [内存管理与平衡机制](./05_memory_management_and_balance.md)

## 总结

Rust通过可变性与内部可变性机制，在保证类型安全的前提下，实现了灵活的数据修改和高效的并发支持。理解这些机制是编写健壮、并发安全Rust代码的关键。
