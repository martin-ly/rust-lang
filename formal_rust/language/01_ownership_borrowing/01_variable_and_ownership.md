# 01.1 变量系统与所有权基础

## 概述

本章系统梳理 Rust 变量系统与所有权基础，阐释变量声明、绑定、所有权转移、不可变性与可变性等核心机制，为后续生命周期、借用等理论奠定基础。

## 理论基础

- 变量绑定与作用域
- 所有权模型的三大规则
- 不可变性与可变性
- 所有权转移（Move）、复制（Copy）、借用（Borrow）

## 变量声明与所有权转移

### 1. 变量声明与绑定

```rust
let x = 5; // 不可变绑定
let mut y = 10; // 可变绑定
```

### 2. 所有权转移（Move）

```rust
let s1 = String::from("hello");
let s2 = s1; // s1 的所有权转移给 s2，s1 失效
// println!("{}", s1); // 编译错误
```

### 3. 复制（Copy）类型

```rust
let a = 42;
let b = a; // i32 实现 Copy，a 依然有效
println!("a = {}, b = {}", a, b);
```

### 4. 借用（Borrow）

```rust
let s = String::from("world");
let r = &s; // 不可变借用
let m = &mut y; // 可变借用
```

## 典型代码示例

```rust
fn ownership_demo() {
    let s = String::from("Rust");
    takes_ownership(s); // s 的所有权被转移
    // println!("{}", s); // 编译错误

    let x = 5;
    makes_copy(x); // x 实现 Copy，依然有效
    println!("x = {}", x);
}

fn takes_ownership(some_string: String) {
    println!("{}", some_string);
}

fn makes_copy(some_integer: i32) {
    println!("{}", some_integer);
}
```

## 批判性分析

- Rust 所有权模型极大提升了内存安全性，但对初学者有一定学习曲线
- 变量系统的不可变性默认设计有助于并发安全，但灵活性需通过可变绑定实现
- 所有权转移与借用机制在工程实践中需注意生命周期与悬垂引用风险

## FAQ

- Rust 变量为何默认不可变？
  - 保证线程安全与数据一致性，减少意外修改。
- 所有权转移后原变量还能用吗？
  - 不能，除非实现 Copy trait。
- 如何安全地在多线程中共享变量？
  - 需结合 Arc/Mutex 等并发原语。

## 交叉引用

- [生命周期与作用域分析](./02_lifetime_and_scope.md)
- [可变性与内部可变性](./03_mutability_and_interior.md)
- [内存管理与平衡机制](./05_memory_management_and_balance.md)

## 总结

Rust 变量系统与所有权基础为内存安全、并发安全和高性能编程提供了坚实理论支撑，是理解 Rust 语言的核心起点。
