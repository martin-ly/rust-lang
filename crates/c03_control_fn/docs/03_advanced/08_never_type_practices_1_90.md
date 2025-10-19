# 08. 发散类型 `!` 实战 (Never Type Practices - Rust 1.90)

> **文档类型**：高级  
> **难度等级**：⭐⭐⭐  
> **预计阅读时间**：45分钟  
> **前置知识**：类型系统基础、错误处理

## 📖 内容概述

`!` (never type) 表示永不返回的类型。本文档深入讲解其在不可达分支、终止程序、无限循环等场景的应用，以及在类型推断中的特殊作用。

## 🎯 学习目标

完成本文档学习后，你将能够：

- [ ] 理解 never type 的语义
- [ ] 在错误处理中使用发散函数
- [ ] 标记不可达分支
- [ ] 理解 ! 在类型推断中的作用
- [ ] 设计使用 never type 的 API

## 📚 目录

- [08. 发散类型 `!` 实战 (Never Type Practices - Rust 1.90)](#08-发散类型--实战-never-type-practices---rust-190)
  - [📖 内容概述](#-内容概述)
  - [🎯 学习目标](#-学习目标)
  - [📚 目录](#-目录)
  - [8.1. 与 `Option::unwrap_or_else` 配合](#81-与-optionunwrap_or_else-配合)
  - [不可达分支（如 `match` 的逻辑保证）](#不可达分支如-match-的逻辑保证)
  - [无限循环/进程退出](#无限循环进程退出)

---

## 8.1. 与 `Option::unwrap_or_else` 配合

```rust
fn abort(msg: &str) -> ! { panic!("{}", msg); }

fn must(v: Option<i32>) -> i32 {
    v.unwrap_or_else(|| abort("none"))
}
```

## 不可达分支（如 `match` 的逻辑保证）

```rust
fn only_true(b: bool) {
    match b {
        true => {}
        false => unreachable!(),
    }
}
```

## 无限循环/进程退出

```rust
fn never_returns() -> ! { loop {} }
```

---

工程建议：

- 谨慎使用 `panic!/abort`，限定在不可恢复错误；
- `!` 有助于 API 设计中的“永不返回”表达，但注意可测试性。
