# RwLock 共享状态

**主题**: Concurrency  
**难度**: Medium  
**练习编号**: ex04_rwlock_shared

---

## 题目描述

使用 RwLock 实现并发缓存，支持多读单写。

## 代码位置

- 代码框架: `exercises/src/concurrency/ex04_rwlock_shared.rs`
- 测试用例: 同一文件内的 `#[cfg(test)]` 模块

## 学习目标

- 理解 concurrency 的核心概念
- 能够独立编写通过测试的实现
- 掌握相关的 Rust 语法和惯用法

## 运行测试

```bash
cd exercises
cargo test concurrency::ex04_rwlock_shared
```

或运行整个主题的测试：

```bash
cd exercises
cargo test concurrency::
```
