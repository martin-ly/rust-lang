# 可变引用规则

**主题**: Ownership Borrowing
**难度**: Easy
**练习编号**: ex03_mutable_borrow

---

## 题目描述

理解可变引用的排他性，实现字符串修改与读取。

## 代码位置

- 代码框架: `exercises/src/ownership_borrowing/ex03_mutable_borrow.rs`
- 测试用例: 同一文件内的 `#[cfg(test)]` 模块

## 学习目标

- 理解 ownership/borrowing 的核心概念
- 能够独立编写通过测试的实现
- 掌握相关的 Rust 语法和惯用法

## 运行测试

```bash
cd exercises
cargo test ownership_borrowing::ex03_mutable_borrow
```

或运行整个主题的测试：

```bash
cd exercises
cargo test ownership_borrowing::
```
