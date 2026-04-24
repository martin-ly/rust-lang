# Rc 智能指针共享所有权

**主题**: Ownership Borrowing
**难度**: Medium
**练习编号**: ex05_smart_pointer_rc

---

## 题目描述

使用 Rc<T> 实现共享配置项，理解引用计数。

## 代码位置

- 代码框架: `exercises/src/ownership_borrowing/ex05_smart_pointer_rc.rs`
- 测试用例: 同一文件内的 `#[cfg(test)]` 模块

## 学习目标

- 理解 ownership/borrowing 的核心概念
- 能够独立编写通过测试的实现
- 掌握相关的 Rust 语法和惯用法

## 运行测试

```bash
cd exercises
cargo test ownership_borrowing::ex05_smart_pointer_rc
```

或运行整个主题的测试：

```bash
cd exercises
cargo test ownership_borrowing::
```
