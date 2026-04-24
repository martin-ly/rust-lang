# 声明宏

**主题**: Macros  
**难度**: Medium  
**练习编号**: ex01_declarative_macro

---

## 题目描述

编写 set!、ok_or_return!、timed! 宏。

## 代码位置

- 代码框架: `exercises/src/macros/ex01_declarative_macro.rs`
- 测试用例: 同一文件内的 `#[cfg(test)]` 模块

## 学习目标

- 理解 macros 的核心概念
- 能够独立编写通过测试的实现
- 掌握相关的 Rust 语法和惯用法

## 运行测试

```bash
cd exercises
cargo test macros::ex01_declarative_macro
```

或运行整个主题的测试：

```bash
cd exercises
cargo test macros::
```
