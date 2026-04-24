# 错误传播

**主题**: Error Handling  
**难度**: Medium  
**练习编号**: ex03_error_propagation

---

## 题目描述

使用 ? 运算符和 map_err 在多层调用中传播错误。

## 代码位置

- 代码框架: `exercises/src/error_handling/ex03_error_propagation.rs`
- 测试用例: 同一文件内的 `#[cfg(test)]` 模块

## 学习目标

- 理解 error/handling 的核心概念
- 能够独立编写通过测试的实现
- 掌握相关的 Rust 语法和惯用法

## 运行测试

```bash
cd exercises
cargo test error_handling::ex03_error_propagation
```

或运行整个主题的测试：

```bash
cd exercises
cargo test error_handling::
```
