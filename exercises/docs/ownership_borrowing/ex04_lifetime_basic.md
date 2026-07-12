# 基础生命周期标注

**主题**: Ownership Borrowing
**难度**: Medium
**练习编号**: ex04_lifetime_basic

---

## 题目描述

为函数添加显式生命周期参数，使其能够编译。

## 代码位置

- 代码框架: `exercises/src/ownership_borrowing/ex04_lifetime_basic.rs`
- 测试用例: 同一文件内的 `#[cfg(test)]` 模块

## 学习目标

- 理解 ownership/borrowing 的核心概念
- 能够独立编写通过测试的实现
- 掌握相关的 Rust 语法和惯用法

## 运行测试

```bash
cd exercises
cargo test ownership_borrowing::ex04_lifetime_basic
```

或运行整个主题的测试：

```bash
cd exercises
cargo test ownership_borrowing::
```

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [Authority Source Sprint Batch 8](../../../concept/00_meta/02_sources/05_international_authority_index.md)

**文档版本**: 1.1
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
