# 派生宏框架

**主题**: Macros
**难度**: Hard
**练习编号**: ex02_derive_macro_stub

---

## 题目描述

理解过程宏概念，手动实现 Describe 特质。

## 代码位置

- 代码框架: `exercises/src/macros/ex02_derive_macro_stub.rs`
- 测试用例: 同一文件内的 `#[cfg(test)]` 模块

## 学习目标

- 理解 macros 的核心概念
- 能够独立编写通过测试的实现
- 掌握相关的 Rust 语法和惯用法

## 运行测试

```bash
cd exercises
cargo test macros::ex02_derive_macro_stub
```

或运行整个主题的测试：

```bash
cd exercises
cargo test macros::
```

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
