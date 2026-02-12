# Unsafe Rust 专题指南

> **最后更新**: 2026-02-11
> **前置**: 需熟练掌握 C01 所有权、C02 类型系统
> **官方权威**: [The Rustonomicon](https://doc.rust-lang.org/nomicon/)

---

## 文档定位

本指南为 **Rustonomicon** 的补充与项目内导航，帮助在系统学习 unsafe Rust 时快速定位到本项目的相关模块和示例。

---

## 核心内容导航

| 主题         | Rustonomicon 章节     | 本项目对应             |
| ------------ | --------------------- | ---------------------- |
| 裸指针       | Ch. 1 Meet Safe and Unsafe | C01 高级所有权       |
| 借用与可变性 | Ch. 2 Representations | C01 借用检查器         |
| 类型与布局   | Ch. 3 Type Layout     | C02 类型系统           |
| 所有权与生命周期 | Ch. 4 Ownership   | C01 生命周期           |
| 类型转换     | Ch. 5 Type Coercions  | C02 类型转换           |
| 未定义行为   | Ch. 6 Unwinding       | 本文档                 |
| 并发与数据竞争 | Ch. 7 Concurrency   | C05 线程与并发         |
| 内联汇编     | Ch. 8 Assembly        | 系统编程专题           |

---

## 安全抽象原则

1. **封装 unsafe**: 将 `unsafe` 块封装在安全 API 内部
2. **不变式文档化**: 明确写出 `unsafe` 依赖的前提条件
3. **最小化范围**: 仅对必需的操作使用 `unsafe`

---

## 本项目 unsafe 相关资源

- **C01**: [高级所有权模式](../crates/c01_ownership_borrow_scope/docs/tier_03_references/06_高级所有权模式参考.md)
- **C05**: 同步原语、原子操作
- **forms**: [research_notes/formal_methods/](../research_notes/formal_methods/) - 借用检查器证明、生命周期形式化

---

## 推荐学习顺序

1. 通读 Rustonomicon 前 3 章
2. 学习 C01 的零成本抽象与高级所有权
3. 研究本项目 `formal_methods` 中的形式化证明
4. 实践：为现有安全 API 编写 `unsafe` 实现（如自定义集合）
