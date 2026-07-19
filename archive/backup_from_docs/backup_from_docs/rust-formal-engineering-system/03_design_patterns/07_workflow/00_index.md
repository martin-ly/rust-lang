# 工作流模式（Workflow Patterns）索引

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: 🔄 进行中

---

## 📊 目录

- [工作流模式（Workflow Patterns）索引](#工作流模式workflow-patterns索引)
  - [📊 目录](#-目录)
  - [目的](#目的)
  - [核心模式](#核心模式)
  - [Rust 化要点](#rust-化要点)
  - [术语（Terminology）](#术语terminology)
  - [实践与样例（Practice）](#实践与样例practice)
    - [文件级清单（精选）](#文件级清单精选)
  - [相关索引](#相关索引)
  - [导航](#导航)

---

## 目的

- 介绍工作流设计模式在 Rust 中的实现与应用。
- 提供工作流编排的最佳实践与 Rust 化改造方案。

---

## 核心模式

- **顺序执行模式（Sequential）**: 按顺序执行任务
- **并行执行模式（Parallel）**: 并行执行多个任务
- **条件分支模式（Conditional）**: 根据条件选择执行路径
- **循环模式（Loop）**: 重复执行任务
- **错误处理模式**: 工作流中的错误处理和恢复
- **补偿模式（Compensation）**: 回滚已执行的操作

---

## Rust 化要点

- **状态机**: 使用枚举实现工作流状态机
- **异步执行**: 使用 `async/await` 实现异步工作流
- **错误传播**: 使用 `Result` 和 `?` 操作符
- **组合操作**: 使用组合子组合工作流步骤

---

## 术语（Terminology）

- 工作流模式（Workflow Patterns）
- 顺序执行（Sequential）、并行执行（Parallel）
- 条件分支（Conditional）、循环（Loop）
- 补偿（Compensation）

---

## 实践与样例（Practice）

### 文件级清单（精选）

- 参见 [`crates/c06_async/`](../../../../crates/c06_async/) 目录
- 参见 [`08_practical_examples/`](../../08_practical_examples/) 目录

---

## 相关索引

- [异步编程范式](../../02_programming_paradigms/02_async/00_index.md)
- [设计模式总索引](../00_index.md)

---

## 导航

- 返回总索引：[`../00_index.md`](../00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
- 异步编程：[`../../02_programming_paradigms/02_async/00_index.md`](../../02_programming_paradigms/02_async/00_index.md)
