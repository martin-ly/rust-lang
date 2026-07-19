# Actor模型编程范式（Actor Model Programming Paradigm）索引

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: 🔄 进行中

---

## 📊 目录

- [Actor模型编程范式（Actor Model Programming Paradigm）索引](#actor模型编程范式actor-model-programming-paradigm索引)
  - [📊 目录](#-目录)
  - [目的](#目的)
  - [术语](#术语)
  - [核心概念](#核心概念)
  - [💻 实际代码示例](#-实际代码示例)
  - [实践与示例（仓库内）](#实践与示例仓库内)
  - [设计建议](#设计建议)
  - [常见陷阱](#常见陷阱)
  - [参考资料](#参考资料)
  - [📚 内容文档](#-内容文档)
  - [导航](#导航)

---

## 目的

- 明确 Actor 模型在 Rust 中的定位与适用场景。
- 统一 Actor 模型相关术语，建立与其他编程范式的映射关系。
- 汇总仓库中与 Actor 模型相关的示例与深度文章。

---

## 术语

- **Actor**: 并发计算的基本单元，通过消息传递通信。
- **消息传递（Message Passing）**: Actor 之间通过消息通信。
- **邮箱（Mailbox）**: Actor 接收消息的队列。
- **监督（Supervision）**: Actor 的错误处理和恢复机制。

---

## 核心概念

- **Actor 系统**: Actor 的创建、管理和通信。
- **消息传递**: 异步消息传递机制。
- **监督策略**: Actor 失败处理策略。
- **位置透明**: Actor 的位置对用户透明。

---

## 💻 实际代码示例

将 Actor 模型形式化理论知识应用到实际代码中：

- **[C06 异步模块](../../../../crates/c06_async/)** - Actor 模式实现
- **Actix**: Rust Actor 框架

**学习路径**: 形式化理论 → 实际代码 → 验证理解

---

## 实践与示例（仓库内）

- Actor 实现：参见 `crates/c06_async/src/actix/`。
- Actor 示例：参见 `crates/c06_async/examples/`。

---

## 设计建议

- 设计清晰的 Actor 边界。
- 使用消息传递而非共享状态。
- 实现适当的监督策略。
- 考虑 Actor 的生命周期管理。

---

## 常见陷阱

- Actor 之间共享可变状态。
- 消息顺序问题。
- 死锁和活锁。

---

## 参考资料

- Actix 文档：`actix`
- Actor 模型理论
- 并发编程最佳实践

---

## 📚 内容文档

- **[Actor 模型基础](./01_actor_system_basics.md)** - Actor 系统实践和示例 ✅

## 导航

- 返回总索引：[`../00_index.md`](../00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
- 事件驱动：[`../08_event_driven/00_index.md`](../08_event_driven/00_index.md)
- 并发编程：[`../05_concurrent/00_index.md`](../05_concurrent/00_index.md)
