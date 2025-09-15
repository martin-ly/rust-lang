# Actor 模型（Actor Model）索引

## 目的

- 介绍 Actor 模型在 Rust 中的实现与应用。
- 提供基于 Actor 的并发系统设计指导。

## 核心概念

- Actor 模型：基于消息传递的并发计算模型
- Actor：独立的计算单元，拥有私有状态
- 消息传递：Actor 间通过消息通信
- 邮箱：消息队列与调度机制
- 监督：错误处理与恢复机制

## 与 Rust 的关联

- 消息传递：`mpsc`/`broadcast` 通道
- 异步任务：`tokio::spawn` 任务管理
- 状态管理：基于所有权的数据隔离
- 错误处理：`Result` 类型与错误传播

## 术语（Terminology）

- Actor、消息（Message）、邮箱（Mailbox）
- 监督（Supervision）、容错（Fault Tolerance）
- 位置透明（Location Transparency）
- 消息传递（Message Passing）

## 实践与样例（Practice）

- Actor 实现：参见 [crates/c06_async](../../../crates/c06_async/)
- 分布式系统：[crates/c20_distributed](../../../crates/c20_distributed/)
- 微服务：[crates/c13_microservice](../../../crates/c13_microservice/)

## 相关索引

- 并发范式：[`../05_concurrent/00_index.md`](../05_concurrent/00_index.md)
- 事件驱动：[`../08_event_driven/00_index.md`](../08_event_driven/00_index.md)
- 理论基础（并发模型）：[`../../01_theoretical_foundations/04_concurrency_models/00_index.md`](../../01_theoretical_foundations/04_concurrency_models/00_index.md)

## 导航

- 返回范式总览：[`../00_index.md`](../00_index.md)
- 并发范式：[`../05_concurrent/00_index.md`](../05_concurrent/00_index.md)
- 事件驱动：[`../08_event_driven/00_index.md`](../08_event_driven/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
