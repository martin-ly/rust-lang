# 事件驱动范式（Event-Driven Paradigm）索引

## 目的

- 介绍事件驱动编程在 Rust 中的实现与应用。
- 提供事件驱动系统设计与事件处理的最佳实践。

## 核心概念

- 事件驱动：基于事件和消息的编程模型
- 事件循环：事件分发与处理机制
- 事件总线：事件路由与分发中心
- 异步事件：非阻塞事件处理
- 事件溯源：基于事件的状态管理

## 与 Rust 的关联

- 异步事件：`tokio` 事件循环
- 消息传递：`mpsc`/`broadcast` 通道
- 事件处理：基于 trait 的事件处理器
- 状态机：`enum` 与模式匹配

## 术语（Terminology）

- 事件（Event）、事件循环（Event Loop）
- 事件总线（Event Bus）、事件处理器（Event Handler）
- 事件溯源（Event Sourcing）、CQRS（Command Query Responsibility Segregation）
- 消息传递（Message Passing）

## 实践与样例（Practice）

- 事件驱动系统：参见 [crates/c06_async](../../../crates/c06_async/)
- 网络事件处理：[crates/c10_networks](../../../crates/c10_networks/)
- 微服务事件：[crates/c13_microservice](../../../crates/c13_microservice/)

## 相关索引

- 响应式范式：[`../07_reactive/00_index.md`](../07_reactive/00_index.md)
- 异步范式：[`../02_async/00_index.md`](../02_async/00_index.md)
- 设计模式（观察者模式）：[`../../03_design_patterns/00_index.md`](../../03_design_patterns/00_index.md)

## 导航

- 返回范式总览：[`../00_index.md`](../00_index.md)
- 响应式范式：[`../07_reactive/00_index.md`](../07_reactive/00_index.md)
- 异步范式：[`../02_async/00_index.md`](../02_async/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
