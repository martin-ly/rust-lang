# 事件驱动范式（Event-Driven Paradigm）索引

## 📊 目录

- [事件驱动范式（Event-Driven Paradigm）索引](#事件驱动范式event-driven-paradigm索引)
  - [📊 目录](#-目录)
  - [目的](#目的)
  - [核心概念](#核心概念)
  - [与 Rust 的关联](#与-rust-的关联)
  - [术语（Terminology）](#术语terminology)
  - [实践与样例（Practice）](#实践与样例practice)
    - [文件级清单（精选）](#文件级清单精选)
    - [关联基准与指南](#关联基准与指南)
  - [相关索引](#相关索引)
  - [导航](#导航)

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

### 文件级清单（精选）

- `crates/c06_async/examples/`：
  - `axum_exp01.rs`：HTTP 事件处理与异步路由
  - `tokio_exp01.rs`：事件循环与 select 协作示例
- `crates/c06_async/benches/`：
  - `async_benches.rs`：mpsc、Semaphore 参数化吞吐
- 对照（同步端）：`crates/c05_threads/examples/` 中的背压/限速示例
- 微服务示例（`crates/c13_microservice/examples/`）：
- `simple_axum.rs`：最小 REST 事件入口
- `grpc_service.rs` / `grpc_client_demo.rs`：RPC 事件管道
- `messaging_demo.rs` / `messaging_advanced_demo.rs`：消息事件驱动
- `observability_demo*`：事件链路观测

### 关联基准与指南

- 最小基准指南：[`../11_benchmark_minimal_guide.md`](../11_benchmark_minimal_guide.md)
- 同步基准：[`../../../crates/c05_threads/benches/`](../../../crates/c05_threads/benches/)
- 异步基准：[`../../../crates/c06_async/benches/`](../../../crates/c06_async/benches/)

## 相关索引

- 响应式范式：[`../07_reactive/00_index.md`](../07_reactive/00_index.md)
- 异步范式：[`../02_async/00_index.md`](../02_async/00_index.md)
- 设计模式（观察者模式）：[`../../03_design_patterns/00_index.md`](../../03_design_patterns/00_index.md)

## 导航

- 返回范式总览：[`../00_index.md`](../00_index.md)
- 响应式范式：[`../07_reactive/00_index.md`](../07_reactive/00_index.md)
- 异步范式：[`../02_async/00_index.md`](../02_async/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
