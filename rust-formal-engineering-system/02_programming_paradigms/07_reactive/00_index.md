# 响应式范式（Reactive Paradigm）索引

## 目的

- 介绍响应式编程在 Rust 中的实现与应用。
- 提供响应式系统设计与事件流处理的指导。

## 核心概念

- 响应式编程：基于数据流和变化传播的编程范式
- 观察者模式：发布-订阅机制
- 事件流：异步数据流处理
- 背压：流量控制与压力管理
- 组合性：响应式组件的组合与复用

## 与 Rust 的关联

- 异步流：`Stream` trait 与异步迭代器
- 通道：`mpsc`/`broadcast` 消息传递
- 观察者：基于 trait 的观察者模式实现
- 函数式：函数式响应式编程

## 术语（Terminology）

- 响应式（Reactive）、观察者（Observer）
- 事件流（Event Stream）、数据流（Data Stream）
- 背压（Backpressure）、流量控制（Flow Control）
- 组合性（Composability）

## 实践与样例（Practice）

- 异步流处理：参见 [crates/c06_async](../../../crates/c06_async/)
- 网络编程：[crates/c10_networks](../../../crates/c10_networks/)
- 微服务：[crates/c13_microservice](../../../crates/c13_microservice/)

## 相关索引

- 异步范式：[`../02_async/00_index.md`](../02_async/00_index.md)
- 事件驱动：[`../08_event_driven/00_index.md`](../08_event_driven/00_index.md)
- 设计模式（观察者模式）：[`../../03_design_patterns/00_index.md`](../../03_design_patterns/00_index.md)

## 导航

- 返回范式总览：[`../00_index.md`](../00_index.md)
- 异步范式：[`../02_async/00_index.md`](../02_async/00_index.md)
- 事件驱动：[`../08_event_driven/00_index.md`](../08_event_driven/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
