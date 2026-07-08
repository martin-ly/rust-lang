> **EN**: Advanced Network Protocols in Rust
> **Summary**: A canonical overview of gRPC, MQTT, QUIC, AMQP, GraphQL over HTTP, and Server-Sent Events, with selection guidance for Rust ecosystem libraries.

# Rust 高级网络协议概览

> **权威页地位**：本页为 Rust 生态中高级网络协议概念的 canonical 解释来源。
> **对应 crate 示例**：`crates/c10_networks/docs/rust_190_examples_part3_advanced_protocols.md` 现为摘要页，指向此处。

---

## 1. 协议分类与适用场景

| 协议 | 通信模型 | 最佳场景 | Rust 生态代表库 |
| :--- | :--- | :--- | :--- |
| **gRPC** | RPC / 双向流 | 微服务间高性能调用 | `tonic` + `prost` |
| **MQTT** | 发布/订阅 | IoT、低带宽、不可靠网络 | `rumqttc` |
| **QUIC** | 基于 UDP 的安全传输 | 实时游戏、0-RTT、多路复用 | `quinn` + `rustls` |
| **AMQP** | 消息队列 | 异步任务队列、企业集成 | `lapin` |
| **GraphQL** | 查询语言 over HTTP | 灵活 API 查询、减少过度获取 | `async-graphql`、`cynic` |
| **SSE** | 服务器推送 | 单向实时更新、日志流 | `tokio-stream`、`axum` |

---

## 2. gRPC

gRPC 是基于 HTTP/2 和 Protocol Buffers 的高性能 RPC 框架，支持四种调用模式：

- **Unary RPC**：客户端一次请求，服务器一次响应。
- **Server Streaming RPC**：服务器返回多个响应。
- **Client Streaming RPC**：客户端发送多个请求，服务器返回一个响应。
- **Bidirectional Streaming RPC**：双向流式通信。

Rust 生态使用 `tonic` 作为服务端/客户端框架，`prost` 用于 Protocol Buffers 编解码。

---

## 3. MQTT

MQTT 是轻量级发布/订阅协议，专为 IoT 设计：

- **QoS 0**：最多一次交付。
- **QoS 1**：至少一次交付。
- **QoS 2**：恰好一次交付。

Rust 中常用 `rumqttc` 实现客户端，支持自动重连、遗嘱消息、桥接等高级特性。

---

## 4. QUIC

QUIC 是基于 UDP 的传输协议，内置 TLS 1.3，提供：

- 低连接建立延迟（0-RTT 或 1-RTT）。
- 内置多路复用，避免队头阻塞。
- 连接迁移能力。

Rust 中 `quinn` 是主流 QUIC 实现，常与 `rustls` 和 `rcgen` 配合使用。

---

## 5. AMQP

AMQP 是面向消息中间件的应用层协议，支持：

- 队列、交换机、绑定等核心抽象。
- 生产者/消费者模式。
- 工作队列、发布/订阅、路由、主题等模式。

Rust 中 `lapin` 是常用的 AMQP 0.9.1 客户端。

---

## 6. GraphQL over HTTP

GraphQL 允许客户端精确指定所需字段，减少过度获取。在 Rust 中可作为 HTTP 服务暴露，常与 `axum`、`async-graphql` 等库结合使用。

---

## 7. Server-Sent Events (SSE)

SSE 是服务器向客户端单向推送文本事件的 Web 标准，基于 HTTP：

- 自动重连。
- 事件 ID 与断点续传。
- 适合日志流、通知、实时仪表板。

---

## 8. 技术选型指南

| 场景 | 推荐协议 | 原因 |
| :--- | :--- | :--- |
| 微服务 RPC | gRPC | 高性能、类型安全、双向流 |
| IoT 设备通信 | MQTT | 轻量级、QoS 支持、低带宽 |
| 实时游戏 | QUIC | 低延迟、多路复用、0-RTT |
| 异步任务队列 | AMQP | 可靠消息传递、工作队列 |
| API 查询 | GraphQL | 灵活查询、减少过度获取 |
| 实时推送 | SSE / WebSocket | 服务器推送、实时更新 |

---

## 9. 学习路径

1. **初级**（1-2 周）
   - gRPC Unary RPC
   - MQTT 基础发布订阅
   - QUIC 基本通信
2. **中级**（2-3 周）
   - gRPC Streaming
   - MQTT QoS 和自动重连
   - QUIC 多路复用
   - AMQP 工作队列
3. **高级**（3-4 周）
   - gRPC 拦截器
   - MQTT 桥接
   - AMQP 高级模式
   - GraphQL 集成
   - SSE 实时通信
   - 微服务架构

---

## 10. 相关概念

- [并发模型](../../03_advanced/00_concurrency/01_concurrency.md)
- [异步编程](../../03_advanced/01_async/02_async.md)
- [设计模式](../03_design_patterns/02_patterns.md)
- [执行模型同构性：同步 · 异步 · 并发 · 并行](../../05_comparative/00_paradigms/05_execution_model_isomorphism.md)

---

> **L5 向下引用**: 协议选型可结合 [Rust vs Go：线性所有权 vs CSP 过程逻辑](../../05_comparative/01_systems_languages/02_rust_vs_go.md) 中的并发与通信模型对比进行理解。

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
