# 网络编程（Networking）

**EN**: Networking
**Summary**: Rust network programming: socket basics, protocol quick start, advanced protocols, network security, custom protocol implementation, and formal protocol theory.

> **权威来源**: 本目录为 `concept/06_ecosystem/` 网络编程专题目录。
> **重编号说明**: 本目录原编号 `09_networking`，因与 `09_testing_and_quality` 编号冲突，于 2026-07-12 重编号为 `12_networking`。

## 目录分工（04 vs 12）

| 目录 | 职责 |
|---|---|
| `04_web_and_networking/` | **Web/云原生应用架构层**：Web 框架、HTTP 客户端、WebSocket 实时通信、云原生、分布式系统、响应式编程、高性能网络服务架构 |
| `12_networking/`（本目录） | **网络编程基础与协议实现层**：socket 编程基础、协议快速入门、高级协议（gRPC/MQTT/QUIC/AMQP/GraphQL/SSE）、网络安全、自定义协议实现、形式化网络协议理论 |

两者互补：本目录提供协议与编程机制基础，`04_web_and_networking/` 在其上构建应用架构。

## 文件索引

- [高级网络协议概览：gRPC / MQTT / QUIC / AMQP / GraphQL / SSE](01_advanced_network_protocols.md)
- [网络安全 (Network Security)](02_network_security.md)
- [自定义协议实现 (Custom Protocol Implementation)](03_custom_protocol_implementation.md)
- [Rust 网络编程快速入门](04_network_programming_quick_start.md)
- [形式化网络协议理论](05_formal_network_protocol_theory.md)
- [网络编程基础 (Networking Basics)](06_networking_basics.md)
