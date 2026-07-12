> **EN**: Advanced Network Protocol Examples in Rust (c10_networks example index)
> **Summary**: A stub page pointing to the canonical concept authority for gRPC, MQTT, QUIC, AMQP, GraphQL, and SSE. The c10_networks crate provides runnable protocol examples.

# Rust 1.90 网络编程实战示例大全 Part 3 — 高级协议（c10_networks 示例索引）

> **权威来源**: gRPC、MQTT、QUIC、AMQP、GraphQL over HTTP、SSE 等协议概念、选型与学习路径见
> [`concept/06_ecosystem/12_networking/01_advanced_network_protocols.md`](../../../concept/06_ecosystem/12_networking/01_advanced_network_protocols.md)。

本文件原为 `c10_networks` crate 的高级协议代码示例集合，同时包含大量通用协议理论叙述。
根据 AGENTS.md §6.4 治理规则，通用协议概念解释已迁移至
`concept/06_ecosystem/12_networking/`，此处仅保留索引与 canonical 链接。

## 本 crate 相关示例

- `crates/c10_networks/examples/`：gRPC、MQTT、QUIC、AMQP、WebSocket、libp2p 等可运行示例。
- `crates/c10_networks/proto/`：gRPC `.proto` 定义文件。
- `crates/c10_networks/src/bin/main.rs`：网络模块入口。

## 快速导航

| 主题 | 权威来源 |
| :--- | :--- |
| 高级网络协议概览与选型 | [`concept/06_ecosystem/12_networking/01_advanced_network_protocols.md`](../../../concept/06_ecosystem/12_networking/01_advanced_network_protocols.md) |
| 异步编程 | [`concept/03_advanced/01_async/01_async.md`](../../../concept/03_advanced/01_async/01_async.md) |
| 并发模型 | [`concept/03_advanced/00_concurrency/01_concurrency.md`](../../../concept/03_advanced/00_concurrency/01_concurrency.md) |

## 备注

原文件中的完整协议代码示例（~2000+ 行）仍可通过 git 历史恢复；
后续如需在 crate 中保留可编译示例，建议将其拆分至 `crates/c10_networks/examples/` 下独立文件。
