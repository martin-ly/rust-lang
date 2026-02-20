# C10 网络编程 - 一页纸总结

> **用途**: 快速回顾核心概念、常见坑、学习路径
> **完整文档**: [00_MASTER_INDEX](./00_MASTER_INDEX.md)

---

## 核心概念（4 条）

| 概念 | 说明 |
| :--- | :--- || **TCP/UDP** | `TcpListener`/`TcpStream`；`UdpSocket`；同步与异步 |
| **HTTP** | `reqwest`、`hyper`、`axum`；客户端与服务端 |
| **WebSocket** | `tungstenite`；双向实时通信 |
| **异步网络** | Tokio 运行时；`tokio::net`；与 C06 结合 |

---

## 常见坑与解决

| 坑 | 解决 |
| :--- | :--- || 同步阻塞运行时 | 用 `tokio::net` 或 `spawn_blocking` |
| 连接泄漏 | 设置超时、连接池、`Drop` 确保关闭 |
| 半关闭处理 | 正确 `shutdown`；区分读/写关闭 |
| 跨平台差异 | 用 `tokio` 抽象；注意 Windows 差异 |

---

## 网络速选

| 场景 | 选型 |
| :--- | :--- || HTTP 客户端 | `reqwest` |
| HTTP 服务端 | `axum` 或 `actix-web` |
| 原始 TCP/UDP | `tokio::net::TcpListener` |
| WebSocket | `tokio-tungstenite` |
| gRPC | `tonic` |

---

## 学习路径

1. **入门** (1–2 周): TCP 基础 → HTTP 客户端 → 简单服务端
2. **进阶** (2–3 周): 异步网络 → WebSocket → 生产实践
3. **高级** (持续): 性能调优、gRPC、与 C06 深入结合

---

## 速查与练习

- **速查卡**: [network_programming_cheatsheet](../../../docs/02_reference/quick_reference/network_programming_cheatsheet.md)
- **RBE 练习**: [TCP](https://doc.rust-lang.org/rust-by-example/std_misc/net.html)
- **Rustlings**: 无网络专题；参考 C10 模块与 Tokio 教程
