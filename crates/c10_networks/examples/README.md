# C10 网络编程示例

本目录包含 Rust 网络编程的核心示例代码。

---

## 📚 示例列表

### 基础示例 ⭐

| 示例 | 描述 | 核心概念 |
|------|------|----------|
| `tcp_server.rs` | TCP 服务器 | TcpListener |
| `tcp_client.rs` | TCP 客户端 | TcpStream |
| `udp_socket.rs` | UDP 通信 | UdpSocket |
| `http_request.rs` | HTTP 请求 | reqwest |

### 进阶示例 ⭐⭐

| 示例 | 描述 | 核心概念 |
|------|------|----------|
| `async_server.rs` | 异步服务器 | tokio::net |
| `websocket.rs` | WebSocket | tungstenite |
| `grpc_demo.rs` | gRPC | tonic |
| `tls_config.rs` | TLS 配置 | rustls |

### 高级示例 ⭐⭐⭐

| 示例 | 描述 | 核心概念 |
|------|------|----------|
| `custom_protocol.rs` | 自定义协议 | 协议设计 |
| `load_balancer.rs` | 负载均衡 | 代理模式 |
| `proxy_server.rs` | 代理服务器 | 反向代理 |

---

## 🚀 快速开始

```bash
# 运行 TCP 服务器
cargo run --example tcp_server

# 运行 HTTP 请求示例
cargo run --example http_request

# 运行异步服务器示例
cargo run --example async_server
```

---

## 🔗 相关文档

- [网络编程指南](../docs/)

---

*示例基于 Rust 1.94+，Edition 2024*
