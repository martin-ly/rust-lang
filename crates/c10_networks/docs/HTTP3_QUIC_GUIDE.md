# HTTP/3 与 QUIC 基础指南

## QUIC 协议概述

QUIC（Quick UDP Internet Connections）是基于 UDP 的通用传输协议，由 Google 提出，现为 IETF 标准（RFC 9000）。它将 TCP 的可靠传输、TLS 1.3 的安全性和 HTTP/2 的多流复用整合到用户态实现中。

## HTTP/3 vs HTTP/2 差异

| 特性 | HTTP/2 | HTTP/3 |
|------|--------|--------|
| **传输层** | TCP + TLS | QUIC (基于 UDP) |
| **连接建立** | TCP 握手 + TLS 握手 (2-3 RTT) | QUIC 握手 (0-1 RTT，支持 0-RTT 恢复) |
| **队头阻塞** | TCP 层队头阻塞影响所有流 | QUIC 流独立，单流丢包不影响其他流 |
| **连接迁移** | 依赖四元组（源 IP、端口、目的 IP、端口），变化需重连 | 使用连接 ID 标识，支持 IP/端口变化无感迁移 |
| **拥塞控制** | 内核 TCP 实现 | 用户态 QUIC 实现，可灵活定制 |
| **安全性** | TLS 1.2/1.3 在 TCP 之上 | TLS 1.3 集成在 QUIC 内部（1-RTT 或 0-RTT） |
| **中间设备干扰** | TCP 被中间设备广泛修改 | UDP+QUIC 更难被中间设备干扰 |

## 核心优势详解

### 1. 消除队头阻塞

HTTP/2 虽然通过多路复用解决了应用层队头阻塞，但所有流共享一个 TCP 连接。一旦某个 TCP 包丢失，整个连接的后续数据都会被阻塞（TCP 重传）。

QUIC 在 UDP 之上为每个流提供独立的可靠传输，一个流的丢包不会影响其他流的数据交付。

### 2. 更快的连接建立

- **HTTP/2**: TCP (1 RTT) + TLS 1.2 (2 RTT) = 3 RTT；TLS 1.3 (1 RTT) = 2 RTT
- **HTTP/3**: QUIC 集成 TLS 1.3，首次连接 1 RTT，恢复连接 0 RTT

### 3. 连接迁移

移动设备在 WiFi 和蜂窝网络之间切换时，IP 地址会变化。

- HTTP/2: TCP 连接断开，需要重新建立（DNS、TCP、TLS 全部重来）
- HTTP/3: QUIC 使用连接 ID，IP 变化后只需发送包含相同连接 ID 的包即可继续

## Rust 生态

### 主要 crate

- `quinn`: 纯 Rust QUIC 实现，异步，基于 tokio
- `h3`: HTTP/3 实现，可与 quinn 配合使用
- `s2n-quic`: AWS 的 QUIC 实现

### 最小 QUIC 示例（quinn）

```rust
use quinn::{Endpoint, ServerConfig};
use std::net::SocketAddr;

fn create_server(bind_addr: SocketAddr) -> anyhow::Result<Endpoint> {
    let (cert, key) = generate_self_signed_cert()?;
    let mut server_config = ServerConfig::with_single_cert(vec![cert], key)?;
    let endpoint = Endpoint::server(server_config, bind_addr)?;
    Ok(endpoint)
}
```

### 条件编译

由于 QUIC 依赖可选，代码使用 feature gate：

```rust
#[cfg(feature = "quic")]
pub mod quic_impl {
    // 真实 quinn 代码
}

#[cfg(not(feature = "quic"))]
pub mod quic_stub {
    // 占位实现与概念说明
}
```

## 编译与运行

```bash
# 启用 QUIC feature
cargo check -p c10_networks --features quic

# 注意：QUIC 示例需要有效的 TLS 证书配置才能运行服务端
```

## 参考

- [RFC 9000 - QUIC](https://datatracker.ietf.org/doc/html/rfc9000)
- [RFC 9114 - HTTP/3](https://datatracker.ietf.org/doc/html/rfc9114)
- [quinn 文档](https://docs.rs/quinn/)
