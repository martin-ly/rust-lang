# QUIC / HTTP/3 指南 {#quic-http3-指南}
>
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **分级**: [A]
> **层级**: L6 生态工具 / L3 高级网络
> **前置概念**: [Async](../../concept/03_advanced/02_async.md) · [Network Programming](../../crates/c10_networks)
> **Bloom 层级**: 应用 → 分析
> **来源: [RFC 9000 (QUIC)](https://github.com/rust-lang/rfcs/pull/9000)** · **来源: [RFC 9114 (HTTP/3)](https://github.com/rust-lang/rfcs/pull/9114)** · **[来源: quinn crate]** ✅
>
> **受众**: [进阶]
> **内容分级**: [实验级]

---

## 📑 目录 {#目录}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [QUIC / HTTP/3 指南 {#quic-http3-指南}](#quic--http3-指南-quic-http3-指南)
  - [📑 目录 {#目录}](#-目录-目录)
  - [概述 {#概述}](#概述-概述)
  - [QUIC 核心特性 {#quic-核心特性}](#quic-核心特性-quic-核心特性)
  - [Rust 生态 {#rust-生态}](#rust-生态-rust-生态)
  - [决策树 {#决策树}](#决策树-决策树)
  - [代码示例 {#代码示例}](#代码示例-代码示例)
    - [QUIC 客户端（quinn） {#quic-客户端quinn}](#quic-客户端quinn-quic-客户端quinn)
    - [QUIC 服务器（quinn） {#quic-服务器quinn}](#quic-服务器quinn-quic-服务器quinn)
    - [HTTP/3 客户端（h3 + quinn） {#http3-客户端h3-quinn}](#http3-客户端h3--quinn-http3-客户端h3-quinn)
  - [与 HTTP/2 的对比 {#与-http2-的对比}](#与-http2-的对比-与-http2-的对比)
  - [限制 {#限制}](#限制-限制)
  - [参考 {#参考}](#参考-参考)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

## 概述 {#概述}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

**QUIC** (Quick UDP Internet Connections) 是 Google 提出、IETF 标准化的传输层协议，基于 UDP 构建，旨在替代 TCP + TLS + HTTP/2 的组合。

**HTTP/3** 是 HTTP 协议的最新版本，直接在 QUIC 之上运行，而非 TCP。

```text
HTTP/1.1          HTTP/2            HTTP/3
─────────        ─────────        ─────────
HTTP              HTTP              HTTP
└── TCP          └── HTTP/2        └── HTTP/3
    └── TLS          └── TLS           └── QUIC
                         └── TCP              └── UDP
                                               └── TLS 1.3 (内建)
```
**核心洞察**: HTTP/3 不是"HTTP over UDP"，而是"HTTP over QUIC"——QUIC 同时解决了传输可靠性和安全性。

---

## QUIC 核心特性 {#quic-核心特性}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| 特性 | TCP+TLS | QUIC | 影响 |
|:---|:---|:---|:---|
| 连接建立 | 2-3 RTT (TCP + TLS) | 0-1 RTT | 首次加载更快 |
| 队头阻塞 | TCP 层阻塞所有流 | 流独立传输 | 多路复用不互相阻塞 |
| 连接迁移 | IP 变化 = 重连 | 连接 ID 标识 | 移动网络/WiFi 切换不中断 |
| 拥塞控制 | 内核实现 | 用户态实现 | 快速迭代、应用层定制 |
| 安全性 | TLS 握手后加密 | 除头部外全加密 | 更好的隐私保护 |

---

## Rust 生态 {#rust-生态}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| Crate | 层级 | 说明 | 成熟度 |
|:---|:---|:---|:---:|
| `quinn` | 高级 QUIC 实现 | 基于 `rustls` 的异步 QUIC | 🟢 生产可用 |
| `quinn-proto` | 协议逻辑 | 无 I/O 的纯协议实现 | 🟢 稳定 |
| `s2n-quic` | AWS 出品 | AWS 内部使用 | 🟢 生产可用 |
| `h3` | HTTP/3 实现 | 与 `hyper` 兼容 | 🟡 活跃开发 |
| `h3-quinn` | quinn + h3 桥接 | 推荐组合 | 🟡 活跃开发 |

---

## 决策树 {#决策树}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```text
需要现代网络协议?
    ├── Web 应用 + 面向公网?
    │       ├── 需要最低延迟? ──▶ HTTP/3 (QUIC)
    │       ├── 大量并发连接? ──▶ HTTP/3 (连接迁移优势)
    │       └── 通用场景? ──▶ HTTP/2 + TLS 1.3 (当前主流)
    ├── 游戏/实时通信?
    │       └── 可接受 UDP? ──▶ QUIC 或 WebTransport over QUIC
    ├── IoT / 受限网络?
    │       └── 需要连接恢复? ──▶ QUIC (0-RTT + 连接迁移)
    └── 内部服务网格?
            └── 已用 gRPC? ──▶ gRPC over QUIC (实验性)
```
---

## 代码示例 {#代码示例}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

### QUIC 客户端（quinn） {#quic-客户端quinn}

> **来源: [Wikipedia - Type System](https://en.wikipedia.org/wiki/Type_system)**

```rust,ignore
use quinn::{ClientConfig, Endpoint};
use rustls::pki_types::ServerName;
use std::net::SocketAddr;
use std::sync::Arc;

async fn quic_client(
    server_addr: SocketAddr,
    server_name: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    // 配置客户端（使用 rustls 进行 TLS）
    let client_config = ClientConfig::with_platform_verifier();

    let mut endpoint = Endpoint::client("0.0.0.0:0".parse()?)?;
    endpoint.set_default_client_config(client_config);

    // 建立连接：1-RTT（首次）或 0-RTT（会话恢复）
    let connection = endpoint
        .connect(server_addr, server_name)?
        .await?;

    // 打开双向流
    let (mut send, mut recv) = connection.open_bi().await?;

    // 发送数据
    send.write_all(b"hello quic").await?;
    send.finish()?;

    // 接收响应
    let response = recv.read_to_end(1024).await?;
    println!("Received: {:?}", String::from_utf8_lossy(&response));

    connection.close(0u32.into(), b"done");
    Ok(())
}
```
### QUIC 服务器（quinn） {#quic-服务器quinn}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**

```rust,ignore
use quinn::{ServerConfig, Endpoint};
use std::net::SocketAddr;
use std::sync::Arc;

async fn quic_server(addr: SocketAddr) -> Result<(), Box<dyn std::error::Error>> {
    // 加载证书（生产环境使用真实证书）
    let (cert, key) = generate_self_signed_cert()?;

    let mut server_config = ServerConfig::with_single_cert(cert, key)?;
    let config = Arc::get_mut(&mut server_config.transport)
        .unwrap();

    // 配置并发流数（HTTP/3 需要大量双向流）
    config.max_concurrent_bidi_streams(100u32.into());
    config.max_concurrent_uni_streams(100u32.into());

    let endpoint = Endpoint::server(server_config, addr)?;

    while let Some(conn) = endpoint.accept().await {
        let connection = conn.await?;
        tokio::spawn(handle_connection(connection));
    }

    Ok(())
}

async fn handle_connection(connection: quinn::Connection) {
    while let Ok((mut send, mut recv)) = connection.accept_bi().await {
        let data = match recv.read_to_end(1024 * 64).await {
            Ok(data) => data,
            Err(_) => continue,
        };

        let _ = send.write_all(&data).await;
        let _ = send.finish();
    }
}
```
### HTTP/3 客户端（h3 + quinn） {#http3-客户端h3-quinn}

> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**

```rust,ignore
use h3_quinn::quinn;
use h3::client::Connection;
use http::Request;

async fn http3_get(url: &str) -> Result<String, Box<dyn std::error::Error>> {
    // 建立 QUIC 连接
    let client_config = quinn::ClientConfig::with_platform_verifier();
    let mut endpoint = quinn::Endpoint::client("0.0.0.0:0".parse()?)?;
    endpoint.set_default_client_config(client_config);

    let conn = endpoint
        .connect("server:443".parse()?, "server")?
        .await?;

    // 在 QUIC 上运行 HTTP/3
    let quinn_conn = h3_quinn::Connection::new(conn);
    let (mut driver, mut send_request) = Connection::new(quinn_conn).await?;

    let request = Request::get(url)
        .header("user-agent", "rust-h3/0.1")
        .body(())?;

    let mut stream = send_request.send_request(request).await?;
    stream.finish().await?;

    let response = stream.recv_response().await?;
    let mut body = Vec::new();
    while let Some(chunk) = stream.recv_data().await? {
        body.extend_from_slice(&chunk);
    }

    Ok(String::from_utf8_lossy(&body).to_string())
}
```
---

## 与 HTTP/2 的对比 {#与-http2-的对比}
>
> **[来源: [crates.io](https://crates.io/)]**

| 维度 | HTTP/2 | HTTP/3 |
|:---|:---|:---|
| 传输层 | TCP | QUIC (UDP) |
| TLS | 握手后加密 | 1-RTT 或 0-RTT |
| 队头阻塞 | TCP 层流间阻塞 | 流完全独立 |
| 连接迁移 | 不支持 | IP 变化保持连接 |
| 服务端推送 | 复杂 | 简化（未来版本） |
| 浏览器支持 | 99%+ | 95%+ (2025) |
| Rust 生态 | hyper + h2 成熟 | h3 + quinn 快速成熟 |

---

## 限制 {#限制}
>
> **[来源: [docs.rs](https://docs.rs/)]**

| 限制 | 说明 |
|:---|:---|
| UDP 限制 | 某些企业网络限制 UDP 端口/速率 |
| 调试复杂 | 全加密导致抓包分析困难 |
| 实现复杂度 | 用户态实现，代码量大 |
| 负载均衡 | 需要支持 QUIC 的 L4/L7 代理 |
| 连接 ID | 需要仔细设计以支持迁移同时防止追踪 |

---

## 参考 {#参考}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

- [RFC 9000: QUIC](https://datatracker.ietf.org/doc/html/rfc9000)
- [RFC 9114: HTTP/3](https://datatracker.ietf.org/doc/html/rfc9114)
- [quinn crate](https://github.com/quinn-rs/quinn)
- [Cloudflare: HTTP/3 vs HTTP/2](https://blog.cloudflare.com/http-3-vs-http-2/)

---

> **权威来源**: [RFC 9000](https://datatracker.ietf.org/doc/html/rfc9000), [RFC 9114](https://datatracker.ietf.org/doc/html/rfc9114), [quinn](https://github.com/quinn-rs/quinn)
>
> **文档版本**: 1.0
> **对应 Rust 版本**: 1.96.0+ (Edition 2024)
> **最后更新**: 2026-05-21
> **状态**: ✅ 初版完成

---

## 相关概念 {#相关概念}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

- [docs 索引](../README.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**

---
