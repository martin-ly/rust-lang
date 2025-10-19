# C10 网络编程: 术语表 (Glossary)

> **文档定位**: 网络编程核心术语快速参考，涵盖协议、并发、安全等关键概念  
> **使用方式**: 通过术语索引快速查找定义，理解网络编程核心概念  
> **相关文档**: [主索引](./00_MASTER_INDEX.md) | [README](./README.md) | [FAQ](./FAQ.md)

**最后更新**: 2025-10-19  
**适用版本**: Rust 1.90+, Tokio 1.35+  
**文档类型**: 📚 参考资料

---

## 📋 术语索引

[A](#async-异步) | [D](#dns) | [H](#http) | [T](#tcp) | [U](#udp) | [W](#websocket)

---

## 协议基础

### TCP

**定义**: Transmission Control Protocol，传输控制协议，提供可靠的、面向连接的字节流服务。

**特点**:

- 三次握手建立连接
- 四次挥手关闭连接
- 流量控制和拥塞控制
- 数据有序、可靠传输

**Rust 示例**:

```rust
use tokio::net::TcpListener;

let listener = TcpListener::bind("127.0.0.1:8080").await?;
let (socket, _) = listener.accept().await?;
```

**相关**: [SOCKET_GUIDE.md](./SOCKET_GUIDE.md)

---

### UDP

**定义**: User Datagram Protocol，用户数据报协议，提供无连接的数据报服务。

**特点**:

- 无连接，无握手
- 不保证可靠性
- 不保证顺序
- 低延迟

**Rust 示例**:

```rust
use tokio::net::UdpSocket;

let socket = UdpSocket::bind("0.0.0.0:8080").await?;
socket.send_to(b"hello", "127.0.0.1:9090").await?;
```

**相关**: [SOCKET_GUIDE.md](./SOCKET_GUIDE.md)

---

### HTTP

**定义**: Hypertext Transfer Protocol，超文本传输协议，应用层协议。

**版本**:

- HTTP/1.1: 持久连接、管道化
- HTTP/2: 多路复用、服务器推送
- HTTP/3: 基于QUIC，UDP传输

**Rust 实现**:

```rust
use reqwest::Client;

let resp = Client::new()
    .get("https://api.example.com")
    .send()
    .await?;
```

**相关**: [HTTP_CLIENT_GUIDE.md](./HTTP_CLIENT_GUIDE.md)

---

### WebSocket

**定义**: 全双工通信协议，在单个TCP连接上提供双向通信。

**特点**:

- 基于TCP
- 握手基于HTTP
- 全双工通信
- 实时性好

**Rust 实现**:

```rust
use tokio_tungstenite::connect_async;

let (ws_stream, _) = connect_async("ws://localhost:8080").await?;
```

**相关**: [WEBSOCKET_GUIDE.md](./WEBSOCKET_GUIDE.md)

---

### DNS

**定义**: Domain Name System，域名系统，将域名解析为IP地址。

**记录类型**:

- A: IPv4地址
- AAAA: IPv6地址
- CNAME: 别名
- MX: 邮件交换
- TXT: 文本记录

**Rust 实现**:

```rust
use hickory_resolver::TokioAsyncResolver;

let resolver = TokioAsyncResolver::tokio_from_system_conf()?;
let response = resolver.lookup_ip("example.com").await?;
```

**相关**: [DNS_RESOLVER_GUIDE.md](./DNS_RESOLVER_GUIDE.md)

---

## 异步编程

### Async (异步)

**定义**: 异步编程模型，允许任务在等待IO时让出执行权。

**Rust 中**: 基于 Future trait

```rust
pub trait Future {
    type Output;
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output>;
}
```

**async/await**:

```rust
async fn fetch_data() -> Result<String> {
    let data = network_call().await?;
    Ok(data)
}
```

**相关**: [TUTORIALS.md](./TUTORIALS.md)

---

### Tokio

**定义**: Rust 的异步运行时，提供任务调度、IO、定时器等功能。

**核心组件**:

- Runtime: 运行时调度器
- Task: 异步任务
- Channel: 任务间通信
- Timer: 定时器

**使用**:

```rust
#[tokio::main]
async fn main() {
    // 异步代码
}
```

**相关**: [QUICK_START.md](./QUICK_START.md)

---

### Reactor

**定义**: 事件驱动的IO模型，通过事件循环和回调处理IO事件。

**工作原理**:

1. 注册IO事件
2. 等待事件发生（epoll/kqueue）
3. 执行回调处理

**Tokio 中**: 底层使用 mio 实现 Reactor

**相关**: [NETWORK_THEORY_FOUNDATION.md](./NETWORK_THEORY_FOUNDATION.md)

---

## 性能相关

### 连接池 (Connection Pool)

**定义**: 预先创建并维护一组可复用的连接，避免频繁建立和关闭连接的开销。

**reqwest 配置**:

```rust
Client::builder()
    .pool_max_idle_per_host(10)
    .pool_idle_timeout(Duration::from_secs(90))
    .build()?
```

**优点**:

- 减少连接建立开销
- 提高响应速度
- 降低服务器负载

**相关**: [PERFORMANCE_OPTIMIZATION_GUIDE.md](./PERFORMANCE_OPTIMIZATION_GUIDE.md)

---

### 零拷贝 (Zero-Copy)

**定义**: 数据传输过程中避免在内核空间和用户空间之间复制数据。

**技术**:

- `sendfile()` 系统调用
- `mmap()` 内存映射
- `splice()` 管道拼接

**Rust 中**:

```rust
use tokio::io::copy;
use tokio::fs::File;

let mut file = File::open("data.bin").await?;
copy(&mut file, &mut socket).await?; // 零拷贝
```

**性能提升**: 可达 2-3倍

**相关**: [PERFORMANCE_OPTIMIZATION_GUIDE.md](./PERFORMANCE_OPTIMIZATION_GUIDE.md)

---

### 背压 (Backpressure)

**定义**: 当消费者处理速度慢于生产者时，控制生产速度以避免资源耗尽。

**实现策略**:

- 有界通道（bounded channel）
- 流量控制（flow control）
- 拒绝服务（reject）

**Tokio 示例**:

```rust
use tokio::sync::mpsc;

let (tx, mut rx) = mpsc::channel(100); // 有界通道

// 当通道满时，send 会等待
tx.send(data).await?;
```

**相关**: [BEST_PRACTICES.md](./BEST_PRACTICES.md)

---

## 安全相关

### TLS/SSL

**定义**: Transport Layer Security / Secure Sockets Layer，传输层安全协议。

**版本**:

- TLS 1.2: 当前标准
- TLS 1.3: 最新版本，更安全更快

**Rust 实现**:

```rust
use reqwest::Client;

let client = Client::builder()
    .min_tls_version(reqwest::tls::Version::TLS_1_2)
    .build()?;
```

**相关**: [SECURITY_GUIDE.md](./SECURITY_GUIDE.md)

---

### DoH/DoT

**定义**: DNS over HTTPS / DNS over TLS，加密的DNS查询协议。

**DoH**: DNS查询通过HTTPS传输  
**DoT**: DNS查询通过TLS传输

**Rust 实现**:

```rust
use hickory_resolver::{TokioAsyncResolver, config::*};

let resolver = TokioAsyncResolver::tokio(
    ResolverConfig::cloudflare_https(), // DoH
    ResolverOpts::default()
)?;
```

**相关**: [dns_hickory_integration.md](./dns_hickory_integration.md)

---

### ALPN

**定义**: Application-Layer Protocol Negotiation，应用层协议协商。

**用途**: TLS握手时协商使用的应用层协议（HTTP/1.1、HTTP/2等）

**示例**:

```text
Client Hello: [h2, http/1.1]
Server Hello: h2 (选择HTTP/2)
```

**相关**: [SECURITY_GUIDE.md](./SECURITY_GUIDE.md)

---

## 协议细节

### 三次握手 (Three-Way Handshake)

**定义**: TCP建立连接的过程。

**步骤**:

1. Client → Server: SYN
2. Server → Client: SYN-ACK
3. Client → Server: ACK

**时序**:

```text
Client                Server
  |       SYN          |
  |------------------>|
  |     SYN-ACK        |
  |<------------------|
  |       ACK          |
  |------------------>|
  |   (连接建立)        |
```

**相关**: [NETWORK_THEORY_FOUNDATION.md](./NETWORK_THEORY_FOUNDATION.md)

---

### 四次挥手 (Four-Way Handshake)

**定义**: TCP关闭连接的过程。

**步骤**:

1. Client → Server: FIN
2. Server → Client: ACK
3. Server → Client: FIN
4. Client → Server: ACK

**时序**:

```text
Client                Server
  |       FIN          |
  |------------------>|
  |       ACK          |
  |<------------------|
  |                    |
  |       FIN          |
  |<------------------|
  |       ACK          |
  |------------------>|
  |   (连接关闭)        |
```

**相关**: [NETWORK_THEORY_FOUNDATION.md](./NETWORK_THEORY_FOUNDATION.md)

---

### Keep-Alive

**定义**: 保持TCP连接不关闭，以便复用连接。

**HTTP/1.1**: 默认启用  
**配置**: `Connection: keep-alive` 头

**好处**:

- 减少握手开销
- 降低延迟
- 提高吞吐量

**Rust 配置**:

```rust
Client::builder()
    .tcp_keepalive(Duration::from_secs(60))
    .build()?
```

**相关**: [HTTP_CLIENT_GUIDE.md](./HTTP_CLIENT_GUIDE.md)

---

### 多路复用 (Multiplexing)

**定义**: 在单个连接上同时传输多个数据流。

**HTTP/2 中**:

- Stream: 逻辑数据流
- Frame: 数据帧
- 并发多个请求

**优点**:

- 减少连接数
- 避免队头阻塞
- 提高带宽利用率

**相关**: [PROTOCOL_IMPLEMENTATION_GUIDE.md](./PROTOCOL_IMPLEMENTATION_GUIDE.md)

---

## 工具与库

### reqwest

**定义**: Rust 的 HTTP 客户端库。

**特点**:

- 基于 Tokio
- 支持 HTTP/1.1 和 HTTP/2
- 连接池管理
- Cookie 管理

**基本使用**:

```rust
let resp = reqwest::get("https://httpbin.org/ip")
    .await?
    .text()
    .await?;
```

**相关**: [HTTP_CLIENT_GUIDE.md](./HTTP_CLIENT_GUIDE.md)

---

### hickory-dns

**定义**: Rust 的 DNS 库，前身为 trust-dns。

**功能**:

- 异步DNS解析
- DoH/DoT 支持
- 自定义解析器
- DNS服务器实现

**使用**:

```rust
use hickory_resolver::TokioAsyncResolver;

let resolver = TokioAsyncResolver::tokio_from_system_conf()?;
```

**相关**: [DNS_RESOLVER_GUIDE.md](./DNS_RESOLVER_GUIDE.md)

---

### tokio-tungstenite

**定义**: Tokio 的 WebSocket 实现。

**功能**:

- 客户端和服务器
- 自动 Ping/Pong
- 消息分帧

**使用**:

```rust
use tokio_tungstenite::connect_async;

let (ws, _) = connect_async("ws://localhost:8080").await?;
```

**相关**: [WEBSOCKET_GUIDE.md](./WEBSOCKET_GUIDE.md)

---

### libp2p

**定义**: 模块化的 P2P 网络库。

**功能**:

- 传输层抽象
- NAT 穿透
- 多路复用
- 加密通信

**相关**: 示例 `p2p_minimal.rs`

---

### libpnet

**定义**: 底层网络数据包操作库。

**功能**:

- 数据包构造
- 数据包解析
- 原始套接字
- 流量捕获

**相关**: [libpnet_guide.md](./libpnet_guide.md)

---

## 📚 延伸阅读

- [主索引](./00_MASTER_INDEX.md) - 完整文档导航
- [FAQ](./FAQ.md) - 常见问题解答
- [README](./README.md) - 项目概述
- [网络理论基础](./NETWORK_THEORY_FOUNDATION.md) - 理论知识
- [协议实现指南](./PROTOCOL_IMPLEMENTATION_GUIDE.md) - 实现细节

---

**需要更多帮助？**

- 查看 [示例代码](../examples/)
- 运行 [测试用例](../tests/)
- 阅读 [API文档](./API_DOCUMENTATION.md)
