# C10 Networks - Rust 1.89 网络编程库

[![Rust](https://img.shields.io/badge/rust-1.89+-orange.svg)](https://www.rust-lang.org/)
[![License](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)
[![Crates.io](https://img.shields.io/crates/v/c10_networks.svg)](https://crates.io/crates/c10_networks)

## 概述

C10 Networks 是一个基于 Rust 1.89 的现代网络编程库，提供了完整的网络编程解决方案，包括异步网络通信、多种协议支持、高性能网络工具和安全通信功能。

## 🚀 特性

- **基于 Rust 1.89**: 充分利用最新语言特性
- **异步/await 支持**: 高性能异步网络编程
- **多种协议支持**: HTTP/1.1, HTTP/2, WebSocket, TCP, UDP, DNS
- **P2P 能力**: 节点发现、DHT、GossipSub、NAT 穿透（基于 libp2p）
- **内置安全功能**: 加密通信、数字签名、证书验证
- **性能监控**: 网络性能统计和监控
- **完整测试覆盖**: 单元测试、集成测试、性能测试
- **零拷贝优化**: 高效的内存管理
- **错误恢复**: 智能错误处理和重试机制

## 📦 安装

在 `Cargo.toml` 中添加依赖：

```toml
[dependencies]
c10_networks = "0.1.0"
```

## 🎯 快速开始

### HTTP 客户端示例

```rust
use c10_networks::protocol::http::{HttpClient, HttpMethod, HttpVersion};
use c10_networks::error::NetworkResult;

#[tokio::main]
async fn main() -> NetworkResult<()> {
    let client = HttpClient::new();
    
    // 发送 GET 请求
    let response = client.get("https://httpbin.org/get").await?;
    
    println!("状态码: {}", response.status);
    println!("响应体: {}", String::from_utf8_lossy(&response.body));
    
    Ok(())
}
```

### 错误处理示例

```rust
use c10_networks::error::{NetworkError, NetworkResult};

async fn handle_network_operation() -> NetworkResult<()> {
    match some_network_operation().await {
        Ok(result) => Ok(result),
        Err(error) => {
            if error.is_retryable() {
                println!("错误可重试，延迟 {:?} 后重试", error.retry_delay().unwrap());
                // 实现重试逻辑
            }
            Err(error)
        }
    }
}
```

### 异步网络服务器示例

```rust
use c10_networks::protocol::http::{HttpRequest, HttpResponse, HttpStatusCode, HttpVersion};
use tokio::net::TcpListener;

#[tokio::main]
async fn main() -> NetworkResult<()> {
    let listener = TcpListener::bind("127.0.0.1:8080").await?;
    
    loop {
        let (stream, _) = listener.accept().await?;
        tokio::spawn(async move {
            handle_connection(stream).await;
        });
    }
}

async fn handle_connection(mut stream: tokio::net::TcpStream) {
    // 读取 HTTP 请求
    let request = HttpRequest::read_from(&mut stream).await.unwrap();
    
    // 创建响应
    let mut response = HttpResponse::new(HttpVersion::Http1_1, HttpStatusCode::OK);
    response.set_body(b"Hello, World!");
    
    // 发送响应
    response.write_to(&mut stream).await.unwrap();
}
```

## 📚 模块结构

```text
c10_networks/
├── error/              # 错误处理模块
├── protocol/           # 网络协议实现
│   ├── http/          # HTTP 协议
│   ├── websocket/     # WebSocket 协议
│   ├── tcp/           # TCP 协议
│   ├── udp/           # UDP 协议
│   └── dns/           # DNS 协议
├── socket/            # 套接字封装
├── packet/            # 数据包处理
├── asynchronous_communication/  # 异步通信
├── network_topology/  # 网络拓扑
└── p2p/               # P2P（身份、发现、DHT、PubSub、NAT）
```

## 🔧 Rust 1.89 新特性应用

## 🌐 P2P 最小示例（基于 libp2p）

```rust
use libp2p::{gossipsub, identity, kad, ping, identify, Multiaddr, PeerId, Swarm};
use futures::prelude::*;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let key = identity::Keypair::generate_ed25519();
    let peer_id = PeerId::from(key.public());
    let transport = libp2p::tokio_development_transport(key.clone()).await?;

    let behaviour = libp2p::swarm::NetworkBehaviour::combine((
        gossipsub::Behaviour::new(
            gossipsub::MessageAuthenticity::Signed(key.clone()),
            gossipsub::Config::default(),
        )?,
        kad::Behaviour::new(kad::Config::default(), kad::store::MemoryStore::new(peer_id)),
        ping::Behaviour::default(),
        identify::Behaviour::new(identify::Config::new("c10/1.0".into(), key.public())),
    ));

    let mut swarm = Swarm::new(transport, behaviour, peer_id);
    Swarm::listen_on(&mut swarm, "/ip4/0.0.0.0/tcp/0".parse::<Multiaddr>()?)?;

    loop {
        match swarm.select_next_some().await {
            libp2p::swarm::SwarmEvent::NewListenAddr { address, .. } => println!("listening on {}", address),
            _ => {}
        }
    }
}
```

### 生命周期语法检查

```rust
// 明确标示生命周期参数
async fn handle_connection<'a>(stream: &'a TcpStream) -> NetworkResult<()> {
    // 处理连接
}
```

### 常量泛型推断

```rust
// 使用 _ 让编译器推断数组长度
fn process_packet<const N: usize>(data: [u8; N]) -> NetworkResult<()> {
    // 处理数据包
}

// 调用时使用 _
let result = process_packet([0u8; _]);
```

### Result::flatten 方法

```rust
// 简化嵌套 Result 处理
fn parse_http_request(data: &[u8]) -> NetworkResult<HttpRequest> {
    parse_headers(data)
        .and_then(|parsed| parse_body(parsed))
        .flatten()
}
```

## 🧪 测试

运行所有测试：

```bash
cargo test
```

运行性能测试：

```bash
cargo bench
```

运行示例程序：

```bash
cargo run --bin c10_networks

# WebSocket 回显（需开两窗）
cargo run --example ws_echo_server
cargo run --example ws_echo_client

# UDP 回显
cargo run --example udp_echo

# gRPC（需开两窗）
cargo run --example grpc_server
cargo run --example grpc_client

# P2P 最小示例
cargo run --example p2p_minimal
```

## 🧩 统一 API 示例

```rust
use c10_networks::unified_api::NetClient;

#[tokio::main]
async fn main() -> c10_networks::NetworkResult<()> {
    let api = NetClient::new();
    let ws = api.ws_echo("ws://127.0.0.1:9001", "hello").await?;
    println!("ws: {}", ws);

    let udp = api.udp_echo("127.0.0.1:9002", b"ping").await?;
    println!("udp: {}", String::from_utf8_lossy(&udp));

    let hello = api.grpc_hello("http://127.0.0.1:50051", "c10").await?;
    println!("grpc: {}", hello);

    let addrs = api.p2p_start_minimal().await?;
    println!("p2p addrs: {:?}", addrs);
    Ok(())
}
```

## 🛠️ 网络诊断快速使用

```rust
use c10_networks::diagnostics::NetDiagnostics;

#[tokio::main]
async fn main() {
    let d = NetDiagnostics::new();
    println!("dns ok: {}", d.check_dns("example.com"));
    let rep = d.check_tcp_connect("127.0.0.1:9001", 300);
    println!("tcp: {:?}", rep);
    let open = d.scan_tcp_ports("127.0.0.1", &[22,80,443,9001], 200).await;
    println!("open ports: {:?}", open);
}
```

## 🔁 带重试的统一 API

```rust
use c10_networks::unified_api::NetClient;

#[tokio::main]
async fn main() -> c10_networks::NetworkResult<()> {
    let api = NetClient::new();
    // WebSocket 带重试
    let ws = api.ws_echo_with_retry("ws://127.0.0.1:9001", "hello", 3, 100).await?;
    // UDP 带重试
    let udp = api.udp_echo_with_retry("127.0.0.1:9002", b"ping", 3, 100).await?;
    // gRPC 带重试
    let hello = api.grpc_hello_with_retry("http://127.0.0.1:50051", "c10", 3, 100).await?;
    println!("ws={}, udp_len={}, grpc={}", ws, udp.len(), hello);
    Ok(())
}
```

## 📊 性能特性

- **零拷贝网络编程**: 使用 `bytes::Bytes` 和 `IoSlice` 减少内存拷贝
- **连接池管理**: 高效的连接复用
- **异步 I/O**: 基于 `tokio` 的高性能异步运行时
- **内存优化**: 智能缓冲区管理
- **并发处理**: 支持高并发网络连接

## 🔒 安全特性

- **TLS/SSL 支持**: 基于 `rustls` 的安全通信
- **证书验证**: 完整的证书链验证
- **数字签名**: 消息完整性验证
- **加密通信**: 端到端加密支持
- **安全配置**: 最佳安全实践

## 📈 监控和诊断

- **性能统计**: 网络性能指标收集
- **错误统计**: 错误类型和频率统计
- **连接监控**: 连接状态和健康检查
- **流量分析**: 网络流量模式分析

## 🤝 贡献

欢迎贡献代码！请查看 [CONTRIBUTING.md](CONTRIBUTING.md) 了解贡献指南。

## 📄 许可证

本项目采用 MIT 许可证。详情请查看 [LICENSE](LICENSE) 文件。

## 🔗 相关链接

- [Rust 官方文档](https://doc.rust-lang.org/)
- [Tokio 异步运行时](https://tokio.rs/)
- [网络编程最佳实践](https://doc.rust-lang.org/book/)
- [Rust 1.89 发布说明](https://blog.rust-lang.org/)

## 📞 支持

如果您遇到问题或有建议，请：

1. 查看 [文档](https://docs.rs/c10_networks)
2. 搜索 [已知问题](https://github.com/your-org/c10_networks/issues)
3. 创建 [新问题](https://github.com/your-org/c10_networks/issues/new)
4. 参与 [讨论](https://github.com/your-org/c10_networks/discussions)

---

**C10 Networks** - 让 Rust 网络编程更简单、更安全、更高效！
