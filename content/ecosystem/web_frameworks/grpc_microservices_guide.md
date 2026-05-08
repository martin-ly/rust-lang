# gRPC 微服务实战指南

> **定位**: Rust 构建高性能 gRPC 微服务
> **版本**: tonic 0.14.x, prost 0.14.x
> **适用场景**: 服务间通信、微服务架构、高性能 API

---

## 📋 目录

- [gRPC 微服务实战指南](#grpc-微服务实战指南)
  - [📋 目录](#-目录)
  - [🎯 为什么选择 gRPC](#-为什么选择-grpc)
  - [⚡ 快速开始](#-快速开始)
    - [1. 定义 Protocol Buffers](#1-定义-protocol-buffers)
    - [2. 生成 Rust 代码](#2-生成-rust-代码)
    - [3. 实现服务端](#3-实现服务端)
    - [4. 实现客户端](#4-实现客户端)
  - [🔐 TLS 安全传输](#-tls-安全传输)
  - [🔄 流式通信](#-流式通信)
  - [📊 与 REST 对比](#-与-rest-对比)
  - [🔗 参考资源](#-参考资源)

---

## 🎯 为什么选择 gRPC

```
┌─────────────────────────────────────────────┐
│              gRPC 核心优势                   │
├─────────────────────────────────────────────┤
│ ✅ HTTP/2 多路复用 → 单连接多请求            │
│ ✅ Protocol Buffers → 紧凑二进制序列化        │
│ ✅ 强类型契约 → 编译期 API 验证              │
│ ✅ 双向流式 → 实时数据推送                   │
│ ✅ 代码生成 → 减少样板代码                   │
└─────────────────────────────────────────────┘
```

**适用场景**:

- 微服务间内部通信
- 高性能实时数据流
- 多语言服务生态
- 移动/前端后端通信

**不适用场景**:

- 浏览器直接调用（需 gRPC-Web 代理）
- 简单的 CRUD 对外 API（REST 更友好）
- 调试频繁的开发环境

---

## ⚡ 快速开始

### 1. 定义 Protocol Buffers

```protobuf
// proto/echo.proto
syntax = "proto3";
package echo;

service EchoService {
    rpc Echo (EchoRequest) returns (EchoResponse);
    rpc StreamEcho (stream EchoRequest) returns (stream EchoResponse);
}

message EchoRequest {
    string message = 1;
    int32 repeat = 2;
}

message EchoResponse {
    string message = 1;
    int64 timestamp = 2;
}
```

### 2. 生成 Rust 代码

```toml
# Cargo.toml
[dependencies]
tonic = { version = "0.14", features = ["transport", "tls-ring"] }
prost = "0.14"
tokio = { version = "1", features = ["full"] }

[build-dependencies]
tonic-build = "0.14"
```

```rust
// build.rs
fn main() {
    tonic_build::compile_protos("proto/echo.proto")
        .unwrap_or_else(|e| panic!("Failed to compile protos: {}", e));
}
```

### 3. 实现服务端

```rust
use tonic::{transport::Server, Request, Response, Status};
use echo::{EchoRequest, EchoResponse};
use echo::echo_service_server::{EchoService, EchoServiceServer};

pub mod echo {
    tonic::include_proto!("echo");
}

#[derive(Default)]
pub struct EchoServiceImpl;

#[tonic::async_trait]
impl EchoService for EchoServiceImpl {
    async fn echo(
        &self,
        request: Request<EchoRequest>,
    ) -> Result<Response<EchoResponse>, Status> {
        let req = request.into_inner();

        let reply = EchoResponse {
            message: req.message,
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs() as i64,
        };

        Ok(Response::new(reply))
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let addr = "[::1]:50051".parse()?;

    println!("gRPC server listening on {}", addr);

    Server::builder()
        .add_service(EchoServiceServer::new(EchoServiceImpl::default()))
        .serve(addr)
        .await?;

    Ok(())
}
```

### 4. 实现客户端

```rust
use tonic::transport::Channel;
use echo::{EchoRequest, EchoResponse};
use echo::echo_service_client::EchoServiceClient;

pub mod echo {
    tonic::include_proto!("echo");
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut client = EchoServiceClient::connect("http://[::1]:50051").await?;

    let request = tonic::Request::new(EchoRequest {
        message: "Hello gRPC".into(),
        repeat: 1,
    });

    let response = client.echo(request).await?;

    println!("RESPONSE={:?}", response.into_inner());

    Ok(())
}
```

---

## 🔐 TLS 安全传输

```rust
use tonic::transport::{Server, Identity, ServerTlsConfig};

// 加载证书和私钥
let cert = std::fs::read_to_string("server.crt")?;
let key = std::fs::read_to_string("server.key")?;
let identity = Identity::from_pem(cert, key);

Server::builder()
    .tls_config(ServerTlsConfig::new().identity(identity))?
    .add_service(EchoServiceServer::new(EchoServiceImpl::default()))
    .serve(addr)
    .await?;
```

---

## 🔄 流式通信

```rust
use tonic::{Request, Response, Status};
use tokio_stream::wrappers::ReceiverStream;
use tokio::sync::mpsc;

#[tonic::async_trait]
impl EchoService for EchoServiceImpl {
    type StreamEchoStream = ReceiverStream<Result<EchoResponse, Status>>;

    async fn stream_echo(
        &self,
        request: Request<tonic::Streaming<EchoRequest>>,
    ) -> Result<Response<Self::StreamEchoStream>, Status> {
        let mut stream = request.into_inner();
        let (tx, rx) = mpsc::channel(4);

        tokio::spawn(async move {
            while let Some(req) = stream.message().await.unwrap_or(None) {
                let reply = EchoResponse {
                    message: req.message,
                    timestamp: chrono::Utc::now().timestamp(),
                };
                if tx.send(Ok(reply)).await.is_err() {
                    break;
                }
            }
        });

        Ok(Response::new(ReceiverStream::new(rx)))
    }
}
```

---

## 📊 与 REST 对比

| 维度 | gRPC | REST (HTTP/JSON) |
|------|------|------------------|
| 传输协议 | HTTP/2 | HTTP/1.1 或 HTTP/2 |
| 序列化 | Protobuf (二进制) | JSON (文本) |
| 性能 | ⭐⭐⭐ | ⭐⭐ |
| 可读性 | 需工具 | 直接可读 |
| 浏览器支持 | 需 gRPC-Web | 原生支持 |
| 强类型 | ✅ 编译期 | ⚠️ 运行时 |
| 流式 | 原生支持 | SSE / WebSocket |
| 调试 | 需 grpcurl / BloomRPC | curl 直接调用 |

---

## 🔗 参考资源

- [Tonic 文档](https://docs.rs/tonic)
- [Protobuf 指南](https://protobuf.dev/)
- [gRPC 官方文档](https://grpc.io/docs/)
- [项目 C10 网络模块](../../crates/c10_networks/)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-05-08
**状态**: ✅ 已完善
