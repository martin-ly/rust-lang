# gRPC - 高性能RPC框架

## 📋 目录

- [gRPC - 高性能RPC框架](#grpc---高性能rpc框架)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [核心依赖](#核心依赖)
  - [Tonic](#tonic)
    - [定义 Proto 文件](#定义-proto-文件)
    - [生成 Rust 代码](#生成-rust-代码)
    - [服务端实现](#服务端实现)
    - [客户端实现](#客户端实现)
  - [Protocol Buffers](#protocol-buffers)
    - [数据类型](#数据类型)
    - [枚举类型](#枚举类型)
  - [实战示例](#实战示例)
    - [双向流式 RPC](#双向流式-rpc)
  - [最佳实践](#最佳实践)
    - [1. 错误处理](#1-错误处理)
    - [2. 拦截器（中间件）](#2-拦截器中间件)
  - [参考资源](#参考资源)

---

## 概述

gRPC 是 Google 开发的高性能、开源 RPC 框架，基于 HTTP/2 和 Protocol Buffers。

### 核心依赖

```toml
[dependencies]
# Tonic - Rust 的 gRPC 实现
tonic = "0.11"
prost = "0.12"

[build-dependencies]
tonic-build = "0.11"
```

---

## Tonic

### 定义 Proto 文件

```protobuf
// proto/hello.proto
syntax = "proto3";

package hello;

service Greeter {
  rpc SayHello (HelloRequest) returns (HelloReply);
}

message HelloRequest {
  string name = 1;
}

message HelloReply {
  string message = 1;
}
```

### 生成 Rust 代码

```rust
// build.rs
fn main() {
    tonic_build::compile_protos("proto/hello.proto")
        .unwrap_or_else(|e| panic!("Failed to compile protos {:?}", e));
}
```

### 服务端实现

```rust
use tonic::{transport::Server, Request, Response, Status};

pub mod hello {
    tonic::include_proto!("hello");
}

use hello::{
    greeter_server::{Greeter, GreeterServer},
    HelloRequest, HelloReply,
};

#[derive(Default)]
pub struct MyGreeter {}

#[tonic::async_trait]
impl Greeter for MyGreeter {
    async fn say_hello(
        &self,
        request: Request<HelloRequest>,
    ) -> Result<Response<HelloReply>, Status> {
        let name = request.into_inner().name;
        
        let reply = HelloReply {
            message: format!("Hello, {}!", name),
        };
        
        Ok(Response::new(reply))
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let addr = "[::1]:50051".parse()?;
    let greeter = MyGreeter::default();
    
    Server::builder()
        .add_service(GreeterServer::new(greeter))
        .serve(addr)
        .await?;
    
    Ok(())
}
```

### 客户端实现

```rust
use hello::{greeter_client::GreeterClient, HelloRequest};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut client = GreeterClient::connect("http://[::1]:50051").await?;
    
    let request = tonic::Request::new(HelloRequest {
        name: "Tonic".into(),
    });
    
    let response = client.say_hello(request).await?;
    
    println!("RESPONSE={:?}", response.into_inner());
    
    Ok(())
}
```

---

## Protocol Buffers

### 数据类型

```protobuf
syntax = "proto3";

message User {
  int32 id = 1;
  string name = 2;
  string email = 3;
  repeated string tags = 4;  // 数组
  map<string, string> metadata = 5;  // 映射
}
```

### 枚举类型

```protobuf
enum UserRole {
  UNKNOWN = 0;
  ADMIN = 1;
  USER = 2;
  GUEST = 3;
}

message User {
  int32 id = 1;
  string name = 2;
  UserRole role = 3;
}
```

---

## 实战示例

### 双向流式 RPC

```protobuf
// proto/chat.proto
syntax = "proto3";

package chat;

service Chat {
  rpc Exchange (stream Message) returns (stream Message);
}

message Message {
  string user = 1;
  string content = 2;
}
```

```rust
use tonic::{Request, Response, Status, Streaming};
use tokio_stream::wrappers::ReceiverStream;

pub mod chat {
    tonic::include_proto!("chat");
}

use chat::{
    chat_server::{Chat, ChatServer},
    Message,
};

#[derive(Default)]
pub struct MyChatServer {}

#[tonic::async_trait]
impl Chat for MyChatServer {
    type ExchangeStream = ReceiverStream<Result<Message, Status>>;
    
    async fn exchange(
        &self,
        request: Request<Streaming<Message>>,
    ) -> Result<Response<Self::ExchangeStream>, Status> {
        let mut stream = request.into_inner();
        let (tx, rx) = tokio::sync::mpsc::channel(4);
        
        tokio::spawn(async move {
            while let Some(result) = stream.message().await.transpose() {
                match result {
                    Ok(msg) => {
                        let reply = Message {
                            user: "Server".to_string(),
                            content: format!("Echo: {}", msg.content),
                        };
                        tx.send(Ok(reply)).await.unwrap();
                    }
                    Err(e) => {
                        tx.send(Err(e)).await.unwrap();
                        break;
                    }
                }
            }
        });
        
        Ok(Response::new(ReceiverStream::new(rx)))
    }
}
```

---

## 最佳实践

### 1. 错误处理

```rust
use tonic::{Status, Code};

fn handle_error() -> Result<(), Status> {
    Err(Status::new(Code::NotFound, "User not found"))
}
```

### 2. 拦截器（中间件）

```rust
use tonic::{Request, Status};

fn intercept(req: Request<()>) -> Result<Request<()>, Status> {
    // 检查认证
    match req.metadata().get("authorization") {
        Some(_) => Ok(req),
        None => Err(Status::unauthenticated("Missing token")),
    }
}

// 使用拦截器
let svc = GreeterServer::with_interceptor(greeter, intercept);
```

---

## 参考资源

- [Tonic GitHub](https://github.com/hyperium/tonic)
- [Protocol Buffers 文档](https://protobuf.dev/)
- [gRPC 官网](https://grpc.io/)
