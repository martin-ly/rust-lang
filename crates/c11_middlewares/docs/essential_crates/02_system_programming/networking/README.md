# 网络编程

> **核心库**: hyper, reqwest, tonic, quinn  
> **适用场景**: HTTP客户端/服务器、gRPC、QUIC、网络协议

---

## 📋 核心库概览

| 库 | 用途 | 特点 | 推荐度 |
|-----|------|------|--------|
| **hyper** | HTTP底层库 | 高性能、异步 | ⭐⭐⭐⭐⭐ |
| **reqwest** | HTTP客户端 | 易用、功能全 | ⭐⭐⭐⭐⭐ |
| **tonic** | gRPC框架 | 完整、类型安全 | ⭐⭐⭐⭐⭐ |
| **quinn** | QUIC协议 | 现代、快速 | ⭐⭐⭐⭐ |

---

## 🌐 reqwest - HTTP客户端

```rust
use reqwest;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // GET 请求
    let response = reqwest::get("https://api.github.com/repos/rust-lang/rust")
        .await?
        .json::<serde_json::Value>()
        .await?;
    
    println!("{:#?}", response);
    
    // POST 请求
    let client = reqwest::Client::new();
    let res = client.post("https://httpbin.org/post")
        .json(&serde_json::json!({"key": "value"}))
        .send()
        .await?;
    
    println!("Status: {}", res.status());
    
    Ok(())
}
```

---

## ⚡ hyper - HTTP底层

```rust
use hyper::{Body, Request, Response, Server};
use hyper::service::{make_service_fn, service_fn};

async fn handle_request(_req: Request<Body>) -> Result<Response<Body>, hyper::Error> {
    Ok(Response::new(Body::from("Hello, World!")))
}

#[tokio::main]
async fn main() {
    let make_svc = make_service_fn(|_conn| async {
        Ok::<_, hyper::Error>(service_fn(handle_request))
    });
    
    let addr = ([127, 0, 0, 1], 3000).into();
    let server = Server::bind(&addr).serve(make_svc);
    
    println!("Listening on http://{}", addr);
    
    if let Err(e) = server.await {
        eprintln!("server error: {}", e);
    }
}
```

---

## 🚀 tonic - gRPC

```rust
// proto 文件定义后自动生成代码
use tonic::{transport::Server, Request, Response, Status};

pub mod hello_world {
    tonic::include_proto!("helloworld");
}

use hello_world::greeter_server::{Greeter, GreeterServer};
use hello_world::{HelloReply, HelloRequest};

#[derive(Debug, Default)]
pub struct MyGreeter {}

#[tonic::async_trait]
impl Greeter for MyGreeter {
    async fn say_hello(
        &self,
        request: Request<HelloRequest>,
    ) -> Result<Response<HelloReply>, Status> {
        let reply = HelloReply {
            message: format!("Hello {}!", request.into_inner().name),
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

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-20

