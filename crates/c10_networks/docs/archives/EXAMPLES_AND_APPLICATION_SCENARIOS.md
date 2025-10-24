# C10 Networks 示例与应用场景

> 适用范围：Rust 1.90+，Tokio 1.35+。文档风格遵循 [`DOCUMENTATION_STYLE_GUIDE.md`](DOCUMENTATION_STYLE_GUIDE.md)。


## 📊 目录

- [📋 目录](#目录)
- [🎯 概述](#概述)
  - [1. 示例分类](#1-示例分类)
  - [2. 应用场景](#2-应用场景)
  - [3. 学习路径](#3-学习路径)
- [🔧 基础示例](#基础示例)
  - [1. TCP客户端示例](#1-tcp客户端示例)
    - [1.1 基本TCP连接](#11-基本tcp连接)
    - [1.2 带重连的TCP客户端](#12-带重连的tcp客户端)
  - [2. HTTP客户端示例](#2-http客户端示例)
    - [2.1 基本HTTP请求](#21-基本http请求)
    - [2.2 带认证的HTTP客户端](#22-带认证的http客户端)
  - [3. WebSocket客户端示例](#3-websocket客户端示例)
    - [3.1 基本WebSocket连接](#31-基本websocket连接)
    - [3.2 实时消息处理](#32-实时消息处理)
  - [4. UDP通信示例](#4-udp通信示例)
    - [4.1 基本UDP通信](#41-基本udp通信)
- [🌐 高级示例](#高级示例)
  - [1. 异步网络编程](#1-异步网络编程)
    - [1.1 并发连接处理](#11-并发连接处理)
    - [1.2 异步任务管理](#12-异步任务管理)
  - [2. 连接池管理](#2-连接池管理)
    - [2.1 连接池实现](#21-连接池实现)
  - [3. 负载均衡](#3-负载均衡)
    - [3.1 轮询负载均衡](#31-轮询负载均衡)
  - [4. 故障恢复](#4-故障恢复)
    - [4.1 自动重试机制](#41-自动重试机制)
- [🏭 实际应用场景](#实际应用场景)
  - [1. 微服务通信](#1-微服务通信)
    - [1.1 服务间HTTP通信](#11-服务间http通信)
  - [2. 实时数据流](#2-实时数据流)
    - [2.1 WebSocket数据流处理](#21-websocket数据流处理)
  - [3. 分布式系统](#3-分布式系统)
    - [3.1 分布式锁](#31-分布式锁)
  - [4. 云原生应用](#4-云原生应用)
    - [4.1 Kubernetes服务发现](#41-kubernetes服务发现)
- [📊 性能优化示例](#性能优化示例)
  - [1. 内存优化](#1-内存优化)
    - [1.1 零拷贝数据传输](#11-零拷贝数据传输)
  - [2. 并发优化](#2-并发优化)
    - [2.1 异步批处理](#21-异步批处理)
- [🔒 安全示例](#安全示例)
  - [1. TLS加密通信](#1-tls加密通信)
    - [1.1 HTTPS客户端](#11-https客户端)
  - [2. 身份认证](#2-身份认证)
    - [2.1 JWT认证](#21-jwt认证)
- [🧪 测试示例](#测试示例)
  - [1. 单元测试](#1-单元测试)
    - [1.1 HTTP客户端测试](#11-http客户端测试)
  - [2. 集成测试](#2-集成测试)
    - [2.1 端到端测试](#21-端到端测试)
- [🔗 相关文档](#相关文档)


## 📋 目录

- [C10 Networks 示例与应用场景](#c10-networks-示例与应用场景)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
    - [1. 示例分类](#1-示例分类)
    - [2. 应用场景](#2-应用场景)
    - [3. 学习路径](#3-学习路径)
  - [🔧 基础示例](#-基础示例)
    - [1. TCP客户端示例](#1-tcp客户端示例)
      - [1.1 基本TCP连接](#11-基本tcp连接)
      - [1.2 带重连的TCP客户端](#12-带重连的tcp客户端)
    - [2. HTTP客户端示例](#2-http客户端示例)
      - [2.1 基本HTTP请求](#21-基本http请求)
      - [2.2 带认证的HTTP客户端](#22-带认证的http客户端)
    - [3. WebSocket客户端示例](#3-websocket客户端示例)
      - [3.1 基本WebSocket连接](#31-基本websocket连接)
      - [3.2 实时消息处理](#32-实时消息处理)
    - [4. UDP通信示例](#4-udp通信示例)
      - [4.1 基本UDP通信](#41-基本udp通信)
  - [🌐 高级示例](#-高级示例)
    - [1. 异步网络编程](#1-异步网络编程)
      - [1.1 并发连接处理](#11-并发连接处理)
      - [1.2 异步任务管理](#12-异步任务管理)
    - [2. 连接池管理](#2-连接池管理)
      - [2.1 连接池实现](#21-连接池实现)
    - [3. 负载均衡](#3-负载均衡)
      - [3.1 轮询负载均衡](#31-轮询负载均衡)
    - [4. 故障恢复](#4-故障恢复)
      - [4.1 自动重试机制](#41-自动重试机制)
  - [🏭 实际应用场景](#-实际应用场景)
    - [1. 微服务通信](#1-微服务通信)
      - [1.1 服务间HTTP通信](#11-服务间http通信)
    - [2. 实时数据流](#2-实时数据流)
      - [2.1 WebSocket数据流处理](#21-websocket数据流处理)
    - [3. 分布式系统](#3-分布式系统)
      - [3.1 分布式锁](#31-分布式锁)
    - [4. 云原生应用](#4-云原生应用)
      - [4.1 Kubernetes服务发现](#41-kubernetes服务发现)
  - [📊 性能优化示例](#-性能优化示例)
    - [1. 内存优化](#1-内存优化)
      - [1.1 零拷贝数据传输](#11-零拷贝数据传输)
    - [2. 并发优化](#2-并发优化)
      - [2.1 异步批处理](#21-异步批处理)
  - [🔒 安全示例](#-安全示例)
    - [1. TLS加密通信](#1-tls加密通信)
      - [1.1 HTTPS客户端](#11-https客户端)
    - [2. 身份认证](#2-身份认证)
      - [2.1 JWT认证](#21-jwt认证)
  - [🧪 测试示例](#-测试示例)
    - [1. 单元测试](#1-单元测试)
      - [1.1 HTTP客户端测试](#11-http客户端测试)
    - [2. 集成测试](#2-集成测试)
      - [2.1 端到端测试](#21-端到端测试)
  - [🔗 相关文档](#-相关文档)

## 🎯 概述

本文档提供了C10 Networks项目的详细示例和实际应用场景，帮助开发者快速上手并理解网络编程的最佳实践。

### 1. 示例分类

示例按照复杂度和应用场景分为以下几类：

1. **基础示例**: 简单的网络通信示例
2. **高级示例**: 复杂的网络编程模式
3. **实际应用场景**: 真实世界的应用案例
4. **性能优化示例**: 性能调优和优化技巧
5. **安全示例**: 网络安全和加密通信
6. **测试示例**: 各种测试方法和技巧

### 2. 应用场景

| 场景类型 | 描述 | 技术栈 |
|---------|------|--------|
| 微服务通信 | 服务间通信 | HTTP, gRPC, WebSocket |
| 实时数据流 | 实时数据处理 | WebSocket, TCP |
| 分布式系统 | 分布式应用 | 多协议支持 |
| 云原生应用 | 容器化部署 | Kubernetes, Docker |

### 3. 学习路径

建议的学习路径：

1. **入门**: 从基础示例开始
2. **进阶**: 学习高级示例
3. **实践**: 应用实际场景
4. **优化**: 性能和安全优化
5. **测试**: 测试和验证

## 🔧 基础示例

### 1. TCP客户端示例

#### 1.1 基本TCP连接

```rust
use c10_networks::tcp::TcpClient;
use tokio::io::{AsyncReadExt, AsyncWriteExt};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建TCP客户端
    let mut client = TcpClient::new("127.0.0.1:8080").await?;
    
    // 发送数据
    let message = "Hello, Server!";
    client.write_all(message.as_bytes()).await?;
    
    // 接收响应
    let mut buffer = vec![0; 1024];
    let n = client.read(&mut buffer).await?;
    let response = String::from_utf8_lossy(&buffer[..n]);
    
    println!("服务器响应: {}", response);
    
    Ok(())
}
```

#### 1.2 带重连的TCP客户端

```rust
use c10_networks::tcp::TcpClient;
use tokio::time::{sleep, Duration};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut client = TcpClient::new("127.0.0.1:8080").await?;
    
    loop {
        match client.write_all(b"ping").await {
            Ok(_) => {
                println!("发送成功");
                sleep(Duration::from_secs(1)).await;
            }
            Err(e) => {
                println!("连接错误: {}", e);
                // 重连逻辑
                client = TcpClient::new("127.0.0.1:8080").await?;
            }
        }
    }
}
```

### 2. HTTP客户端示例

#### 2.1 基本HTTP请求

```rust
use c10_networks::http::HttpClient;
use serde_json::json;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建HTTP客户端
    let client = HttpClient::new();
    
    // GET请求
    let response = client.get("https://api.example.com/users").await?;
    println!("GET响应: {}", response.body);
    
    // POST请求
    let data = json!({
        "name": "John Doe",
        "email": "john@example.com"
    });
    let response = client.post("https://api.example.com/users", data).await?;
    println!("POST响应: {}", response.body);
    
    Ok(())
}
```

#### 2.2 带认证的HTTP客户端

```rust
use c10_networks::http::HttpClient;
use c10_networks::auth::BearerToken;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建带认证的HTTP客户端
    let token = BearerToken::new("your-api-token");
    let client = HttpClient::new().with_auth(token);
    
    // 发送认证请求
    let response = client.get("https://api.example.com/protected").await?;
    println!("认证响应: {}", response.body);
    
    Ok(())
}
```

### 3. WebSocket客户端示例

#### 3.1 基本WebSocket连接

```rust
use c10_networks::websocket::WebSocketClient;
use tokio::time::{sleep, Duration};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建WebSocket客户端
    let mut client = WebSocketClient::new("ws://127.0.0.1:8080").await?;
    
    // 发送消息
    client.send_text("Hello, WebSocket!").await?;
    
    // 接收消息
    if let Some(message) = client.receive().await? {
        println!("收到消息: {}", message);
    }
    
    Ok(())
}
```

#### 3.2 实时消息处理

```rust
use c10_networks::websocket::WebSocketClient;
use tokio::time::{sleep, Duration};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut client = WebSocketClient::new("ws://127.0.0.1:8080").await?;
    
    // 启动消息接收任务
    let mut receiver = client.clone();
    tokio::spawn(async move {
        loop {
            if let Some(message) = receiver.receive().await.unwrap() {
                println!("实时消息: {}", message);
            }
            sleep(Duration::from_millis(100)).await;
        }
    });
    
    // 发送消息
    loop {
        client.send_text("ping").await?;
        sleep(Duration::from_secs(1)).await;
    }
}
```

### 4. UDP通信示例

#### 4.1 基本UDP通信

```rust
use c10_networks::udp::UdpSocket;
use std::net::SocketAddr;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建UDP套接字
    let socket = UdpSocket::bind("127.0.0.1:0").await?;
    
    // 发送数据
    let target: SocketAddr = "127.0.0.1:8080".parse()?;
    socket.send_to(b"Hello, UDP!", target).await?;
    
    // 接收数据
    let mut buffer = vec![0; 1024];
    let (n, addr) = socket.recv_from(&mut buffer).await?;
    let message = String::from_utf8_lossy(&buffer[..n]);
    
    println!("从 {} 收到: {}", addr, message);
    
    Ok(())
}
```

## 🌐 高级示例

### 1. 异步网络编程

#### 1.1 并发连接处理

```rust
use c10_networks::tcp::TcpClient;
use tokio::sync::mpsc;
use std::sync::Arc;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let (tx, mut rx) = mpsc::channel(100);
    
    // 启动多个连接任务
    for i in 0..10 {
        let tx = tx.clone();
        tokio::spawn(async move {
            let mut client = TcpClient::new("127.0.0.1:8080").await?;
            client.write_all(format!("Message {}", i).as_bytes()).await?;
            
            let mut buffer = vec![0; 1024];
            let n = client.read(&mut buffer).await?;
            let response = String::from_utf8_lossy(&buffer[..n]);
            
            tx.send(format!("连接 {} 收到: {}", i, response)).await?;
            Ok::<(), Box<dyn std::error::Error>>(())
        });
    }
    
    // 接收所有响应
    while let Some(response) = rx.recv().await {
        println!("{}", response);
    }
    
    Ok(())
}
```

#### 1.2 异步任务管理

```rust
use c10_networks::http::HttpClient;
use tokio::time::{sleep, Duration};
use std::sync::Arc;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = Arc::new(HttpClient::new());
    
    // 创建任务管理器
    let mut tasks = Vec::new();
    
    for i in 0..5 {
        let client = client.clone();
        let task = tokio::spawn(async move {
            loop {
                let response = client.get("https://api.example.com/data").await?;
                println!("任务 {} 收到: {}", i, response.status);
                sleep(Duration::from_secs(1)).await;
            }
            Ok::<(), Box<dyn std::error::Error>>(())
        });
        tasks.push(task);
    }
    
    // 等待所有任务完成
    for task in tasks {
        task.await??;
    }
    
    Ok(())
}
```

### 2. 连接池管理

#### 2.1 连接池实现

```rust
use c10_networks::pool::ConnectionPool;
use c10_networks::tcp::TcpClient;
use std::sync::Arc;
use tokio::sync::Mutex;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建连接池
    let pool = Arc::new(ConnectionPool::new(
        "127.0.0.1:8080",
        10, // 最大连接数
        5,  // 最小连接数
    ));
    
    // 使用连接池
    for i in 0..20 {
        let pool = pool.clone();
        tokio::spawn(async move {
            let mut client = pool.get_connection().await?;
            client.write_all(format!("Request {}", i).as_bytes()).await?;
            
            let mut buffer = vec![0; 1024];
            let n = client.read(&mut buffer).await?;
            let response = String::from_utf8_lossy(&buffer[..n]);
            
            println!("请求 {} 响应: {}", i, response);
            Ok::<(), Box<dyn std::error::Error>>(())
        });
    }
    
    Ok(())
}
```

### 3. 负载均衡

#### 3.1 轮询负载均衡

```rust
use c10_networks::load_balancer::RoundRobinBalancer;
use c10_networks::http::HttpClient;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建负载均衡器
    let servers = vec![
        "http://server1.example.com",
        "http://server2.example.com",
        "http://server3.example.com",
    ];
    let mut balancer = RoundRobinBalancer::new(servers);
    
    // 使用负载均衡器
    for i in 0..10 {
        let server = balancer.next_server();
        let client = HttpClient::new();
        let response = client.get(server).await?;
        println!("请求 {} 发送到: {}, 状态: {}", i, server, response.status);
    }
    
    Ok(())
}
```

### 4. 故障恢复

#### 4.1 自动重试机制

```rust
use c10_networks::retry::RetryPolicy;
use c10_networks::http::HttpClient;
use tokio::time::{sleep, Duration};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = HttpClient::new();
    let retry_policy = RetryPolicy::new()
        .max_attempts(3)
        .backoff(Duration::from_secs(1))
        .exponential_backoff();
    
    // 使用重试策略
    let response = retry_policy.execute(|| async {
        client.get("https://api.example.com/data").await
    }).await?;
    
    println!("最终响应: {}", response.body);
    
    Ok(())
}
```

## 🏭 实际应用场景

### 1. 微服务通信

#### 1.1 服务间HTTP通信

```rust
use c10_networks::http::HttpClient;
use c10_networks::service_discovery::ServiceRegistry;
use serde_json::json;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 服务注册
    let registry = ServiceRegistry::new();
    registry.register("user-service", "http://user-service:8080").await;
    registry.register("order-service", "http://order-service:8080").await;
    
    // 服务发现
    let user_service = registry.discover("user-service").await?;
    let order_service = registry.discover("order-service").await?;
    
    // 服务间通信
    let client = HttpClient::new();
    
    // 获取用户信息
    let user_response = client.get(&format!("{}/users/123", user_service)).await?;
    let user: serde_json::Value = serde_json::from_str(&user_response.body)?;
    
    // 创建订单
    let order_data = json!({
        "user_id": user["id"],
        "items": ["item1", "item2"]
    });
    let order_response = client.post(&format!("{}/orders", order_service), order_data).await?;
    
    println!("订单创建成功: {}", order_response.body);
    
    Ok(())
}
```

### 2. 实时数据流

#### 2.1 WebSocket数据流处理

```rust
use c10_networks::websocket::WebSocketClient;
use c10_networks::stream::DataStream;
use tokio::time::{sleep, Duration};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut client = WebSocketClient::new("ws://data-stream.example.com").await?;
    
    // 创建数据流处理器
    let mut stream = DataStream::new();
    
    // 启动数据接收任务
    let mut receiver = client.clone();
    tokio::spawn(async move {
        loop {
            if let Some(message) = receiver.receive().await.unwrap() {
                // 处理实时数据
                stream.process_message(message).await;
            }
            sleep(Duration::from_millis(10)).await;
        }
    });
    
    // 订阅数据流
    client.send_text(r#"{"type": "subscribe", "channel": "market-data"}"#).await?;
    
    // 处理数据流
    loop {
        if let Some(data) = stream.next().await {
            println!("处理数据: {:?}", data);
        }
        sleep(Duration::from_millis(100)).await;
    }
}
```

### 3. 分布式系统

#### 3.1 分布式锁

```rust
use c10_networks::distributed::DistributedLock;
use c10_networks::consensus::RaftNode;
use std::sync::Arc;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建分布式锁
    let lock = Arc::new(DistributedLock::new("resource-1"));
    
    // 获取锁
    let guard = lock.lock().await?;
    
    // 执行临界区代码
    println!("执行临界区操作");
    tokio::time::sleep(tokio::time::Duration::from_secs(5)).await;
    
    // 锁会自动释放
    drop(guard);
    
    Ok(())
}
```

### 4. 云原生应用

#### 4.1 Kubernetes服务发现

```rust
use c10_networks::kubernetes::K8sServiceDiscovery;
use c10_networks::http::HttpClient;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建Kubernetes服务发现
    let discovery = K8sServiceDiscovery::new();
    
    // 发现服务
    let services = discovery.discover_services("default").await?;
    
    for service in services {
        println!("发现服务: {} -> {}", service.name, service.endpoint);
        
        // 调用服务
        let client = HttpClient::new();
        let response = client.get(&service.endpoint).await?;
        println!("服务 {} 响应: {}", service.name, response.status);
    }
    
    Ok(())
}
```

## 📊 性能优化示例

### 1. 内存优化

#### 1.1 零拷贝数据传输

```rust
use c10_networks::tcp::TcpClient;
use c10_networks::zero_copy::ZeroCopyBuffer;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut client = TcpClient::new("127.0.0.1:8080").await?;
    
    // 使用零拷贝缓冲区
    let mut buffer = ZeroCopyBuffer::new(1024);
    
    // 零拷贝发送
    buffer.write(b"Hello, Zero Copy!");
    client.send_zero_copy(&buffer).await?;
    
    // 零拷贝接收
    let received = client.receive_zero_copy(&mut buffer).await?;
    println!("零拷贝接收: {:?}", received);
    
    Ok(())
}
```

### 2. 并发优化

#### 2.1 异步批处理

```rust
use c10_networks::batch::BatchProcessor;
use c10_networks::http::HttpClient;
use std::sync::Arc;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = Arc::new(HttpClient::new());
    
    // 创建批处理器
    let mut processor = BatchProcessor::new(100, Duration::from_millis(100));
    
    // 添加请求到批处理
    for i in 0..1000 {
        let client = client.clone();
        processor.add_request(move || {
            let client = client.clone();
            async move {
                client.get("https://api.example.com/data").await
            }
        }).await;
    }
    
    // 处理批次
    let results = processor.process_all().await?;
    println!("处理了 {} 个请求", results.len());
    
    Ok(())
}
```

## 🔒 安全示例

### 1. TLS加密通信

#### 1.1 HTTPS客户端

```rust
use c10_networks::tls::TlsClient;
use c10_networks::certificate::CertificateStore;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建证书存储
    let cert_store = CertificateStore::new();
    cert_store.load_ca_certificates("ca-certs.pem").await?;
    
    // 创建TLS客户端
    let client = TlsClient::new()
        .with_certificate_store(cert_store)
        .with_verification(true);
    
    // 发送HTTPS请求
    let response = client.get("https://secure-api.example.com/data").await?;
    println!("安全响应: {}", response.body);
    
    Ok(())
}
```

### 2. 身份认证

#### 2.1 JWT认证

```rust
use c10_networks::auth::JwtAuth;
use c10_networks::http::HttpClient;
use serde_json::json;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建JWT认证
    let auth = JwtAuth::new("your-secret-key");
    
    // 生成JWT令牌
    let claims = json!({
        "user_id": 123,
        "role": "admin"
    });
    let token = auth.generate_token(claims).await?;
    
    // 使用JWT令牌
    let client = HttpClient::new().with_auth(auth);
    let response = client.get("https://api.example.com/protected").await?;
    
    println!("认证响应: {}", response.body);
    
    Ok(())
}
```

## 🧪 测试示例

### 1. 单元测试

#### 1.1 HTTP客户端测试

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use c10_networks::http::HttpClient;
    use mockito::mock;

    #[tokio::test]
    async fn test_http_get() {
        // 创建模拟服务器
        let mock_server = mock("GET", "/test")
            .with_status(200)
            .with_body("test response")
            .create();

        // 测试HTTP客户端
        let client = HttpClient::new();
        let response = client.get(&mockito::server_url()).await.unwrap();

        assert_eq!(response.status, 200);
        assert_eq!(response.body, "test response");

        mock_server.assert();
    }
}
```

### 2. 集成测试

#### 2.1 端到端测试

```rust
#[cfg(test)]
mod integration_tests {
    use super::*;
    use c10_networks::http::HttpClient;
    use c10_networks::tcp::TcpClient;

    #[tokio::test]
    async fn test_end_to_end_communication() {
        // 启动测试服务器
        let server = TestServer::new().await;
        
        // 测试HTTP通信
        let http_client = HttpClient::new();
        let response = http_client.get(&server.http_url()).await.unwrap();
        assert_eq!(response.status, 200);
        
        // 测试TCP通信
        let mut tcp_client = TcpClient::new(&server.tcp_addr()).await.unwrap();
        tcp_client.write_all(b"test").await.unwrap();
        
        let mut buffer = vec![0; 1024];
        let n = tcp_client.read(&mut buffer).await.unwrap();
        assert_eq!(&buffer[..n], b"test response");
        
        server.shutdown().await;
    }
}
```

## 🔗 相关文档

- [网络通信理论](NETWORK_COMMUNICATION_THEORY.md) - 网络通信的理论基础
- [数学基础](MATHEMATICAL_FOUNDATIONS.md) - 网络编程的数学基础
- [网络通信概念](NETWORK_COMMUNICATION_CONCEPTS.md) - 网络通信概念详解
- [形式化证明](FORMAL_PROOFS_AND_MATHEMATICAL_ARGUMENTS.md) - 形式化证明和数学论证
- [协议实现指南](PROTOCOL_IMPLEMENTATION_GUIDE.md) - 协议实现的具体指导
- [性能优化指南](PERFORMANCE_OPTIMIZATION_GUIDE.md) - 性能优化的详细指导
- [API文档](API_DOCUMENTATION.md) - API接口的详细说明

---

**C10 Networks 示例与应用场景** - 从基础到高级的网络编程实践！

*最后更新: 2025年1月*  
*文档版本: v1.0*  
*维护者: C10 Networks 开发团队*
