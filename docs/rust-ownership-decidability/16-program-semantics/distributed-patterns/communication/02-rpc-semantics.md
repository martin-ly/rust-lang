# RPC 语义 (Remote Procedure Call Semantics)

## 目录

- [RPC 语义 (Remote Procedure Call Semantics)](#rpc-语义-remote-procedure-call-semantics)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. RPC 基本模型](#2-rpc-基本模型)
    - [2.1 语义抽象](#21-语义抽象)
    - [2.2 形式化定义](#22-形式化定义)
  - [3. 请求-响应语义](#3-请求-响应语义)
    - [3.1 同步 RPC](#31-同步-rpc)
    - [3.2 异步 RPC](#32-异步-rpc)
    - [3.3 流式 RPC](#33-流式-rpc)
  - [4. RPC 失败语义](#4-rpc-失败语义)
    - [4.1 失败模式分类](#41-失败模式分类)
    - [4.2 幂等性语义](#42-幂等性语义)
    - [4.3 断路器模式](#43-断路器模式)
  - [5. gRPC 语义详解](#5-grpc-语义详解)
    - [5.1 gRPC 四种服务类型](#51-grpc-四种服务类型)
    - [5.2 Rust gRPC 语义 (tonic)](#52-rust-grpc-语义-tonic)
  - [6. 形式化正确性](#6-形式化正确性)
    - [6.1 RPC 契约语义](#61-rpc-契约语义)
    - [6.2 超时与因果性](#62-超时与因果性)
  - [7. 总结](#7-总结)

## 1. 引言

RPC（远程过程调用）是分布式系统中最基本的通信范式之一，它将网络通信抽象为本地函数调用。本文档深入分析 RPC 的形式化语义、Rust 实现以及可靠性保证。

---

## 2. RPC 基本模型

### 2.1 语义抽象

```
本地调用语义 vs RPC 语义:

本地调用:                RPC 调用:
┌──────────────┐        ┌──────────┐  序列化   ┌──────────┐
│ caller()     │        │ Client   │ ────────→│ Network  │
│   ↓          │        │          │          │          │
│ callee()     │        │ ←────────│  反序列化 │ ←────────│
│   ↓          │        │  响应     │          │  响应     │
│ return val   │        └──────────┘          └──────────┘
└──────────────┘

关键区别:
  1. 网络延迟（非瞬时）
  2. 部分失败（caller 可能不知道 callee 是否执行）
  3. 序列化/反序列化开销
```

### 2.2 形式化定义

**RPC 计算模型:**

```
RPC = (Request, Response, Handler, Timeout)

其中:
  Request:  参数 × 序列化格式
  Response: 返回值 × 状态码
  Handler:  Request → Response 的函数
  Timeout:  时间上限
```

**操作语义:**

$$
\frac{
  \text{serialize}(args) = payload \quad
  \text{network\_send}(addr, payload) \downarrow^t
}{
  \langle \text{rpc\_call}(addr, f, args), \sigma \rangle
  \rightarrow^t \langle \text{deserialize}(result), \sigma' \rangle
}
\quad\text{(S-RPC-Success)}
$$

$$
\frac{
  \text{timeout}(t) \lor \text{network\_failure}()
}{
  \langle \text{rpc\_call}(addr, f, args), \sigma \rangle
  \rightarrow \langle \text{Err(RpcError)}, \sigma \rangle
}
\quad\text{(S-RPC-Fail)}
$$

---

## 3. 请求-响应语义

### 3.1 同步 RPC

```rust
use std::time::Duration;
use serde::{Serialize, Deserialize};

// 请求/响应类型
#[derive(Serialize, Deserialize)]
struct AddRequest {
    a: i32,
    b: i32,
}

#[derive(Serialize, Deserialize)]
struct AddResponse {
    result: i32,
}

// 同步 RPC 客户端语义
trait SyncRpcClient {
    fn call<Req, Resp>(
        &self,
        method: &str,
        request: Req,
    ) -> Result<Resp, RpcError>
    where
        Req: Serialize,
        Resp: DeserializeOwned;
}

// 语义等价于:
// result = timeout(deadline) {
//   send_request(request)
//   wait_response()
// }
```

### 3.2 异步 RPC

```rust
use std::future::Future;

// 异步 RPC 语义
trait AsyncRpcClient {
    fn call_async<Req, Resp>(
        &self,
        method: &str,
        request: Req,
    ) -> impl Future<Output = Result<Resp, RpcError>>
    where
        Req: Serialize + Send,
        Resp: DeserializeOwned + Send;
}

// 使用示例
async fn async_rpc_example(client: &impl AsyncRpcClient) {
    // 发起调用，立即返回 Future
    let future1 = client.call_async::<_, AddResponse>(
        "add",
        AddRequest { a: 1, b: 2 }
    );

    let future2 = client.call_async::<_, AddResponse>(
        "add",
        AddRequest { a: 3, b: 4 }
    );

    // 并发执行
    let (resp1, resp2) = tokio::join!(future1, future2);
}
```

### 3.3 流式 RPC

```rust
// 双向流式 RPC (gRPC 风格)
trait StreamingRpc {
    type Request;
    type Response;

    // 客户端流
    async fn client_streaming(
        &self,
        requests: impl Stream<Item = Self::Request>,
    ) -> Result<Self::Response, RpcError>;

    // 服务端流
    fn server_streaming(
        &self,
        request: Self::Request,
    ) -> impl Stream<Item = Result<Self::Response, RpcError>>;

    // 双向流
    fn bidirectional_stream(
        &self,
        requests: impl Stream<Item = Self::Request>,
    ) -> impl Stream<Item = Result<Self::Response, RpcError>>;
}
```

---

## 4. RPC 失败语义

### 4.1 失败模式分类

```
RPC 失败语义:

┌─────────────────────────────────────────────────────────────┐
│                     失败检测                                 │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  1. 快速失败 (Fail-Fast)                                     │
│     任何网络错误立即返回错误                                  │
│     ┌──────────┐    X    ┌──────────┐                      │
│     │ Client   │ ───────→│ Network  │                      │
│     │ ← Err()  │         │ (失败)   │                      │
│     └──────────┘         └──────────┘                      │
│                                                             │
│  2. 超时失败 (Fail-Timeout)                                  │
│     等待直到超时                                            │
│     ┌──────────┐    ?    ┌──────────┐    ?    ┌──────────┐ │
│     │ Client   │ ───────→│ Network  │ ───────→│ Server   │ │
│     │ ← Timeout│         │          │         │ (?执行)  │ │
│     └──────────┘         └──────────┘         └──────────┘ │
│                                                             │
│  3. 重试失败 (Fail-After-Retry)                              │
│     重试 N 次后失败                                         │
│     ┌──────────┐ ×3  ┌──────────┐                          │
│     │ Client   │ ───→│ 失败     │                          │
│     └──────────┘     └──────────┘                          │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 4.2 幂等性语义

```rust
// 幂等 RPC: 多次调用效果相同
#[derive(Clone)]
struct IdempotentRpc<T> {
    inner: T,
    dedup: Arc<Mutex<HashSet<RequestId>>>,
}

impl<T: RpcClient> IdempotentRpc<T> {
    async fn call<Req: Clone, Resp>(
        &self,
        request_id: RequestId,
        request: Req,
    ) -> Result<Resp, RpcError>
    where
        Req: Serializable,
        Resp: Deserializable,
    {
        // 去重检查
        if self.dedup.lock().await.contains(&request_id) {
            // 返回缓存结果或等待原请求完成
            return self.wait_for_result(request_id).await;
        }

        self.dedup.lock().await.insert(request_id);

        // 带重试的调用
        let result = self.retry_with_backoff(request).await;

        // 缓存结果
        self.cache_result(request_id, &result);

        result
    }
}

// 幂等键 trait
pub trait IdempotentKey {
    fn key(&self) -> String;
}

impl IdempotentKey for TransferRequest {
    fn key(&self) -> String {
        format!("{}:{}:{}:{}", self.from, self.to, self.amount, self.nonce)
    }
}
```

### 4.3 断路器模式

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

enum CircuitState {
    Closed,    // 正常，允许请求
    Open,      // 断开，拒绝请求
    HalfOpen,  // 半开，测试恢复
}

struct CircuitBreaker {
    state: AtomicUsize,
    failure_count: AtomicUsize,
    threshold: usize,
    timeout: Duration,
    last_failure_time: AtomicUsize,
}

impl CircuitBreaker {
    async fn call<F, T>(&self, f: F) -> Result<T, CircuitError>
    where
        F: Future<Output = Result<T, RpcError>>,
    {
        match self.state() {
            CircuitState::Open => {
                if self.should_attempt_reset() {
                    self.set_state(CircuitState::HalfOpen);
                } else {
                    return Err(CircuitError::Open);
                }
            }
            CircuitState::HalfOpen | CircuitState::Closed => {}
        }

        match f.await {
            Ok(v) => {
                self.on_success();
                Ok(v)
            }
            Err(e) => {
                self.on_failure();
                Err(CircuitError::Underlying(e))
            }
        }
    }
}
```

---

## 5. gRPC 语义详解

### 5.1 gRPC 四种服务类型

```protobuf
// 1. Unary (一元)
rpc SayHello (HelloRequest) returns (HelloResponse);

// 2. Server Streaming (服务端流)
rpc ListFeatures (Rectangle) returns (stream Feature);

// 3. Client Streaming (客户端流)
rpc RecordRoute (stream Point) returns (RouteSummary);

// 4. Bidirectional Streaming (双向流)
rpc RouteChat (stream RouteNote) returns (stream RouteNote);
```

### 5.2 Rust gRPC 语义 (tonic)

```rust
use tonic::{Request, Response, Status, Streaming};
use tokio_stream::wrappers::ReceiverStream;

// Unary RPC 语义
async fn unary_semantics(
    request: Request<HelloRequest>,
) -> Result<Response<HelloResponse>, Status> {
    // Request 包含元数据
    let metadata = request.metadata();
    let deadline = request.timeout(); // 超时信息

    // 处理请求
    let response = HelloResponse {
        message: format!("Hello, {}!", request.into_inner().name),
    };

    Ok(Response::new(response))
}

// 服务端流语义
async fn server_streaming_semantics(
    request: Request<Rectangle>,
) -> Result<Response<ReceiverStream<Result<Feature, Status>>>, Status> {
    let (tx, rx) = tokio::sync::mpsc::channel(4);

    tokio::spawn(async move {
        for feature in database.iter() {
            // 流式发送
            if tx.send(Ok(feature.clone())).await.is_err() {
                break; // 客户端断开
            }
        }
    });

    Ok(Response::new(ReceiverStream::new(rx)))
}

// 双向流语义
async fn bidirectional_semantics(
    request: Request<Streaming<RouteNote>>,
) -> Result<Response<ReceiverStream<Result<RouteNote, Status>>>, Status> {
    let mut stream = request.into_inner();
    let (tx, rx) = tokio::sync::mpsc::channel(4);

    tokio::spawn(async move {
        while let Some(note) = stream.message().await.unwrap_or(None) {
            // 处理并响应
            let response = process_note(note);
            if tx.send(Ok(response)).await.is_err() {
                break;
            }
        }
    });

    Ok(Response::new(ReceiverStream::new(rx)))
}
```

---

## 6. 形式化正确性

### 6.1 RPC 契约语义

```
前置条件:  request 有效且 server 可达
后置条件:  response = f(request) ∨ error ∈ {Timeout, Network, Server}
不变量:    at_most_once?(idempotent)
```

### 6.2 超时与因果性

```
因果一致性 (Causal Consistency):

  如果 request₁ → request₂（因果序）
  那么 server 必须按因果序处理

  问题: 超时重试可能破坏因果序

  解决方案:
    1. 逻辑时钟 (Lamport Timestamps)
    2. 向量时钟 (Vector Clocks)
    3. 客户端序列号
```

---

## 7. 总结

| 语义维度 | 关键保证 | Rust 实现 |
|----------|----------|-----------|
| 调用模型 | 同步/异步/流式 | tonic, tarpc |
| 失败处理 | 断路器、重试、幂等 | 自定义实现 |
| 类型安全 | 编译期验证 | Protobuf + Serde |
| 性能 | 连接池、批处理 | tonic 内置 |

关键公式:

$$
\text{RPC}_{\text{reliable}} = \text{Retry} \times \text{Timeout} \times \text{Idempotency} \times \text{CircuitBreaker}
$$
