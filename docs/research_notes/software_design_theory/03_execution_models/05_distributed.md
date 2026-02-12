# 分布式执行模型形式化

> **创建日期**: 2026-02-12
> **分类**: 执行模型
> **安全边界**: 纯 Safe 或 需 unsafe

---

## 形式化定义

**Def 1.1（分布式执行）**:

分布式执行满足：

- 跨进程/跨节点通信
- 无共享内存；仅通过消息传递
- 网络 I/O、序列化、RPC、消息队列

**Def 1.2（Actor 模型）**:

Actor 为封装状态与行为的单元；通过消息传递通信。形式化：

- $\mathit{send}(a, m)$：向 actor $a$ 发送消息 $m$
- $a$ 内部：$\mathit{receive}(m) \to \mathit{state}'$，状态转换

**Axiom DI1**：网络边界无共享内存；消息序列化/反序列化类型安全。

**Axiom DI2**：失败与超时；分布式系统需处理部分失败。

**定理 DI-T1**：tonic、actix 等库封装网络与序列化；Rust 类型系统保证序列化前后类型一致。FFI 绑定需 unsafe。

**引理 DI-L1（序列化类型安全）**：若 $T$ 实现 `Serialize`/`Deserialize`，则 `serde` 保证序列化 $v:T$ 与反序列化结果类型一致；跨边界无类型混淆。

*证明*：由 serde 实现；类型信息编码于格式；反序列化时类型确定；Axiom DI1 类型安全。∎

**推论 DI-C1**：分布式模型为 Safe 当且仅当无裸 FFI；tonic、actix 为 Safe；自定义 C 绑定需 unsafe 封装。见 [06_boundary_analysis](06_boundary_analysis.md) EB-T1。

---

## Rust 实现与代码示例

### gRPC (tonic)

```rust
// 定义 service
pub mod pb {
    tonic::include_proto!("myservice");
}

use pb::my_service_client::MyServiceClient;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut client = MyServiceClient::connect("http://[::1]:50051").await?;
    let request = tonic::Request::new(MyRequest { data: "hello".into() });
    let response = client.call(request).await?;
    Ok(())
}
```

### Actor (actix)

```rust
use actix::prelude::*;

struct MyActor;
impl Actor for MyActor {
    type Context = Context<Self>;
}

struct MyMessage(String);
impl Message for MyMessage {
    type Result = String;
}

impl Handler<MyMessage> for MyActor {
    fn handle(&mut self, msg: MyMessage, _: &mut Context<Self>) -> Self::Result {
        msg.0.to_uppercase()
    }
}
```

**形式化对应**：gRPC 为 RPC；actor 为消息传递。两者均为 Safe，库封装网络细节。

---

## 典型场景（实质内容）

| 场景 | 说明 | 选型 |
| :--- | :--- | :--- |
| 微服务 | gRPC、HTTP API | tonic、axum、actix-web |
| 消息队列 | Kafka、RabbitMQ 客户端 | rdkafka、lapin |
| Actor 集群 | 分布式 actor 系统 | actix |
| 分布式存储 | 客户端协议 | etcd、redis 客户端 |
| 服务发现 | 健康检查、负载均衡 | consul、自定义 |

### 与设计模式组合

| 组合 | 说明 |
| :--- | :--- |
| 分布式 + DTO | 跨边界序列化；见 [02_complete_43_catalog](../../02_workflow_safe_complete_models/02_complete_43_catalog.md) DTO |
| 分布式 + Gateway | 外部系统集成；见 [02_complete_43_catalog](../../02_workflow_safe_complete_models/02_complete_43_catalog.md) Gateway |
| 分布式 + Remote Facade | 粗粒度接口；batch 减少 RPC；见 02_complete_43_catalog |
| 分布式 + Observer | 事件总线、消息队列；见 [observer](../../01_design_patterns_formal/03_behavioral/observer.md) |

### 常见陷阱

| 陷阱 | 后果 | 规避 |
| :--- | :--- | :--- |
| 忽略超时 | 永久阻塞 | `tokio::time::timeout`、`tokio::time::interval` |
| 非幂等重试 | 重复操作 | 设计幂等接口；或去重 |
| 序列化版本不兼容 | 反序列化失败 | 版本管理；向后兼容 schema |
| 无熔断 | 雪崩 | 熔断器、限流；见 [02_effectiveness_proofs](../../04_compositional_engineering/02_effectiveness_proofs.md) |

---

## 分布式系统特性

### CAP 与失败模式

**Axiom DI3**：分布式系统满足 CAP 中至多两项： Consistency（一致性）、Availability（可用性）、Partition tolerance（分区容错）。

**失败模式**：

| 失败 | 处理 | Rust 对应 |
| :--- | :--- | :--- |
| 网络超时 | 超时设置、重试 | `tokio::time::timeout` |
| 部分失败 | 幂等、补偿 | `Result`、`?` 传播 |
| 节点宕机 | 副本、心跳 | 库实现 |
| 消息丢失 | 确认、重传 | 协议层 |

---

## 序列化与类型安全

**Def 1.3（序列化契约）**:

设 $T$ 为可序列化类型。$\mathit{serialize}(v : T) \to \mathit{bytes}$，$\mathit{deserialize}(\mathit{bytes}) \to \mathit{Result}\langle T, E \rangle$。类型 $T$ 在序列化前后一致。

**定理 DI-T2**：`serde`、`prost` 等保证类型与 schema 一致；错误反序列化返回 `Err`，非 UB。

```rust
// serde 序列化
#[derive(serde::Serialize, serde::Deserialize)]
struct Request { id: u64, data: String }

let bytes = serde_json::to_vec(&req)?;
let parsed: Request = serde_json::from_slice(&bytes)?;
```

---

## RPC 与 Actor 对比

| 模型 | 通信 | 语义 | 典型库 |
| :--- | :--- | :--- | :--- |
| RPC | 请求-响应 | 同步风格 | tonic、tarpc |
| Actor | 消息传递 | 异步、无共享 | actix |
| 消息队列 | 发布-订阅 | 解耦 | rdkafka、lapin |

---

## 重试与熔断

```rust
// 指数退避重试
async fn retry_with_backoff<F, T>(mut f: F) -> Result<T, Error>
where
    F: FnMut() -> Result<T, Error>,
{
    let mut delay = Duration::from_millis(100);
    loop {
        match f() {
            Ok(v) => return Ok(v),
            Err(e) if e.is_retryable() => {
                tokio::time::sleep(delay).await;
                delay *= 2;
            }
            Err(e) => return Err(e),
        }
    }
}
```

---

## 安全边界与 FFI

| 边界 | 说明 |
| :--- | :--- |
| 纯 Safe | tonic、actix、serde 等高层 API |
| 需 unsafe | 直接 `extern`、`libc` 绑定、自定义协议 |
| 安全抽象 | 将 unsafe 封装在库内，对外 Safe API |

---

## 与形式化基础衔接

| 模型 | 引用 |
| :--- | :--- |
| 消息传递 | Send 类型跨边界；无共享内存 |
| 序列化 | 类型安全；无 transmute |
| 超时 | 有限 Future（async T6.3） |

---

## 边界

| 维度 | 分类 |
| :--- | :--- |
| 安全 | 纯 Safe（库封装）；FFI 需 unsafe |
| 支持 | 库支持 |
| 表达 | 近似（无内置 RPC） |
