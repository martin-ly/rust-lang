# 传输（Transport）

- RPC 抽象、流控与背压、超时与重试、幂等性
- 接口：`RpcClient`, `RpcServer`

## 重试策略

```rust
use c20_distributed::transport::{InMemoryRpcServer, InMemoryRpcClient, RetryClient, RetryPolicy};

let mut srv = InMemoryRpcServer::new();
srv.register("echo", Box::new(|b| b.to_vec()));
let cli = InMemoryRpcClient::new(srv);
let retry = RetryClient { inner: cli, policy: RetryPolicy { max_retries: 3, retry_on_empty: true, backoff_base_ms: Some(10) } };
let _ = retry.call("echo", b"hi");
```

## 超时与截止时间（Deadline）

- 为每次请求设置总预算（如 200ms），重试共享同一截止时间，避免“无界重试”。
- 与 `scheduling` 配合：根据剩余预算动态计算下一次超时与退避间隔。

## 幂等键与去重缓存

- 客户端携带 `idempotency_key`；服务端维护去重缓存（LRU/时间窗）。
- 返回上次成功的结果或拒绝重复副作用，确保在重试/乱序场景下安全。

## 背压（Backpressure）

- 通过限流器/令牌桶防止过载；在客户端侧可根据错误信号进行指数退避。

## 进一步阅读

- Wiki：`Remote procedure call`, `Exponential backoff`, `Backpressure`, `Idempotence`
- 课程：MIT 6.824（RPC, Failures and Timeouts）、UWash CSE452（Communication）
- 实践：gRPC Retry/hedging 指南、Envoy 连接池与熔断、Finagle/Hystrix 模式
