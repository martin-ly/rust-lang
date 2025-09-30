# 分布式与微服务设计：分层、模型与Rust 1.90 落地

> 关联：`concurrency/backpressure-models.md`、`concurrency/async-sync-classification.md`、`algorithms/models.md`

## 分层视角（从语义到工程）

- 语义层（What）：一致性/时序/可终止性性质；规范化接口与契约。
- 并发层（How）：线程/任务/调度/背压；Actor、CSP、结构化并发。
- 架构层（Shape）：BFF、API 网关、服务网格、事件总线、数据分区/复制。
- 工程层（With）：Tokio、tower、axum/tonic、tracing、OpenTelemetry、Kafka/NATS。

## 通信与交互模型

- 同步 RPC：HTTP/1.1、HTTP/2（gRPC）；适合低延迟请求-响应。
- 异步事件：消息队列/日志（Kafka、NATS JetStream）；天然背压与解耦。
- 流式双工：gRPC streaming/WebSocket；用于持续数据与反压信号。
- 选择指南：
  - 强一致、低延迟：RPC + 有界重试 + 限流/超时。
  - 高解耦、弹性：事件驱动 + 有界主题/分区背压 + 幂等消费。

## 一致性与事务

- CAP/PACELC：在分区发生时的可用性与一致性权衡；平时延迟与一致性权衡。
- 事务模型：2PC、3PC、Sagas（编排/舞蹈）、Outbox/Inbox、幂等键。
- 读一致性：单调读、读己之写、会话一致；可通过读路由与版本向量实现。
- 失败与不可能性：FLP（异步系统中确定性共识不可能）、拜占庭失败；通过随机化、超时与视图变更取得工程可用的近似保证。

## 复制与共识

- 主从/主备、Quorum（N/2+1）、多主 CRDT、基于日志复制（Raft/Paxos）。
- 选择：
  - 强一致：Raft + 线性一致读写；
  - 最终一致：CRDT + 去中心化合并 + 冲突可交换。
- 读写路径优化：只读租约（lease read）、乐观读 + 版本校验；写合并与批量提交降低复制开销。

## 背压与限流（系统稳态）

- 入站：有界队列、令牌桶/漏桶、优先级与公平性、按类隔离。
- 出站：并发上限、批处理、超时/重试（退避+jitter）、熔断降级。
- 观测：到达率 λ、服务率 μ、丢弃率 p_drop、P99 延迟、队列长度 L。
- 舱壁与隔离：按租户/优先级/业务域划分隔离池，避免级联失效与资源抢占。

## 多线程/多任务与微服务边界

- 服务边界：按一致性域/数据所有权/变更频率划分，避免跨边界事务。
- 计算形态：
  - I/O 密集：async/Tokio + `tower` 中间件；
  - CPU 密集：线程池/`spawn_blocking`/Rayon；
  - 混合：异步外壳 + 同步内核（明确定义阻塞边界）。
- 数据通道与一致性边界：跨服务避免分布式事务；以事件驱动 + 编排补偿实现最终一致。

## Rust 1.90 落地映射

- 语言/库：
  - `async/await` 状态机；`Send`/`Sync` 边界；`Pin` 自引用安全；常量泛型 `_` 推断。
  - Tokio：`mpsc`、`Semaphore`、`JoinSet`、`timeout`、`spawn_blocking`。
  - `tower`：`Buffer`、`RateLimit`、`ConcurrencyLimit`、`Timeout`、`Retry`、`LoadShed`。
  - 服务栈：`axum`/`hyper`、`tonic`、`tracing` + OpenTelemetry、`metrics`。
  - 存储：`sqlx`/`sea-orm`（连接池上限 + 超时）/`redis`（管道/批处理）。
- 工程守护：在入口/出口与内部调用路径统一使用 `tower::{LoadShed,RateLimit,Timeout,Retry,ConcurrencyLimit,Buffer}` 组合，形成立体稳态保护。

## 参考设计蓝图

```text
Client → API Gateway → (Service A) → (Service B) → DB_B
                    ↘               ↘            ↘
                      Event Bus → (Service C) → DB_C
```

- A→B：RPC（gRPC），A→Bus：事件；B/C 订阅处理，按分区并发；所有出站均 `timeout+retry+jitter`。
- 失败注入：在灰度/预生产环境启用延迟/错误注入，验证限流、重试、降级与补偿的有效性。

## 检查清单

- 明确每条通路的背压与容量；所有队列有上界与溢出策略。
- 定义取消、超时、重试与熔断策略；幂等键与去重窗口。
- 记录端到端 trace 与关键指标；基于 SLO 的保护阈值（限流/负载卸载）。
- 验证 FLP 边界与网络分区策略；开展故障演练覆盖 broker、DB、下游依赖。

## 事务与编排（补充）

- Sagas：编排（中心协调器）与舞蹈（去中心）两类；在 Rust 中以工作流状态机实现，补偿动作需具备幂等与可重入性。
- Outbox/Inbox：服务内以事务提交事件到 Outbox，异步转发至总线；Inbox 去重窗口以幂等键实现。

### Rust 1.90 落地要点

- RPC 路径：`tonic` + `tower` 中间件（`Timeout`/`Retry`/`LoadShed`/`ConcurrencyLimit`）。
- 事件路径：Kafka/NATS 客户端设置有界缓冲与批处理；消费者按照分区并发，控制最大在途消息。
- 可观测：`tracing` + OpenTelemetry 注入 trace id，端到端关联 RPC 与事件。
