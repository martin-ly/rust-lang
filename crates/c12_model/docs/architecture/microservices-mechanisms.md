# 微服务设计机制与并发/背压策略（Rust 1.90）

> 侧重机制与组合：命名、发现、配置、限流、超时、重试、熔断、隔离、舱壁、缓存、幂等、去重、编排/补偿、观测性、部署拓扑。


## 📊 目录

- [📋 目录](#目录)
- [机制清单与Rust落地](#机制清单与rust落地)
- [部署拓扑与流量治理](#部署拓扑与流量治理)
- [缓存与一致性](#缓存与一致性)
- [参考组合栈](#参考组合栈)
- [数据与一致性](#数据与一致性)
- [Rust 1.90 关键API](#rust-190-关键api)
- [检查清单](#检查清单)


## 📋 目录

- [微服务设计机制与并发/背压策略（Rust 1.90）](#微服务设计机制与并发背压策略rust-190)
  - [📋 目录](#-目录)
  - [机制清单与Rust落地](#机制清单与rust落地)
  - [部署拓扑与流量治理](#部署拓扑与流量治理)
  - [缓存与一致性](#缓存与一致性)
  - [参考组合栈](#参考组合栈)
  - [数据与一致性](#数据与一致性)
  - [Rust 1.90 关键API](#rust-190-关键api)
  - [检查清单](#检查清单)

## 机制清单与Rust落地

- 发现与配置：服务注册/配置中心；Rust 使用 `config` + `OnceLock` 初始化，读写分离只读快照。
- 入站稳态：`tower::limit::ConcurrencyLimit`, `RateLimit`, `Buffer(K)`；BFF/API 网关前置限流。
- 出站稳态：`tower::Timeout` + `Retry`（退避 + jitter）+ `LoadShed`；连接池上限与超时（`sqlx`/`redis`）。
- 事件通路：Kafka/NATS 分区并发 + 有界批处理；消费端最大在途消息约束；幂等键与 Inbox 去重。
- 事务与一致性：Sagas（编排/舞蹈），Outbox/Inbox；幂等补偿；读一致性策略（单调读、读己之写）。
- 隔离与舱壁：按租户/业务域/优先级分队列与线程/任务池；避免级联放大。
- 观测性：`tracing` + OpenTelemetry；端到端 trace id 注入；关键指标（λ, μ, ρ, p_drop, P99）。

## 部署拓扑与流量治理

- 拓扑：多副本 + 区域/可用区分布；灰度/金丝雀与蓝绿发布；
- 治理：服务网格（断路、重试、超时、限流）与应用内 `tower` 策略对齐；
- 入口：API 网关前置身份鉴权/配额；就地限流保护下游；
- 出口：每个下游通路配置 `Timeout+Retry+jitter+LoadShed+ConcurrencyLimit`。

## 缓存与一致性

- 本地缓存：只读快照 + TTL；失效广播（Pub/Sub）；
- 分布式缓存：写穿/回写/旁路；幂等键 + 去重窗口；
- 读一致性：读己之写/会话一致通过路由粘性或版本向量保障；
- 数据新鲜度：按 SLO 设 TTL 与刷新阈值，降级到近似结果。

## 参考组合栈

```text
Ingress → [RateLimit] → [Auth] → [Buffer(K)] → Service → [Timeout+Retry+jitter] → Downstream
                                       ↘ metrics+tracing ↗
```

## 数据与一致性

- 复制：主从、Quorum、Raft；最终一致采用 CRDT/版本向量。
- 分区：按所有权/访问模式划分；跨区操作以异步编排与补偿。

## Rust 1.90 关键API

- `tokio::{mpsc, Semaphore, JoinSet, time::timeout, task::spawn_blocking}`
- `tower::{Buffer, RateLimit, ConcurrencyLimit, Timeout, Retry, LoadShed}`
- `axum`/`tonic`、`tracing` + OTel、`metrics`、`sqlx`/`sea-orm`、`redis`。

## 检查清单

- 每条通路是否声明容量、超时、重试、熔断、幂等、去重？
- 入站/出站是否对称配置背压与并发上限？
- 事件路径是否设批大小、最大在途、消费超时与重试退避？
- 指标与追踪是否覆盖关键路径并关联上下游？
- 发布流量是否支持灰度/回滚？缓存失效/一致性策略是否与事务/事件链路对齐？
