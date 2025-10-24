# 模型分层总览（Rust 1.90 视角）

> 覆盖范围：语言语义模型、并发/异步模型、算法模型、分布式与微服务架构模型，以及它们在 Rust 1.90 的工程落地与等价关系。

---

## 📊 目录

- [模型分层总览（Rust 1.90 视角）](#模型分层总览rust-190-视角)
  - [📊 目录](#-目录)
  - [📋 目录](#-目录-1)
  - [分层框架](#分层框架)
  - [同步与异步：分类与等价](#同步与异步分类与等价)
  - [背压与消息队列](#背压与消息队列)
  - [递归异步与结构化并发](#递归异步与结构化并发)
  - [算法模型关系图谱](#算法模型关系图谱)
  - [分布式与微服务](#分布式与微服务)
  - [Rust 1.90 落地映射（精选）](#rust-190-落地映射精选)
  - [检查清单（Checklists）](#检查清单checklists)
  - [参阅文档](#参阅文档)

## 📋 目录

- [模型分层总览（Rust 1.90 视角）](#模型分层总览rust-190-视角)
  - [📊 目录](#-目录)
  - [📋 目录](#-目录-1)
  - [分层框架](#分层框架)
  - [同步与异步：分类与等价](#同步与异步分类与等价)
  - [背压与消息队列](#背压与消息队列)
  - [递归异步与结构化并发](#递归异步与结构化并发)
  - [算法模型关系图谱](#算法模型关系图谱)
  - [分布式与微服务](#分布式与微服务)
  - [Rust 1.90 落地映射（精选）](#rust-190-落地映射精选)
  - [检查清单（Checklists）](#检查清单checklists)
  - [参阅文档](#参阅文档)

---

## 分层框架

- 语义层（What）：操作/指称/公理语义，类型系统与内存模型（`Send`/`Sync`/`Pin`）。
- 并发层（How）：线程/任务、结构化并发、消息传递、背压、取消与超时。
- 算法层（Logic）：分治/动规/贪心/图与流/随机化/在线/流式算法。
- 架构层（Shape）：CSP/Actor、事件驱动、RPC、分布式一致性与事务、微服务拓扑。
- 工程层（With）：Tokio、tower、axum/tonic、tracing/OTel、Kafka/NATS、Rayon。

## 同步与异步：分类与等价

- 控制流载体：同步以调用栈为主；异步以状态机 + Waker 驱动。
- 等价视角：可观测等价可通过 trace/bisimulation 校验；性能不保证等价。
- 工程映射：阻塞边界用 `spawn_blocking`；I/O 改用 `tokio` 等价 API；生命周期以 `JoinSet`/`scope` 管理。

## 背压与消息队列

- 策略：容量上限、令牌桶/漏桶、信用窗口、优先级/公平性。
- Rust 生态：`tokio::mpsc`、`async-channel`、`tower::{Buffer,RateLimit,ConcurrencyLimit,Timeout,Retry}`。
- 指标：λ、μ、ρ、L、W、p_drop、P99；目标保持 `ρ < 1` 或引入降级/丢弃/采样。

## 递归异步与结构化并发

- 避免自引用的 `async fn` 递归：改用显式栈/队列迭代或分治 + 并发上限。
- 取消与超时：所有外部 I/O 设置 `timeout`；父级取消向下传播；预算与度量确保可终止性。

## 算法模型关系图谱

- 并行复杂度：工作-跨度（W,D）与 Amdahl/Gustafson；优先降低 D。
- 关系映射：
  - 分治 ↔ 任务树/Join；动规 ↔ 分块波前；贪心 ↔ 流水线；回溯 ↔ 分支并发 + 剪枝；
  - 图/流 ↔ 背压/容量约束；随机化 ↔ 采样/分位数速估；在线/流式 ↔ 批处理/窗口化。

## 分布式与微服务

- 通信范式：RPC、事件、流式双工；根据一致性/延迟/解耦选择。
- 一致性与事务：CAP/PACELC、2PC/3PC、Sagas、Outbox/Inbox、幂等键。
- 复制与共识：Quorum、Raft、CRDT；按一致性需求选择线性一致或最终一致。

## Rust 1.90 落地映射（精选）

| 主题 | API/类型 | 要点 |
|------|---------|------|
| 异步执行 | `async/await`, `JoinSet`, `spawn_blocking` | 状态机 + 边界阻塞隔离 |
| 通道与背压 | `tokio::mpsc`, `async-channel` | 有界容量、`try_send`/`reserve` |
| 限流/超时/重试 | `tower::{RateLimit,Timeout,Retry,ConcurrencyLimit}` | 端到端稳态 |
| 取消 | `tokio::time::timeout` | 显式设置并向下传播 |
| 初始化 | `OnceLock` | 线程安全一次初始化 |

## 检查清单（Checklists）

- 是否存在阻塞驻留在异步路径？若是，迁移或 `spawn_blocking` 隔离。
- 是否定义队列容量与溢出策略？记录 p_drop 与 P99。
- 是否为每条通路配置 `timeout+retry+jitter+limit`？
- 是否具备端到端 tracing 与关键指标？

---

## 参阅文档

- 并发/异步分类与等价：`../concurrency/async-sync-classification.md`
- 背压模型：`../concurrency/backpressure-models.md`
- 递归异步：`../concurrency/async-recursion.md`
- 算法模型关系：`../algorithms/models.md`
- 分布式与微服务：`../architecture/distributed-design.md`
