# 消息队列与背压模型

> 关联：`concurrency/async-sync-classification.md`、示例 `examples/async_backpressure_demo.rs`

## 背压为何重要

- 防止入站速率 > 出站处理能力导致内存膨胀与延迟爆炸。
- 将系统压力向上游反馈，实现稳态与可恢复性。

## 常见策略

- 固定容量队列：`bounded(n)`，满时阻塞/丢弃/覆盖。
- 令牌桶/漏桶：速率整形；`tower::limit::ConcurrencyLimit`、`RateLimit`。
- 信用/窗口：按消费确认发放额度（流控）。
- 优先级与公平性：多队列或加权轮询。
- 负载卸载（Load Shedding）：在超载时拒绝部分请求以保护尾延迟与核心服务。

## Rust 生态落地

- `async-channel::bounded(n)`：异步 MPMC，容量受限即自然背压。
- `tokio::sync::mpsc::channel(n)`：Tokio 原生 MPSC，支持 `try_send`/`reserve`。
- `tower` 中间件：`timeout`、`buffer`、`limit`、`retry` 组合构建稳定客户端/服务端。
- `tower::load_shed`：丢弃在超载时无法立即服务的请求，保护系统稳态。

## 建模要点

- 指标：到达率 λ、服务率 μ、队列长度 L、丢弃率 p_drop、99p 延迟。
- 不变量：有界内存；无饥饿；有界等待（若采用丢弃或降级）。
- 验证：基于 `loom` 的并发语义检查；属性测试覆盖边界条件。
- 稳态定义：在 `ρ < 1` 区域维持 P99 低于 SLO；超载区域采取丢弃/降级确保恢复性。

## 选择指南

- 延迟敏感：小容量 + 丢弃最新/最旧 + 降级路径。
- 吞吐优先：较大容量 + 批处理 + 并行消费（`ConcurrencyLimit`）。
- 有序性强：单队列 + 显式背压；或分片并保持分片内有序。
- 多租户：配额/权重限流 + 独立缓冲区（舱壁）避免干扰。

## 与排队论的连接

- M/M/1/K：容量 K 的有界系统；`ρ = λ/μ < 1` 为稳态必要条件。
- 背压等价于对有效到达率 λ_eff 的调节，使 `ρ_eff < 1`。

## 最佳实践清单

- 明确容量与溢出策略；度量丢弃比例。
- 拉模式优先（消费者驱动）或使用背压信号。
- 在 `tower` 客户端加入 `timeout + retry + jitter`。

## 消息队列与日志系统中的背压

- Kafka：分区为并行度单位；生产端 `batch.size`/`linger.ms`；消费端 `max.poll.interval.ms`、`max.in.flight.requests.per.connection` 控制；磁盘/网络拥塞时以 broker 端限流与磁盘队列作为自然背压。
- NATS JetStream：`Ack`/`Nak`/`Term` 信令驱动背压；基于 `MaxAckPending` 限制未确认消息；按 `Consumer` 配置并发与拉取窗口。

### 溢出策略对照

| 策略 | 行为 | 适用场景 | Rust 对应 |
|------|------|----------|-----------|
| 阻塞等待 | 生产者等待容量 | 吞吐优先、可接受延迟 | `send().await` 有界通道 |
| 丢弃最新 | 丢弃新入队项 | 实时流，重在新鲜度 | `try_send` + 自定义策略 |
| 丢弃最旧 | 淘汰旧项 | 缓存/传感器数据 | 环形缓冲/覆盖写 |
| 降级 | 产出低成本替代 | 降低压力维持稳态 | 热点关闭/采样 |
 | 负载卸载 | 拒绝新请求 | 保护尾延迟与核心路径 | `tower::load_shed` |

### 计算与指标

- 有界系统 M/M/1/K：阻塞或丢弃导致有效到达率 λ_eff = λ·(1 - p_block)。
- 观测：记录 `p_block/p_drop`、`L`、`W`、P99；将 `Retry` 纳入成功率分母计算避免指标造假。

## Rust 1.90 落地（中间件组合）

示意：在客户端和工作者两侧统一组合中间件，形成端到端稳态保护。

```text
Producer → [RateLimit] → [Buffer(K)] → Broker → Consumer → [ConcurrencyLimit] → Handler
                                       ↘ retry+timeout ↗
```

要点：

- 生产端设置最大并发与缓冲；消费端以 `ConcurrencyLimit` 与批处理吸收抖动。
- 超时+重试需加随机抖动（jitter），避免同步重试风暴。
- 与并发上限联动：在计算密集型环节使用 `Semaphore`/`spawn_blocking` 控制 CPU 竞争。
