# 分布式模式概念族谱 - 思维导图

> **创建日期**: 2026-02-21
> **最后更新**: 2026-02-21
> **状态**: 🔄 新建
> **对应任务**: P1-T11

---

## 全局思维导图

```
                        分布式模式概念族
                               │
        ┌──────────────────────┼──────────────────────┐
        │                      │                      │
   【事务模式】              【容错模式】            【通信模式】
        │                      │                      │
    ├─Saga模式             ├─熔断器模式           ├─消息队列
    │  ├─编排式              │  ├─Closed状态        │  ├─点对点
    │  ├─编制式              │  ├─Open状态          │  └─发布订阅
    │  ├─向后补偿             │  └─Half-Open状态      ├─RPC
    │  └─向前补偿             ├─舱壁模式             │  ├─gRPC
    ├─CQRS模式               │  └─资源隔离           │  └─Thrift
    │  ├─命令端              ├─超时模式              └─事件流
    │  ├─查询端              │  ├─固定超时            ├─Kafka
    │  └─事件溯源            │  └─自适应超时          ├─Pulsar
    ├─2PC/3PC                └─重试模式               └─NATS
    │  ├─准备阶段              ├─立即重试
    │  ├─提交阶段              ├─固定间隔
    │  └─协调者                └─指数退避
    └─Outbox模式
       ├─事务性发件箱
       └─中继进程
```

---

## 详细概念族谱

### 1. Saga 模式族

```
                            Saga模式
                               │
            ┌──────────────────┼──────────────────┐
            │                  │                  │
       【协调方式】          【补偿策略】        【适用场景】
            │                  │                  │
        ├─编排式            ├─向后补偿         ├─长事务
        │  └─中央协调器        │  └─撤销已执行     ├─跨服务事务
        └─编制式            └─向前补偿         └─最终一致性
           └─事件驱动            └─继续执行
```

**核心概念**:
- **Saga**: 由多个本地事务组成的长事务，每个本地事务有对应的补偿操作
- **补偿 (Compensation)**: 当 Saga 中某个步骤失败时，用于撤销之前步骤效果的操作
- **编排 (Orchestration)**: 由中央协调器控制 Saga 的执行流程
- **编制 (Choreography)**: 各服务通过事件交换自发协调 Saga 流程

**形式化定义** (Coq):
```coq
Record SagaStep := mkSagaStep {
  step_id : TxId;
  step_action : Value -> OpResult;
  step_compensation : Value -> OpResult
}.
```

---

### 2. CQRS 模式族

```
                            CQRS模式
                               │
            ┌──────────────────┼──────────────────┐
            │                  │                  │
       【命令端】            【查询端】          【一致性】
            │                  │                  │
        ├─写模型            ├─读模型           ├─强一致性
        │  ├─验证              ├─物化视图        ├─最终一致性
        │  ├─业务逻辑          ├─查询优化        └─有界陈旧性
        │  └─事件发布          └─读取扩展
        └─事件存储
           ├─追加-only
           └─不可变
```

**核心概念**:
- **命令 (Command)**: 改变系统状态的意图，如 "创建订单"
- **查询 (Query)**: 读取系统状态的请求，不引起副作用
- **事件溯源 (Event Sourcing)**: 将状态变化存储为事件序列
- **物化视图 (Materialized View)**: 为查询优化的预计算视图

**形式化定义** (Coq):
```coq
Record CQRSSystem := mkCQRSSystem {
  cqrs_event_store : EventStore;
  cqrs_read_model : ReadModel;
  cqrs_projection : EventStore -> ReadModel
}.
```

---

### 3. 熔断器模式族

```
                         熔断器模式
                               │
            ┌──────────────────┼──────────────────┐
            │                  │                  │
       【状态】              【触发条件】        【恢复策略】
            │                  │                  │
        ├─Closed            ├─失败阈值         ├─超时恢复
        │  └─正常调用          │  └─N次失败       ├─半开探测
        ├─Open              ├─错误率阈值        └─渐进恢复
        │  └─快速失败          └─超过X%
        └─Half-Open         └─响应时间阈值
           └─试探调用
```

**核心概念**:
- **熔断 (Circuit Breaker)**: 防止故障扩散的代理模式
- **失败阈值 (Failure Threshold)**: 触发熔断的失败次数
- **超时 (Timeout)**: 熔断后尝试恢复的等待时间
- **半开 (Half-Open)**: 试探性恢复状态

---

## 概念关系矩阵

| 概念A | 关系 | 概念B | 说明 |
|:---|:---:|:---|:---|
| Saga | 使用 | 补偿 | Saga 通过补偿实现原子性 |
| Saga | 结合 | 熔断器 | 防止 Saga 参与者级联故障 |
| CQRS | 使用 | 事件溯源 | 命令端生成事件，查询端消费 |
| 事件溯源 | 支持 | Saga | Saga 审计日志基于事件溯源 |
| 熔断器 | 保护 | RPC | 防止 RPC 调用无限阻塞 |
| 消息队列 | 实现 | 编制式Saga | 事件驱动通信 |
| 2PC | 替代 | Saga | 强一致性 vs 最终一致性 |

---

## 与其他概念族的关系

```
                    分布式模式概念族
                           │
        ┌──────────────────┼──────────────────┐
        │                  │                  │
   【并发模式】          【所有权模式】      【类型系统】
        │                  │                  │
    ├─Actor            ├─Send/Sync        ├─泛型
    ├─锁                │  └─跨线程传递     ├─Trait对象
    └─无锁              └─Arc<RwLock>      └─生命周期
        │                      │
        └──────────────────────┘
                  │
           【Rust实现】
           ├─tokio::sync
           ├─async-trait
           └─serde
```

---

## Rust 实现映射

| 模式 | Rust 实现 | Crate |
|:---|:---|:---|
| Saga | Result + 闭包补偿 | 原生 |
| CQRS | 事件流 + 物化视图 | eventstore |
| 熔断器 | 状态机 + 计数器 | resilience4j-rust |
| 消息队列 | 异步生产者/消费者 | lapin, rdkafka |
| RPC | tonic (gRPC) | tonic |
| 事件溯源 | eventstore | eventstore |

---

## 相关文档

- [Coq 形式化定义](../coq_skeleton/DISTRIBUTED_PATTERNS.v)
- [Saga 详细说明](../../software_design_theory/04_compositional_engineering/README.md)
- [CQRS 实现指南](../../../docs/05_guides/DISTRIBUTED_SYSTEMS_GUIDE.md)

---

**维护者**: Rust Formal Methods Research Team  
**对应任务**: P1-T11 - 分布式模式概念族谱新建
