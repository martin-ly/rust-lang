# 分布式系统概念族谱

> **创建日期**: 2026-03-08
> **版本**: v1.0
> **描述**: 分布式系统核心模式与概念的完整族谱

---

## 🧬 核心概念族谱

```mermaid
mindmap
  root((分布式系统))
    事务模式
      Saga模式
        编排式 Saga
        协调式 Saga
        补偿操作
      长事务 LRT
        持久化点
        状态恢复
    数据模式
      CQRS
        命令端
        查询端
        事件投影
      Event Sourcing
        事件存储
        状态重建
        事件不可变
      Outbox模式
        事务性消息
        中继进程
    容错模式
      Circuit Breaker
        Closed
        Open
        HalfOpen
      重试模式
        固定间隔
        指数退避
        抖动策略
      超时模式
        连接超时
        请求超时
      Fallback
        静态降级
        缓存降级
        简化逻辑
    一致性模型
      强一致性
      最终一致性
      因果一致性
      读己之写
    通信模式
      同步 RPC
      异步消息
      事件驱动
      发布订阅
```

---

## 📊 概念关系矩阵

| 概念A | 关系 | 概念B | 说明 |
|-------|------|-------|------|
| Saga | uses | Compensation | Saga使用补偿保证一致性 |
| CQRS | combines with | Event Sourcing | 常组合使用 |
| Outbox | ensures | Exactly Once | Outbox保证恰好一次投递 |
| Circuit Breaker | protects | Remote Service | 熔断器保护远程服务 |
| Retry | complements | Timeout | 重试与超时配合 |
| Fallback | triggered by | Circuit Breaker | 熔断触发降级 |

---

## 🎯 核心定理映射

| 定理编号 | 定理名称 | 相关概念 |
|----------|----------|----------|
| T-SG1 | Saga最终一致性定理 | Saga |
| T-CQ1 | CQRS读写分离定理 | CQRS |
| T-CB1 | 熔断故障隔离定理 | Circuit Breaker |
| T-OB1 | Outbox消息不丢失定理 | Outbox |
| T-ES1 | Event Sourcing可重现性定理 | Event Sourcing |

---

## 🌿 概念层次结构

### Level 1: 基础模式

- Saga 事务
- CQRS 读写分离
- Event Sourcing 事件溯源

### Level 2: 容错机制

- Circuit Breaker 熔断
- Retry 重试
- Timeout 超时
- Fallback 降级

### Level 3: 消息可靠性

- Outbox 发件箱
- Idempotency 幂等性
- Deduplication 去重

### Level 4: 一致性模型

- 强一致性
- 最终一致性
- CAP 权衡

---

## 🔗 与Rust示例的映射

| 概念 | 形式化定义 | Rust实现 |
|------|-----------|----------|
| Saga | `05_distributed/01_saga_pattern.md` | 见文档内代码 |
| CQRS | `05_distributed/02_cqrs_pattern.md` | 见文档内代码 |
| Circuit Breaker | `05_distributed/03_circuit_breaker.md` | 见文档内代码 |
| Event Sourcing | `05_distributed/04_event_sourcing.md` | 见文档内代码 |
| Outbox | `05_distributed/05_outbox_pattern.md` | 见文档内代码 |
| Retry | `05_distributed/07_retry_pattern.md` | 见文档内代码 |

---

## 📚 相关文档

- [Saga形式化定义](./software_design_theory/05_distributed/01_saga_pattern.md)
- [CQRS形式化定义](./software_design_theory/05_distributed/02_cqrs_pattern.md)
- [分布式架构决策树](./DISTRIBUTED_ARCHITECTURE_DECISION_TREE.md)
- [分布式模式矩阵](./DISTRIBUTED_PATTERNS_MATRIX.md)
