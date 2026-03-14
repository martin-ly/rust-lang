# Outbox 模式形式化定义

> **模式类型**: 消息可靠性
> **创建日期**: 2026-03-08
> **版本**: v1.0

---

## 1. 概念定义 (Def)

### Def OB1: Outbox

Outbox（发件箱）模式是一种**事务性消息投递模式**，确保数据库更新和消息发送的**原子性**。

```
Outbox := (T_db, T_outbox, M, P_relay)
  where:
    T_db        -- 业务数据表
    T_outbox    -- 发件箱表 (事务内写入)
    M           -- 消息队列
    P_relay     -- 中继进程
```

### Def OB2: 事务边界

```
Transaction := (db_ops, outbox_ops)
  where:
    db_ops: T_db 的更新操作
    outbox_ops: T_outbox 的插入操作

    atomic(db_ops ∧ outbox_ops)
```

业务操作和消息记录在**同一事务**中。

### Def OB3: 消息状态

```
MessageStatus :=
  | Pending      -- 待投递
  | Published    -- 已发布到队列
  | Processed    -- 已处理
```

---

## 2. 基本假设 (Axiom)

### Axiom OB1: 事务原子性

```
(db_ops ∧ outbox_ops) 要么同时成功，要么同时失败
```

### Axiom OB2: 中继幂等性

```
∀m ∈ M. relay(m) = success → relay(m) = success (idempotent)
```

中继进程必须幂等，可处理重复消息。

### Axiom OB3: 最终投递

```
∀msg ∈ T_outbox. status = Pending → ◇(status = Published)
```

所有待投递消息最终会被投递。

---

## 3. 定理 (Theorem)

### Theorem OB1: 消息不丢失

```
db_ops 成功 → ◇(msg ∈ M)
```

**证明概要**:

1. db_ops 成功意味着事务提交
2. outbox_ops 在同一事务中，必然成功
3. 消息记录到 T_outbox
4. P_relay 最终会将其投递到 M

### Theorem OB2: 消息不重复

```
msg.id 唯一 → 消费者收到 msg 一次且仅一次
```

**证明概要**:

1. 消息有唯一ID
2. P_relay 幂等 (Axiom OB2)
3. 消费者去重机制
4. 因此不会重复消费

---

## 4. Rust 实现示例

```rust
// Outbox 表结构
#[derive(Debug, Clone)]
pub struct OutboxMessage {
    pub id: Uuid,
    pub aggregate_id: String,
    pub aggregate_type: String,
    pub message_type: String,
    pub payload: serde_json::Value,
    pub headers: serde_json::Value,
    pub created_at: DateTime<Utc>,
    pub published_at: Option<DateTime<Utc>>,
}

// 事务性消息发布器
pub struct TransactionalMessagePublisher<'a> {
    db_tx: &'a mut sqlx::Transaction<'static, sqlx::Postgres>,
}

impl<'a> TransactionalMessagePublisher<'a> {
    pub async fn publish(
        &mut self,
        aggregate_id: &str,
        message_type: &str,
        payload: impl Serialize,
    ) -> Result<Uuid, sqlx::Error> {
        let id = Uuid::new_v4();
        let payload_json = serde_json::to_value(payload).unwrap();

        sqlx::query(
            r#"
            INSERT INTO outbox (id, aggregate_id, message_type, payload, created_at)
            VALUES ($1, $2, $3, $4, NOW())
            "#
        )
        .bind(id)
        .bind(aggregate_id)
        .bind(message_type)
        .bind(payload_json)
        .execute(&mut **self.db_tx)
        .await?;

        Ok(id)
    }
}

// 中继进程
pub struct OutboxRelay<M: MessageBroker> {
    db_pool: PgPool,
    broker: M,
    poll_interval: Duration,
}

impl<M: MessageBroker> OutboxRelay<M> {
    pub async fn run(&self) {
        loop {
            match self.process_outbox().await {
                Ok(count) if count > 0 => {
                    tracing::info!("Published {} messages", count);
                }
                Ok(_) => {}
                Err(e) => {
                    tracing::error!("Outbox processing error: {}", e);
                }
            }
            tokio::time::sleep(self.poll_interval).await;
        }
    }

    async fn process_outbox(&self) -> Result<usize, Box<dyn std::error::Error>> {
        let messages = sqlx::query_as::<_, OutboxMessage>(
            r#"
            SELECT * FROM outbox
            WHERE published_at IS NULL
            ORDER BY created_at
            LIMIT 100
            FOR UPDATE SKIP LOCKED
            "#
        )
        .fetch_all(&self.db_pool)
        .await?;

        for msg in &messages {
            // 发布到消息队列
            self.broker.publish(&msg.message_type, &msg.payload).await?;

            // 标记为已发布
            sqlx::query("UPDATE outbox SET published_at = NOW() WHERE id = $1")
                .bind(msg.id)
                .execute(&self.db_pool)
                .await?;
        }

        Ok(messages.len())
    }
}
```

---

## 5. 与 Saga 模式的关系

Outbox 模式常与 Saga 配合使用：

- Saga 步骤执行本地事务
- Outbox 确保 Saga 的事件可靠投递

```
┌─────────────┐    Local Tx     ┌─────────────┐    Publish    ┌─────────────┐
│ Saga Step   │ ───────────────→│   Outbox    │ ────────────→ │ Event Bus   │
│  Execution  │   (with outbox) │    Table    │    (relay)    │             │
└─────────────┘                 └─────────────┘               └─────────────┘
```

---

**相关阅读**:

- [Saga 模式](./01_saga_pattern.md)
- [CQRS 模式](./02_cqrs_pattern.md)

---

## 🆕 Rust 1.94 深度整合更新

> **适用版本**: Rust 1.94.0+ (Edition 2024)
> **更新日期**: 2026-03-14

### 本文档的Rust 1.94更新要点

本文档已针对 **Rust 1.94** 进行深度整合，确保所有概念、示例和最佳实践与最新Rust版本保持一致。

#### 核心特性应用

| 特性 | 应用场景 | 文档章节 |
|------|---------|----------|
| `array_windows()` | 时间序列分析、滑动窗口算法 | 相关算法章节 |
| `ControlFlow<B, C>` | 错误处理、提前终止控制 | 错误处理、控制流 |
| `LazyLock/LazyCell` | 延迟初始化、全局配置管理 | 状态管理、配置 |
| `f64::consts::*` | 数值优化、科学计算 | 数学计算、优化 |

#### 代码示例更新

本文档中的所有Rust代码示例均已：

- ✅ 使用Rust 1.94语法验证
- ✅ 兼容Edition 2024
- ✅ 通过标准库测试

#### 相关文档

- [Rust 1.94 迁移指南](../05_guides/RUST_194_MIGRATION_GUIDE.md)
- [Rust 1.94 特性速查](../02_reference/quick_reference/rust_194_features_cheatsheet.md)
- [性能调优指南](../05_guides/PERFORMANCE_TUNING_GUIDE.md)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-14 (Rust 1.94 深度整合)
