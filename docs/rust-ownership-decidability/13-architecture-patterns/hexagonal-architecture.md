# 六边形架构 (Hexagonal Architecture)

## 核心概念

```text
      驱动适配器        应用服务层        被驱动适配器
   (HTTP/CLI/消息)    (编排/协调)      (数据库/外部API)
          │                 │                 ▲
          ▼                 ▼                 │
   ┌──────────────────────────────────────────────┐
   │                 领域层 (核心)                 │
   │  ┌──────────────────────────────────────┐    │
   │  │  - 实体 (Entity)                      │    │
   │  │  - 值对象 (Value Object)              │    │
   │  │  - 领域服务 (Domain Service)          │    │
   │  │  - 仓库接口 (Repository Port)         │    │
   │  └──────────────────────────────────────┘    │
   └──────────────────────────────────────────────┘
```

## Rust实现

### 1. 领域层

```rust
pub struct Order {
    id: OrderId,
    items: Vec<OrderLine>,
    status: OrderStatus,
}

impl Order {
    pub fn add_item(&mut self, line: OrderLine) -> Result<(), OrderError> {
        if self.status != OrderStatus::Pending {
            return Err(OrderError::AlreadyConfirmed);
        }
        self.items.push(line);
        Ok(())
    }
}

// 端口定义
#[async_trait]
pub trait OrderRepository: Send + Sync {
    async fn by_id(&self, id: OrderId) -> Result<Option<Order>, Error>;
    async fn save(&self, order: &Order) -> Result<(), Error>;
}
```

### 2. 应用服务层

```rust
pub struct OrderApplicationService {
    order_repo: Arc<dyn OrderRepository>,
    event_pub: Arc<dyn EventPublisher>,
}

impl OrderApplicationService {
    pub async fn create_order(&self, cmd: CreateOrderCommand) -> Result<OrderId, Error> {
        let mut order = Order::new(cmd.customer_id);
        for item in cmd.items {
            order.add_item(item)?;
        }
        self.order_repo.save(&order).await?;
        self.event_pub.publish(DomainEvent::OrderCreated { ... }).await?;
        Ok(order.id())
    }
}
```

### 3. 适配器实现

```rust
pub struct PostgresOrderRepository { pool: PgPool }

#[async_trait]
impl OrderRepository for PostgresOrderRepository {
    async fn save(&self, order: &Order) -> Result<(), Error> {
        sqlx::query("INSERT INTO orders ...")
            .bind(order.id())
            .execute(&self.pool).await?;
        Ok(())
    }
}
```

## 依赖注入

```rust
// main.rs
let order_repo: Arc<dyn OrderRepository> = Arc::new(PostgresOrderRepository::new(pool));
let event_pub: Arc<dyn EventPublisher> = Arc::new(KafkaEventPublisher::new(kafka));
let service = Arc::new(OrderApplicationService::new(order_repo, event_pub));
```
