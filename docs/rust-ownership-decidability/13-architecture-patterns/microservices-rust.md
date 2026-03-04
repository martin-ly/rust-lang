# 微服务架构模式 (Rust实现)

## 1. 服务边界与所有权

### 核心原则

```rust
// 服务作为所有权边界
mod order_service {
    pub struct OrderService {
        db: DatabasePool,
        event_bus: EventPublisher,
    }

    impl OrderService {
        // 每个请求处理都是所有权转移
        pub async fn create_order(
            &self,
            cmd: CreateOrderCommand
        ) -> Result<OrderId, OrderError> {
            let order = Order::new(cmd)?;
            let id = self.db.save(&order).await?;
            self.event_bus.publish(OrderCreated::from(&order)).await?;
            Ok(id)
        }
    }
}
```

## 2. 服务通信模式

```
API Gateway ←──HTTP/gRPC──→ Order Service
                               │
                      Kafka/RabbitMQ
                               ▼
                      Inventory Service
```

## 3. 断路器模式

```rust
pub struct CircuitBreaker {
    state: Arc<RwLock<CircuitState>>,
}

impl CircuitBreaker {
    pub async fn call<F, T, E>(&self, op: F) -> Result<T, CircuitError<E>>
    where F: FnOnce() -> Future<Output = Result<T, E>> {
        if !self.allow().await {
            return Err(CircuitError::Open);
        }
        match op().await {
            Ok(r) => { self.record_success().await; Ok(r) }
            Err(e) => { self.record_failure().await; Err(CircuitError::Inner(e)) }
        }
    }
}
```

## 4. CQRS

```rust
// 命令端 - 写操作
pub struct OrderCommandHandler {
    event_store: Arc<EventStore>,
}

// 查询端 - 读操作
pub struct OrderQueryHandler {
    projection_reader: ProjectionReader,
}
```

## 5. 事件溯源

```rust
#[derive(Serialize, Deserialize)]
pub enum OrderEvent {
    OrderCreated { id: OrderId, items: Vec<LineItem> },
    OrderPaid { id: OrderId, amount: Money },
}
```
