# Actor设计模式

> **从Akka到Rust：生产级Actor模式**

---

## 1. 基础模式

### 1.1 Ask vs Tell模式

```rust
// Tell模式 (Fire-and-Forget)
// 不等待响应，异步执行
actor.do_send(OrderCreated { id, items });

// Ask模式 (Request-Response)
// 等待响应，阻塞式
let result = actor.send(GetOrder { id }).await?;

// Ask带超时
let result = tokio::time::timeout(
    Duration::from_secs(5),
    actor.send(GetOrder { id })
).await??;
```

**选择指南**:

- **Tell**: 事件通知、日志记录、不需要响应的场景
- **Ask**: 需要结果、需要确认、同步需求场景

### 1.2 前摄模式 (Proactor Pattern)

```rust
// Actor主动发送消息给其他Actor
struct OrderActor {
    inventory: Addr<InventoryActor>,
    payment: Addr<PaymentActor>,
}

impl Handler<CreateOrder> for OrderActor {
    type Result = ResponseActFuture<Self, OrderResult>;

    fn handle(&mut self, msg: CreateOrder, ctx: &mut Context<Self>) -> Self::Result {
        let inventory = self.inventory.clone();
        let payment = self.payment.clone();

        async move {
            // 1. 检查库存
            let stock = inventory.send(CheckStock(msg.items)).await??;

            // 2. 扣减库存
            inventory.send(ReserveStock(msg.items)).await??;

            // 3. 处理支付
            let payment_result = payment.send(ProcessPayment(msg.payment)).await??;

            // 4. 确认订单
            OrderResult::Success(Order { ... })
        }
        .into_actor(self)
        .spawn(ctx)
    }
}
```

---

## 2. 监督模式

### 2.1 监督者模式

```rust
use bastion::prelude::*;

// 创建监督树
fn create_supervision_tree() {
    Bastion::supervisor(|sp| {
        sp.with_strategy(SupervisionStrategy::OneForOne)
          .with_restart_policy(RestartPolicy::TriesWithinDuration {
              tries: 3,
              duration: Duration::from_secs(60),
          })
    })
    .children(|ch| {
        ch.with_name("worker_pool")
          .with_redundancy(5)  // 5个实例
          .with_exec(worker_actor)
    })
    .children(|ch| {
        ch.with_name("coordinator")
          .with_exec(coordinator_actor)
    });
}

// 工作Actor
async fn worker_actor(ctx: BastionContext) -> Result<()> {
    loop {
        msg! { ctx.recv().await?,
            msg: WorkTask => {
                if let Err(e) = process_task(msg).await {
                    // 失败会让监督者重启这个Actor
                    panic!("Worker failed: {}", e);
                }
            }
            _: _ => {}
        }
    }
}
```

### 2.2 Circuit Breaker模式

```rust
use std::sync::atomic::{AtomicU32, Ordering};

struct CircuitBreakerActor {
    target: Addr<TargetActor>,
    failure_count: AtomicU32,
    state: CircuitState,
    threshold: u32,
    timeout: Duration,
}

enum CircuitState {
    Closed,     // 正常
    Open,       // 熔断
    HalfOpen,   // 测试恢复
}

impl Handler<CallRequest> for CircuitBreakerActor {
    type Result = ResponseFuture<Result<Response>>;

    fn handle(&mut self, msg: CallRequest, ctx: &mut Context<Self>) -> Self::Result {
        match self.state {
            CircuitState::Open => {
                // 快速失败
                Box::pin(async move {
                    Err(Error::CircuitOpen)
                })
            }
            CircuitState::Closed | CircuitState::HalfOpen => {
                let target = self.target.clone();
                let failure_count = self.failure_count.clone();
                let threshold = self.threshold;

                Box::pin(async move {
                    match tokio::time::timeout(
                        Duration::from_secs(5),
                        target.send(msg)
                    ).await {
                        Ok(Ok(response)) => {
                            // 成功，重置计数
                            failure_count.store(0, Ordering::SeqCst);
                            Ok(response)
                        }
                        _ => {
                            // 失败
                            let count = failure_count.fetch_add(1, Ordering::SeqCst);
                            if count + 1 >= threshold {
                                // 熔断
                            }
                            Err(Error::ServiceUnavailable)
                        }
                    }
                })
            }
        }
    }
}
```

---

## 3. 路由模式

### 3.1 负载均衡路由

```rust
struct LoadBalancerActor {
    workers: Vec<Addr<WorkerActor>>,
    current: AtomicUsize,
    strategy: LoadBalancingStrategy,
}

enum LoadBalancingStrategy {
    RoundRobin,
    Random,
    LeastBusy,
}

impl Handler<Task> for LoadBalancerActor {
    type Result = ResponseFuture<TaskResult>;

    fn handle(&mut self, msg: Task, ctx: &mut Context<Self>) -> Self::Result {
        let worker = match self.strategy {
            LoadBalancingStrategy::RoundRobin => {
                let idx = self.current.fetch_add(1, Ordering::SeqCst) % self.workers.len();
                &self.workers[idx]
            }
            LoadBalancingStrategy::Random => {
                let idx = rand::random::<usize>() % self.workers.len();
                &self.workers[idx]
            }
            LoadBalancingStrategy::LeastBusy => {
                // 查询每个worker的负载
                self.find_least_busy().await
            }
        };

        Box::pin(async move {
            worker.send(msg).await?
        })
    }
}
```

### 3.2 一致性哈希路由

```rust
struct ShardedActorSystem {
    shards: HashMap<u64, Addr<ShardActor>>,
    hasher: DefaultHasher,
}

impl ShardedActorSystem {
    fn route(&self, key: &str) -> &Addr<ShardActor> {
        let hash = self.hash_key(key);
        let shard_id = hash % self.shards.len() as u64;
        &self.shards[&shard_id]
    }

    fn hash_key(&self, key: &str) -> u64 {
        let mut hasher = self.hasher.clone();
        key.hash(&mut hasher);
        hasher.finish()
    }
}

// 使用
impl Handler<UserCommand> for ShardedActorSystem {
    fn handle(&mut self, msg: UserCommand, ctx: &mut Context<Self>) -> Self::Result {
        let shard = self.route(&msg.user_id);
        shard.send(msg)
    }
}
```

---

## 4. 状态管理模式

### 4.1 有限状态机 (FSM)

```rust
enum OrderState {
    Created,
    PendingPayment,
    Paid,
    Shipped,
    Delivered,
    Cancelled,
}

struct OrderActor {
    state: OrderState,
    order: Order,
}

impl Actor for OrderActor {
    fn handle(&mut self, msg: OrderCommand, ctx: &mut Context) {
        match (&self.state, msg) {
            (OrderState::Created, OrderCommand::Submit) => {
                self.state = OrderState::PendingPayment;
                // 启动支付计时器
            }
            (OrderState::PendingPayment, OrderCommand::Pay { amount }) => {
                if amount >= self.order.total {
                    self.state = OrderState::Paid;
                    // 通知仓库准备发货
                }
            }
            (OrderState::Paid, OrderCommand::Ship) => {
                self.state = OrderState::Shipped;
            }
            (OrderState::PendingPayment, OrderCommand::Timeout) => {
                self.state = OrderState::Cancelled;
            }
            _ => {
                // 无效状态转换
                ctx.sender().send(Error::InvalidStateTransition);
            }
        }
    }
}
```

### 4.2 Event Sourcing

```rust
struct EventSourcedActor {
    id: String,
    events: Vec<Event>,
    snapshot: Option<State>,
}

impl EventSourcedActor {
    fn apply_event(&mut self, event: Event) {
        self.events.push(event.clone());

        match event {
            Event::OrderCreated { items, .. } => {
                self.state.items = items;
            }
            Event::ItemAdded { item } => {
                self.state.items.push(item);
            }
            Event::ItemRemoved { item_id } => {
                self.state.items.retain(|i| i.id != item_id);
            }
            _ => {}
        }

        // 每100个事件创建快照
        if self.events.len() % 100 == 0 {
            self.create_snapshot();
        }
    }

    fn recover(&mut self, events: Vec<Event>) {
        for event in events {
            self.apply_event(event);
        }
    }
}
```

---

## 5. 通信模式

### 5.1 Pub-Sub模式

```rust
struct PubSubActor {
    subscribers: HashMap<String, Vec<Addr<SubscriberActor>>>,
}

impl PubSubActor {
    fn subscribe(&mut self, topic: String, subscriber: Addr<SubscriberActor>) {
        self.subscribers
            .entry(topic)
            .or_default()
            .push(subscriber);
    }

    fn publish(&self, topic: &str, message: Message) {
        if let Some(subscribers) = self.subscribers.get(topic) {
            for subscriber in subscribers {
                subscriber.do_send(message.clone());
            }
        }
    }
}
```

### 5.2 请求管道

```rust
// 管道: A -> B -> C -> D
struct PipelineStage<T, R> {
    next: Option<Addr<PipelineStage<R, FinalResult>>>,
    processor: Box<dyn Fn(T) -> R>,
}

impl<T, R> Handler<T> for PipelineStage<T, R> {
    fn handle(&mut self, msg: T, ctx: &mut Context) {
        let result = (self.processor)(msg);

        if let Some(next) = &self.next {
            next.send(result);
        } else {
            // 管道结束
        }
    }
}

// 构建管道
let stage_d = PipelineStage::new(final_processor, None);
let stage_c = PipelineStage::new(processor_c, Some(stage_d));
let stage_b = PipelineStage::new(processor_b, Some(stage_c));
let stage_a = PipelineStage::new(processor_a, Some(stage_b));
```

---

**维护者**: Rust Actor Patterns Team
**更新日期**: 2026-03-05
