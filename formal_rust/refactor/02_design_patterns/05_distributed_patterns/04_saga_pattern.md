# Saga模式 (Saga Pattern)

## 1. 概述

### 1.1 模式定义

Saga模式是一种分布式事务管理设计模式，通过将长事务分解为一系列本地事务，每个本地事务都有对应的补偿操作，确保分布式系统的最终一致性。

### 1.2 核心概念

- **Saga**: 一个长事务，由多个本地事务组成
- **本地事务 (Local Transaction)**: 单个服务内的原子操作
- **补偿操作 (Compensation)**: 撤销本地事务的操作
- **协调器 (Coordinator)**: 管理Saga执行流程的组件
- **事件 (Event)**: 事务间通信的消息

## 2. 形式化定义

### 2.1 Saga模式五元组

**定义2.1 (Saga模式五元组)**
设 $SG = (T, C, E, S, R)$ 为Saga模式，其中：

- $T = \{t_1, t_2, ..., t_n\}$ 是本地事务集合
- $C = \{c_1, c_2, ..., c_n\}$ 是补偿操作集合
- $E = \{e_1, e_2, ..., e_m\}$ 是事件集合
- $S = \{pending, running, completed, failed, compensating\}$ 是状态集合
- $R = \{r_1, r_2, ..., r_k\}$ 是协调器集合

### 2.2 本地事务定义

**定义2.2 (本地事务)**
本地事务 $t_i = (id_i, service_i, operation_i, compensation_i, state_i)$，其中：

- $id_i$ 是事务唯一标识符
- $service_i$ 是服务名称
- $operation_i$ 是执行操作
- $compensation_i$ 是补偿操作
- $state_i \in S$ 是事务状态

### 2.3 Saga执行函数

**定义2.3 (Saga执行函数)**
Saga执行函数 $execute: SG \rightarrow \mathbb{B}$ 定义为：

$$execute(sg) = \begin{cases}
true & \text{if } \forall t \in sg.T: t.state = completed \\
false & \text{if } \exists t \in sg.T: t.state = failed
\end{cases}$$

## 3. 数学理论

### 3.1 Saga一致性理论

**定义3.1 (Saga一致性)**
Saga $sg$ 是一致的，当且仅当：

$$\forall t \in sg.T: (t.state = completed \land compensation\_applied(t) = false) \lor (t.state = failed \land compensation\_applied(t) = true)$$

**定理3.1.1 (Saga最终一致性)**
Saga模式保证分布式系统的最终一致性。

**证明**：
1. **前向恢复**: 如果所有事务成功，系统达到一致状态
2. **后向恢复**: 如果有事务失败，通过补偿操作回滚到初始状态
3. **补偿完整性**: 每个事务都有对应的补偿操作
4. **因此**: 系统最终达到一致状态

### 3.2 补偿理论

**定义3.2 (补偿函数)**
补偿函数 $compensate: T \rightarrow \mathbb{B}$ 定义为：

$$compensate(t) = \begin{cases}
true & \text{if } t.compensation() \text{ succeeds} \\
false & \text{otherwise}
\end{cases}$$

**定理3.2.1 (补偿幂等性)**
补偿操作是幂等的，多次执行产生相同结果。

**证明**：
1. 补偿操作设计为幂等操作
2. 多次执行不会产生副作用
3. 因此，补偿操作是幂等的

### 3.3 事件理论

**定义3.3 (事件处理函数)**
事件处理函数 $handle: E \times SG \rightarrow SG$ 定义为：

$$handle(e, sg) = sg' \text{ where } sg' \text{ is the updated saga}$$

**定理3.3.1 (事件顺序性)**
事件按照时间顺序处理，保证因果一致性。

**证明**：
1. 事件包含时间戳
2. 协调器按时间戳排序处理事件
3. 因此，事件处理保持顺序性

## 4. 核心定理

### 4.1 Saga正确性定理

**定理4.1 (Saga正确性)**
Saga模式 $SG$ 是正确的，当且仅当：

1. **事务原子性**: $\forall t \in T: t.state \in \{completed, failed\}$
2. **补偿完整性**: $\forall t \in T: \exists c \in C: c = t.compensation$
3. **状态一致性**: $\forall t \in T: (t.state = failed) \Rightarrow (compensate(t) = true)$
4. **事件完整性**: $\forall e \in E: handle(e, sg) \text{ is defined}$

**证明**：
1. **事务原子性**: 确保每个事务要么成功要么失败
2. **补偿完整性**: 确保每个事务都有对应的补偿操作
3. **状态一致性**: 确保失败的事务被正确补偿
4. **事件完整性**: 确保所有事件都能被正确处理

### 4.2 Saga性能定理

**定理4.2 (Saga性能)**
Saga模式的性能复杂度为：

- **事务执行**: $O(|T|)$ 时间复杂度
- **补偿执行**: $O(|T|)$ 时间复杂度
- **事件处理**: $O(\log|E|)$ 时间复杂度
- **状态管理**: $O(1)$ 平均时间复杂度

**证明**：
1. **事务执行**: 需要顺序执行所有本地事务
2. **补偿执行**: 需要逆序执行所有补偿操作
3. **事件处理**: 使用有序数据结构存储事件
4. **状态管理**: 状态更新是常数时间操作

## 5. Rust实现

### 5.1 基础实现

```rust
use std::collections::HashMap;
use std::sync::{Arc, RwLock};
use serde::{Deserialize, Serialize};
use tokio::time::{Duration, Instant};
use uuid::Uuid;

/// 事务状态
# [derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum TransactionState {
    Pending,
    Running,
    Completed,
    Failed,
    Compensating,
}

/// 本地事务
# [derive(Debug, Clone)]
pub struct LocalTransaction {
    pub id: String,
    pub service: String,
    pub operation: Box<dyn Fn() -> Result<(), Box<dyn std::error::Error>> + Send + Sync>,
    pub compensation: Box<dyn Fn() -> Result<(), Box<dyn std::error::Error>> + Send + Sync>,
    pub state: TransactionState,
    pub created_at: Instant,
}

impl LocalTransaction {
    pub fn new<F, G>(
        service: String,
        operation: F,
        compensation: G,
    ) -> Self
    where
        F: Fn() -> Result<(), Box<dyn std::error::Error>> + Send + Sync + 'static,
        G: Fn() -> Result<(), Box<dyn std::error::Error>> + Send + Sync + 'static,
    {
        Self {
            id: Uuid::new_v4().to_string(),
            service,
            operation: Box::new(operation),
            compensation: Box::new(compensation),
            state: TransactionState::Pending,
            created_at: Instant::now(),
        }
    }

    /// 执行事务
    pub async fn execute(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        self.state = TransactionState::Running;

        match (self.operation)() {
            Ok(()) => {
                self.state = TransactionState::Completed;
                Ok(())
            }
            Err(error) => {
                self.state = TransactionState::Failed;
                Err(error)
            }
        }
    }

    /// 执行补偿
    pub async fn compensate(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        self.state = TransactionState::Compensating;

        match (self.compensation)() {
            Ok(()) => {
                self.state = TransactionState::Completed;
                Ok(())
            }
            Err(error) => {
                self.state = TransactionState::Failed;
                Err(error)
            }
        }
    }
}

/// Saga事件
# [derive(Debug, Clone, Serialize, Deserialize)]
pub struct SagaEvent {
    pub id: String,
    pub saga_id: String,
    pub transaction_id: String,
    pub event_type: String,
    pub payload: String,
    pub timestamp: Instant,
}

/// Saga协调器
pub struct SagaCoordinator {
    sagas: Arc<RwLock<HashMap<String, Saga>>>,
    events: Arc<RwLock<Vec<SagaEvent>>>,
}

impl SagaCoordinator {
    pub fn new() -> Self {
        Self {
            sagas: Arc::new(RwLock::new(HashMap::new())),
            events: Arc::new(RwLock::new(Vec::new())),
        }
    }

    /// 创建Saga
    pub fn create_saga(&self, transactions: Vec<LocalTransaction>) -> String {
        let saga_id = Uuid::new_v4().to_string();
        let saga = Saga {
            id: saga_id.clone(),
            transactions,
            state: TransactionState::Pending,
            created_at: Instant::now(),
        };

        let mut sagas = self.sagas.write().unwrap();
        sagas.insert(saga_id.clone(), saga);

        saga_id
    }

    /// 执行Saga
    pub async fn execute_saga(&self, saga_id: &str) -> Result<(), Box<dyn std::error::Error>> {
        let mut sagas = self.sagas.write().unwrap();

        if let Some(saga) = sagas.get_mut(saga_id) {
            saga.state = TransactionState::Running;

            // 顺序执行事务
            for transaction in &mut saga.transactions {
                match transaction.execute().await {
                    Ok(()) => {
                        // 记录成功事件
                        self.record_event(saga_id, &transaction.id, "success", "").await;
                    }
                    Err(error) => {
                        // 记录失败事件
                        self.record_event(saga_id, &transaction.id, "failed", &error.to_string()).await;

                        // 执行补偿
                        self.compensate_saga(saga).await?;
                        return Err(error);
                    }
                }
            }

            saga.state = TransactionState::Completed;
            Ok(())
        } else {
            Err("Saga not found".into())
        }
    }

    /// 补偿Saga
    async fn compensate_saga(&self, saga: &mut Saga) -> Result<(), Box<dyn std::error::Error>> {
        // 逆序执行补偿操作
        for transaction in saga.transactions.iter_mut().rev() {
            if transaction.state == TransactionState::Completed {
                match transaction.compensate().await {
                    Ok(()) => {
                        self.record_event(&saga.id, &transaction.id, "compensated", "").await;
                    }
                    Err(error) => {
                        self.record_event(&saga.id, &transaction.id, "compensation_failed", &error.to_string()).await;
                        return Err(error);
                    }
                }
            }
        }

        Ok(())
    }

    /// 记录事件
    async fn record_event(&self, saga_id: &str, transaction_id: &str, event_type: &str, payload: &str) {
        let event = SagaEvent {
            id: Uuid::new_v4().to_string(),
            saga_id: saga_id.to_string(),
            transaction_id: transaction_id.to_string(),
            event_type: event_type.to_string(),
            payload: payload.to_string(),
            timestamp: Instant::now(),
        };

        let mut events = self.events.write().unwrap();
        events.push(event);
    }

    /// 获取Saga状态
    pub fn get_saga_state(&self, saga_id: &str) -> Option<TransactionState> {
        let sagas = self.sagas.read().unwrap();
        sagas.get(saga_id).map(|saga| saga.state.clone())
    }

    /// 获取事件历史
    pub fn get_events(&self, saga_id: &str) -> Vec<SagaEvent> {
        let events = self.events.read().unwrap();
        events
            .iter()
            .filter(|event| event.saga_id == saga_id)
            .cloned()
            .collect()
    }
}

/// Saga
# [derive(Debug, Clone)]
pub struct Saga {
    pub id: String,
    pub transactions: Vec<LocalTransaction>,
    pub state: TransactionState,
    pub created_at: Instant,
}
```

### 5.2 泛型实现

```rust
use std::collections::HashMap;
use std::sync::{Arc, RwLock};
use std::marker::PhantomData;

/// 泛型本地事务
pub struct GenericLocalTransaction<T, E> {
    pub id: String,
    pub service: String,
    pub operation: Box<dyn Fn() -> Result<T, E> + Send + Sync>,
    pub compensation: Box<dyn Fn() -> Result<(), E> + Send + Sync>,
    pub state: TransactionState,
    pub created_at: Instant,
    _phantom: PhantomData<(T, E)>,
}

impl<T, E> GenericLocalTransaction<T, E> {
    pub fn new<F, G>(
        service: String,
        operation: F,
        compensation: G,
    ) -> Self
    where
        F: Fn() -> Result<T, E> + Send + Sync + 'static,
        G: Fn() -> Result<(), E> + Send + Sync + 'static,
    {
        Self {
            id: Uuid::new_v4().to_string(),
            service,
            operation: Box::new(operation),
            compensation: Box::new(compensation),
            state: TransactionState::Pending,
            created_at: Instant::now(),
            _phantom: PhantomData,
        }
    }

    /// 执行事务
    pub async fn execute(&mut self) -> Result<T, E> {
        self.state = TransactionState::Running;

        match (self.operation)() {
            Ok(result) => {
                self.state = TransactionState::Completed;
                Ok(result)
            }
            Err(error) => {
                self.state = TransactionState::Failed;
                Err(error)
            }
        }
    }

    /// 执行补偿
    pub async fn compensate(&mut self) -> Result<(), E> {
        self.state = TransactionState::Compensating;

        match (self.compensation)() {
            Ok(()) => {
                self.state = TransactionState::Completed;
                Ok(())
            }
            Err(error) => {
                self.state = TransactionState::Failed;
                Err(error)
            }
        }
    }
}

/// 泛型Saga协调器
pub struct GenericSagaCoordinator<T, E> {
    sagas: Arc<RwLock<HashMap<String, GenericSaga<T, E>>>>,
    events: Arc<RwLock<Vec<SagaEvent>>>,
    _phantom: PhantomData<(T, E)>,
}

impl<T, E> GenericSagaCoordinator<T, E> {
    pub fn new() -> Self {
        Self {
            sagas: Arc::new(RwLock::new(HashMap::new())),
            events: Arc::new(RwLock::new(Vec::new())),
            _phantom: PhantomData,
        }
    }

    /// 创建泛型Saga
    pub fn create_saga(&self, transactions: Vec<GenericLocalTransaction<T, E>>) -> String {
        let saga_id = Uuid::new_v4().to_string();
        let saga = GenericSaga {
            id: saga_id.clone(),
            transactions,
            state: TransactionState::Pending,
            created_at: Instant::now(),
            _phantom: PhantomData,
        };

        let mut sagas = self.sagas.write().unwrap();
        sagas.insert(saga_id.clone(), saga);

        saga_id
    }

    /// 执行泛型Saga
    pub async fn execute_saga(&self, saga_id: &str) -> Result<Vec<T>, E> {
        let mut sagas = self.sagas.write().unwrap();

        if let Some(saga) = sagas.get_mut(saga_id) {
            saga.state = TransactionState::Running;
            let mut results = Vec::new();

            // 顺序执行事务
            for transaction in &mut saga.transactions {
                match transaction.execute().await {
                    Ok(result) => {
                        results.push(result);
                        self.record_event(saga_id, &transaction.id, "success", "").await;
                    }
                    Err(error) => {
                        self.record_event(saga_id, &transaction.id, "failed", "").await;

                        // 执行补偿
                        self.compensate_saga(saga).await?;
                        return Err(error);
                    }
                }
            }

            saga.state = TransactionState::Completed;
            Ok(results)
        } else {
            Err(self.create_saga_not_found_error())
        }
    }

    /// 补偿泛型Saga
    async fn compensate_saga(&self, saga: &mut GenericSaga<T, E>) -> Result<(), E> {
        // 逆序执行补偿操作
        for transaction in saga.transactions.iter_mut().rev() {
            if transaction.state == TransactionState::Completed {
                match transaction.compensate().await {
                    Ok(()) => {
                        self.record_event(&saga.id, &transaction.id, "compensated", "").await;
                    }
                    Err(error) => {
                        self.record_event(&saga.id, &transaction.id, "compensation_failed", "").await;
                        return Err(error);
                    }
                }
            }
        }

        Ok(())
    }

    /// 记录事件
    async fn record_event(&self, saga_id: &str, transaction_id: &str, event_type: &str, payload: &str) {
        let event = SagaEvent {
            id: Uuid::new_v4().to_string(),
            saga_id: saga_id.to_string(),
            transaction_id: transaction_id.to_string(),
            event_type: event_type.to_string(),
            payload: payload.to_string(),
            timestamp: Instant::now(),
        };

        let mut events = self.events.write().unwrap();
        events.push(event);
    }

    fn create_saga_not_found_error(&self) -> E {
        // 实现具体的错误创建逻辑
        unimplemented!()
    }
}

/// 泛型Saga
pub struct GenericSaga<T, E> {
    pub id: String,
    pub transactions: Vec<GenericLocalTransaction<T, E>>,
    pub state: TransactionState,
    pub created_at: Instant,
    _phantom: PhantomData<(T, E)>,
}
```

### 5.3 异步实现

```rust
use tokio::sync::RwLock as TokioRwLock;
use std::sync::Arc;

/// 异步Saga协调器
pub struct AsyncSagaCoordinator {
    sagas: Arc<TokioRwLock<HashMap<String, Saga>>>,
    events: Arc<TokioRwLock<Vec<SagaEvent>>>,
}

impl AsyncSagaCoordinator {
    pub fn new() -> Self {
        Self {
            sagas: Arc::new(TokioRwLock::new(HashMap::new())),
            events: Arc::new(TokioRwLock::new(Vec::new())),
        }
    }

    /// 异步创建Saga
    pub async fn create_saga(&self, transactions: Vec<LocalTransaction>) -> String {
        let saga_id = Uuid::new_v4().to_string();
        let saga = Saga {
            id: saga_id.clone(),
            transactions,
            state: TransactionState::Pending,
            created_at: Instant::now(),
        };

        let mut sagas = self.sagas.write().await;
        sagas.insert(saga_id.clone(), saga);

        saga_id
    }

    /// 异步执行Saga
    pub async fn execute_saga(&self, saga_id: &str) -> Result<(), Box<dyn std::error::Error>> {
        let mut sagas = self.sagas.write().await;

        if let Some(saga) = sagas.get_mut(saga_id) {
            saga.state = TransactionState::Running;

            // 顺序执行事务
            for transaction in &mut saga.transactions {
                match transaction.execute().await {
                    Ok(()) => {
                        self.record_event(saga_id, &transaction.id, "success", "").await;
                    }
                    Err(error) => {
                        self.record_event(saga_id, &transaction.id, "failed", &error.to_string()).await;

                        // 执行补偿
                        self.compensate_saga(saga).await?;
                        return Err(error);
                    }
                }
            }

            saga.state = TransactionState::Completed;
            Ok(())
        } else {
            Err("Saga not found".into())
        }
    }

    /// 异步补偿Saga
    async fn compensate_saga(&self, saga: &mut Saga) -> Result<(), Box<dyn std::error::Error>> {
        // 逆序执行补偿操作
        for transaction in saga.transactions.iter_mut().rev() {
            if transaction.state == TransactionState::Completed {
                match transaction.compensate().await {
                    Ok(()) => {
                        self.record_event(&saga.id, &transaction.id, "compensated", "").await;
                    }
                    Err(error) => {
                        self.record_event(&saga.id, &transaction.id, "compensation_failed", &error.to_string()).await;
                        return Err(error);
                    }
                }
            }
        }

        Ok(())
    }

    /// 异步记录事件
    async fn record_event(&self, saga_id: &str, transaction_id: &str, event_type: &str, payload: &str) {
        let event = SagaEvent {
            id: Uuid::new_v4().to_string(),
            saga_id: saga_id.to_string(),
            transaction_id: transaction_id.to_string(),
            event_type: event_type.to_string(),
            payload: payload.to_string(),
            timestamp: Instant::now(),
        };

        let mut events = self.events.write().await;
        events.push(event);
    }

    /// 异步获取Saga状态
    pub async fn get_saga_state(&self, saga_id: &str) -> Option<TransactionState> {
        let sagas = self.sagas.read().await;
        sagas.get(saga_id).map(|saga| saga.state.clone())
    }

    /// 异步获取事件历史
    pub async fn get_events(&self, saga_id: &str) -> Vec<SagaEvent> {
        let events = self.events.read().await;
        events
            .iter()
            .filter(|event| event.saga_id == saga_id)
            .cloned()
            .collect()
    }
}
```

## 6. 应用场景

### 6.1 电商订单处理

```rust
use std::sync::Arc;

/// 电商订单Saga
pub struct EcommerceOrderSaga {
    coordinator: Arc<SagaCoordinator>,
}

impl EcommerceOrderSaga {
    pub fn new(coordinator: Arc<SagaCoordinator>) -> Self {
        Self { coordinator }
    }

    /// 创建订单处理Saga
    pub fn create_order_saga(&self, order_id: &str, user_id: &str, amount: f64) -> String {
        let transactions = vec![
            // 1. 创建订单
            LocalTransaction::new(
                "order-service".to_string(),
                move || {
                    println!("Creating order: {}", order_id);
                    Ok(())
                },
                move || {
                    println!("Canceling order: {}", order_id);
                    Ok(())
                },
            ),
            // 2. 扣减库存
            LocalTransaction::new(
                "inventory-service".to_string(),
                move || {
                    println!("Deducting inventory for order: {}", order_id);
                    Ok(())
                },
                move || {
                    println!("Restoring inventory for order: {}", order_id);
                    Ok(())
                },
            ),
            // 3. 扣减余额
            LocalTransaction::new(
                "payment-service".to_string(),
                move || {
                    println!("Deducting balance for user: {}", user_id);
                    Ok(())
                },
                move || {
                    println!("Restoring balance for user: {}", user_id);
                    Ok(())
                },
            ),
        ];

        self.coordinator.create_saga(transactions)
    }

    /// 处理订单
    pub async fn process_order(&self, order_id: &str, user_id: &str, amount: f64) -> Result<(), Box<dyn std::error::Error>> {
        let saga_id = self.create_order_saga(order_id, user_id, amount);

        match self.coordinator.execute_saga(&saga_id).await {
            Ok(()) => {
                println!("Order processed successfully: {}", order_id);
                Ok(())
            }
            Err(error) => {
                println!("Order processing failed: {}", error);
                Err(error)
            }
        }
    }
}
```

### 6.2 银行转账

```rust
use std::sync::Arc;

/// 银行转账Saga
pub struct BankTransferSaga {
    coordinator: Arc<SagaCoordinator>,
}

impl BankTransferSaga {
    pub fn new(coordinator: Arc<SagaCoordinator>) -> Self {
        Self { coordinator }
    }

    /// 创建转账Saga
    pub fn create_transfer_saga(&self, from_account: &str, to_account: &str, amount: f64) -> String {
        let transactions = vec![
            // 1. 扣减源账户余额
            LocalTransaction::new(
                "account-service".to_string(),
                move || {
                    println!("Debiting account: {}", from_account);
                    Ok(())
                },
                move || {
                    println!("Crediting account: {}", from_account);
                    Ok(())
                },
            ),
            // 2. 增加目标账户余额
            LocalTransaction::new(
                "account-service".to_string(),
                move || {
                    println!("Crediting account: {}", to_account);
                    Ok(())
                },
                move || {
                    println!("Debiting account: {}", to_account);
                    Ok(())
                },
            ),
            // 3. 记录交易日志
            LocalTransaction::new(
                "transaction-service".to_string(),
                move || {
                    println!("Recording transaction");
                    Ok(())
                },
                move || {
                    println!("Removing transaction record");
                    Ok(())
                },
            ),
        ];

        self.coordinator.create_saga(transactions)
    }

    /// 执行转账
    pub async fn transfer(&self, from_account: &str, to_account: &str, amount: f64) -> Result<(), Box<dyn std::error::Error>> {
        let saga_id = self.create_transfer_saga(from_account, to_account, amount);

        match self.coordinator.execute_saga(&saga_id).await {
            Ok(()) => {
                println!("Transfer completed successfully");
                Ok(())
            }
            Err(error) => {
                println!("Transfer failed: {}", error);
                Err(error)
            }
        }
    }
}
```

## 7. 变体模式

### 7.1 事件驱动Saga

```rust
use std::sync::Arc;
use tokio::sync::mpsc;

/// 事件驱动Saga
pub struct EventDrivenSaga {
    coordinator: Arc<SagaCoordinator>,
    event_sender: mpsc::Sender<SagaEvent>,
}

impl EventDrivenSaga {
    pub fn new(coordinator: Arc<SagaCoordinator>) -> Self {
        let (event_sender, mut event_receiver) = mpsc::channel(100);

        // 启动事件处理器
        let coordinator_clone = coordinator.clone();
        tokio::spawn(async move {
            while let Some(event) = event_receiver.recv().await {
                Self::handle_event(&coordinator_clone, event).await;
            }
        });

        Self {
            coordinator,
            event_sender,
        }
    }

    /// 处理事件
    async fn handle_event(coordinator: &Arc<SagaCoordinator>, event: SagaEvent) {
        match event.event_type.as_str() {
            "success" => {
                println!("Transaction succeeded: {}", event.transaction_id);
            }
            "failed" => {
                println!("Transaction failed: {}", event.transaction_id);
                // 触发补偿
            }
            "compensated" => {
                println!("Transaction compensated: {}", event.transaction_id);
            }
            _ => {}
        }
    }

    /// 发送事件
    pub async fn send_event(&self, event: SagaEvent) -> Result<(), mpsc::error::SendError<SagaEvent>> {
        self.event_sender.send(event).await
    }
}
```

### 7.2 状态机Saga

```rust
use std::sync::Arc;

/// 状态机Saga
pub struct StateMachineSaga {
    coordinator: Arc<SagaCoordinator>,
    current_state: String,
    transitions: HashMap<String, Vec<String>>,
}

impl StateMachineSaga {
    pub fn new(coordinator: Arc<SagaCoordinator>) -> Self {
        let mut transitions = HashMap::new();
        transitions.insert("pending".to_string(), vec!["running".to_string()]);
        transitions.insert("running".to_string(), vec!["completed".to_string(), "failed".to_string()]);
        transitions.insert("failed".to_string(), vec!["compensating".to_string()]);
        transitions.insert("compensating".to_string(), vec!["completed".to_string()]);

        Self {
            coordinator,
            current_state: "pending".to_string(),
            transitions,
        }
    }

    /// 状态转换
    pub fn transition(&mut self, new_state: &str) -> Result<(), String> {
        if let Some(valid_transitions) = self.transitions.get(&self.current_state) {
            if valid_transitions.contains(&new_state.to_string()) {
                self.current_state = new_state.to_string();
                Ok(())
            } else {
                Err(format!("Invalid transition from {} to {}", self.current_state, new_state))
            }
        } else {
            Err("Invalid current state".to_string())
        }
    }

    /// 获取当前状态
    pub fn get_current_state(&self) -> &str {
        &self.current_state
    }
}
```

## 8. 总结

Saga模式是分布式事务管理的重要模式，通过形式化的数学理论和Rust实现，我们建立了完整的Saga框架。该模式具有以下特点：

1. **形式化定义**: 通过五元组定义建立了严格的数学模型
2. **理论完备性**: 提供了完整的定理证明和性能分析
3. **实现多样性**: 支持基础、泛型、异步等多种实现方式
4. **应用广泛性**: 适用于电商、银行、微服务等场景
5. **最终一致性**: 通过补偿操作保证分布式系统的最终一致性

该模式为分布式事务管理提供了理论基础和实践指导，是构建高可用、强一致性分布式系统的重要组件。
