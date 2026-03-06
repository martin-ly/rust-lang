# 17 临界区模式 (Critical Section)

## 模式定义与语义

临界区模式确保两个或多个活动的特定区域互斥执行。这是并发编程中最基本的同步原语之一。

### 核心语义

$$
\text{CriticalSection}(R, CS_1, CS_2, \ldots, CS_n) = \forall i \neq j: \neg(CS_i \text{ active} \land CS_j \text{ active})
$$

其中 $R$ 是共享资源，$CS_i$ 是第 $i$ 个活动的临界区代码。

### 形式化表示

**状态机表示：**

$$
\begin{aligned}
& \text{State}_i = \{ \text{Outside}, \text{Waiting}, \text{Inside}, \text{Done} \} \quad \forall i \\
& \text{Invariant}: \sum_{i} \mathbb{1}_{\text{State}_i = \text{Inside}} \leq 1 \\
& \text{Transition} = \{ \\
& \quad (\text{Outside}, \text{request}, \text{Waiting}), \\
& \quad (\text{Waiting}, \text{acquire}, \text{Inside}) \text{ if no one inside}, \\
& \quad (\text{Inside}, \text{release}, \text{Done}) \\
& \}
\end{aligned}
$$

**互斥逻辑：**

$$
\square \neg(\text{InCritical}(P_i) \land \text{InCritical}(P_j)) \quad \forall i \neq j
$$

## Rust 实现示例

```rust
use std::sync::Arc;
use tokio::sync::{Mutex, RwLock, Semaphore};

/// 基于 Mutex 的临界区
pub struct CriticalSection<T> {
    data: Arc<Mutex<T>>,
}

impl<T> CriticalSection<T> {
    pub fn new(data: T) -> Self {
        Self {
            data: Arc::new(Mutex::new(data)),
        }
    }

    /// 执行临界区代码
    pub async fn execute<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R,
    {
        let mut guard = self.data.lock().await;
        f(&mut *guard)
    }
}

/// 使用示例：银行账户转账
#[derive(Clone, Debug)]
struct BankAccount {
    id: String,
    balance: f64,
}

pub struct BankTransfer {
    accounts: Arc<RwLock<Vec<BankAccount>>>,
}

impl BankTransfer {
    pub fn new(accounts: Vec<BankAccount>) -> Self {
        Self {
            accounts: Arc::new(RwLock::new(accounts)),
        }
    }

    /// 安全转账：使用临界区保护账户操作
    pub async fn transfer(
        &self,
        from_id: &str,
        to_id: &str,
        amount: f64,
    ) -> Result<(), String> {
        // 获取写锁 - 进入临界区
        let mut accounts = self.accounts.write().await;

        // 验证余额
        let from_idx = accounts
            .iter()
            .position(|a| a.id == from_id)
            .ok_or("源账户不存在")?;

        if accounts[from_idx].balance < amount {
            return Err("余额不足".to_string());
        }

        let to_idx = accounts
            .iter()
            .position(|a| a.id == to_id)
            .ok_or("目标账户不存在")?;

        // 执行转账
        accounts[from_idx].balance -= amount;
        accounts[to_idx].balance += amount;

        println!(
            "转账完成: {} -> {}, 金额: {}",
            from_id, to_id, amount
        );

        // 锁自动释放 - 离开临界区
        Ok(())
    }
}

/// 基于 Semaphore 的多重临界区
pub struct LimitedCriticalSection {
    semaphore: Arc<Semaphore>,
}

impl LimitedCriticalSection {
    /// 允许同时 n 个进入临界区
    pub fn new(n: usize) -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(n)),
        }
    }

    pub async fn acquire(&self) -> tokio::sync::OwnedSemaphorePermit {
        self.semaphore
            .clone()
            .acquire_owned()
            .await
            .expect("Semaphore closed")
    }
}

/// 使用示例：限流访问
pub async fn rate_limited_access() {
    let limiter = Arc::new(LimitedCriticalSection::new(3)); // 最多3个并发

    let mut handles = vec![];

    for i in 0..10 {
        let limiter = Arc::clone(&limiter);
        let handle = tokio::spawn(async move {
            let _permit = limiter.acquire().await;

            println!("任务 {} 进入临界区", i);
            tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
            println!("任务 {} 离开临界区", i);

            // _permit 在这里释放
        });
        handles.push(handle);
    }

    for h in handles {
        let _ = h.await;
    }
}

/// 读写临界区 - 读共享，写独占
pub struct ReadWriteCriticalSection<T> {
    data: Arc<RwLock<T>>,
}

impl<T> ReadWriteCriticalSection<T> {
    pub fn new(data: T) -> Self {
        Self {
            data: Arc::new(RwLock::new(data)),
        }
    }

    /// 读临界区 - 可多个同时读
    pub async fn read<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&T) -> R,
    {
        let guard = self.data.read().await;
        f(&*guard)
    }

    /// 写临界区 - 独占
    pub async fn write<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R,
    {
        let mut guard = self.data.write().await;
        f(&mut *guard)
    }
}

/// 使用示例：缓存
#[derive(Clone)]
struct Cache {
    data: std::collections::HashMap<String, String>,
}

pub async fn cache_example() {
    let cache = Arc::new(ReadWriteCriticalSection::new(Cache {
        data: std::collections::HashMap::new(),
    }));

    // 多个读操作可以并发
    let cache_clone = Arc::clone(&cache);
    let read_handle = tokio::spawn(async move {
        let value = cache_clone.read(|c| c.data.get("key1").cloned()).await;
        println!("读取: {:?}", value);
    });

    // 写操作独占
    let cache_clone = Arc::clone(&cache);
    let write_handle = tokio::spawn(async move {
        cache_clone.write(|c| {
            c.data.insert("key1".to_string(), "value1".to_string());
        }).await;
        println!("写入完成");
    });

    let _ = tokio::join!(read_handle, write_handle);
}

/// 作用域保护的临界区
pub struct ScopedCriticalSection;

impl ScopedCriticalSection {
    /// 确保临界区代码正确配对
    pub async fn with_lock<F, R>(mutex: &Mutex<()>, f: F) -> R
    where
        F: FnOnce() -> R,
    {
        let _guard = mutex.lock().await;
        f()
    }
}

/// 死锁预防：按固定顺序获取锁
pub async fn safe_nested_locks() {
    let lock_a = Arc::new(Mutex::new(1));
    let lock_b = Arc::new(Mutex::new(2));

    // 任务 1: 按 A -> B 顺序
    let a1 = Arc::clone(&lock_a);
    let b1 = Arc::clone(&lock_b);
    let t1 = tokio::spawn(async move {
        let _a = a1.lock().await;
        tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
        let _b = b1.lock().await;
        println!("任务 1 获取两个锁");
    });

    // 任务 2: 也按 A -> B 顺序（避免死锁）
    let a2 = Arc::clone(&lock_a);
    let b2 = Arc::clone(&lock_b);
    let t2 = tokio::spawn(async move {
        let _a = a2.lock().await;
        tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
        let _b = b2.lock().await;
        println!("任务 2 获取两个锁");
    });

    let _ = tokio::join!(t1, t2);
}
```

## 与其他模式的关系

| 模式 | 互斥范围 | 并发度 |
|------|----------|--------|
| **临界区** | 代码块 | 1 |
| 读写锁 | 读/写分离 | 多读/单写 |
| 信号量 | 资源计数 | N |
| 交错路由 | 活动级别 | 1（伪并行） |

**关系公式：**

$$
\text{CriticalSection} = \text{Mutex}(R) + \text{CodeBlock}
$$

## 应用场景

1. **数据一致性**：保护共享数据修改
2. **资源访问**：独占硬件资源
3. **事务处理**：保证事务原子性
4. **限流控制**：控制系统并发度

### 注意事项

- 避免长时间持有锁
- 注意死锁预防
- 优先使用高级抽象（如 channel）
- 考虑使用读写锁提高并发度
- 使用作用域模式确保锁释放
