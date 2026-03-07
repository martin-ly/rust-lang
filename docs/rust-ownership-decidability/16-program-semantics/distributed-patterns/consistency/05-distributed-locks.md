# 分布式锁语义 (Distributed Lock Semantics)

## 目录

- [分布式锁语义 (Distributed Lock Semantics)](#分布式锁语义-distributed-lock-semantics)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 分布式锁基础](#2-分布式锁基础)
    - [2.1 为什么需要分布式锁](#21-为什么需要分布式锁)
    - [2.2 形式化定义](#22-形式化定义)
  - [3. 基于 Redis 的分布式锁](#3-基于-redis-的分布式锁)
    - [3.1 Redlock 算法](#31-redlock-算法)
    - [3.2 续租机制](#32-续租机制)
  - [4. 基于 etcd/ZooKeeper 的锁](#4-基于-etcdzookeeper-的锁)
    - [4.1 etcd 分布式锁](#41-etcd-分布式锁)
    - [4.2 ZooKeeper 分布式锁](#42-zookeeper-分布式锁)
  - [5. 分布式读写锁](#5-分布式读写锁)
    - [5.1 读写锁语义](#51-读写锁语义)
  - [6. 形式化性质](#6-形式化性质)
    - [6.1 安全性证明](#61-安全性证明)
    - [6.2 活性分析](#62-活性分析)
  - [7. 最佳实践](#7-最佳实践)
    - [7.1 锁使用准则](#71-锁使用准则)
  - [8. 总结](#8-总结)

## 1. 引言

分布式锁是协调分布式系统中互斥访问共享资源的核心机制。本文档深入分析分布式锁的形式化语义、实现算法和 Rust 实践。

---

## 2. 分布式锁基础

### 2.1 为什么需要分布式锁

```
单机锁 vs 分布式锁:

单机锁:                      分布式锁:
┌──────────┐                ┌──────────┐
│ Process  │                │ Node A   │
│  lock()  │                │ lock()   │
│    ↓     │                │    ↓     │
│ Critical │                │ Critical │
│ Section  │                │ Section  │
│    ↓     │                │    ↓     │
│ unlock() │                │ unlock() │
└──────────┘                └──────────┘
                                 │
                            ┌────┴────┐
                            ↓         ↓
                       ┌────────┐ ┌────────┐
                       │ Node B │ │ Node C │
                       │ (等待) │ │ (等待) │
                       └────────┘ └────────┘

核心挑战:
  • 网络延迟和分区
  • 节点故障
  • 锁的活性与安全性
```

### 2.2 形式化定义

```
分布式锁 = (Acquire, Release, Safety, Liveness)

Safety (安全性):
  □ (Owner(lock) = p₁ ∧ Owner(lock) = p₂ → p₁ = p₂)

  任意时刻最多只有一个持有者

Liveness (活性):
  ◇ (Request(p, lock) → ◇ Acquire(p, lock))

  请求锁的进程最终能获得锁（无饥饿）

容错性:
  Failure(p) → ◇ Released(lock, p)

  持有锁的进程故障后，锁最终能被释放
```

---

## 3. 基于 Redis 的分布式锁

### 3.1 Redlock 算法

```
Redlock 算法:

1. 获取当前时间 T1
2. 依次向 N 个 Redis 节点请求锁（key, value=唯一标识, ttl）
   - 使用相同的 key 和随机 value
   - 设置过期时间（防止死锁）
3. 计算获取锁的总耗时 ΔT = now() - T1
4. 如果成功获取了多数派（N/2 + 1）且 ΔT < ttl，则获得锁
5. 锁的有效时间 = ttl - ΔT
6. 释放锁时向所有节点发送解锁请求

容错性:
  - 容忍 (N - 1) / 2 个节点故障
  - 异步时钟假设
```

```rust
use redis::{Client, Commands, RedisResult};

struct Redlock {
    nodes: Vec<Client>,
    quorum: usize,
    default_ttl: Duration,
}

struct Lock {
    resource: String,
    value: String,  // 唯一标识，用于安全释放
    validity_time: Duration,
}

impl Redlock {
    async fn lock(&self, resource: &str, ttl: Duration) -> Result<Lock, LockError> {
        let value = generate_unique_id();
        let start_time = Instant::now();

        let mut acquired = 0;
        let mut errors = vec![];

        // 向所有节点尝试获取锁
        for node in &self.nodes {
            match self.lock_single_node(node, resource, &value, ttl).await {
                Ok(true) => acquired += 1,
                Ok(false) => {}
                Err(e) => errors.push(e),
            }
        }

        let elapsed = start_time.elapsed();

        // 检查是否获得多数派且未超时
        if acquired >= self.quorum && elapsed < ttl {
            let validity = ttl - elapsed;
            Ok(Lock {
                resource: resource.to_string(),
                value,
                validity_time: validity,
            })
        } else {
            // 获取失败，释放已获取的锁
            self.unlock_all(resource, &value).await;
            Err(LockError::NotAcquired)
        }
    }

    async fn lock_single_node(
        &self,
        client: &Client,
        resource: &str,
        value: &str,
        ttl: Duration,
    ) -> RedisResult<bool> {
        let mut conn = client.get_async_connection().await?;
        let result: Option<String> = redis::cmd("SET")
            .arg(resource)
            .arg(value)
            .arg("NX")  // Only if Not eXists
            .arg("PX")  // Milliseconds
            .arg(ttl.as_millis() as u64)
            .query_async(&mut conn)
            .await?;
        Ok(result.is_some())
    }

    async fn unlock(&self, lock: &Lock) {
        let script = r#"
            if redis.call("get", KEYS[1]) == ARGV[1] then
                return redis.call("del", KEYS[1])
            else
                return 0
            end
        "#;

        for node in &self.nodes {
            let mut conn = match node.get_async_connection().await {
                Ok(c) => c,
                Err(_) => continue,
            };

            let _: RedisResult<i32> = redis::cmd("EVAL")
                .arg(script)
                .arg(1)  // number of keys
                .arg(&lock.resource)
                .arg(&lock.value)
                .query_async(&mut conn)
                .await;
        }
    }
}

// 使用示例
async fn critical_section(redlock: &Redlock) {
    // 尝试获取锁
    let lock = match redlock.lock("my_resource", Duration::from_secs(10)).await {
        Ok(l) => l,
        Err(e) => {
            tracing::error!("Failed to acquire lock: {:?}", e);
            return;
        }
    };

    // 执行业务逻辑
    do_work().await;

    // 释放锁
    redlock.unlock(&lock).await;
}
```

### 3.2 续租机制

```rust
// 锁续租（Watchdog 模式）
struct LockGuard {
    redlock: Arc<Redlock>,
    lock: Lock,
    shutdown: Sender<()>,
}

impl LockGuard {
    fn new(redlock: Arc<Redlock>, lock: Lock) -> Self {
        let (tx, rx) = oneshot::channel();

        // 启动续租任务
        let redlock_clone = redlock.clone();
        let lock_clone = lock.clone();
        tokio::spawn(async move {
            let mut interval = interval(Duration::from_secs(5));
            let mut rx = rx;

            loop {
                tokio::select! {
                    _ = interval.tick() => {
                        // 续租
                        if redlock_clone.extend(&lock_clone).await.is_err() {
                            tracing::error!("Lock extension failed!");
                            break;
                        }
                    }
                    _ = &mut rx => {
                        // 正常释放
                        break;
                    }
                }
            }
        });

        Self {
            redlock,
            lock,
            shutdown: tx,
        }
    }
}

impl Drop for LockGuard {
    fn drop(&mut self) {
        // 停止续租
        let _ = self.shutdown.send(());

        // 释放锁
        let redlock = self.redlock.clone();
        let lock = self.lock.clone();
        tokio::spawn(async move {
            redlock.unlock(&lock).await;
        });
    }
}
```

---

## 4. 基于 etcd/ZooKeeper 的锁

### 4.1 etcd 分布式锁

```rust
use etcd_client::{Client, Compare, CompareOp, Txn, TxnOp};

struct EtcdDistributedLock {
    client: Client,
    key: String,
    lease_id: i64,
    ttl: i64,
}

impl EtcdDistributedLock {
    async fn acquire(&mut self) -> Result<(), LockError> {
        // 创建租约（自动过期）
        let lease = self.client.lease_grant(self.ttl, None).await?;
        self.lease_id = lease.id();

        // 保持租约存活
        let (mut keeper, mut stream) = self.client.lease_keep_alive(lease.id()).await?;
        tokio::spawn(async move {
            loop {
                if keeper.keep_alive().await.is_err() {
                    break;
                }
                if stream.message().await.is_err() {
                    break;
                }
                sleep(Duration::from_secs(self.ttl as u64 / 3)).await;
            }
        });

        // 尝试获取锁（原子 Compare-And-Swap）
        let txn = Txn::new()
            .when([Compare::version(self.key.clone(), CompareOp::Equal, 0)])
            .and_then([TxnOp::put(
                self.key.clone(),
                self.node_id().to_string(),
                Some(PutOptions::new().with_lease(lease.id())),
            )]);

        let response = self.client.txn(txn).await?;

        if response.succeeded() {
            Ok(())
        } else {
            Err(LockError::AlreadyLocked)
        }
    }

    async fn release(&mut self) -> Result<(), LockError> {
        // 原子删除（只有自己能删除）
        let txn = Txn::new()
            .when([Compare::value(
                self.key.clone(),
                CompareOp::Equal,
                self.node_id().to_string(),
            )])
            .and_then([TxnOp::delete(self.key.clone(), None)]);

        self.client.txn(txn).await?;

        // 撤销租约
        self.client.lease_revoke(self.lease_id).await?;

        Ok(())
    }
}
```

### 4.2 ZooKeeper 分布式锁

```rust
use zookeeper::{Acl, CreateMode, WatchedEvent, Watcher, ZkError, ZooKeeper};

struct ZkDistributedLock {
    zk: Arc<ZooKeeper>,
    lock_path: String,
    node_path: Option<String>,
}

impl ZkDistributedLock {
    async fn acquire(&mut self) -> Result<(), LockError> {
        // 创建临时顺序节点
        let node = self.zk.create(
            &format!("{}/lock-", self.lock_path),
            vec![],
            Acl::open_unsafe().clone(),
            CreateMode::EphemeralSequential,
        ).await?;

        self.node_path = Some(node.clone());

        loop {
            // 获取所有子节点
            let children = self.zk.get_children(&self.lock_path, false).await?;
            let mut sorted: Vec<_> = children.iter()
                .filter(|c| c.starts_with("lock-"))
                .collect();
            sorted.sort();

            let node_name = node.rsplit('/').next().unwrap();

            if sorted[0] == node_name {
                // 是最小节点，获得锁
                return Ok(());
            }

            // 找到前一个节点
            let pos = sorted.iter().position(|&x| x == node_name).unwrap();
            let prev_node = &sorted[pos - 1];

            // 监听前一个节点
            let (tx, rx) = oneshot::channel();
            let watcher = move |e: WatchedEvent| {
                let _ = tx.send(e);
            };

            self.zk.exists(
                &format!("{}/{}", self.lock_path, prev_node),
                Some(watcher),
            ).await?;

            // 等待前一个节点被删除
            let _ = rx.await;
        }
    }

    async fn release(&mut self) -> Result<(), LockError> {
        if let Some(ref path) = self.node_path {
            self.zk.delete(path, None).await?;
            self.node_path = None;
        }
        Ok(())
    }
}

// 使用 RAII 模式
struct ZkLockGuard {
    lock: ZkDistributedLock,
}

impl Drop for ZkLockGuard {
    fn drop(&mut self) {
        // 临时节点在会话结束时自动删除
        // 但显式删除更优雅
        let zk = self.lock.zk.clone();
        if let Some(ref path) = self.lock.node_path {
            let path = path.clone();
            tokio::spawn(async move {
                let _ = zk.delete(&path, None).await;
            });
        }
    }
}
```

---

## 5. 分布式读写锁

### 5.1 读写锁语义

```rust
// 分布式读写锁
struct DistributedRwLock {
    read_locks: Vec<String>,
    write_lock: String,
    redlock: Arc<Redlock>,
}

enum LockMode {
    Read,
    Write,
}

struct RwLockGuard {
    resource: String,
    mode: LockMode,
    redlock: Arc<Redlock>,
}

impl DistributedRwLock {
    async fn acquire_read(&self, resource: &str) -> Result<RwLockGuard, LockError> {
        // 读锁：允许多个读者
        let lock_key = format!("{}:read", resource);
        let lock = self.redlock.lock(&lock_key, Duration::from_secs(30)).await?;

        Ok(RwLockGuard {
            resource: lock_key,
            mode: LockMode::Read,
            redlock: self.redlock.clone(),
        })
    }

    async fn acquire_write(&self, resource: &str) -> Result<RwLockGuard, LockError> {
        // 写锁：独占访问
        // 1. 先获取写锁标记
        let write_key = format!("{}:write", resource);
        let _ = self.redlock.lock(&write_key, Duration::from_secs(30)).await?;

        // 2. 等待所有读锁释放
        self.wait_for_readers(resource).await?;

        Ok(RwLockGuard {
            resource: write_key,
            mode: LockMode::Write,
            redlock: self.redlock.clone(),
        })
    }

    async fn wait_for_readers(&self, resource: &str) -> Result<(), LockError> {
        let pattern = format!("{}:read:*", resource);

        loop {
            let readers = self.redlock.scan_keys(&pattern).await?;
            if readers.is_empty() {
                return Ok(());
            }
            sleep(Duration::from_millis(100)).await;
        }
    }
}

impl Drop for RwLockGuard {
    fn drop(&mut self) {
        // 释放锁
        let redlock = self.redlock.clone();
        let resource = self.resource.clone();
        tokio::spawn(async move {
            // 释放实现...
        });
    }
}
```

---

## 6. 形式化性质

### 6.1 安全性证明

```
互斥性 (Mutual Exclusion):

定理: Redlock 满足互斥性

证明:
  1. 设进程 p₁ 和 p₂ 同时持有锁 L
  2. p₁ 获得多数派 M₁ 确认，p₂ 获得多数派 M₂ 确认
  3. M₁ ∩ M₂ ≠ ∅ (由鸽巢原理)
  4. 存在节点 n ∈ M₁ ∩ M₂ 同时确认了两个锁请求
  5. 但 Redis SET NX 保证 key 不存在时才设置成功
  6. 矛盾！因此假设不成立

时钟假设:
  要求各节点时钟漂移不超过 ttl 的某个比例
```

### 6.2 活性分析

```
活性保证:

无死锁 (Deadlock-Free):
  □ (Request(p, lock) → ◇ (Acquire(p, lock) ∨ Abort(p)))

无饥饿 (Starvation-Free):
  需要公平队列机制（如 ZooKeeper 的顺序节点）

容错性:
  Failure(p) ∧ Owner(lock) = p → ◇ Free(lock)
```

---

## 7. 最佳实践

### 7.1 锁使用准则

```rust
// 1. 始终使用超时
trait LockWithTimeout {
    async fn lock_with_timeout(
        &self,
        resource: &str,
        acquire_timeout: Duration,
        lock_ttl: Duration,
    ) -> Result<LockGuard, LockError>;
}

// 2. 幂等性保护
struct IdempotentLock {
    operation_id: String,
}

impl IdempotentLock {
    async fn execute<F, Fut, T>(&self, f: F) -> Result<T, LockError>
    where
        F: FnOnce() -> Fut,
        Fut: Future<Output = T>,
    {
        // 检查是否已经执行过
        if self.is_executed().await? {
            return self.get_cached_result().await;
        }

        // 获取锁
        let lock = self.acquire_lock().await?;

        // 再次检查（双重检查）
        if self.is_executed().await? {
            return self.get_cached_result().await;
        }

        // 执行业务逻辑
        let result = f().await;

        // 标记已执行
        self.mark_executed(result).await?;

        drop(lock);
        Ok(result)
    }
}

// 3. 锁粒度控制
enum LockGranularity {
    Global,      // 全局锁（慎用）
    Shard(String), // 分片锁
    Resource(String), // 资源级锁
    User(String),    // 用户级锁
}
```

---

## 8. 总结

| 实现 | 一致性 | 容错性 | 性能 | 适用场景 |
|------|--------|--------|------|----------|
| Redis Redlock | 高 | 中 | 高 | 通用分布式锁 |
| etcd | 高 | 高 | 中 | 配置/协调 |
| ZooKeeper | 高 | 高 | 中 | 选举/队列 |

关键公式:

$$
\text{Safety} = \text{Majority} \land \text{UniqueValue} \land \text{ClockBound}
$$

$$
\text{Liveness} = \text{Timeout} \land \text{Lease} \land \text{Retry}
$$
