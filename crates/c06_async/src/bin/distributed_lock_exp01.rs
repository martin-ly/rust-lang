use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::Mutex;
use tokio::time::sleep;

/// 模拟分布式锁实现
/// 在实际生产环境中，这通常基于 Redis、ZooKeeper 或 etcd
#[derive(Debug)]
struct DistributedLock {
    id: String,
    resource: String,
    acquired_at: Option<Instant>,
    ttl: Duration,
}

#[allow(dead_code)]
impl DistributedLock {
    fn new(resource: String, ttl: Duration) -> Self {
        Self {
            id: format!("lock-{}", uuid::Uuid::new_v4().simple()),
            resource,
            acquired_at: None,
            ttl,
        }
    }

    /// 尝试获取锁
    async fn try_acquire(&mut self) -> bool {
        // 模拟网络延迟和竞争
        sleep(Duration::from_millis(rand::random::<u64>() % 100)).await;

        // 模拟锁获取成功或失败
        let success = rand::random::<bool>();
        if success {
            self.acquired_at = Some(Instant::now());
            println!("🔒 锁 {} 获取成功", self.id);
        } else {
            println!("❌ 锁 {} 获取失败", self.id);
        }
        success
    }

    /// 释放锁
    async fn release(&mut self) -> bool {
        if self.acquired_at.is_some() {
            self.acquired_at = None;
            println!("🔓 锁 {} 释放成功", self.id);
            true
        } else {
            println!("⚠️  锁 {} 未持有，无法释放", self.id);
            false
        }
    }

    /// 检查锁是否仍然有效
    fn is_valid(&self) -> bool {
        if let Some(acquired_at) = self.acquired_at {
            acquired_at.elapsed() < self.ttl
        } else {
            false
        }
    }

    /// 自动续期
    async fn renew(&mut self) -> bool {
        if self.is_valid() {
            self.acquired_at = Some(Instant::now());
            println!("🔄 锁 {} 续期成功", self.id);
            true
        } else {
            println!("⚠️  锁 {} 已过期，无法续期", self.id);
            false
        }
    }
}

/// 分布式锁管理器
struct LockManager {
    locks: Arc<Mutex<Vec<DistributedLock>>>,
}

impl LockManager {
    fn new() -> Self {
        Self {
            locks: Arc::new(Mutex::new(Vec::new())),
        }
    }

    /// 获取指定资源的锁
    async fn acquire_lock(&self, resource: &str, ttl: Duration) -> Option<String> {
        let mut lock = DistributedLock::new(resource.to_string(), ttl);

        if lock.try_acquire().await {
            let lock_id = lock.id.clone();
            self.locks.lock().await.push(lock);
            Some(lock_id)
        } else {
            None
        }
    }

    /// 释放指定锁
    async fn release_lock(&self, lock_id: &str) -> bool {
        let mut locks = self.locks.lock().await;
        if let Some(index) = locks.iter().position(|l| l.id == lock_id) {
            let mut lock = locks.remove(index);
            lock.release().await
        } else {
            false
        }
    }

    /// 获取所有活跃锁的状态
    async fn get_locks_status(&self) -> Vec<(String, String, bool)> {
        let locks = self.locks.lock().await;
        locks
            .iter()
            .map(|lock| (lock.id.clone(), lock.resource.clone(), lock.is_valid()))
            .collect()
    }
}

/// 模拟分布式任务执行
async fn execute_distributed_task(manager: Arc<LockManager>, resource: &str, task_id: u32) {
    println!("🚀 任务 {} 尝试获取资源 {} 的锁", task_id, resource);

    // 尝试获取锁
    let lock_id = match manager
        .acquire_lock(resource, Duration::from_secs(30))
        .await
    {
        Some(id) => id,
        None => {
            println!("❌ 任务 {} 无法获取锁，跳过执行", task_id);
            return;
        }
    };

    // 执行任务
    println!("✅ 任务 {} 开始执行，持有锁 {}", task_id, lock_id);

    // 模拟任务执行时间
    let execution_time = Duration::from_millis(rand::random::<u64>() % 2000 + 500);
    sleep(execution_time).await;

    println!("🏁 任务 {} 执行完成，耗时 {:?}", task_id, execution_time);

    // 释放锁
    if manager.release_lock(&lock_id).await {
        println!("🔓 任务 {} 成功释放锁 {}", task_id, lock_id);
    }
}

#[tokio::main]
async fn main() {
    println!("🚀 分布式锁示例启动");
    println!("{}", "=".repeat(50));

    let manager = Arc::new(LockManager::new());

    // 模拟多个任务竞争同一个资源
    let resource = "database-connection";
    let task_count = 8;

    println!("📋 启动 {} 个任务竞争资源: {}", task_count, resource);
    println!();

    // 并发执行任务
    let handles: Vec<_> = (0..task_count)
        .map(|task_id| {
            let manager = Arc::clone(&manager);
            tokio::spawn(execute_distributed_task(
                Arc::clone(&manager),
                resource,
                task_id,
            ))
        })
        .collect();

    // 等待所有任务完成
    for handle in handles {
        handle.await.expect("等待任务完成不应失败");
    }

    println!();
    println!("{}", "=".repeat(50));

    // 显示最终状态
    let status = manager.get_locks_status().await;
    if status.is_empty() {
        println!("✅ 所有锁已正确释放");
    } else {
        println!("⚠️  仍有活跃锁:");
        for (id, resource, valid) in status {
            println!("  - {} ({}) - 有效: {}", id, resource, valid);
        }
    }

    println!();
    println!("🎯 分布式锁示例完成");
}
