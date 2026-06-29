//! 限流（Rate Limiting）与幂等（Idempotency）模式示例
//!
//! 本示例展示四种常见限流算法中的两种（Token Bucket、Sliding Window）以及
//! 一个基于内存的幂等执行器。所有实现仅依赖标准库与已在 `c06_async` 中声明的
//! `tokio`、`dashmap`、`parking_lot`、`anyhow` 依赖，无需外部服务即可运行。

use std::future::Future;
use std::sync::Arc;
use std::time::{Duration, Instant};

use anyhow::Result;
use dashmap::DashMap;
use parking_lot::Mutex;
use tokio::time::sleep;

// -----------------------------------------------------------------------------
// 1. Token Bucket（令牌桶）
// -----------------------------------------------------------------------------

#[derive(Clone)]
pub struct TokenBucket {
    capacity: u64,
    refill_rate_per_sec: u64,
    state: Arc<Mutex<BucketState>>,
}

struct BucketState {
    tokens: u64,
    last_refill: Instant,
}

impl TokenBucket {
    pub fn new(capacity: u64, refill_rate_per_sec: u64) -> Self {
        let state = BucketState {
            tokens: capacity,
            last_refill: Instant::now(),
        };
        Self {
            capacity,
            refill_rate_per_sec,
            state: Arc::new(Mutex::new(state)),
        }
    }

    /// 异步获取 `n` 个令牌；若桶内不足则等待直到可用或返回 false。
    /// 生产环境通常会返回 `Result` 或立即拒绝，这里演示“阻塞等待”语义。
    pub async fn acquire(&self, n: u64) -> bool {
        loop {
            let wait = {
                let mut s = self.state.lock();
                let now = Instant::now();
                let elapsed = now.duration_since(s.last_refill).as_secs();
                s.tokens = (s.tokens + elapsed * self.refill_rate_per_sec).min(self.capacity);
                s.last_refill = now;

                if s.tokens >= n {
                    s.tokens -= n;
                    return true;
                }

                // 计算还需等待多长时间才能凑够 n 个令牌。
                let missing = n - s.tokens;
                let refill_interval = 1.0 / self.refill_rate_per_sec as f64;
                Duration::from_secs_f64(missing as f64 * refill_interval)
            };

            sleep(wait).await;
        }
    }
}

// -----------------------------------------------------------------------------
// 2. Sliding Window（滑动窗口）
// -----------------------------------------------------------------------------

#[derive(Clone)]
pub struct SlidingWindow {
    window: Duration,
    max: usize,
    requests: Arc<Mutex<Vec<Instant>>>,
}

impl SlidingWindow {
    pub fn new(window: Duration, max: usize) -> Self {
        Self {
            window,
            max,
            requests: Arc::new(Mutex::new(Vec::new())),
        }
    }

    /// 非阻塞尝试通过窗口；若当前窗口内请求数已达上限则返回 false。
    pub fn try_request(&self) -> bool {
        let mut reqs = self.requests.lock();
        let cutoff = Instant::now() - self.window;
        reqs.retain(|t| *t >= cutoff);
        if reqs.len() < self.max {
            reqs.push(Instant::now());
            true
        } else {
            false
        }
    }
}

// -----------------------------------------------------------------------------
// 3. Idempotency（幂等执行器）
// -----------------------------------------------------------------------------

/// 单个幂等键对应的异步锁单元。
type IdempotencyCell = Arc<tokio::sync::Mutex<Option<(Instant, String)>>>;

pub struct IdempotencyStore {
    /// 每个幂等键对应一个独立的异步锁单元。
    /// 这样不同键之间可以并发，同一键只会触发一次实际执行。
    cells: DashMap<String, IdempotencyCell>,
    ttl: Duration,
}

impl IdempotencyStore {
    pub fn new(ttl: Duration) -> Self {
        Self {
            cells: DashMap::new(),
            ttl,
        }
    }

    /// 使用 `key` 执行一次幂等操作。
    /// - 若 key 已有未过期的结果，直接返回缓存结果。
    /// - 否则执行 `op`，成功后缓存结果并返回。
    pub async fn execute<F, Fut>(&self, key: &str, op: F) -> Result<String>
    where
        F: FnOnce() -> Fut,
        Fut: Future<Output = Result<String>>,
    {
        let cell = self
            .cells
            .entry(key.to_string())
            .or_insert_with(|| Arc::new(tokio::sync::Mutex::new(None)))
            .clone();

        let mut guard = cell.lock().await;
        if let Some((ts, cached)) = guard.as_ref()
            && ts.elapsed() < self.ttl
        {
            return Ok(cached.clone());
        }

        let result = op().await?;
        *guard = Some((Instant::now(), result.clone()));
        Ok(result)
    }

    /// 清理已过期条目，防止内存无限增长。
    pub fn purge_expired(&self) {
        self.cells.retain(|_, cell| {
            if let Ok(guard) = cell.try_lock()
                && let Some((ts, _)) = guard.as_ref()
            {
                return ts.elapsed() < self.ttl;
            }
            true
        });
    }
}

// -----------------------------------------------------------------------------
// 4. 演示
// -----------------------------------------------------------------------------

#[tokio::main(flavor = "multi_thread")]
async fn main() -> Result<()> {
    // 4.1 令牌桶：容量 5，每秒回填 2 个。
    let bucket = TokenBucket::new(5, 2);
    let mut allowed = 0;
    for i in 0..10u32 {
        if bucket.acquire(1).await {
            allowed += 1;
            println!(
                "[token bucket] request {} allowed (total allowed {})",
                i, allowed
            );
        } else {
            println!("[token bucket] request {} rejected", i);
        }
    }
    println!(">>> token bucket: {}/10 requests allowed\n", allowed);

    // 4.2 滑动窗口：1 秒内最多 3 次请求。
    let window = SlidingWindow::new(Duration::from_secs(1), 3);
    for i in 0..5u32 {
        let status = if window.try_request() {
            "allowed"
        } else {
            "rejected"
        };
        println!("[sliding window] request {} {}", i, status);
    }
    println!(">>> sliding window: 2 requests should be rejected\n");

    // 4.3 幂等执行：3 个并发任务使用同一个 key，只会触发一次真实处理。
    let store = Arc::new(IdempotencyStore::new(Duration::from_secs(5)));
    let mut handles = Vec::new();
    for task_id in 0..3u32 {
        let store = store.clone();
        handles.push(tokio::spawn(async move {
            let outcome = store
                .execute("payment-order-42", || async {
                    // 模拟一个需要保证幂等的下游写操作。
                    sleep(Duration::from_millis(50)).await;
                    Ok::<_, anyhow::Error>("payment processed".to_string())
                })
                .await;
            (task_id, outcome)
        }));
    }

    for handle in handles {
        let (task_id, outcome) = handle.await?;
        println!("[idempotency] task {} -> {:?}", task_id, outcome);
    }

    // 清理过期条目（生产环境应放在定时任务中）。
    store.purge_expired();
    println!(">>> idempotency: all tasks share the same result\n");

    // 4.4 边界说明：分布式锁 + 幂等
    // 当业务需要在多个实例间保证“最多执行一次”时，仅靠内存级幂等键不够。
    // 典型做法是：先获取分布式锁（如 Redis RedLock / SET NX EX），再执行幂等键判断。
    // 锁的持有期必须覆盖整个执行窗口，避免以下反例：
    //   - 锁过期但业务仍在执行，另一个实例重入导致重复处理。
    //   - 幂等键 TTL 短于锁 TTL，成功后 key 被提前清理，后续相同 key 再次执行。

    Ok(())
}

// -----------------------------------------------------------------------------
// 单元测试（仅做基本不变量验证）
// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn token_bucket_respects_capacity() {
        let bucket = TokenBucket::new(3, 10);
        assert!(bucket.acquire(2).await);
        assert!(bucket.acquire(2).await); // 剩余 1，需等待 0.1s  refill
        assert!(!bucket.acquire(10).await); // 永远不等待足够
    }

    #[tokio::test]
    async fn sliding_window_blocks_excess() {
        let window = SlidingWindow::new(Duration::from_secs(10), 2);
        assert!(window.try_request());
        assert!(window.try_request());
        assert!(!window.try_request());
    }

    #[tokio::test]
    async fn idempotency_returns_same_result() {
        let store = IdempotencyStore::new(Duration::from_secs(10));
        let counter = Arc::new(Mutex::new(0usize));
        let counter1 = counter.clone();
        let r1 = store
            .execute("id-1", move || {
                let c = counter1.clone();
                async move {
                    *c.lock() += 1;
                    Ok::<_, anyhow::Error>("ok".to_string())
                }
            })
            .await
            .unwrap();
        let r2 = store
            .execute("id-1", || async {
                Ok::<_, anyhow::Error>("different".to_string())
            })
            .await
            .unwrap();
        assert_eq!(r1, r2);
        assert_eq!(*counter.lock(), 1);
    }
}
