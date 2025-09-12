use std::sync::Arc;
use tokio::sync::{Semaphore, OwnedSemaphorePermit};
use tokio::time::{timeout, Duration};

pub struct RateLimiter {
    semaphore: Arc<Semaphore>,
    max_permits: usize,
}

impl RateLimiter {
    pub fn new(max_concurrency: usize) -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(max_concurrency)),
            max_permits: max_concurrency,
        }
    }

    pub async fn acquire(&self) -> OwnedSemaphorePermit {
        self.semaphore.clone().acquire_owned().await.unwrap()
    }

    pub fn capacity(&self) -> usize { self.max_permits }
}

pub async fn run_with_timeout<F, T>(dur: Duration, fut: F) -> Result<T, &'static str>
where
    F: std::future::Future<Output = T>,
{
    match timeout(dur, fut).await {
        Ok(val) => Ok(val),
        Err(_) => Err("timeout"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_timeout_ok() {
        let res = run_with_timeout(Duration::from_millis(50), async {
            tokio::time::sleep(Duration::from_millis(10)).await;
            42
        }).await;
        assert_eq!(res.unwrap(), 42);
    }

    #[tokio::test]
    async fn test_timeout_err() {
        let res = run_with_timeout(Duration::from_millis(10), async {
            tokio::time::sleep(Duration::from_millis(50)).await;
            42
        }).await;
        assert!(matches!(res, Err("timeout")));
    }

    #[tokio::test]
    async fn test_rate_limiter_concurrency() {
        let limiter = RateLimiter::new(2);

        let _p1 = limiter.acquire().await;
        let _p2 = limiter.acquire().await;

        // 尝试短暂等待以验证第三个无法立即获取
        let sem = limiter.semaphore.clone();
        let try_third = tokio::spawn(async move {
            tokio::time::timeout(Duration::from_millis(20), sem.acquire_owned()).await.is_ok()
        });

        let acquired_third = try_third.await.unwrap();
        assert!(!acquired_third);
    }
}


