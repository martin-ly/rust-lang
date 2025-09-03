use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

#[derive(Clone)]
pub struct CircuitBreaker {
    inner: Arc<Inner>,
}

struct Inner {
    failures: AtomicU64,
    opened_at: parking_lot::Mutex<Option<Instant>>,
    fail_threshold: u64,
    open_window: Duration,
}

impl CircuitBreaker {
    pub fn new(fail_threshold: u64, open_window: Duration) -> Self {
        Self { inner: Arc::new(Inner { failures: AtomicU64::new(0), opened_at: parking_lot::Mutex::new(None), fail_threshold, open_window }) }
    }

    pub async fn run<F, T, E>(&self, fut: F) -> Result<T, E>
    where
        F: std::future::Future<Output = Result<T, E>>,
    {
        // half-open/closed 判断
        {
            let mut opened = self.inner.opened_at.lock();
            if let Some(t) = *opened {
                if t.elapsed() < self.inner.open_window { return Err(self.synthetic_err()); }
                *opened = None; // half-open: 允许一次尝试
            }
        }

        match fut.await {
            Ok(v) => {
                self.inner.failures.store(0, Ordering::Relaxed);
                Ok(v)
            }
            Err(e) => {
                let f = self.inner.failures.fetch_add(1, Ordering::Relaxed) + 1;
                if f >= self.inner.fail_threshold {
                    *self.inner.opened_at.lock() = Some(Instant::now());
                }
                Err(e)
            }
        }
    }

    fn synthetic_err<E>(&self) -> E {
        // 仅用于示例：无法构造具体 E，调用端应在外层处理被熔断的情况
        panic!("circuit open")
    }
}


