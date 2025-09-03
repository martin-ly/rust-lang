use std::future::Future;
use std::sync::Arc;
use std::time::Duration;
use futures::future::{AbortHandle, Abortable};

pub async fn retry_with_backoff<F, Fut, T, E>(mut make_fut: F, max_attempts: u32, start_delay: Duration) -> Result<T, E>
where
    F: FnMut(u32) -> Fut,
    Fut: Future<Output = Result<T, E>>,
{
    let mut delay = start_delay;
    let mut attempt = 0u32;
    loop {
        attempt += 1;
        match make_fut(attempt).await {
            Ok(v) => return Ok(v),
            Err(e) if attempt >= max_attempts => return Err(e),
            Err(_) => {
                tokio::time::sleep(delay).await;
                delay = delay.saturating_mul(2);
            }
        }
    }
}

pub struct CancelScope {
    handle: AbortHandle,
}

impl CancelScope {
    pub fn new() -> (Self, futures::future::AbortRegistration) {
        let (h, reg) = AbortHandle::new_pair();
        (Self { handle: h }, reg)
    }
    pub fn cancel(&self) { self.handle.abort(); }
}

pub async fn with_timeout<T, F>(dur: Duration, fut: F) -> Option<T>
where
    F: Future<Output = T>,
{
    tokio::time::timeout(dur, fut).await.ok()
}

#[derive(Clone)]
pub struct SemaphoreLimiter {
    inner: Arc<tokio::sync::Semaphore>,
}

impl SemaphoreLimiter {
    pub fn new(concurrency: usize) -> Self { Self { inner: Arc::new(tokio::sync::Semaphore::new(concurrency)) } }
    pub async fn run<F, T>(&self, fut: F) -> T
    where
        F: Future<Output = T>,
    {
        let permit = self.inner.clone().acquire_owned().await.expect("acquire permit");
        let res = fut.await;
        drop(permit);
        res
    }
}

pub async fn abortable<F, T>(reg: futures::future::AbortRegistration, fut: F) -> Result<T, futures::future::Aborted>
where
    F: Future<Output = T>,
{
    Abortable::new(fut, reg).await
}

pub mod circuit_breaker;


