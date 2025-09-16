// 条件变量模块
// 这个模块提供了进程安全的条件变量实现

use crate::error::SyncResult;
use crate::types::SyncConfig;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, MutexGuard};
use std::time::{Duration, Instant};

/// 进程安全的条件变量
#[allow(dead_code)]
pub struct ProcessCondVar {
    name: String,
    inner: Condvar,
    config: SyncConfig,
    stats: Arc<CondVarStats>,
}

#[allow(dead_code)]
struct CondVarStats {
    wait_count: AtomicUsize,
    notify_count: AtomicUsize,
    total_wait_time: AtomicUsize,
    max_wait_time: AtomicUsize,
}

impl ProcessCondVar {
    /// 创建新的条件变量
    pub fn new(name: &str, config: SyncConfig) -> Self {
        Self {
            name: name.to_string(),
            inner: Condvar::new(),
            config,
            stats: Arc::new(CondVarStats {
                wait_count: AtomicUsize::new(0),
                notify_count: AtomicUsize::new(0),
                total_wait_time: AtomicUsize::new(0),
                max_wait_time: AtomicUsize::new(0),
            }),
        }
    }

    /// 等待条件满足
    pub fn wait<'a, T>(&self, guard: MutexGuard<'a, T>) -> SyncResult<MutexGuard<'a, T>> {
        let start = Instant::now();

        self.stats.wait_count.fetch_add(1, Ordering::Relaxed);

        let guard = self
            .inner
            .wait(guard)
            .map_err(|e| crate::error::SyncError::CondVarError(e.to_string()))?;

        let wait_time = start.elapsed();
        let wait_time_ns = wait_time.as_nanos() as usize;

        self.stats
            .total_wait_time
            .fetch_add(wait_time_ns, Ordering::Relaxed);

        Ok(guard)
    }

    /// 带超时的等待
    pub fn wait_timeout<'a, T>(
        &self,
        guard: MutexGuard<'a, T>,
        timeout: Duration,
    ) -> SyncResult<MutexGuard<'a, T>> {
        let start = Instant::now();

        self.stats.wait_count.fetch_add(1, Ordering::Relaxed);

        let (guard, _) = self
            .inner
            .wait_timeout(guard, timeout)
            .map_err(|e| crate::error::SyncError::CondVarError(e.to_string()))?;

        let wait_time = start.elapsed();
        let wait_time_ns = wait_time.as_nanos() as usize;

        self.stats
            .total_wait_time
            .fetch_add(wait_time_ns, Ordering::Relaxed);

        Ok(guard)
    }

    /// 通知一个等待者
    pub fn notify_one(&self) {
        self.stats.notify_count.fetch_add(1, Ordering::Relaxed);
        self.inner.notify_one();
    }

    /// 通知所有等待者
    pub fn notify_all(&self) {
        self.stats.notify_count.fetch_add(1, Ordering::Relaxed);
        self.inner.notify_all();
    }
}
