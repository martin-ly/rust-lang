// 信号量模块
// 这个模块提供了进程安全的信号量实现

use crate::error::SyncResult;
use crate::types::SyncConfig;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

/// 进程安全的信号量
#[allow(dead_code)]
pub struct ProcessSemaphore {
    name: String,
    permits: Arc<Mutex<usize>>,
    config: SyncConfig,
    stats: Arc<SemaphoreStats>,
}

#[allow(dead_code)]
struct SemaphoreStats {
    acquire_count: std::sync::atomic::AtomicUsize,
    release_count: std::sync::atomic::AtomicUsize,
    total_wait_time: std::sync::atomic::AtomicUsize,
    max_wait_time: std::sync::atomic::AtomicUsize,
}

impl ProcessSemaphore {
    /// 创建新的信号量
    pub fn new(name: &str, permits: usize, config: SyncConfig) -> Self {
        Self {
            name: name.to_string(),
            permits: Arc::new(Mutex::new(permits)),
            config,
            stats: Arc::new(SemaphoreStats {
                acquire_count: std::sync::atomic::AtomicUsize::new(0),
                release_count: std::sync::atomic::AtomicUsize::new(0),
                total_wait_time: std::sync::atomic::AtomicUsize::new(0),
                max_wait_time: std::sync::atomic::AtomicUsize::new(0),
            }),
        }
    }

    /// 尝试获取许可
    pub fn try_acquire(&self) -> Option<SemaphorePermit> {
        let mut permits = self.permits.lock().unwrap();

        if *permits > 0 {
            *permits -= 1;
            self.stats
                .acquire_count
                .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            Some(SemaphorePermit {
                semaphore: Arc::clone(&self.permits),
                stats: Arc::clone(&self.stats),
            })
        } else {
            None
        }
    }

    /// 获取许可（阻塞）
    pub fn acquire(&self) -> SyncResult<SemaphorePermit> {
        let start = Instant::now();

        loop {
            if let Some(permit) = self.try_acquire() {
                return Ok(permit);
            }

            if self.config.timeout != Duration::ZERO && start.elapsed() >= self.config.timeout {
                return Err(crate::error::SyncError::Timeout(self.config.timeout));
            }

            std::thread::yield_now();
        }
    }

    /// 带超时的许可获取
    pub fn acquire_timeout(&self, timeout: Duration) -> SyncResult<SemaphorePermit> {
        let start = Instant::now();

        loop {
            if let Some(permit) = self.try_acquire() {
                return Ok(permit);
            }

            if start.elapsed() >= timeout {
                return Err(crate::error::SyncError::Timeout(timeout));
            }

            std::thread::yield_now();
        }
    }

    /// 获取当前可用许可数量
    pub fn available_permits(&self) -> usize {
        *self.permits.lock().unwrap()
    }

    /// 检查信号量是否被锁定
    pub fn is_locked(&self) -> bool {
        self.available_permits() == 0
    }
}

/// 信号量许可
pub struct SemaphorePermit {
    semaphore: Arc<Mutex<usize>>,
    stats: Arc<SemaphoreStats>,
}

impl Drop for SemaphorePermit {
    fn drop(&mut self) {
        let mut permits = self.semaphore.lock().unwrap();
        *permits += 1;
        self.stats
            .release_count
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }
}
