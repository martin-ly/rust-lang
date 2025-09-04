// 互斥锁模块
// 这个模块提供了进程安全的互斥锁实现

use crate::types::SyncConfig;
use crate::error::SyncResult;
use std::sync::{Arc, Mutex as StdMutex};
use std::time::{Duration, Instant};

/// 进程安全的互斥锁
#[allow(dead_code)]
pub struct ProcessMutex {
    name: String,
    inner: StdMutex<()>,
    config: SyncConfig,
    stats: Arc<MutexStats>,
}

struct MutexStats {
    lock_count: std::sync::atomic::AtomicUsize,
    unlock_count: std::sync::atomic::AtomicUsize,
    total_wait_time: std::sync::atomic::AtomicUsize, // 以纳秒为单位
    max_wait_time: std::sync::atomic::AtomicUsize,
}

impl ProcessMutex {
    /// 创建新的互斥锁
    pub fn new(name: &str, config: SyncConfig) -> Self {
        Self {
            name: name.to_string(),
            inner: StdMutex::new(()),
            config,
            stats: Arc::new(MutexStats {
                lock_count: std::sync::atomic::AtomicUsize::new(0),
                unlock_count: std::sync::atomic::AtomicUsize::new(0),
                total_wait_time: std::sync::atomic::AtomicUsize::new(0),
                max_wait_time: std::sync::atomic::AtomicUsize::new(0),
            }),
        }
    }

    /// 尝试获取锁
    #[allow(dead_code)]
    pub fn try_lock(&self) -> Option<MutexGuard> {
        if let Ok(guard) = self.inner.try_lock() {
            self.stats.lock_count.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            Some(MutexGuard {
                guard,
                stats: Arc::clone(&self.stats),
            })
        } else {
            None
        }
    }

    /// 获取锁（阻塞）
    pub fn lock(&self) -> SyncResult<MutexGuard> {
        let start = Instant::now();
        
        let guard = self.inner.lock()
            .map_err(|e| crate::error::SyncError::LockAcquisitionFailed(e.to_string()))?;
        
        let wait_time = start.elapsed();
        let wait_time_ns = wait_time.as_nanos() as usize;
        
        self.stats.lock_count.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        self.stats.total_wait_time.fetch_add(wait_time_ns, std::sync::atomic::Ordering::Relaxed);
        
        // 更新最大等待时间
        let mut current_max = self.stats.max_wait_time.load(std::sync::atomic::Ordering::Relaxed);
        while current_max < wait_time_ns {
            match self.stats.max_wait_time.compare_exchange_weak(
                current_max,
                wait_time_ns,
                std::sync::atomic::Ordering::Relaxed,
                std::sync::atomic::Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(new_current) => current_max = new_current,
            }
        }
        
        Ok(MutexGuard {
            guard,
            stats: Arc::clone(&self.stats),
        })
    }

    /// 带超时的锁获取
    pub fn lock_timeout(&self, timeout: Duration) -> SyncResult<MutexGuard> {
        let start = Instant::now();
        
        loop {
            if let Some(guard) = self.try_lock() {
                return Ok(guard);
            }
            
            if start.elapsed() >= timeout {
                return Err(crate::error::SyncError::Timeout(timeout));
            }
            
            std::thread::yield_now();
        }
    }
    
    /// 检查锁是否被持有
    pub fn is_locked(&self) -> bool {
        self.inner.try_lock().is_err()
    }
}

/// 互斥锁守卫
pub struct MutexGuard<'a> {
    guard: std::sync::MutexGuard<'a, ()>,
    stats: Arc<MutexStats>,
}

impl<'a> Drop for MutexGuard<'a> {
    fn drop(&mut self) {
        self.stats.unlock_count.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }
}
