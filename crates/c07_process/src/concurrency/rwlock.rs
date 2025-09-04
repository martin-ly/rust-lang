// 读写锁模块
// 这个模块提供了进程安全的读写锁实现

use crate::types::SyncConfig;
use crate::error::SyncResult;
use std::sync::{Arc, RwLock as StdRwLock};
use std::time::Instant;

/// 进程安全的读写锁
pub struct ProcessRwLock {
    name: String,
    inner: StdRwLock<()>,
    config: SyncConfig,
    stats: Arc<RwLockStats>,
}

struct RwLockStats {
    read_lock_count: std::sync::atomic::AtomicUsize,
    write_lock_count: std::sync::atomic::AtomicUsize,
    read_unlock_count: std::sync::atomic::AtomicUsize,
    write_unlock_count: std::sync::atomic::AtomicUsize,
    total_wait_time: std::sync::atomic::AtomicUsize,
    max_wait_time: std::sync::atomic::AtomicUsize,
}

impl ProcessRwLock {
    /// 创建新的读写锁
    pub fn new(name: &str, config: SyncConfig) -> Self {
        Self {
            name: name.to_string(),
            inner: StdRwLock::new(()),
            config,
            stats: Arc::new(RwLockStats {
                read_lock_count: std::sync::atomic::AtomicUsize::new(0),
                write_lock_count: std::sync::atomic::AtomicUsize::new(0),
                read_unlock_count: std::sync::atomic::AtomicUsize::new(0),
                write_unlock_count: std::sync::atomic::AtomicUsize::new(0),
                total_wait_time: std::sync::atomic::AtomicUsize::new(0),
                max_wait_time: std::sync::atomic::AtomicUsize::new(0),
            }),
        }
    }

    /// 尝试获取读锁
    pub fn try_read(&self) -> Option<RwLockReadGuard> {
        if let Ok(guard) = self.inner.try_read() {
            self.stats.read_lock_count.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            Some(RwLockReadGuard {
                guard,
                stats: Arc::clone(&self.stats),
            })
        } else {
            None
        }
    }

    /// 尝试获取写锁
    pub fn try_write(&self) -> Option<RwLockWriteGuard> {
        if let Ok(guard) = self.inner.try_write() {
            self.stats.write_lock_count.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            Some(RwLockWriteGuard {
                guard,
                stats: Arc::clone(&self.stats),
            })
        } else {
            None
        }
    }

    /// 获取读锁
    pub fn read(&self) -> SyncResult<RwLockReadGuard> {
        let start = Instant::now();
        
        let guard = self.inner.read()
            .map_err(|e| crate::error::SyncError::LockAcquisitionFailed(e.to_string()))?;
        
        let wait_time = start.elapsed();
        let wait_time_ns = wait_time.as_nanos() as usize;
        
        self.stats.read_lock_count.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        self.stats.total_wait_time.fetch_add(wait_time_ns, std::sync::atomic::Ordering::Relaxed);
        
        Ok(RwLockReadGuard {
            guard,
            stats: Arc::clone(&self.stats),
        })
    }

    /// 获取写锁
    pub fn write(&self) -> SyncResult<RwLockWriteGuard> {
        let start = Instant::now();
        
        let guard = self.inner.write()
            .map_err(|e| crate::error::SyncError::LockAcquisitionFailed(e.to_string()))?;
        
        let wait_time = start.elapsed();
        let wait_time_ns = wait_time.as_nanos() as usize;
        
        self.stats.write_lock_count.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        self.stats.total_wait_time.fetch_add(wait_time_ns, std::sync::atomic::Ordering::Relaxed);
        
        Ok(RwLockWriteGuard {
            guard,
            stats: Arc::clone(&self.stats),
        })
    }
    
    /// 检查锁是否被持有
    pub fn is_locked(&self) -> bool {
        self.inner.try_read().is_err() && self.inner.try_write().is_err()
    }
}

/// 读写锁读守卫
pub struct RwLockReadGuard<'a> {
    guard: std::sync::RwLockReadGuard<'a, ()>,
    stats: Arc<RwLockStats>,
}

impl<'a> Drop for RwLockReadGuard<'a> {
    fn drop(&mut self) {
        self.stats.read_unlock_count.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }
}

/// 读写锁写守卫
pub struct RwLockWriteGuard<'a> {
    guard: std::sync::RwLockWriteGuard<'a, ()>,
    stats: Arc<RwLockStats>,
}

impl<'a> Drop for RwLockWriteGuard<'a> {
    fn drop(&mut self) {
        self.stats.write_unlock_count.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }
}
