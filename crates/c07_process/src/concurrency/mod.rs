pub mod mutex;
pub mod semaphore;
pub mod barrier;
pub mod atomic;
pub mod rwlock;
pub mod condvar;

use crate::types::{SyncConfig, SyncPrimitive};
use crate::error::{SyncResult, SyncError};
use std::sync::{Arc, Mutex as StdMutex, RwLock as StdRwLock, Condvar as StdCondvar};
use std::collections::HashMap;
use std::time::{Duration, Instant};
use std::sync::atomic::{AtomicUsize, Ordering};

/// 同步管理器
pub struct SyncManager {
    primitives: Arc<StdMutex<HashMap<String, Arc<dyn SyncPrimitiveTrait>>>>,
    config: SyncConfig,
}

/// 同步原语trait
pub trait SyncPrimitiveTrait: Send + Sync {
    /// 获取原语名称
    fn name(&self) -> &str;
    
    /// 获取原语类型
    fn primitive_type(&self) -> SyncPrimitive;
    
    /// 检查是否被锁定
    fn is_locked(&self) -> bool;
    
    /// 获取等待者数量
    fn waiter_count(&self) -> usize;
    
    /// 获取统计信息
    fn get_stats(&self) -> PrimitiveStats;
}

/// 原语统计信息
#[derive(Debug, Clone)]
pub struct PrimitiveStats {
    pub name: String,
    pub primitive_type: SyncPrimitive,
    pub is_locked: bool,
    pub waiter_count: usize,
    pub lock_count: u64,
    pub unlock_count: u64,
    pub total_wait_time: Duration,
    pub max_wait_time: Duration,
}

impl SyncManager {
    /// 创建新的同步管理器
    pub fn new(config: SyncConfig) -> Self {
        Self {
            primitives: Arc::new(StdMutex::new(HashMap::new())),
            config,
        }
    }

    /// 创建互斥锁
    pub fn create_mutex(&mut self, name: &str) -> SyncResult<Arc<ProcessMutex>> {
        let mutex = ProcessMutex::new(name, self.config.clone());
        let arc_mutex = Arc::new(mutex);
        
        let primitive = arc_mutex.clone() as Arc<dyn SyncPrimitiveTrait>;
        self.primitives.lock().unwrap().insert(name.to_string(), primitive);
        
        Ok(arc_mutex)
    }

    /// 创建读写锁
    pub fn create_rwlock(&mut self, name: &str) -> SyncResult<Arc<ProcessRwLock>> {
        let rwlock = ProcessRwLock::new(name, self.config.clone());
        let arc_rwlock = Arc::new(rwlock);
        
        let primitive = arc_rwlock.clone() as Arc<dyn SyncPrimitiveTrait>;
        self.primitives.lock().unwrap().insert(name.to_string(), primitive);
        
        Ok(arc_rwlock)
    }

    /// 创建条件变量
    pub fn create_condvar(&mut self, name: &str) -> SyncResult<Arc<ProcessCondVar>> {
        let condvar = ProcessCondVar::new(name, self.config.clone());
        let arc_condvar = Arc::new(condvar);
        
        let primitive = arc_condvar.clone() as Arc<dyn SyncPrimitiveTrait>;
        self.primitives.lock().unwrap().insert(name.to_string(), primitive);
        
        Ok(arc_condvar)
    }

    /// 创建信号量
    pub fn create_semaphore(&mut self, name: &str, permits: usize) -> SyncResult<Arc<ProcessSemaphore>> {
        let semaphore = ProcessSemaphore::new(name, permits, self.config.clone());
        let arc_semaphore = Arc::new(semaphore);
        
        let primitive = arc_semaphore.clone() as Arc<dyn SyncPrimitiveTrait>;
        self.primitives.lock().unwrap().insert(name.to_string(), primitive);
        
        Ok(arc_semaphore)
    }

    /// 创建屏障
    pub fn create_barrier(&mut self, name: &str, parties: usize) -> SyncResult<Arc<ProcessBarrier>> {
        let barrier = ProcessBarrier::new(name, parties, self.config.clone());
        let arc_barrier = Arc::new(barrier);
        
        let primitive = arc_barrier.clone() as Arc<dyn SyncPrimitiveTrait>;
        self.primitives.lock().unwrap().insert(name.to_string(), primitive);
        
        Ok(arc_barrier)
    }

    /// 获取所有原语名称
    pub fn get_primitive_names(&self) -> Vec<String> {
        self.primitives.lock().unwrap().keys().cloned().collect()
    }

    /// 检查原语是否存在
    pub fn has_primitive(&self, name: &str) -> bool {
        self.primitives.lock().unwrap().contains_key(name)
    }

    /// 获取原语统计信息
    pub fn get_primitive_stats(&self, name: &str) -> Option<PrimitiveStats> {
        let primitives = self.primitives.lock().unwrap();
        primitives.get(name).map(|p| p.get_stats())
    }

    /// 获取所有原语统计信息
    pub fn get_all_stats(&self) -> HashMap<String, PrimitiveStats> {
        let primitives = self.primitives.lock().unwrap();
        let mut stats = HashMap::new();
        
        for (name, primitive) in primitives.iter() {
            stats.insert(name.clone(), primitive.get_stats());
        }
        
        stats
    }
}

impl Default for SyncManager {
    fn default() -> Self {
        Self::new(SyncConfig::default())
    }
}

/// 进程安全的互斥锁
pub struct ProcessMutex {
    name: String,
    inner: StdMutex<()>,
    config: SyncConfig,
    stats: Arc<MutexStats>,
}

struct MutexStats {
    lock_count: AtomicUsize,
    unlock_count: AtomicUsize,
    total_wait_time: AtomicUsize, // 以纳秒为单位
    max_wait_time: AtomicUsize,
}

impl ProcessMutex {
    /// 创建新的互斥锁
    pub fn new(name: &str, config: SyncConfig) -> Self {
        Self {
            name: name.to_string(),
            inner: StdMutex::new(()),
            config,
            stats: Arc::new(MutexStats {
                lock_count: AtomicUsize::new(0),
                unlock_count: AtomicUsize::new(0),
                total_wait_time: AtomicUsize::new(0),
                max_wait_time: AtomicUsize::new(0),
            }),
        }
    }

    /// 尝试获取锁
    pub fn try_lock(&self) -> Option<MutexGuard> {
        if let Ok(guard) = self.inner.try_lock() {
            self.stats.lock_count.fetch_add(1, Ordering::Relaxed);
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
            .map_err(|e| SyncError::LockAcquisitionFailed(e.to_string()))?;
        
        let wait_time = start.elapsed();
        let wait_time_ns = wait_time.as_nanos() as usize;
        
        self.stats.lock_count.fetch_add(1, Ordering::Relaxed);
        self.stats.total_wait_time.fetch_add(wait_time_ns, Ordering::Relaxed);
        
        // 更新最大等待时间
        let mut current_max = self.stats.max_wait_time.load(Ordering::Relaxed);
        while current_max < wait_time_ns {
            match self.stats.max_wait_time.compare_exchange_weak(
                current_max,
                wait_time_ns,
                Ordering::Relaxed,
                Ordering::Relaxed,
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
                return Err(SyncError::Timeout(timeout));
            }
            
            std::thread::yield_now();
        }
    }
}

/// 互斥锁守卫
pub struct MutexGuard<'a> {
    guard: std::sync::MutexGuard<'a, ()>,
    stats: Arc<MutexStats>,
}

impl<'a> Drop for MutexGuard<'a> {
    fn drop(&mut self) {
        self.stats.unlock_count.fetch_add(1, Ordering::Relaxed);
    }
}

/// 进程安全的读写锁
pub struct ProcessRwLock {
    name: String,
    inner: StdRwLock<()>,
    stats: Arc<RwLockStats>,
}

struct RwLockStats {
    read_lock_count: AtomicUsize,
    write_lock_count: AtomicUsize,
    read_unlock_count: AtomicUsize,
    write_unlock_count: AtomicUsize,
    total_wait_time: AtomicUsize,
    max_wait_time: AtomicUsize,
}

impl ProcessRwLock {
    /// 创建新的读写锁
    pub fn new(name: &str, config: SyncConfig) -> Self {
        Self {
            name: name.to_string(),
            inner: StdRwLock::new(()),
            stats: Arc::new(RwLockStats {
                read_lock_count: AtomicUsize::new(0),
                write_lock_count: AtomicUsize::new(0),
                read_unlock_count: AtomicUsize::new(0),
                write_unlock_count: AtomicUsize::new(0),
                total_wait_time: AtomicUsize::new(0),
                max_wait_time: AtomicUsize::new(0),
            }),
        }
    }

    /// 尝试获取读锁
    pub fn try_read(&self) -> Option<RwLockReadGuard<'_>> {
        if let Ok(guard) = self.inner.try_read() {
            self.stats.read_lock_count.fetch_add(1, Ordering::Relaxed);
            Some(RwLockReadGuard {
                guard,
                stats: Arc::clone(&self.stats),
            })
        } else {
            None
        }
    }

    /// 尝试获取写锁
    pub fn try_write(&self) -> Option<RwLockWriteGuard<'_>> {
        if let Ok(guard) = self.inner.try_write() {
            self.stats.write_lock_count.fetch_add(1, Ordering::Relaxed);
            Some(RwLockWriteGuard {
                guard,
                stats: Arc::clone(&self.stats),
            })
        } else {
            None
        }
    }

    /// 获取读锁
    pub fn read(&self) -> SyncResult<RwLockReadGuard<'_>> {
        let start = Instant::now();
        
        let guard = self.inner.read()
            .map_err(|e| SyncError::LockAcquisitionFailed(e.to_string()))?;
        
        let wait_time = start.elapsed();
        let wait_time_ns = wait_time.as_nanos() as usize;
        
        self.stats.read_lock_count.fetch_add(1, Ordering::Relaxed);
        self.stats.total_wait_time.fetch_add(wait_time_ns, Ordering::Relaxed);
        
        Ok(RwLockReadGuard {
            guard,
            stats: Arc::clone(&self.stats),
        })
    }

    /// 获取写锁
    pub fn write(&self) -> SyncResult<RwLockWriteGuard<'_>> {
        let start = Instant::now();
        
        let guard = self.inner.write()
            .map_err(|e| SyncError::LockAcquisitionFailed(e.to_string()))?;
        
        let wait_time = start.elapsed();
        let wait_time_ns = wait_time.as_nanos() as usize;
        
        self.stats.write_lock_count.fetch_add(1, Ordering::Relaxed);
        self.stats.total_wait_time.fetch_add(wait_time_ns, Ordering::Relaxed);
        
        Ok(RwLockWriteGuard {
            guard,
            stats: Arc::clone(&self.stats),
        })
    }
}

/// 读写锁读守卫
pub struct RwLockReadGuard<'a> {
    guard: std::sync::RwLockReadGuard<'a, ()>,
    stats: Arc<RwLockStats>,
}

impl<'a> Drop for RwLockReadGuard<'a> {
    fn drop(&mut self) {
        self.stats.read_unlock_count.fetch_add(1, Ordering::Relaxed);
    }
}

/// 读写锁写守卫
pub struct RwLockWriteGuard<'a> {
    guard: std::sync::RwLockWriteGuard<'a, ()>,
    stats: Arc<RwLockStats>,
}

impl<'a> Drop for RwLockWriteGuard<'a> {
    fn drop(&mut self) {
        self.stats.write_unlock_count.fetch_add(1, Ordering::Relaxed);
    }
}

/// 进程安全的条件变量
pub struct ProcessCondVar {
    name: String,
    inner: StdCondvar,
    stats: Arc<CondVarStats>,
}

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
            inner: StdCondvar::new(),
            stats: Arc::new(CondVarStats {
                wait_count: AtomicUsize::new(0),
                notify_count: AtomicUsize::new(0),
                total_wait_time: AtomicUsize::new(0),
                max_wait_time: AtomicUsize::new(0),
            }),
        }
    }

    /// 等待条件满足
    pub fn wait<'a, T>(&self, guard: std::sync::MutexGuard<'a, T>) -> SyncResult<std::sync::MutexGuard<'a, T>> {
        let start = Instant::now();
        
        self.stats.wait_count.fetch_add(1, Ordering::Relaxed);
        
        let guard = self.inner.wait(guard)
            .map_err(|e| SyncError::CondVarError(e.to_string()))?;
        
        let wait_time = start.elapsed();
        let wait_time_ns = wait_time.as_nanos() as usize;
        
        self.stats.total_wait_time.fetch_add(wait_time_ns, Ordering::Relaxed);
        
        Ok(guard)
    }

    /// 带超时的等待
    pub fn wait_timeout<'a, T>(
        &self,
        guard: std::sync::MutexGuard<'a, T>,
        timeout: Duration,
    ) -> SyncResult<std::sync::MutexGuard<'a, T>> {
        let start = Instant::now();
        
        self.stats.wait_count.fetch_add(1, Ordering::Relaxed);
        
        let (guard, _) = self.inner.wait_timeout(guard, timeout)
            .map_err(|e| SyncError::CondVarError(e.to_string()))?;
        
        let wait_time = start.elapsed();
        let wait_time_ns = wait_time.as_nanos() as usize;
        
        self.stats.total_wait_time.fetch_add(wait_time_ns, Ordering::Relaxed);
        
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

/// 进程安全的信号量
pub struct ProcessSemaphore {
    name: String,
    permits: Arc<AtomicUsize>,
    config: SyncConfig,
    stats: Arc<SemaphoreStats>,
}

struct SemaphoreStats {
    acquire_count: AtomicUsize,
    release_count: AtomicUsize,
    total_wait_time: AtomicUsize,
    max_wait_time: AtomicUsize,
}

impl ProcessSemaphore {
    /// 创建新的信号量
    pub fn new(name: &str, permits: usize, config: SyncConfig) -> Self {
        Self {
            name: name.to_string(),
            permits: Arc::new(AtomicUsize::new(permits)),
            config,
            stats: Arc::new(SemaphoreStats {
                acquire_count: AtomicUsize::new(0),
                release_count: AtomicUsize::new(0),
                total_wait_time: AtomicUsize::new(0),
                max_wait_time: AtomicUsize::new(0),
            }),
        }
    }

    /// 尝试获取许可
    pub fn try_acquire(&self) -> Option<SemaphorePermit> {
        let mut current = self.permits.load(Ordering::Relaxed);
        
        loop {
            if current == 0 {
                return None;
            }
            
            match self.permits.compare_exchange_weak(
                current,
                current - 1,
                Ordering::Acquire,
                Ordering::Relaxed,
            ) {
                Ok(_) => {
                    self.stats.acquire_count.fetch_add(1, Ordering::Relaxed);
                    return Some(SemaphorePermit {
                        semaphore: Arc::clone(&self.permits),
                        stats: Arc::clone(&self.stats),
                    });
                }
                Err(actual) => {
                    current = actual;
                }
            }
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
                return Err(SyncError::Timeout(self.config.timeout));
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
                return Err(SyncError::Timeout(timeout));
            }
            
            std::thread::yield_now();
        }
    }

    /// 获取当前可用许可数量
    pub fn available_permits(&self) -> usize {
        self.permits.load(Ordering::Relaxed)
    }
}

/// 信号量许可
pub struct SemaphorePermit {
    semaphore: Arc<AtomicUsize>,
    stats: Arc<SemaphoreStats>,
}

impl Drop for SemaphorePermit {
    fn drop(&mut self) {
        self.semaphore.fetch_add(1, Ordering::Relaxed);
        self.stats.release_count.fetch_add(1, Ordering::Relaxed);
    }
}

/// 进程安全的屏障
pub struct ProcessBarrier {
    name: String,
    parties: usize,
    current: AtomicUsize,
    generation: AtomicUsize,
    config: SyncConfig,
    stats: Arc<BarrierStats>,
}

struct BarrierStats {
    wait_count: AtomicUsize,
    total_wait_time: AtomicUsize,
    max_wait_time: AtomicUsize,
}

impl ProcessBarrier {
    /// 创建新的屏障
    pub fn new(name: &str, parties: usize, config: SyncConfig) -> Self {
        Self {
            name: name.to_string(),
            parties,
            current: AtomicUsize::new(parties),
            generation: AtomicUsize::new(0),
            config,
            stats: Arc::new(BarrierStats {
                wait_count: AtomicUsize::new(0),
                total_wait_time: AtomicUsize::new(0),
                max_wait_time: AtomicUsize::new(0),
            }),
        }
    }

    /// 等待所有参与者到达
    pub fn wait(&self) -> SyncResult<BarrierWaitResult> {
        let start = Instant::now();
        
        self.stats.wait_count.fetch_add(1, Ordering::Relaxed);
        
        let generation = self.generation.load(Ordering::Relaxed);
        let position = self.current.fetch_sub(1, Ordering::Relaxed) - 1;
        
        if position == 0 {
            // 最后一个参与者
            self.current.store(self.parties, Ordering::Relaxed);
            self.generation.fetch_add(1, Ordering::Relaxed);
            
            let wait_time = start.elapsed();
            let wait_time_ns = wait_time.as_nanos() as usize;
            
            self.stats.total_wait_time.fetch_add(wait_time_ns, Ordering::Relaxed);
            
            Ok(BarrierWaitResult::Barrier)
        } else {
            // 等待其他参与者
            loop {
                if self.generation.load(Ordering::Relaxed) != generation {
                    let wait_time = start.elapsed();
                    let wait_time_ns = wait_time.as_nanos() as usize;
                    
                    self.stats.total_wait_time.fetch_add(wait_time_ns, Ordering::Relaxed);
                    
                    return Ok(BarrierWaitResult::Wait);
                }
                
                if self.config.timeout != Duration::ZERO && start.elapsed() >= self.config.timeout {
                    return Err(SyncError::Timeout(self.config.timeout));
                }
                
                std::thread::yield_now();
            }
        }
    }
}

/// 屏障等待结果
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BarrierWaitResult {
    /// 等待其他参与者
    Wait,
    /// 所有参与者都已到达
    Barrier,
}

// 为所有同步原语实现SyncPrimitiveTrait
impl SyncPrimitiveTrait for ProcessMutex {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn primitive_type(&self) -> SyncPrimitive {
        SyncPrimitive::Mutex
    }
    
    fn is_locked(&self) -> bool {
        self.inner.try_lock().is_err()
    }
    
    fn waiter_count(&self) -> usize {
        0 // 标准库互斥锁不提供等待者数量
    }
    
    fn get_stats(&self) -> PrimitiveStats {
        PrimitiveStats {
            name: self.name.clone(),
            primitive_type: SyncPrimitive::Mutex,
            is_locked: self.is_locked(),
            waiter_count: self.waiter_count(),
            lock_count: self.stats.lock_count.load(Ordering::Relaxed) as u64,
            unlock_count: self.stats.unlock_count.load(Ordering::Relaxed) as u64,
            total_wait_time: Duration::from_nanos(self.stats.total_wait_time.load(Ordering::Relaxed) as u64),
            max_wait_time: Duration::from_nanos(self.stats.max_wait_time.load(Ordering::Relaxed) as u64),
        }
    }
}

impl SyncPrimitiveTrait for ProcessRwLock {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn primitive_type(&self) -> SyncPrimitive {
        SyncPrimitive::RwLock
    }
    
    fn is_locked(&self) -> bool {
        self.inner.try_read().is_err() && self.inner.try_write().is_err()
    }
    
    fn waiter_count(&self) -> usize {
        0 // 标准库读写锁不提供等待者数量
    }
    
    fn get_stats(&self) -> PrimitiveStats {
        let read_locks = self.stats.read_lock_count.load(Ordering::Relaxed);
        let write_locks = self.stats.write_lock_count.load(Ordering::Relaxed);
        let read_unlocks = self.stats.read_unlock_count.load(Ordering::Relaxed);
        let write_unlocks = self.stats.write_unlock_count.load(Ordering::Relaxed);
        
        PrimitiveStats {
            name: self.name.clone(),
            primitive_type: SyncPrimitive::RwLock,
            is_locked: self.is_locked(),
            waiter_count: self.waiter_count(),
            lock_count: (read_locks + write_locks) as u64,
            unlock_count: (read_unlocks + write_unlocks) as u64,
            total_wait_time: Duration::from_nanos(self.stats.total_wait_time.load(Ordering::Relaxed) as u64),
            max_wait_time: Duration::from_nanos(self.stats.max_wait_time.load(Ordering::Relaxed) as u64),
        }
    }
}

impl SyncPrimitiveTrait for ProcessCondVar {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn primitive_type(&self) -> SyncPrimitive {
        SyncPrimitive::CondVar
    }
    
    fn is_locked(&self) -> bool {
        false // 条件变量本身不锁定
    }
    
    fn waiter_count(&self) -> usize {
        0 // 标准库条件变量不提供等待者数量
    }
    
    fn get_stats(&self) -> PrimitiveStats {
        PrimitiveStats {
            name: self.name.clone(),
            primitive_type: SyncPrimitive::CondVar,
            is_locked: self.is_locked(),
            waiter_count: self.waiter_count(),
            lock_count: self.stats.wait_count.load(Ordering::Relaxed) as u64,
            unlock_count: self.stats.notify_count.load(Ordering::Relaxed) as u64,
            total_wait_time: Duration::from_nanos(self.stats.total_wait_time.load(Ordering::Relaxed) as u64),
            max_wait_time: Duration::from_nanos(self.stats.max_wait_time.load(Ordering::Relaxed) as u64),
        }
    }
}

impl SyncPrimitiveTrait for ProcessSemaphore {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn primitive_type(&self) -> SyncPrimitive {
        SyncPrimitive::Semaphore
    }
    
    fn is_locked(&self) -> bool {
        self.available_permits() == 0
    }
    
    fn waiter_count(&self) -> usize {
        0 // 信号量不提供等待者数量
    }
    
    fn get_stats(&self) -> PrimitiveStats {
        PrimitiveStats {
            name: self.name.clone(),
            primitive_type: SyncPrimitive::Semaphore,
            is_locked: self.is_locked(),
            waiter_count: self.waiter_count(),
            lock_count: self.stats.acquire_count.load(Ordering::Relaxed) as u64,
            unlock_count: self.stats.release_count.load(Ordering::Relaxed) as u64,
            total_wait_time: Duration::from_nanos(self.stats.total_wait_time.load(Ordering::Relaxed) as u64),
            max_wait_time: Duration::from_nanos(self.stats.max_wait_time.load(Ordering::Relaxed) as u64),
        }
    }
}

impl SyncPrimitiveTrait for ProcessBarrier {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn primitive_type(&self) -> SyncPrimitive {
        SyncPrimitive::Barrier
    }
    
    fn is_locked(&self) -> bool {
        self.current.load(Ordering::Relaxed) < self.parties
    }
    
    fn waiter_count(&self) -> usize {
        self.parties - self.current.load(Ordering::Relaxed)
    }
    
    fn get_stats(&self) -> PrimitiveStats {
        PrimitiveStats {
            name: self.name.clone(),
            primitive_type: SyncPrimitive::Barrier,
            is_locked: self.is_locked(),
            waiter_count: self.waiter_count(),
            lock_count: self.stats.wait_count.load(Ordering::Relaxed) as u64,
            unlock_count: 0, // 屏障没有解锁概念
            total_wait_time: Duration::from_nanos(self.stats.total_wait_time.load(Ordering::Relaxed) as u64),
            max_wait_time: Duration::from_nanos(self.stats.max_wait_time.load(Ordering::Relaxed) as u64),
        }
    }
}
