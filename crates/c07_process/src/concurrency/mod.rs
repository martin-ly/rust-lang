pub mod atomic;
pub mod barrier;
pub mod condvar;
pub mod mutex;
pub mod rwlock;
pub mod semaphore;

use crate::error::SyncResult;
use crate::types::{SyncConfig, SyncPrimitive};
use std::collections::HashMap;
use std::sync::{Arc, Mutex as StdMutex};
use std::time::Duration;

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
    pub fn create_mutex(
        &mut self,
        name: &str,
    ) -> SyncResult<Arc<crate::concurrency::mutex::ProcessMutex>> {
        let mutex = crate::concurrency::mutex::ProcessMutex::new(name, self.config.clone());
        let arc_mutex = Arc::new(mutex);

        let primitive = arc_mutex.clone() as Arc<dyn SyncPrimitiveTrait>;
        self.primitives
            .lock()
            .unwrap()
            .insert(name.to_string(), primitive);

        Ok(arc_mutex)
    }

    /// 创建读写锁
    pub fn create_rwlock(
        &mut self,
        name: &str,
    ) -> SyncResult<Arc<crate::concurrency::rwlock::ProcessRwLock>> {
        let rwlock = crate::concurrency::rwlock::ProcessRwLock::new(name, self.config.clone());
        let arc_rwlock = Arc::new(rwlock);

        let primitive = arc_rwlock.clone() as Arc<dyn SyncPrimitiveTrait>;
        self.primitives
            .lock()
            .unwrap()
            .insert(name.to_string(), primitive);

        Ok(arc_rwlock)
    }

    /// 创建条件变量
    pub fn create_condvar(
        &mut self,
        name: &str,
    ) -> SyncResult<Arc<crate::concurrency::condvar::ProcessCondVar>> {
        let condvar = crate::concurrency::condvar::ProcessCondVar::new(name, self.config.clone());
        let arc_condvar = Arc::new(condvar);

        let primitive = arc_condvar.clone() as Arc<dyn SyncPrimitiveTrait>;
        self.primitives
            .lock()
            .unwrap()
            .insert(name.to_string(), primitive);

        Ok(arc_condvar)
    }

    /// 创建信号量
    pub fn create_semaphore(
        &mut self,
        name: &str,
        permits: usize,
    ) -> SyncResult<Arc<crate::concurrency::semaphore::ProcessSemaphore>> {
        let semaphore = crate::concurrency::semaphore::ProcessSemaphore::new(
            name,
            permits,
            self.config.clone(),
        );
        let arc_semaphore = Arc::new(semaphore);

        let primitive = arc_semaphore.clone() as Arc<dyn SyncPrimitiveTrait>;
        self.primitives
            .lock()
            .unwrap()
            .insert(name.to_string(), primitive);

        Ok(arc_semaphore)
    }

    /// 创建屏障
    pub fn create_barrier(
        &mut self,
        name: &str,
        parties: usize,
    ) -> SyncResult<Arc<crate::concurrency::barrier::ProcessBarrier>> {
        let barrier =
            crate::concurrency::barrier::ProcessBarrier::new(name, parties, self.config.clone());
        let arc_barrier = Arc::new(barrier);

        let primitive = arc_barrier.clone() as Arc<dyn SyncPrimitiveTrait>;
        self.primitives
            .lock()
            .unwrap()
            .insert(name.to_string(), primitive);

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

// 为所有同步原语实现SyncPrimitiveTrait
impl SyncPrimitiveTrait for crate::concurrency::mutex::ProcessMutex {
    fn name(&self) -> &str {
        self.name()
    }

    fn primitive_type(&self) -> SyncPrimitive {
        SyncPrimitive::Mutex
    }

    fn is_locked(&self) -> bool {
        self.is_locked()
    }

    fn waiter_count(&self) -> usize {
        0 // 标准库互斥锁不提供等待者数量
    }

    fn get_stats(&self) -> PrimitiveStats {
        PrimitiveStats {
            name: self.name().to_string(),
            primitive_type: SyncPrimitive::Mutex,
            is_locked: self.is_locked(),
            waiter_count: 0,                 // 标准库互斥锁不提供等待者数量
            lock_count: 0,                   // 从子模块获取
            unlock_count: 0,                 // 从子模块获取
            total_wait_time: Duration::ZERO, // 从子模块获取
            max_wait_time: Duration::ZERO,   // 从子模块获取
        }
    }
}

impl SyncPrimitiveTrait for crate::concurrency::rwlock::ProcessRwLock {
    fn name(&self) -> &str {
        self.name()
    }

    fn primitive_type(&self) -> SyncPrimitive {
        SyncPrimitive::RwLock
    }

    fn is_locked(&self) -> bool {
        self.is_locked()
    }

    fn waiter_count(&self) -> usize {
        0 // 标准库读写锁不提供等待者数量
    }

    fn get_stats(&self) -> PrimitiveStats {
        PrimitiveStats {
            name: self.name().to_string(),
            primitive_type: SyncPrimitive::RwLock,
            is_locked: self.is_locked(),
            waiter_count: 0,                 // 标准库读写锁不提供等待者数量
            lock_count: 0,                   // 从子模块获取
            unlock_count: 0,                 // 从子模块获取
            total_wait_time: Duration::ZERO, // 从子模块获取
            max_wait_time: Duration::ZERO,   // 从子模块获取
        }
    }
}

impl SyncPrimitiveTrait for crate::concurrency::condvar::ProcessCondVar {
    fn name(&self) -> &str {
        "ProcessCondVar"
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
            name: self.name().to_string(),
            primitive_type: SyncPrimitive::CondVar,
            is_locked: false,                // 条件变量本身不锁定
            waiter_count: 0,                 // 标准库条件变量不提供等待者数量
            lock_count: 0,                   // 从子模块获取
            unlock_count: 0,                 // 从子模块获取
            total_wait_time: Duration::ZERO, // 从子模块获取
            max_wait_time: Duration::ZERO,   // 从子模块获取
        }
    }
}

impl SyncPrimitiveTrait for crate::concurrency::semaphore::ProcessSemaphore {
    fn name(&self) -> &str {
        "ProcessSemaphore"
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
            name: self.name().to_string(),
            primitive_type: SyncPrimitive::Semaphore,
            is_locked: self.available_permits() == 0,
            waiter_count: 0,                 // 信号量不提供等待者数量
            lock_count: 0,                   // 从子模块获取
            unlock_count: 0,                 // 从子模块获取
            total_wait_time: Duration::ZERO, // 从子模块获取
            max_wait_time: Duration::ZERO,   // 从子模块获取
        }
    }
}

impl SyncPrimitiveTrait for crate::concurrency::barrier::ProcessBarrier {
    fn name(&self) -> &str {
        "ProcessBarrier"
    }

    fn primitive_type(&self) -> SyncPrimitive {
        SyncPrimitive::Barrier
    }

    fn is_locked(&self) -> bool {
        self.is_locked()
    }

    fn waiter_count(&self) -> usize {
        self.waiter_count()
    }

    fn get_stats(&self) -> PrimitiveStats {
        PrimitiveStats {
            name: self.name().to_string(),
            primitive_type: SyncPrimitive::Barrier,
            is_locked: self.is_locked(),
            waiter_count: self.waiter_count(),
            lock_count: 0,                   // 从子模块获取
            unlock_count: 0,                 // 屏障没有解锁概念
            total_wait_time: Duration::ZERO, // 从子模块获取
            max_wait_time: Duration::ZERO,   // 从子模块获取
        }
    }
}
