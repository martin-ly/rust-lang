//! 无锁内存管理
//!
//! 本模块展示无锁数据结构中常见的内存管理技术：
//! - Epoch-Based Reclamation (EBR)
//! - Hazard Pointers
//! - 引用计数
//!
//! ## Epoch-Based Reclamation
//!
//! EBR 是一种高效的内存回收机制，由 `crossbeam-epoch` 实现。
//! 它将操作分为三个阶段（epoch），确保没有线程访问旧 epoch 的内存后安全释放。
//!
//! ## 使用 crossbeam-epoch
//!
//! ```ignore
//! use crossbeam_epoch::{self, Atomic, Owned, Shared, Guard};
//!
//! let guard = &crossbeam_epoch::pin();
//! // 在 guard 保护下安全地访问无锁数据结构
//! ```
use std::sync::atomic::{AtomicUsize, Ordering};

/// 全局 Epoch 计数器
///
/// 用于协调所有线程的内存回收进度。
static GLOBAL_EPOCH: AtomicUsize = AtomicUsize::new(0);

/// Epoch-Based Reclamation 管理器
///
/// 简化版的 EBR 管理器，展示核心概念。
pub struct EpochManager {
    local_epoch: AtomicUsize,
}

impl EpochManager {
    /// 创建新的 Epoch 管理器
    pub const fn new() -> Self {
        Self {
            local_epoch: AtomicUsize::new(0),
        }
    }

    /// 进入当前 epoch（pin）
    ///
    /// 线程在访问共享数据前必须 pin，防止其访问的内存被回收。
    pub fn pin(&self) -> usize {
        let global = GLOBAL_EPOCH.load(Ordering::Acquire);
        self.local_epoch.store(global, Ordering::Release);
        global
    }

    /// 解除 pin
    ///
    /// 线程完成共享数据访问后应 unpin，允许内存回收。
    pub fn unpin(&self) {
        self.local_epoch.store(usize::MAX, Ordering::Release);
    }

    /// 尝试推进全局 epoch
    ///
    /// 当所有线程都进入新 epoch 时，可以安全回收旧 epoch 的内存。
    pub fn try_advance_epoch(&self) -> bool {
        let current = GLOBAL_EPOCH.load(Ordering::Acquire);
        // 简化实现：直接推进 epoch
        GLOBAL_EPOCH
            .compare_exchange_weak(
                current,
                current.wrapping_add(1),
                Ordering::Release,
                Ordering::Relaxed,
            )
            .is_ok()
    }

    /// 获取当前全局 epoch
    pub fn current_epoch() -> usize {
        GLOBAL_EPOCH.load(Ordering::Acquire)
    }
}

/// 基于 Epoch 的内存回收队列
///
/// 将待释放的内存按 epoch 分批管理。
pub struct EpochReclaimer<T> {
    epochs: [Vec<T>; 3],
    current: AtomicUsize,
}

impl<T> EpochReclaimer<T> {
    /// 创建新的 Epoch 回收器
    pub fn new() -> Self {
        Self {
            epochs: [Vec::new(), Vec::new(), Vec::new()],
            current: AtomicUsize::new(0),
        }
    }

    /// 将数据加入当前 epoch 的退役列表
    pub fn defer(&mut self, data: T) {
        let idx = self.current.load(Ordering::Relaxed) % 3;
        self.epochs[idx].push(data);
    }

    /// 推进 epoch，返回可以安全释放的数据
    ///
    /// 三 epoch 轮转：当前 → 上一批次 → 上上批次（可回收）。
    pub fn advance(&mut self) -> Vec<T> {
        let current = self.current.load(Ordering::Relaxed) % 3;
        // 返回上上 epoch 的数据（确保所有线程都已离开）
        let reclaim_idx = (current + 2) % 3;
        self.current.fetch_add(1, Ordering::Relaxed);
        std::mem::take(&mut self.epochs[reclaim_idx])
    }
}

impl<T> Default for EpochReclaimer<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// 引用计数节点包装器
///
/// 使用引用计数管理共享节点的生命周期。
pub struct ArcNode<T> {
    data: T,
    ref_count: AtomicUsize,
}

impl<T> ArcNode<T> {
    /// 创建新的引用计数节点
    pub fn new(data: T) -> Self {
        Self {
            data,
            ref_count: AtomicUsize::new(1),
        }
    }

    /// 增加引用计数
    pub fn acquire(&self) {
        self.ref_count.fetch_add(1, Ordering::Relaxed);
    }

    /// 减少引用计数，返回是否需要释放
    pub fn release(&self) -> bool {
        self.ref_count.fetch_sub(1, Ordering::Release) == 1
    }

    /// 获取数据引用
    pub fn data(&self) -> &T {
        &self.data
    }
}

/// 内存管理策略枚举
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemoryStrategy {
    /// Epoch-Based Reclamation
    EpochReclamation,
    /// Hazard Pointers
    HazardPointers,
    /// Reference Counting
    ReferenceCounting,
}

/// 获取内存管理策略说明
pub fn strategy_description(strategy: MemoryStrategy) -> &'static str {
    match strategy {
        MemoryStrategy::EpochReclamation => {
            "Epoch-Based Reclamation: 高效的无锁内存回收，适用于读多写少的场景"
        }
        MemoryStrategy::HazardPointers => {
            "Hazard Pointers: 每个线程声明正在访问的指针，防止内存被提前释放"
        }
        MemoryStrategy::ReferenceCounting => {
            "Reference Counting: 使用原子引用计数管理共享内存生命周期"
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_epoch_manager() {
        let manager = EpochManager::new();
        let epoch = manager.pin();
        assert_eq!(epoch, EpochManager::current_epoch());
        manager.unpin();
    }

    #[test]
    fn test_epoch_advance() {
        let manager = EpochManager::new();
        manager.pin();
        assert!(manager.try_advance_epoch());
        manager.unpin();
    }

    #[test]
    fn test_epoch_reclaimer() {
        let mut reclaimer = EpochReclaimer::new();
        reclaimer.defer(Box::new(1));
        reclaimer.defer(Box::new(2));
        let reclaimed = reclaimer.advance();
        assert!(reclaimed.is_empty()); // 第一次 advance 没有数据可以回收

        reclaimer.defer(Box::new(3));
        let reclaimed = reclaimer.advance();
        assert_eq!(reclaimed.len(), 2); // 回收前两个
    }

    #[test]
    fn test_arc_node() {
        let node = ArcNode::new(42);
        assert_eq!(*node.data(), 42);

        node.acquire();
        assert!(!node.release());
        assert!(node.release());
    }

    #[test]
    fn test_strategy_description() {
        assert!(strategy_description(MemoryStrategy::EpochReclamation).contains("Epoch"));
        assert!(strategy_description(MemoryStrategy::HazardPointers).contains("Hazard"));
        assert!(strategy_description(MemoryStrategy::ReferenceCounting).contains("Reference"));
    }
}
