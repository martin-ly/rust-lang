//! 无锁内存管理
//! lock-free memory management
//! 本模块展示无锁数据结构中常见的内存管理技术：
//! This module demonstrates lock-free data structure in memory technique ：
//! - 引用计数
//! - reference counting
//! ## Epoch-Based Reclamation
//!
//! ## 使用 crossbeam-epoch
//! ## use crossbeam-epoch
//! ```ignore
//! use crossbeam_epoch::{self, Atomic, Owned, Shared, Guard};
//!
//! let guard = &crossbeam_epoch::pin();
//! // 在 guard 保护下安全地访问无锁数据结构
//! // in guard under lock-free data structure
use std::sync::atomic::{AtomicUsize, Ordering};

/// 全局 Epoch 计数器
/// global Epoch
/// global Epoch 计数器
/// 用于协调所有线程的内存回收进度。
/// all thread memory 。
static GLOBAL_EPOCH: AtomicUsize = AtomicUsize::new(0);

/// Epoch-Based Reclamation 管理器
/// 简化版的 EBR 管理器，展示核心概念。
/// EBR ，core concept 。
/// 简化版 EBR 管理器，displaycoreconcept。
pub struct EpochManager {
    local_epoch: AtomicUsize,
}

impl Default for EpochManager {
    fn default() -> Self {
        Self::new()
    }
}

impl EpochManager {
    pub const fn new() -> Self {
        Self {
            local_epoch: AtomicUsize::new(0),
        }
    }

    /// 进入当前 epoch（pin）
    /// when before epoch（pin）
    /// 进入whenbefore epoch（pin）
    /// 线程在访问共享数据前必须 pin，防止其访问的内存被回收。
    /// thread in before must pin，its memory is 。
    pub fn pin(&self) -> usize {
        let global = GLOBAL_EPOCH.load(Ordering::Acquire);
        self.local_epoch.store(global, Ordering::Release);
        global
    }

    /// 解除 pin
    /// pin
    /// 线程完成共享数据访问后应 unpin，允许内存回收。
    /// thread after unpin，memory 。
    pub fn unpin(&self) {
        self.local_epoch.store(usize::MAX, Ordering::Release);
    }

    /// 尝试推进全局 epoch
    /// Attempts to推进全局 epoch
    /// global epoch
    /// 尝试推进global epoch
    /// Attempts to推进global epoch
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
    /// Gets当前全局 epoch
    /// when before global epoch
    pub fn current_epoch() -> usize {
        GLOBAL_EPOCH.load(Ordering::Acquire)
    }
}

pub struct EpochReclaimer<T> {
    epochs: [Vec<T>; 3],
    current: AtomicUsize,
}

impl<T> EpochReclaimer<T> {
    pub fn new() -> Self {
        Self {
            epochs: [Vec::new(), Vec::new(), Vec::new()],
            current: AtomicUsize::new(0),
        }
    }

    pub fn defer(&mut self, data: T) {
        let idx = self.current.load(Ordering::Relaxed) % 3;
        self.epochs[idx].push(data);
    }

    /// 三 epoch 轮转：当前 → 上一批次 → 上上批次（可回收）。
    /// epoch ：when before → on → on on （）。
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
/// reference counting node
/// 使用引用计数管理共享节点的生命周期。
/// reference counting node lifetime 。
pub struct ArcNode<T> {
    data: T,
    ref_count: AtomicUsize,
}

impl<T> ArcNode<T> {
    /// 创建新的引用计数节点
    /// Creates新的引用计数节点
    /// reference counting node
    pub fn new(data: T) -> Self {
        Self {
            data,
            ref_count: AtomicUsize::new(1),
        }
    }

    /// 增加引用计数
    /// Increases引用计数
    /// reference counting
    /// 增加reference counting
    /// Increasesreference counting
    pub fn acquire(&self) {
        self.ref_count.fetch_add(1, Ordering::Relaxed);
    }

    /// 减少引用计数，返回是否需要释放
    /// Decreases引用计数，返回是否需要释放
    /// reference counting ，
    pub fn release(&self) -> bool {
        self.ref_count.fetch_sub(1, Ordering::Release) == 1
    }

    /// 获取数据引用
    /// Gets a data reference
    /// reference
    /// Get数据reference
    /// Getdatareference
    pub fn data(&self) -> &T {
        &self.data
    }
}

/// 内存管理策略枚举
/// memory strategy enum
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
/// Gets内存管理策略说明
/// memory strategy explain
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
        // compare_exchange_weak 可能有 spurious failure，循环重试
        let mut advanced = false;
        for _ in 0..10 {
            if manager.try_advance_epoch() {
                advanced = true;
                break;
            }
        }
        assert!(advanced);
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
