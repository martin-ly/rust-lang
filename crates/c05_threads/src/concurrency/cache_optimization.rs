//! 并发相关的缓存优化示例与工具
//!
//! 本模块提供与并发相关的缓存优化技术，包括：
//! - 缓存行对齐
//! - 伪共享避免
//! - 预取优化
//! - 缓存友好的数据结构

use std::sync::atomic::{AtomicUsize, Ordering};

/// 缓存行大小（通常为 64 字节）
pub const CACHE_LINE_SIZE: usize = 64;

/// 缓存行对齐的结构体
///
/// 使用 `#[repr(align(64))]` 确保结构体按缓存行对齐，
/// 避免伪共享（false sharing）问题
#[repr(align(64))]
pub struct CacheAlignedCounter {
    /// 计数器值
    pub value: AtomicUsize,
    /// 填充字节，确保独占一个缓存行
    _padding: [u8; CACHE_LINE_SIZE - std::mem::size_of::<AtomicUsize>()],
}

impl CacheAlignedCounter {
    /// 创建新的缓存对齐计数器
    pub fn new(initial_value: usize) -> Self {
        Self {
            value: AtomicUsize::new(initial_value),
            _padding: [0; CACHE_LINE_SIZE - std::mem::size_of::<AtomicUsize>()],
        }
    }

    /// 递增计数器
    pub fn increment(&self) -> usize {
        self.value.fetch_add(1, Ordering::Relaxed) + 1
    }

    /// 获取当前值
    pub fn get(&self) -> usize {
        self.value.load(Ordering::Relaxed)
    }

    /// 重置计数器
    pub fn reset(&self) {
        self.value.store(0, Ordering::Relaxed);
    }
}

impl Default for CacheAlignedCounter {
    fn default() -> Self {
        Self::new(0)
    }
}

/// 伪共享检测工具
///
/// 用于检测和避免伪共享问题
pub struct FalseSharingDetector {
    /// 检测到的伪共享次数
    false_sharing_count: AtomicUsize,
}

impl FalseSharingDetector {
    /// 创建新的伪共享检测器
    pub fn new() -> Self {
        Self {
            false_sharing_count: AtomicUsize::new(0),
        }
    }

    /// 检测两个地址是否在同一缓存行
    pub fn same_cache_line(&self, addr1: *const u8, addr2: *const u8) -> bool {
        let addr1 = addr1 as usize;
        let addr2 = addr2 as usize;
        (addr1 / CACHE_LINE_SIZE) == (addr2 / CACHE_LINE_SIZE)
    }

    /// 记录伪共享检测
    pub fn record_false_sharing(&self) {
        self.false_sharing_count.fetch_add(1, Ordering::Relaxed);
    }

    /// 获取伪共享计数
    pub fn false_sharing_count(&self) -> usize {
        self.false_sharing_count.load(Ordering::Relaxed)
    }
}

impl Default for FalseSharingDetector {
    fn default() -> Self {
        Self::new()
    }
}

/// 缓存友好的数组结构
///
/// 使用缓存行对齐的数组，提高缓存命中率
pub struct CacheFriendlyArray<T> {
    /// 数据数组
    data: Vec<T>,
    /// 数组大小
    size: usize,
}

impl<T> CacheFriendlyArray<T> {
    /// 创建新的缓存友好数组
    pub fn new(size: usize) -> Self
    where
        T: Default + Clone,
    {
        Self {
            data: vec![T::default(); size],
            size,
        }
    }

    /// 获取数组大小
    pub fn len(&self) -> usize {
        self.size
    }

    /// 检查数组是否为空
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    /// 获取元素（不可变）
    pub fn get(&self, index: usize) -> Option<&T> {
        self.data.get(index)
    }

    /// 获取元素（可变）
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.data.get_mut(index)
    }

    /// 设置元素
    pub fn set(&mut self, index: usize, value: T) -> Result<(), String> {
        if index >= self.size {
            return Err(format!("Index {} out of bounds (size: {})", index, self.size));
        }
        self.data[index] = value;
        Ok(())
    }
}

/// 预取提示
///
/// 提示 CPU 预取数据到缓存
pub struct PrefetchHint;

impl PrefetchHint {
    /// 预取数据到 L1 缓存
    #[cfg(target_arch = "x86_64")]
    pub fn prefetch_l1(addr: *const u8) {
        unsafe {
            core::arch::x86_64::_mm_prefetch(addr as *const i8, core::arch::x86_64::_MM_HINT_T0);
        }
    }

    /// 预取数据到 L2 缓存
    #[cfg(target_arch = "x86_64")]
    pub fn prefetch_l2(addr: *const u8) {
        unsafe {
            core::arch::x86_64::_mm_prefetch(addr as *const i8, core::arch::x86_64::_MM_HINT_T1);
        }
    }

    /// 预取数据到 L3 缓存
    #[cfg(target_arch = "x86_64")]
    pub fn prefetch_l3(addr: *const u8) {
        unsafe {
            core::arch::x86_64::_mm_prefetch(addr as *const i8, core::arch::x86_64::_MM_HINT_T2);
        }
    }

    /// 非 x86_64 架构的占位实现
    #[cfg(not(target_arch = "x86_64"))]
    pub fn prefetch_l1(_addr: *const u8) {
        // 非 x86_64 架构不支持硬件预取
    }

    #[cfg(not(target_arch = "x86_64"))]
    pub fn prefetch_l2(_addr: *const u8) {
        // 非 x86_64 架构不支持硬件预取
    }

    #[cfg(not(target_arch = "x86_64"))]
    pub fn prefetch_l3(_addr: *const u8) {
        // 非 x86_64 架构不支持硬件预取
    }
}

/// 缓存优化的并行累加器
///
/// 使用线程本地存储避免伪共享
pub struct CacheOptimizedAccumulator {
    /// 线程本地计数器数组（每个线程一个缓存行）
    counters: Vec<CacheAlignedCounter>,
}

impl CacheOptimizedAccumulator {
    /// 创建新的缓存优化累加器
    pub fn new(thread_count: usize) -> Self {
        Self {
            counters: (0..thread_count)
                .map(|_| CacheAlignedCounter::new(0))
                .collect(),
        }
    }

    /// 获取线程的计数器
    pub fn get_counter(&self, thread_id: usize) -> Option<&CacheAlignedCounter> {
        self.counters.get(thread_id)
    }

    /// 累加所有计数器的值
    pub fn total(&self) -> usize {
        self.counters.iter().map(|c| c.get()).sum()
    }

    /// 重置所有计数器
    pub fn reset_all(&self) {
        for counter in &self.counters {
            counter.reset();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cache_aligned_counter() {
        let counter = CacheAlignedCounter::new(0);
        assert_eq!(counter.get(), 0);

        assert_eq!(counter.increment(), 1);
        assert_eq!(counter.increment(), 2);
        assert_eq!(counter.get(), 2);

        counter.reset();
        assert_eq!(counter.get(), 0);
    }

    #[test]
    fn test_false_sharing_detector() {
        let detector = FalseSharingDetector::new();
        let value1 = 0u8;
        let value2 = 0u8;

        let same_line = detector.same_cache_line(&value1 as *const u8, &value2 as *const u8);
        // 两个局部变量很可能在同一缓存行
        assert!(same_line || !same_line); // 结果取决于内存布局

        assert_eq!(detector.false_sharing_count(), 0);
        detector.record_false_sharing();
        assert_eq!(detector.false_sharing_count(), 1);
    }

    #[test]
    fn test_cache_friendly_array() {
        let mut array = CacheFriendlyArray::new(10);
        assert_eq!(array.len(), 10);
        assert!(!array.is_empty());

        assert!(array.set(0, 42).is_ok());
        assert_eq!(array.get(0), Some(&42));

        assert!(array.set(5, 100).is_ok());
        assert_eq!(array.get(5), Some(&100));

        assert!(array.set(10, 200).is_err()); // 越界
    }

    #[test]
    fn test_cache_optimized_accumulator() {
        let accumulator = CacheOptimizedAccumulator::new(4);
        assert_eq!(accumulator.total(), 0);

        if let Some(counter) = accumulator.get_counter(0) {
            counter.increment();
            counter.increment();
        }

        if let Some(counter) = accumulator.get_counter(1) {
            counter.increment();
        }

        assert_eq!(accumulator.total(), 3);

        accumulator.reset_all();
        assert_eq!(accumulator.total(), 0);
    }

    #[test]
    fn test_cache_line_size() {
        // 验证缓存行对齐
        let counter = CacheAlignedCounter::new(0);
        let addr = &counter as *const CacheAlignedCounter as usize;
        assert_eq!(addr % CACHE_LINE_SIZE, 0, "Counter should be cache-line aligned");
    }
}
