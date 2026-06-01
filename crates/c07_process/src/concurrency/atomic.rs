// 原子操作模块
// 这个模块提供了进程安全的原子操作实现

use std::sync::atomic::{AtomicBool, AtomicIsize, AtomicUsize, Ordering};

/// 进程安全的原子布尔值
/// Process-safe atomic boolean
pub struct ProcessAtomicBool {
    inner: AtomicBool,
}

impl ProcessAtomicBool {
    /// 创建新的原子布尔值
    /// Create new atomic boolean
    pub fn new(value: bool) -> Self {
        Self {
            inner: AtomicBool::new(value),
        }
    }

    /// 获取当前值
    /// Get current value
    pub fn load(&self, ordering: Ordering) -> bool {
        self.inner.load(ordering)
    }

    /// 设置值
    /// Set value
    pub fn store(&self, value: bool, ordering: Ordering) {
        self.inner.store(value, ordering);
    }

    /// 交换值
    /// Swap value
    pub fn swap(&self, value: bool, ordering: Ordering) -> bool {
        self.inner.swap(value, ordering)
    }

    /// 比较并交换
    /// Compare and swap
    pub fn compare_exchange(
        &self,
        current: bool,
        new: bool,
        success: Ordering,
        failure: Ordering,
    ) -> Result<bool, bool> {
        self.inner.compare_exchange(current, new, success, failure)
    }

    /// 获取并设置
    /// Fetch and set
    pub fn fetch_and(&self, value: bool, ordering: Ordering) -> bool {
        self.inner.fetch_and(value, ordering)
    }

    /// 获取或设置
    /// Fetch or set
    pub fn fetch_or(&self, value: bool, ordering: Ordering) -> bool {
        self.inner.fetch_or(value, ordering)
    }

    /// 获取异或设置
    /// Fetch xor set
    pub fn fetch_xor(&self, value: bool, ordering: Ordering) -> bool {
        self.inner.fetch_xor(value, ordering)
    }
}

/// 进程安全的原子无符号整数
/// Process-safe atomic unsigned integer
pub struct ProcessAtomicUsize {
    inner: AtomicUsize,
}

impl ProcessAtomicUsize {
    /// 创建新的原子无符号整数
    /// Create new atomicwithout
    pub fn new(value: usize) -> Self {
        Self {
            inner: AtomicUsize::new(value),
        }
    }

    /// 获取当前值
    /// Get current value
    pub fn load(&self, ordering: Ordering) -> usize {
        self.inner.load(ordering)
    }

    /// 设置值
    /// Set value
    pub fn store(&self, value: usize, ordering: Ordering) {
        self.inner.store(value, ordering);
    }

    /// 交换值
    /// Swap value
    pub fn swap(&self, value: usize, ordering: Ordering) -> usize {
        self.inner.swap(value, ordering)
    }

    /// 比较并交换
    /// Compare and swap
    pub fn compare_exchange(
        &self,
        current: usize,
        new: usize,
        success: Ordering,
        failure: Ordering,
    ) -> Result<usize, usize> {
        self.inner.compare_exchange(current, new, success, failure)
    }

    /// 获取并添加
    /// Fetch and add
    pub fn fetch_add(&self, value: usize, ordering: Ordering) -> usize {
        self.inner.fetch_add(value, ordering)
    }

    /// 获取并减去
    /// Fetch and subtract
    pub fn fetch_sub(&self, value: usize, ordering: Ordering) -> usize {
        self.inner.fetch_sub(value, ordering)
    }

    /// 获取并位与
    /// Fetch and bitand
    pub fn fetch_and(&self, value: usize, ordering: Ordering) -> usize {
        self.inner.fetch_and(value, ordering)
    }

    /// 获取并位或
    /// Fetch and bitor
    pub fn fetch_or(&self, value: usize, ordering: Ordering) -> usize {
        self.inner.fetch_or(value, ordering)
    }

    /// 获取并位异或
    /// Fetch and bitxor
    pub fn fetch_xor(&self, value: usize, ordering: Ordering) -> usize {
        self.inner.fetch_xor(value, ordering)
    }

    /// 获取并取最大值
    /// Get maximumvalue
    pub fn fetch_max(&self, value: usize, ordering: Ordering) -> usize {
        self.inner.fetch_max(value, ordering)
    }

    /// 获取并取最小值
    /// Get minimumvalue
    pub fn fetch_min(&self, value: usize, ordering: Ordering) -> usize {
        self.inner.fetch_min(value, ordering)
    }
}

/// 进程安全的原子有符号整数
/// process symbol
pub struct ProcessAtomicIsize {
    inner: AtomicIsize,
}

impl ProcessAtomicIsize {
    /// 创建新的原子有符号整数
    /// Create new atomichas
    pub fn new(value: isize) -> Self {
        Self {
            inner: AtomicIsize::new(value),
        }
    }

    /// 获取当前值
    /// Get current value
    pub fn load(&self, ordering: Ordering) -> isize {
        self.inner.load(ordering)
    }

    /// 设置值
    /// Set value
    pub fn store(&self, value: isize, ordering: Ordering) {
        self.inner.store(value, ordering);
    }

    /// 交换值
    /// Swap value
    pub fn swap(&self, value: isize, ordering: Ordering) -> isize {
        self.inner.swap(value, ordering)
    }

    /// 比较并交换
    /// Compare and swap
    pub fn compare_exchange(
        &self,
        current: isize,
        new: isize,
        success: Ordering,
        failure: Ordering,
    ) -> Result<isize, isize> {
        self.inner.compare_exchange(current, new, success, failure)
    }

    /// 获取并添加
    /// Fetch and add
    pub fn fetch_add(&self, value: isize, ordering: Ordering) -> isize {
        self.inner.fetch_add(value, ordering)
    }

    /// 获取并减去
    /// Fetch and subtract
    pub fn fetch_sub(&self, value: isize, ordering: Ordering) -> isize {
        self.inner.fetch_sub(value, ordering)
    }

    /// 获取并位与
    /// Fetch and bitand
    pub fn fetch_and(&self, value: isize, ordering: Ordering) -> isize {
        self.inner.fetch_and(value, ordering)
    }

    /// 获取并位或
    /// Fetch and bitor
    pub fn fetch_or(&self, value: isize, ordering: Ordering) -> isize {
        self.inner.fetch_or(value, ordering)
    }

    /// 获取并位异或
    /// Fetch and bitxor
    pub fn fetch_xor(&self, value: isize, ordering: Ordering) -> isize {
        self.inner.fetch_xor(value, ordering)
    }

    /// 获取并取最大值
    /// Get maximumvalue
    pub fn fetch_max(&self, value: isize, ordering: Ordering) -> isize {
        self.inner.fetch_max(value, ordering)
    }

    /// 获取并取最小值
    /// Get minimumvalue
    pub fn fetch_min(&self, value: isize, ordering: Ordering) -> isize {
        self.inner.fetch_min(value, ordering)
    }
}
