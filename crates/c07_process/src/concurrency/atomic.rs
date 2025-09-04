// 原子操作模块
// 这个模块提供了进程安全的原子操作实现

use std::sync::atomic::{AtomicBool, AtomicUsize, AtomicIsize, Ordering};

/// 进程安全的原子布尔值
pub struct ProcessAtomicBool {
    inner: AtomicBool,
}

impl ProcessAtomicBool {
    /// 创建新的原子布尔值
    pub fn new(value: bool) -> Self {
        Self {
            inner: AtomicBool::new(value),
        }
    }
    
    /// 获取当前值
    pub fn load(&self, ordering: Ordering) -> bool {
        self.inner.load(ordering)
    }
    
    /// 设置值
    pub fn store(&self, value: bool, ordering: Ordering) {
        self.inner.store(value, ordering);
    }
    
    /// 交换值
    pub fn swap(&self, value: bool, ordering: Ordering) -> bool {
        self.inner.swap(value, ordering)
    }
    
    /// 比较并交换
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
    pub fn fetch_and(&self, value: bool, ordering: Ordering) -> bool {
        self.inner.fetch_and(value, ordering)
    }
    
    /// 获取或设置
    pub fn fetch_or(&self, value: bool, ordering: Ordering) -> bool {
        self.inner.fetch_or(value, ordering)
    }
    
    /// 获取异或设置
    pub fn fetch_xor(&self, value: bool, ordering: Ordering) -> bool {
        self.inner.fetch_xor(value, ordering)
    }
}

/// 进程安全的原子无符号整数
pub struct ProcessAtomicUsize {
    inner: AtomicUsize,
}

impl ProcessAtomicUsize {
    /// 创建新的原子无符号整数
    pub fn new(value: usize) -> Self {
        Self {
            inner: AtomicUsize::new(value),
        }
    }
    
    /// 获取当前值
    pub fn load(&self, ordering: Ordering) -> usize {
        self.inner.load(ordering)
    }
    
    /// 设置值
    pub fn store(&self, value: usize, ordering: Ordering) {
        self.inner.store(value, ordering);
    }
    
    /// 交换值
    pub fn swap(&self, value: usize, ordering: Ordering) -> usize {
        self.inner.swap(value, ordering)
    }
    
    /// 比较并交换
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
    pub fn fetch_add(&self, value: usize, ordering: Ordering) -> usize {
        self.inner.fetch_add(value, ordering)
    }
    
    /// 获取并减去
    pub fn fetch_sub(&self, value: usize, ordering: Ordering) -> usize {
        self.inner.fetch_sub(value, ordering)
    }
    
    /// 获取并位与
    pub fn fetch_and(&self, value: usize, ordering: Ordering) -> usize {
        self.inner.fetch_and(value, ordering)
    }
    
    /// 获取并位或
    pub fn fetch_or(&self, value: usize, ordering: Ordering) -> usize {
        self.inner.fetch_or(value, ordering)
    }
    
    /// 获取并位异或
    pub fn fetch_xor(&self, value: usize, ordering: Ordering) -> usize {
        self.inner.fetch_xor(value, ordering)
    }
    
    /// 获取并取最大值
    pub fn fetch_max(&self, value: usize, ordering: Ordering) -> usize {
        self.inner.fetch_max(value, ordering)
    }
    
    /// 获取并取最小值
    pub fn fetch_min(&self, value: usize, ordering: Ordering) -> usize {
        self.inner.fetch_min(value, ordering)
    }
}

/// 进程安全的原子有符号整数
pub struct ProcessAtomicIsize {
    inner: AtomicIsize,
}

impl ProcessAtomicIsize {
    /// 创建新的原子有符号整数
    pub fn new(value: isize) -> Self {
        Self {
            inner: AtomicIsize::new(value),
        }
    }
    
    /// 获取当前值
    pub fn load(&self, ordering: Ordering) -> isize {
        self.inner.load(ordering)
    }
    
    /// 设置值
    pub fn store(&self, value: isize, ordering: Ordering) {
        self.inner.store(value, ordering);
    }
    
    /// 交换值
    pub fn swap(&self, value: isize, ordering: Ordering) -> isize {
        self.inner.swap(value, ordering)
    }
    
    /// 比较并交换
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
    pub fn fetch_add(&self, value: isize, ordering: Ordering) -> isize {
        self.inner.fetch_add(value, ordering)
    }
    
    /// 获取并减去
    pub fn fetch_sub(&self, value: isize, ordering: Ordering) -> isize {
        self.inner.fetch_sub(value, ordering)
    }
    
    /// 获取并位与
    pub fn fetch_and(&self, value: isize, ordering: Ordering) -> isize {
        self.inner.fetch_and(value, ordering)
    }
    
    /// 获取并位或
    pub fn fetch_or(&self, value: isize, ordering: Ordering) -> isize {
        self.inner.fetch_or(value, ordering)
    }
    
    /// 获取并位异或
    pub fn fetch_xor(&self, value: isize, ordering: Ordering) -> isize {
        self.inner.fetch_xor(value, ordering)
    }
    
    /// 获取并取最大值
    pub fn fetch_max(&self, value: isize, ordering: Ordering) -> isize {
        self.inner.fetch_max(value, ordering)
    }
    
    /// 获取并取最小值
    pub fn fetch_min(&self, value: isize, ordering: Ordering) -> isize {
        self.inner.fetch_min(value, ordering)
    }
}
