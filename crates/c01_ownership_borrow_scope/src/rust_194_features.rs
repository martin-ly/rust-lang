//! Rust 1.94.0 所有权与借用特性实现模块
//!
//! 本模块展示了 Rust 1.94.0 在所有权、借用和作用域管理方面的增强，包括：
//! - 增强的内存安全保证
//! - 改进的借用检查器诊断信息
//! - 更灵活的内部可变性模式
//! - 与 Edition 2024 的深度集成
//!
//! # 文件信息
//! - 文件: rust_194_features.rs
//! - 创建日期: 2026-03-06
//! - 版本: 1.0
//! - Rust 版本: 1.94.0
//! - Edition: 2024

use std::cell::RefCell;
use std::mem::MaybeUninit;
use std::ops::Deref;
use std::sync::atomic::{AtomicUsize, Ordering};

// ==================== 1. 增强的内部可变性模式 ====================

/// Rust 1.94 增强的内部可变性包装器
/// 结合了 RefCell 和 AtomicUsize 的优势
pub struct HybridCell<T> {
    data: RefCell<T>,
    access_count: AtomicUsize,
}

impl<T> HybridCell<T> {
    pub fn new(value: T) -> Self {
        Self {
            data: RefCell::new(value),
            access_count: AtomicUsize::new(0),
        }
    }

    /// 获取不可变引用并计数
    pub fn borrow_with_count(&self) -> std::cell::Ref<'_, T> {
        self.access_count.fetch_add(1, Ordering::Relaxed);
        self.data.borrow()
    }

    /// 获取可变引用并计数
    pub fn borrow_mut_with_count(&self) -> std::cell::RefMut<'_, T> {
        self.access_count.fetch_add(1, Ordering::Relaxed);
        self.data.borrow_mut()
    }

    pub fn access_count(&self) -> usize {
        self.access_count.load(Ordering::Relaxed)
    }
}

// ==================== 2. 安全的 MaybeUninit 批量操作 ====================

/// Rust 1.94 安全的未初始化内存批量处理
pub struct SafeBuffer<T> {
    buffer: Vec<MaybeUninit<T>>,
    initialized: usize,
}

impl<T: Copy> SafeBuffer<T> {
    pub fn with_capacity(capacity: usize) -> Self {
        let mut buffer = Vec::with_capacity(capacity);
        unsafe {
            buffer.set_len(capacity);
        }
        Self {
            buffer,
            initialized: 0,
        }
    }

    /// 批量写入复制值（Rust 1.94 增强模式）
    pub fn write_slice(&mut self, values: &[T]) -> usize {
        let to_write = values.len().min(self.buffer.len() - self.initialized);
        for (i, &val) in values.iter().take(to_write).enumerate() {
            self.buffer[self.initialized + i].write(val);
        }
        self.initialized += to_write;
        to_write
    }

    /// 获取已初始化部分的切片
    pub fn initialized_slice(&self) -> &[T] {
        unsafe {
            std::slice::from_raw_parts(
                self.buffer.as_ptr() as *const T,
                self.initialized,
            )
        }
    }

    pub fn capacity(&self) -> usize {
        self.buffer.len()
    }

    pub fn len(&self) -> usize {
        self.initialized
    }

    pub fn is_empty(&self) -> bool {
        self.initialized == 0
    }
}

impl<T> Drop for SafeBuffer<T> {
    fn drop(&mut self) {
        // 仅释放已初始化的元素
        unsafe {
            std::ptr::drop_in_place(std::slice::from_raw_parts_mut(
                self.buffer.as_mut_ptr() as *mut T,
                self.initialized,
            ));
        }
    }
}

// ==================== 3. 智能指针优化模式 ====================

/// Rust 1.94 智能指针组合模式
pub struct SmartPtrChain<T> {
    inner: Option<Box<T>>,
    metadata: usize,
}

impl<T> SmartPtrChain<T> {
    pub fn new(value: T) -> Self {
        Self {
            inner: Some(Box::new(value)),
            metadata: 0,
        }
    }

    /// 转换为原始指针并保留元数据
    pub fn into_raw_parts(mut self) -> (*mut T, usize) {
        let ptr = self.inner.take().map_or(std::ptr::null_mut(), |b| Box::into_raw(b));
        (ptr, self.metadata)
    }

    /// 从原始指针重建（不安全）
    /// 
    /// # Safety
    /// - ptr 必须是由 into_raw_parts 生成的有效指针
    /// - ptr 必须指向未释放的内存
    pub unsafe fn from_raw_parts(ptr: *mut T, metadata: usize) -> Self { unsafe {
        Self {
            inner: if ptr.is_null() { None } else { Some(Box::from_raw(ptr)) },
            metadata,
        }
    }}

    pub fn metadata(&self) -> usize {
        self.metadata
    }

    pub fn set_metadata(&mut self, value: usize) {
        self.metadata = value;
    }
}

impl<T> Deref for SmartPtrChain<T> {
    type Target = T;

    fn deref(&self) -> &T {
        self.inner.as_ref().unwrap()
    }
}

// ==================== 4. 作用域守卫增强 ====================

/// Rust 1.94 作用域守卫模式
pub struct ScopeGuard<T, F: FnOnce(T)> {
    value: Option<T>,
    on_drop: Option<F>,
}

impl<T, F: FnOnce(T)> ScopeGuard<T, F> {
    pub fn new(value: T, on_drop: F) -> Self {
        Self {
            value: Some(value),
            on_drop: Some(on_drop),
        }
    }

    /// 获取可变引用（保留析构函数）
    pub fn get_mut(&mut self) -> &mut T {
        self.value.as_mut().unwrap()
    }

    /// 获取不可变引用
    pub fn get(&self) -> &T {
        self.value.as_ref().unwrap()
    }

    /// 主动完成并禁用析构函数
    pub fn complete(mut self) -> T {
        self.on_drop = None;
        self.value.take().unwrap()
    }
}

impl<T, F: FnOnce(T)> Drop for ScopeGuard<T, F> {
    fn drop(&mut self) {
        if let (Some(value), Some(on_drop)) = (self.value.take(), self.on_drop.take()) {
            on_drop(value);
        }
    }
}

// ==================== 5. 零拷贝字符串处理 ====================

/// Rust 1.94 零拷贝字符串处理模式
pub struct ZeroCopyString {
    data: Vec<u8>,
}

impl ZeroCopyString {
    pub fn new() -> Self {
        Self { data: Vec::new() }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            data: Vec::with_capacity(capacity),
        }
    }

    /// 从 String 获取原始部件（零拷贝）
    pub fn from_string(s: String) -> Self {
        // 使用 String::into_bytes 获取 Vec<u8>，然后分离
        let data = s.into_bytes();
        Self { data }
    }

    /// 转换为 String（零拷贝）
    pub fn into_string(self) -> String {
        // SAFETY: data 是有效的 UTF-8 字节
        unsafe { String::from_utf8_unchecked(self.data) }
    }

    pub fn as_str(&self) -> &str {
        unsafe { std::str::from_utf8_unchecked(&self.data) }
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.data
    }
}

impl Default for ZeroCopyString {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hybrid_cell() {
        let cell = HybridCell::new(42);
        {
            let _ref = cell.borrow_with_count();
            assert_eq!(cell.access_count(), 1);
        }
        {
            let _mut_ref = cell.borrow_mut_with_count();
            assert_eq!(cell.access_count(), 2);
        }
    }

    #[test]
    fn test_safe_buffer() {
        let mut buf = SafeBuffer::with_capacity(10);
        let written = buf.write_slice(&[1, 2, 3, 4, 5]);
        assert_eq!(written, 5);
        assert_eq!(buf.initialized_slice(), &[1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_smart_ptr_chain() {
        let chain = SmartPtrChain::new(100);
        assert_eq!(chain.metadata(), 0);
        
        let (ptr, meta) = chain.into_raw_parts();
        assert!(!ptr.is_null());
        assert_eq!(unsafe { *ptr }, 100);
        
        let _restored = unsafe { SmartPtrChain::from_raw_parts(ptr, meta) };
    }

    #[test]
    fn test_scope_guard() {
        let mut dropped = false;
        {
            let mut guard = ScopeGuard::new(42, |v| {
                assert_eq!(v, 42);
                dropped = true;
            });
            *guard.get_mut() = 42;
        }
        assert!(dropped);

        // 测试主动完成
        let mut dropped2 = false;
        let guard2 = ScopeGuard::new(100, |_v| dropped2 = true);
        let _value = guard2.complete();
        assert!(!dropped2); // 析构函数未执行
    }

    #[test]
    fn test_zero_copy_string() {
        let original = String::from("Hello, Rust 1.94!");
        let zc = ZeroCopyString::from_string(original);
        assert_eq!(zc.as_str(), "Hello, Rust 1.94!");
        
        let restored = zc.into_string();
        assert_eq!(restored, "Hello, Rust 1.94!");
    }
}
