//! Unsafe Rust模式
//!
//! 安全地unsafe代码编写指南

use std::ptr::NonNull;

// ============================================
// 原始指针
// ============================================

/// 安全地解引用原始指针
/// 
/// # Safety
/// - ptr必须有效
/// - ptr必须正确对齐
/// - ptr必须指向已初始化的T
pub unsafe fn safe_deref<'a, T>(ptr: *const T) -> &'a T {
    &*ptr
}

/// 原始指针算术
pub unsafe fn pointer_arithmetic() {
    let arr = [1, 2, 3, 4, 5];
    let ptr = arr.as_ptr();
    
    // 偏移必须在分配范围内
    let second = unsafe { ptr.add(1).read() };
    assert_eq!(second, 2);
}

// ============================================
// 自定义智能指针
// ============================================

pub struct MyBox<T> {
    ptr: NonNull<T>,
}

impl<T> MyBox<T> {
    pub fn new(value: T) -> Self {
        let ptr = Box::into_raw(Box::new(value));
        Self {
            ptr: unsafe { NonNull::new_unchecked(ptr) },
        }
    }
    
    pub fn as_ref(&self) -> &T {
        unsafe { self.ptr.as_ref() }
    }
    
    pub fn as_mut(&mut self) -> &mut T {
        unsafe { self.ptr.as_mut() }
    }
}

impl<T> Drop for MyBox<T> {
    fn drop(&mut self) {
        unsafe {
            drop(Box::from_raw(self.ptr.as_ptr()));
        }
    }
}

impl<T> std::ops::Deref for MyBox<T> {
    type Target = T;
    
    fn deref(&self) -> &T {
        self.as_ref()
    }
}

impl<T> std::ops::DerefMut for MyBox<T> {
    fn deref_mut(&mut self) -> &mut T {
        self.as_mut()
    }
}

// ============================================
// 内部可变性
// ============================================

use std::cell::UnsafeCell;

pub struct MyCell<T> {
    value: UnsafeCell<T>,
}

impl<T: Copy> MyCell<T> {
    pub fn new(value: T) -> Self {
        Self { value: UnsafeCell::new(value) }
    }
    
    pub fn get(&self) -> T {
        unsafe { *self.value.get() }
    }
    
    pub fn set(&self, value: T) {
        unsafe { *self.value.get() = value }
    }
}

// ============================================
// 联合体
// ============================================

pub union MyUnion {
    pub i: i32,
    pub f: f32,
}

impl MyUnion {
    pub fn as_int(&self) -> i32 {
        unsafe { self.i }
    }
    
    pub fn as_float(&self) -> f32 {
        unsafe { self.f }
    }
}

// ============================================
// FFI边界
// ============================================

/// C字符串转换
pub fn c_str_to_str(c_str: *const std::ffi::c_char) -> Option<&'static str> {
    if c_str.is_null() {
        return None;
    }
    
    let c_str = unsafe { std::ffi::CStr::from_ptr(c_str) };
    c_str.to_str().ok()
}

// ============================================
// 零成本类型转换
// ============================================

/// transmute的安全封装
/// 
/// # Safety
/// S和T必须具有相同的大小和对齐
pub unsafe fn safe_transmute<S, T>(src: S) -> T {
    assert_eq!(std::mem::size_of::<S>(), std::mem::size_of::<T>());
    assert_eq!(std::mem::align_of::<S>(), std::mem::align_of::<T>());
    std::mem::transmute_copy(&src)
}

// ============================================
// Miri测试
// ============================================

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_my_box() {
        let mut b = MyBox::new(42);
        assert_eq!(*b, 42);
        *b = 100;
        assert_eq!(*b, 100);
    }
    
    #[test]
    fn test_my_cell() {
        let cell = MyCell::new(42);
        assert_eq!(cell.get(), 42);
        cell.set(100);
        assert_eq!(cell.get(), 100);
    }
    
    #[test]
    fn test_union() {
        let u = MyUnion { i: 1 };
        assert_eq!(u.as_int(), 1);
    }
}
