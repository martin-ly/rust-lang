//! Rust 1.97 特性跟踪模块 —— 线程与并发
#![allow(clippy::incompatible_msrv)]

use std::collections::VecDeque;
use std::io::{self, BufRead};
use std::sync::atomic::AtomicU32;

/// # Rust 1.97 线程/并发特性演示
///
/// Rust 1.97 稳定化的核心并发 API：
/// - `Atomic*::from_ptr` — 从裸指针创建原子引用（const stable）
/// - `BufRead` for `VecDeque<u8>` — 无锁缓冲区读取
/// - `std::ptr::swap` / `std::mem::swap` const stable
/// - `NonNull::new` const stable
pub struct Rust197ThreadFeatures;

impl Rust197ThreadFeatures {
    /// 使用 `AtomicU32::from_ptr` 从共享内存指针创建原子引用
    ///
    /// # Safety
    /// 指针必须对齐且指向有效的 `AtomicU32` 兼容内存。
    pub unsafe fn atomic_from_ptr(ptr: *mut u32) -> &'static AtomicU32 {
        // SAFETY: caller ensures pointer is valid and aligned
        unsafe { AtomicU32::from_ptr(ptr) }
    }

    /// 使用 `VecDeque<u8>` 的 `BufRead` 实现进行线程间缓冲区读取
    ///
    /// Rust 1.97 为 `VecDeque<u8>` 实现了 `BufRead`，使其可以直接作为缓冲读取器使用。
    pub fn read_from_vecdeque_buffer(data: &mut VecDeque<u8>) -> io::Result<Vec<u8>> {
        let buf = data.fill_buf()?;
        let result = buf.to_vec();
        let len = buf.len();
        data.consume(len);
        Ok(result)
    }

    /// 演示 `std::mem::swap` 在 const 上下文中的使用
    ///
    /// Rust 1.97 使 `std::mem::swap` 在 const 上下文中稳定可用。
    pub const fn const_swap_example() -> (i32, i32) {
        let mut a = 1;
        let mut b = 2;
        std::mem::swap(&mut a, &mut b);
        (a, b)
    }

    /// 演示 `NonNull::new` 在 const 上下文中的使用
    pub const fn const_nonnull_example() -> Option<std::ptr::NonNull<i32>> {
        let mut value = 42;
        std::ptr::NonNull::new(&mut value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::Ordering;

    #[test]
    fn test_atomic_from_ptr() {
        let mut value = 0u32;
        let atomic = unsafe { Rust197ThreadFeatures::atomic_from_ptr(&mut value) };
        atomic.store(42, Ordering::Relaxed);
        assert_eq!(value, 42);
    }

    #[test]
    fn test_read_from_vecdeque_buffer() {
        let mut deque = VecDeque::from(vec![1u8, 2, 3, 4, 5]);
        let result = Rust197ThreadFeatures::read_from_vecdeque_buffer(&mut deque).unwrap();
        assert_eq!(result, vec![1, 2, 3, 4, 5]);
        assert!(deque.is_empty());
    }

    #[test]
    fn test_const_swap() {
        assert_eq!(Rust197ThreadFeatures::const_swap_example(), (2, 1));
    }
}
