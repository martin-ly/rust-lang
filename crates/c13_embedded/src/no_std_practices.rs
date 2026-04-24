//! no_std 编程实践
//!
//! 演示如何在无标准库环境下使用 Rust 的核心功能。
//!
//! `core` crate 包含以下核心类型和 trait，在所有目标上都可用：
//! - 基本类型：`i32`, `u8`, `bool`, `str` 等
//! - 切片和数组：`[T]`, `[T; N]`
//! - 迭代器：`Iterator`, `IntoIterator`
//! - `Option`, `Result`
//! - `Drop`, `Clone`, `Copy`, `Send`, `Sync`

use core::fmt;

/// 演示使用 `core` 替代 `std`
///
/// 在 `no_std` 中，大部分类型需要从 `core` 引入：
/// - `core::slice` 替代 `std::slice`
/// - `core::fmt` 替代 `std::fmt`
/// - `core::ptr` 替代 `std::ptr`
///
/// 技巧：使用 `use core::...` 而不是 `use std::...`。
pub struct CoreUsageDemo;

impl CoreUsageDemo {
    /// 使用 core::fmt 格式化数字
    ///
    /// 在 no_std 中，`format!` 宏不可用（因为它需要分配器），
    /// 但可以使用 `write!` 到固定大小的缓冲区。
    pub fn format_number(value: u32, buf: &mut [u8]) -> Result<usize, fmt::Error> {
        struct Writer<'a> {
            buf: &'a mut [u8],
            pos: usize,
        }

        impl<'a> fmt::Write for Writer<'a> {
            fn write_str(&mut self, s: &str) -> fmt::Result {
                let bytes = s.as_bytes();
                let remaining = self.buf.len().saturating_sub(self.pos);
                let to_write = bytes.len().min(remaining);
                self.buf[self.pos..self.pos + to_write].copy_from_slice(&bytes[..to_write]);
                self.pos += to_write;
                if to_write < bytes.len() {
                    return Err(fmt::Error);
                }
                Ok(())
            }
        }

        let mut writer = Writer { buf, pos: 0 };
        fmt::write(&mut writer, format_args!("{value}"))?;
        Ok(writer.pos)
    }

    /// 使用 core 迭代器处理数据
    pub fn sum_slice(data: &[u32]) -> u32 {
        // 与 std 中完全相同，因为 Iterator 定义在 core 中
        data.iter().sum()
    }
}

/// 固定容量环形缓冲区（no_std 友好集合示例）
///
/// 在真实项目中，可使用 `heapless::Vec` 或 `heapless::Deque`。
/// 这里展示一个纯 core 实现的固定容量队列，无需 `alloc`。
pub struct FixedRingBuffer<T, const N: usize> {
    buffer: [Option<T>; N],
    head: usize,
    tail: usize,
    count: usize,
}

impl<T: Copy + Default, const N: usize> Default for FixedRingBuffer<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Copy + Default, const N: usize> FixedRingBuffer<T, N> {
    /// 创建新的空环形缓冲区
    pub const fn new() -> Self {
        // 使用 Option<T> 简化实现；生产环境可用 MaybeUninit 优化
        Self {
            buffer: [None; N],
            head: 0,
            tail: 0,
            count: 0,
        }
    }

    /// 向缓冲区添加元素
    pub fn push(&mut self, value: T) -> Result<(), &'static str> {
        if self.count >= N {
            return Err("缓冲区已满");
        }
        self.buffer[self.tail] = Some(value);
        self.tail = (self.tail + 1) % N;
        self.count += 1;
        Ok(())
    }

    /// 从缓冲区取出元素
    pub fn pop(&mut self) -> Option<T> {
        if self.count == 0 {
            return None;
        }
        let value = self.buffer[self.head].take();
        self.head = (self.head + 1) % N;
        self.count -= 1;
        value
    }

    /// 当前元素数量
    pub const fn len(&self) -> usize {
        self.count
    }

    /// 是否为空
    pub const fn is_empty(&self) -> bool {
        self.count == 0
    }
}

/// 自旋锁概念演示（替代 std::sync::Mutex）
///
/// 在单核 bare-metal 中，关闭中断即可实现互斥。
/// 多核环境下需要使用原子操作。
///
/// 真实项目可使用 `spin::Mutex` 或 `critical-section` crate。
pub struct SpinLockConcept;

impl SpinLockConcept {
    /// 描述自旋锁的使用场景
    pub fn description() -> &'static str {
        "在 bare-metal 中，自旋锁通过关闭中断或原子操作实现互斥，替代 std::sync::Mutex"
    }
}

/// 演示 alloc 的条件使用
///
/// 如果启用了全局分配器，可以通过 `extern crate alloc;` 使用：
/// - `alloc::vec::Vec`
/// - `alloc::boxed::Box`
/// - `alloc::string::String`
/// - `alloc::collections::VecDeque`
///
/// ```rust,ignore
/// extern crate alloc;
///
/// use alloc::vec::Vec;
///
/// let mut v = Vec::new();
/// v.push(1);
/// ```
pub struct AllocUsage;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_format_number() {
        let mut buf = [0u8; 32];
        let len = CoreUsageDemo::format_number(12345, &mut buf).unwrap();
        assert_eq!(&buf[..len], b"12345");
    }

    #[test]
    fn test_sum_slice() {
        assert_eq!(CoreUsageDemo::sum_slice(&[1, 2, 3, 4]), 10);
    }

    #[test]
    fn test_ring_buffer() {
        let mut buf = FixedRingBuffer::<u32, 4>::new();
        assert!(buf.is_empty());
        buf.push(1).unwrap();
        buf.push(2).unwrap();
        assert_eq!(buf.len(), 2);
        assert_eq!(buf.pop(), Some(1));
        assert_eq!(buf.pop(), Some(2));
        assert_eq!(buf.pop(), None);
    }

    #[test]
    fn test_ring_buffer_full() {
        let mut buf = FixedRingBuffer::<u32, 2>::new();
        buf.push(1).unwrap();
        buf.push(2).unwrap();
        assert!(buf.push(3).is_err());
    }
}
