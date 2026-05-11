//! # 练习 9: `unsafe_op_in_unsafe_fn` — Rust 2024 的 unsafe 函数体规范 (Rust 1.95)
//!
//! **难度**: Medium  
//! **考点**: `unsafe_op_in_unsafe_fn` lint、Rust 2024 行为变更、unsafe 块粒度控制
//!
//! ## 背景
//!
//! 在 Rust 2021 及之前，`unsafe fn` 的函数体被视为一个隐式的 `unsafe` 块：
//! 函数体内的所有 unsafe 操作都可以直接写，无需额外包裹 `unsafe {}`。
//!
//! 这种设计有一个问题：**模糊了调用者的 unsafe 和实现者的 unsafe**。  
//! `unsafe fn` 标记的是"调用此函数需要 unsafe 权限"，
//! 但并不意味着"此函数的实现中所有操作都自动获得 unsafe 权限"。
//!
//! Rust 2024（默认启用 `unsafe_op_in_unsafe_fn`）改变了这一点：  
//! `unsafe fn` 的函数体**默认是 safe 的**，内部的 unsafe 操作仍然需要显式包裹在 `unsafe {}` 块中。
//! 这让 unsafe 的边界更加清晰，每一行 unsafe 代码都明确可见。
//!
//! ## 要求
//!
//! - 理解 `unsafe fn`（调用约束）与 `unsafe {}`（权限授予）的区别
//! - 将 Rust 2021 风格的 `unsafe fn` 改写为 Rust 2024 风格
//! - 在 unsafe fn 体内合理使用最小粒度的 `unsafe {}` 块

/// 一个模拟的原始内存缓冲区
pub struct RawBuffer {
    ptr: *mut u8,
    len: usize,
}

impl RawBuffer {
    /// 创建指定大小的未初始化原始缓冲区
    ///
    /// # Safety
    ///
    /// 调用者必须确保后续对缓冲区的读写操作在有效范围内。
    pub unsafe fn new_uninitialized(size: usize) -> Self {
        // Rust 2024: unsafe fn 体内仍然需要显式 unsafe 块才能调用 unsafe 函数
        let layout = std::alloc::Layout::from_size_align(size, 1).expect("invalid layout");
        // TODO: 在 unsafe 块中调用 std::alloc::alloc
        let ptr = unsafe { std::alloc::alloc(layout) };
        if ptr.is_null() {
            std::alloc::handle_alloc_error(layout);
        }
        Self { ptr, len: size }
    }

    /// 将数据写入缓冲区的指定偏移位置
    ///
    /// # Safety
    ///
    /// - `offset + data.len()` 必须不超过缓冲区大小
    /// - 如果存在其他活跃的引用，必须遵守别名规则
    pub unsafe fn write_at(&mut self, offset: usize, data: &[u8]) {
        assert!(offset + data.len() <= self.len, "write out of bounds");
        // TODO: 在 unsafe 块中使用 ptr::copy_nonoverlapping
        unsafe {
            std::ptr::copy_nonoverlapping(data.as_ptr(), self.ptr.add(offset), data.len());
        }
    }

    /// 从缓冲区读取指定范围的数据
    ///
    /// # Safety
    ///
    /// - `offset + len` 必须不超过缓冲区大小
    pub unsafe fn read_at(&self, offset: usize, len: usize) -> Vec<u8> {
        assert!(offset + len <= self.len, "read out of bounds");
        let mut result = vec![0u8; len];
        // TODO: 在 unsafe 块中使用 ptr::copy_nonoverlapping
        unsafe {
            std::ptr::copy_nonoverlapping(self.ptr.add(offset), result.as_mut_ptr(), len);
        }
        result
    }

    /// 释放缓冲区
    ///
    /// # Safety
    ///
    /// 调用者必须确保此缓冲区不再被使用。
    pub unsafe fn dealloc(self) {
        let layout = std::alloc::Layout::from_size_align(self.len, 1).expect("invalid layout");
        // TODO: 在 unsafe 块中调用 std::alloc::dealloc
        unsafe {
            std::alloc::dealloc(self.ptr, layout);
        }
        // 防止 Drop 后继续使用
        std::mem::forget(self);
    }
}

/// 解释为什么 `unsafe fn` 体内需要 `unsafe {}` 块
///
/// 回答以下判断题：
///
/// 1. "`unsafe fn` 标记意味着函数体内的所有操作都自动获得 unsafe 权限。" →  false
/// 2. "在 Rust 2024 中，`unsafe fn` 体内的 `unsafe { }` 块可以省略。" → false
/// 3. "`unsafe fn` 约束的是**调用者**，`unsafe {}` 约束的是**实现者**。" → true
/// 4. "最小粒度的 `unsafe {}` 块有助于代码审查时定位潜在 UB。" → true
pub fn unsafe_fn_quiz_answers() -> [bool; 4] {
    [false, false, true, true]
}

/// 将 Rust 2021 风格的代码改写为 Rust 2024 风格
///
/// 原 Rust 2021 代码：
/// ```ignore
/// unsafe fn old_style(ptr: *mut u32) -> u32 {
///     *ptr // 直接解引用，在 Rust 2021 中合法
/// }
/// ```
///
/// Rust 2024 风格：
/// ```ignore
/// unsafe fn new_style(ptr: *mut u32) -> u32 {
///     unsafe { *ptr } // 显式 unsafe 块
/// }
/// ```
pub unsafe fn rust_2024_style_deref(ptr: *const u32) -> u32 {
    // TODO: 将解引用操作包裹在 unsafe 块中
    unsafe { *ptr }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_buffer_write_read() {
        unsafe {
            let mut buf = RawBuffer::new_uninitialized(16);
            let data = b"hello, unsafe!";
            buf.write_at(0, data);
            let read_back = buf.read_at(0, data.len());
            assert_eq!(&read_back[..], data);
            buf.dealloc();
        }
    }

    #[test]
    fn test_buffer_write_at_offset() {
        unsafe {
            let mut buf = RawBuffer::new_uninitialized(8);
            buf.write_at(2, &[0xAB, 0xCD]);
            let read_back = buf.read_at(2, 2);
            assert_eq!(read_back, vec![0xAB, 0xCD]);
            buf.dealloc();
        }
    }

    #[test]
    fn test_quiz_answers() {
        let answers = unsafe_fn_quiz_answers();
        assert_eq!(answers, [false, false, true, true]);
    }

    #[test]
    fn test_rust_2024_style_deref() {
        let x = 42u32;
        unsafe {
            let result = rust_2024_style_deref(&raw const x);
            assert_eq!(result, 42);
        }
    }

    #[test]
    #[should_panic(expected = "write out of bounds")]
    #[cfg_attr(miri, ignore)] // Miri 检测到此 panic 路径的内存泄漏，这是教学代码的已知限制
    fn test_buffer_write_out_of_bounds() {
        unsafe {
            let mut buf = RawBuffer::new_uninitialized(4);
            buf.write_at(0, &[1, 2, 3, 4, 5]); // 5 bytes > 4 bytes
            buf.dealloc();
        }
    }
}
