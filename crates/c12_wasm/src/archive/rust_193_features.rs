//! Rust 1.93.0 WASM 特性实现模块
//! Rust 1.93.0 WASM feature module
//! - Duration::from_nanos_u128 in WASM 高精度计时inapplication
//! - char::MAX_LEN_UTF8/MAX_LEN_UTF16 in WASM 字符串Encodeinapplication
//! # 文件信息
//! #
//! - 文件: rust_193_features.rs
//! - 创建日期: 2026-02-12
//! - date : 2026-02-12
//! - 版本: 1.0
//! - this : 1.0
//! - 版this: 1.0
//! - Rust 版本: 1.93.0
//! - Rust this : 1.93.0
//! - Rust 版this: 1.93.0

// 允许MSRV不兼容警告，因为本模块专门展示Rust 1.93+特性
#![allow(clippy::incompatible_msrv)]

use std::collections::VecDeque;
use std::fmt;
use std::mem::MaybeUninit;
use std::time::Duration;

// ==================== 1. MaybeUninit 增强 API 在 WASM 中的应用 ====================

pub struct WasmBuffer193 {
    buffer: Vec<MaybeUninit<u8>>,
    initialized_len: usize,
}

impl WasmBuffer193 {
    pub fn new(capacity: usize) -> Self {
        let mut buffer = Vec::with_capacity(capacity);
        unsafe {
            buffer.set_len(capacity);
        }
        WasmBuffer193 {
            buffer,
            initialized_len: 0,
        }
    }

    /// 使用 Rust 1.93 write_copy_of_slice 批量写入（需 Rust 1.93+）
    /// Use Rust 1.93 write_copy_of_slice 批量Write（需 Rust 1.93+）
    pub fn write_from_slice(&mut self, data: &[u8]) -> usize {
        let write_len = data.len().min(self.buffer.len() - self.initialized_len);
        let dst = &mut self.buffer[self.initialized_len..self.initialized_len + write_len];
        // Rust 1.93: dst.write_copy_of_slice(&data[..write_len]);
        for (i, &byte) in data.iter().take(write_len).enumerate() {
            dst[i].write(byte);
        }
        self.initialized_len += write_len;
        write_len
    }

    /// Use Rust 1.93 assume_init_ref Get已Initializepartreference
    /// 调用者必须确保 len <= initialized_len
    pub unsafe fn get_initialized_ref(&self, len: usize) -> &[u8] {
        let len = len.min(self.initialized_len);
        let slice = &self.buffer[..len];
        // SAFETY: len <= initialized_len，该范围内已初始化；MaybeUninit<u8> 与 u8 布局相同
        // SAFETY: 已由调用者保证
        unsafe { std::slice::from_raw_parts(slice.as_ptr().cast::<u8>(), len) }
    }

    pub fn initialized_len(&self) -> usize {
        self.initialized_len
    }
}

// ==================== 2. String/Vec into_raw_parts 在 WASM 中的应用 ====================

/// 演示 String::into_raw_parts 用于零拷贝传递
/// demonstration String::into_raw_parts
pub fn string_to_raw_parts_wasm(s: String) -> (usize, usize, usize) {
    let (ptr, len, capacity) = s.into_raw_parts();
    let meta = (ptr as usize, len, capacity);
    // 在 WASM 中通常需要重建 String，此处仅返回元数据用于演示
    let _ = unsafe { String::from_raw_parts(ptr, len, capacity) };
    meta
}

/// 演示 Vec::into_raw_parts 用于零拷贝传递
/// demonstration Vec::into_raw_parts
pub fn vec_to_raw_parts_wasm<T>(v: Vec<T>) -> (usize, usize, usize) {
    let (ptr, len, capacity) = v.into_raw_parts();
    let meta = (ptr as usize, len, capacity);
    let _ = unsafe { Vec::from_raw_parts(ptr, len, capacity) };
    meta
}

// ==================== 3. VecDeque pop_front_if / pop_back_if ====================

pub fn process_deque_conditional(mut deque: VecDeque<i32>) -> VecDeque<i32> {
    // 弹出前端满足条件的元素
    while let Some(v) = deque.pop_front_if(|x| *x < 0) {
        let _ = v; // 丢弃负值
    }
    // 弹出后端满足条件的元素
    while let Some(v) = deque.pop_back_if(|x| *x > 100) {
        let _ = v; // 丢弃超过 100 的值
    }
    deque
}

// ==================== 4. slice.as_array() 在 WASM 中的应用 ====================

/// 使用 Rust 1.93 as_array 处理固定大小数组
/// Rust 1.93 as_array
pub fn slice_to_array_four(slice: &[i32]) -> Option<[i32; 4]> {
    slice.as_array().copied()
}

/// 使用 char::MAX_LEN_UTF8 预分配 UTF-8 缓冲区
/// char::MAX_LEN_UTF8 UTF-8 buffering
pub fn max_utf8_buffer_size() -> usize {
    char::MAX_LEN_UTF8
}

/// 使用 char::MAX_LEN_UTF16 预分配 UTF-16 缓冲区
/// char::MAX_LEN_UTF16 UTF-16 buffering
pub fn max_utf16_buffer_size() -> usize {
    char::MAX_LEN_UTF16
}

// ==================== 5. Duration::from_nanos_u128 在 WASM 中的应用 ====================

/// 使用 Rust 1.93 Duration::from_nanos_u128 处理高精度纳秒
pub fn duration_from_nanos_u128(nanos: u128) -> Duration {
    Duration::from_nanos_u128(nanos)
}

// ==================== 6. fmt::from_fn 在 WASM 中的应用 ====================

/// 使用 Rust 1.93 fmt::from_fn 创建自定义格式化器
/// Rust 1.93 fmt::from_fn definition
pub fn create_wasm_formatter(value: i32) -> impl fmt::Display {
    fmt::from_fn(move |f: &mut fmt::Formatter<'_>| write!(f, "WASM[{}]", value))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_wasm_buffer_193() {
        let mut buf = WasmBuffer193::new(16);
        buf.write_from_slice(b"hello");
        assert_eq!(buf.initialized_len(), 5);
        let slice = unsafe { buf.get_initialized_ref(5) };
        assert_eq!(slice, b"hello");
    }

    #[test]
    fn test_deque_conditional() {
        // pop_front_if 移除前端满足条件的；pop_back_if 移除后端满足条件的
        let deque = VecDeque::from([-1, 2, 3, 5, 150]);
        let result = process_deque_conditional(deque);
        assert_eq!(result, VecDeque::from([2, 3, 5]));
    }

    #[test]
    fn test_slice_to_array() {
        let slice = &[1, 2, 3, 4];
        assert_eq!(slice_to_array_four(slice), Some([1, 2, 3, 4]));
        let short = &[1, 2];
        assert_eq!(slice_to_array_four(short), None);
    }

    #[test]
    fn test_char_constants() {
        assert_eq!(char::MAX_LEN_UTF8, 4);
        assert_eq!(char::MAX_LEN_UTF16, 2);
    }

    #[test]
    fn test_duration_from_nanos() {
        let d = duration_from_nanos_u128(1_000_000_000);
        assert_eq!(d.as_secs(), 1);
    }

    #[test]
    fn test_fmt_from_fn() {
        let f = create_wasm_formatter(42);
        assert_eq!(format!("{}", f), "WASM[42]");
    }
}
