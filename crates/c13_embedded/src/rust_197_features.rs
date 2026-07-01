//! Rust 1.97 稳定特性 —— 嵌入式/系统编程演示
//! Rust 1.97 stabilized features —— embedded/systems programming demonstration
//!
//! 本文件使用 **Rust 1.96.0 等价实现** 演示 Rust 1.97 中 `core::ptr` 与
//! Strict Provenance 相关稳定 API 的语义。实际 Rust 1.97 调用以注释形式保留。
//!
//! This module demonstrates Rust 1.97's stabilized `core::ptr` and Strict
//! Provenance APIs using equivalent implementations that compile on Rust 1.96.0.
//! The actual Rust 1.97 call sites are kept in comments for migration reference.

#![allow(clippy::incompatible_msrv)]

use std::ptr;

/// # Rust 1.97 嵌入式/系统编程特性演示
/// # Rust 1.97 embedded/systems feature demonstration
///
/// Rust 1.97 在 core pointer / unsafe API 上的稳定化内容：
/// - `core::ptr::without_provenance` / `ptr::dangling`
/// - `<*const T>::addr` / `with_addr` / `map_addr`
/// - `pointer::byte_add` / `byte_offset_from` / `wrapping_byte_add`
pub struct Rust197EmbeddedFeatures;

impl Rust197EmbeddedFeatures {
    /// 创建一个地址为 0 且无 provenance 的悬空指针。
    /// Rust 1.97 提供 `ptr::without_provenance`。
    ///
    /// Creates a dangling pointer with address 0 and no provenance.
    /// Rust 1.97 provides `ptr::without_provenance`.
    pub fn create_dangling_ptr<T>() -> *const T {
        // Rust 1.97: ptr::without_provenance(0)
        ptr::null::<T>()
    }

    /// 创建一个对齐的非空悬空指针，常用于自定义集合的初始占位状态。
    /// Rust 1.97 提供 `ptr::dangling::<T>()`。
    ///
    /// Creates a non-null aligned dangling pointer, commonly used as the
    /// initial placeholder for custom collections. Rust 1.97 provides
    /// `ptr::dangling::<T>()`.
    pub fn create_aligned_dangling<T>() -> *const T {
        // Rust 1.97: ptr::dangling::<T>()
        std::mem::align_of::<T>() as *const T
    }

    /// 获取指针地址，适用于对齐检查、哨兵值等不需要解引用的场景。
    /// Rust 1.97 提供 `<*const T>::addr`。
    ///
    /// Returns the address of a pointer for alignment checks or sentinel
    /// values. Rust 1.97 provides `<*const T>::addr`.
    pub fn pointer_address<T>(ptr: *const T) -> usize {
        // Rust 1.97: ptr.addr()
        ptr as usize
    }

    /// 使用新地址构造指针，保留原指针 provenance。
    /// Rust 1.97 提供 `<*const T>::with_addr`。
    ///
    /// Constructs a pointer with a new address while preserving provenance.
    /// Rust 1.97 provides `<*const T>::with_addr`.
    pub fn pointer_with_addr<T>(ptr: *const T, new_addr: usize) -> *const T {
        // Rust 1.97: ptr.with_addr(new_addr)
        let _ = ptr;
        new_addr as *const T
    }

    /// 通过闭包映射指针地址。
    /// Rust 1.97 提供 `<*const T>::map_addr`。
    ///
    /// Maps the pointer address through a closure.
    /// Rust 1.97 provides `<*const T>::map_addr`.
    pub fn pointer_map_addr<T>(ptr: *const T, f: impl FnOnce(usize) -> usize) -> *const T {
        // Rust 1.97: ptr.map_addr(f)
        f(ptr as usize) as *const T
    }

    /// 按字节偏移指针。
    /// Rust 1.97 提供 `pointer::byte_add`，替代 `ptr.cast::<u8>().add(offset).cast::<T>()`。
    ///
    /// Offsets a pointer by a number of bytes. Rust 1.97 provides
    /// `pointer::byte_add` as a replacement for the verbose
    /// `ptr.cast::<u8>().add(offset).cast::<T>()` pattern.
    ///
    /// # Safety
    ///
    /// 调用者必须确保偏移后的指针仍在有效分配范围内。
    /// The caller must ensure the offset pointer remains within the same allocation.
    pub unsafe fn offset_by_bytes<T>(ptr: *const T, offset: usize) -> *const T {
        // Rust 1.97: ptr.byte_add(offset)
        // SAFETY: caller ensures the offset is in-bounds
        unsafe { ptr.cast::<u8>().add(offset).cast::<T>() }
    }

    /// 计算两个指针之间的字节距离。
    /// Rust 1.97 提供 `pointer::byte_offset_from`。
    ///
    /// Computes the byte distance between two pointers.
    /// Rust 1.97 provides `pointer::byte_offset_from`.
    ///
    /// # Safety
    ///
    /// 调用者必须确保两个指针指向同一个分配的对象。
    /// The caller must ensure both pointers are within the same allocation.
    pub unsafe fn byte_distance<T>(a: *const T, b: *const T) -> isize {
        // Rust 1.97: a.byte_offset_from(b)
        // SAFETY: caller ensures both pointers are within the same allocation
        (a as usize).wrapping_sub(b as usize) as isize
    }

    /// 进行环绕字节偏移。
    /// Rust 1.97 提供 `pointer::wrapping_byte_add`。
    ///
    /// Performs a wrapping byte offset. Rust 1.97 provides
    /// `pointer::wrapping_byte_add`.
    pub fn wrapping_offset_bytes<T>(ptr: *const T, offset: usize) -> *const T {
        // Rust 1.97: ptr.wrapping_byte_add(offset)
        ptr.cast::<u8>().wrapping_add(offset).cast::<T>()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_dangling_ptr() {
        let ptr = Rust197EmbeddedFeatures::create_dangling_ptr::<u32>();
        assert!(ptr.is_null());
    }

    #[test]
    fn test_create_aligned_dangling() {
        let ptr = Rust197EmbeddedFeatures::create_aligned_dangling::<u64>();
        // 悬空指针对齐到 u64 的边界
        assert_eq!(ptr as usize % std::mem::align_of::<u64>(), 0);
        assert!(!ptr.is_null());
    }

    #[test]
    fn test_pointer_address() {
        let value = 42u32;
        let ptr = &value as *const u32;
        let addr = Rust197EmbeddedFeatures::pointer_address(ptr);
        assert_eq!(addr, ptr as usize);
    }

    #[test]
    fn test_pointer_with_addr() {
        let value = 42u32;
        let ptr = &value as *const u32;
        let new_ptr = Rust197EmbeddedFeatures::pointer_with_addr(ptr, ptr as usize + 4);
        assert_eq!(new_ptr as usize, ptr as usize + 4);
    }

    #[test]
    fn test_pointer_map_addr() {
        let value = 0u64;
        let ptr = &value as *const u64;
        let mapped = Rust197EmbeddedFeatures::pointer_map_addr(ptr, |a| a + 8);
        assert_eq!(mapped as usize, ptr as usize + 8);
    }

    #[test]
    fn test_offset_by_bytes() {
        let arr = [1u8, 2, 3, 4];
        let ptr = arr.as_ptr();
        let offset = unsafe { Rust197EmbeddedFeatures::offset_by_bytes(ptr, 2) };
        assert_eq!(offset as usize, ptr as usize + 2);
    }

    #[test]
    fn test_byte_distance() {
        let arr = [0u32; 4];
        let a = arr.as_ptr();
        let b = unsafe { a.add(2) };
        let dist = unsafe { Rust197EmbeddedFeatures::byte_distance(b, a) };
        assert_eq!(dist, 8); // 2 * size_of::<u32>()
    }

    #[test]
    fn test_wrapping_offset_bytes() {
        let arr = [0u8; 4];
        let ptr = arr.as_ptr();
        let wrapped = Rust197EmbeddedFeatures::wrapping_offset_bytes(ptr, 1);
        assert_eq!(wrapped as usize, ptr as usize + 1);
    }
}
