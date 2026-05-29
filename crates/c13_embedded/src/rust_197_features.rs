//! Rust 1.97 特性跟踪模块 —— 嵌入式/系统编程
#![allow(clippy::incompatible_msrv)]

use std::ptr;

/// # Rust 1.97 嵌入式/系统编程特性演示
///
/// Rust 1.97 稳定化的核心指针/Unsafe API：
/// - `core::ptr::with_exposed_provenance` / `with_exposed_provenance_mut` — 严格 provenance
/// - `core::ptr::without_provenance` / `without_provenance_mut`
/// - `core::ptr::dangling` / `dangling_mut`
/// - `<*const T>::addr` / `expose_provenance` / `with_addr` / `map_addr`
/// - `pointer::byte_add` / `byte_offset` / `wrapping_byte_add` 等
///
/// **⚠️ 这些 API 涉及 Strict Provenance 模型，是 Rust 内存安全模型的重大演进。**
pub struct Rust197EmbeddedFeatures;

impl Rust197EmbeddedFeatures {
    /// 使用 `ptr::without_provenance` 创建一个无 provenance 的空指针
    ///
    /// 适用于对齐检查、哨兵值等不需要解引用的场景。
    pub fn create_dangling_ptr<T>() -> *const T {
        ptr::without_provenance(0)
    }

    /// 使用 `ptr::dangling<T>()` 创建对齐的正确悬空指针
    ///
    /// 常用于自定义集合的初始占位状态。
    pub fn create_aligned_dangling<T>() -> *const T {
        ptr::dangling::<T>()
    }

    /// 使用 `<*const T>::addr` 获取指针的地址（usize）
    ///
    /// 剥离 provenance，仅保留数值地址。这是 Strict Provenance 的核心操作。
    pub fn pointer_address<T>(ptr: *const T) -> usize {
        ptr.addr()
    }

    /// 使用 `<*const T>::with_addr` 创建具有新地址但保留原 provenance 的指针
    ///
    /// 这是 Strict Provenance 中"替换地址但保留权限"的安全方式。
    pub fn pointer_with_addr<T>(ptr: *const T, new_addr: usize) -> *const T {
        ptr.with_addr(new_addr)
    }

    /// 使用 `<*const T>::map_addr` 通过闭包映射指针地址
    pub fn pointer_map_addr<T>(ptr: *const T, f: impl FnOnce(usize) -> usize) -> *const T {
        ptr.map_addr(f)
    }

    /// 使用 `pointer::byte_add` 按字节偏移指针
    ///
    /// 替代 `ptr.cast::<u8>().add(offset).cast::<T>()` 的繁琐写法。
    ///
    /// # Safety
    /// 调用者必须确保偏移后的指针仍在有效分配范围内。
    pub unsafe fn offset_by_bytes<T>(ptr: *const T, offset: usize) -> *const T {
        // SAFETY: caller ensures the offset is in-bounds
        unsafe { ptr.byte_add(offset) }
    }

    /// 使用 `pointer::byte_offset_from` 计算两个字节指针之间的距离
    ///
    /// # Safety
    /// 两个指针必须指向同一个分配的对象。
    pub unsafe fn byte_distance<T>(a: *const T, b: *const T) -> isize {
        // SAFETY: caller ensures both pointers are within the same allocation
        unsafe { a.byte_offset_from(b) }
    }

    /// 使用 `pointer::wrapping_byte_add` 进行环绕字节偏移
    pub fn wrapping_offset_bytes<T>(ptr: *const T, offset: usize) -> *const T {
        ptr.wrapping_byte_add(offset)
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
