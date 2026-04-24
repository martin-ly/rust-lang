//! 内存布局保证
//!
//! 对照 The Rustonomicon 中关于类型布局、对齐和 size 的章节。
//!
//! Rust 提供了以下关键保证：
//! - `size_of::<T>()` 返回类型占用的字节数
//! - `align_of::<T>()` 返回类型的对齐要求
//! - 类型的对齐要求总是 2 的幂
//! - `size_of::<T>()` 总是 `align_of::<T>()` 的倍数

use std::mem::{align_of, offset_of, size_of};

/// 演示基本类型的布局保证
pub fn demonstrate_primitive_layouts() {
    println!(
        "u8:   size={:2}, align={}",
        size_of::<u8>(),
        align_of::<u8>()
    );
    println!(
        "u16:  size={:2}, align={}",
        size_of::<u16>(),
        align_of::<u16>()
    );
    println!(
        "u32:  size={:2}, align={}",
        size_of::<u32>(),
        align_of::<u32>()
    );
    println!(
        "u64:  size={:2}, align={}",
        size_of::<u64>(),
        align_of::<u64>()
    );
    println!(
        "usize:size={:2}, align={}",
        size_of::<usize>(),
        align_of::<usize>()
    );
    println!(
        "f64:  size={:2}, align={}",
        size_of::<f64>(),
        align_of::<f64>()
    );
}

/// 结构体布局与内存对齐
///
/// Rust 编译器会在字段之间插入 padding 以满足对齐要求。
/// 字段顺序会影响总大小！
#[repr(C)]
pub struct AlignDemoC {
    /// 字段 a，偏移 0
    pub a: u8,
    // 7 bytes padding
    /// 字段 b，偏移 8
    pub b: u64,
}

/// Rust 默认 repr 的结构体（编译器可能重排字段）
#[repr(Rust)]
pub struct AlignDemoRust {
    /// 字段 a
    pub a: u8,
    /// 字段 b
    pub b: u64,
}

/// 演示结构体布局差异
pub fn demonstrate_struct_layout() {
    println!(
        "AlignDemoC:   size={}, align={}",
        size_of::<AlignDemoC>(),
        align_of::<AlignDemoC>()
    );
    println!(
        "AlignDemoRust:size={}, align={}",
        size_of::<AlignDemoRust>(),
        align_of::<AlignDemoRust>()
    );
}

/// 手动布局控制：`#[repr(packed)]`
///
/// `packed` 禁止编译器插入 padding，可能降低对齐要求，
/// 但访问未对齐字段是 unsafe 的。
#[repr(C, packed)]
pub struct PackedStruct {
    /// 字段 a，偏移 0
    pub a: u8,
    /// 字段 b，偏移 1（无 padding）
    pub b: u64,
}

/// 获取 packed struct 的字段偏移量
pub fn packed_struct_offsets() -> (usize, usize) {
    (offset_of!(PackedStruct, a), offset_of!(PackedStruct, b))
}

/// 零大小类型 (ZST)
///
/// ZST 不占用内存，但具有对齐要求（通常为 1）。
pub struct ZeroSizedType;

/// 演示 ZST 特性
pub fn demonstrate_zst() {
    println!(
        "ZST size={}, align={}",
        size_of::<ZeroSizedType>(),
        align_of::<ZeroSizedType>()
    );
    assert_eq!(size_of::<ZeroSizedType>(), 0);
}

/// 动态大小类型 (DST) 概念
///
/// `[T]` 和 `str` 是 DST，必须通过指针使用（如 `&[T]`、`Box<str>`）。
pub fn dst_concepts() {
    let s: &[u8] = &[1, 2, 3];
    println!("胖指针大小: {}", size_of::<&[u8]>()); // 16（指针 + 长度）
    println!("切片长度: {}", s.len());
}

/// 对齐填充计算
///
/// 给定偏移量和类型对齐要求，计算需要多少 padding。
pub const fn padding_needed(offset: usize, align: usize) -> usize {
    let mask = align - 1;
    if offset & mask == 0 {
        0
    } else {
        align - (offset & mask)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_primitive_layouts() {
        demonstrate_primitive_layouts();
        assert_eq!(size_of::<u8>(), 1);
        assert_eq!(align_of::<u64>(), 8);
    }

    #[test]
    fn test_struct_layout() {
        demonstrate_struct_layout();
        assert_eq!(size_of::<AlignDemoC>(), 16);
        assert_eq!(align_of::<AlignDemoC>(), 8);
        assert_eq!(offset_of!(AlignDemoC, a), 0);
        assert_eq!(offset_of!(AlignDemoC, b), 8);
    }

    #[test]
    fn test_packed_struct() {
        let (off_a, off_b) = packed_struct_offsets();
        assert_eq!(off_a, 0);
        assert_eq!(off_b, 1); // packed 后无 padding
        assert_eq!(size_of::<PackedStruct>(), 9);
    }

    #[test]
    fn test_zst() {
        demonstrate_zst();
        assert_eq!(align_of::<ZeroSizedType>(), 1);
    }

    #[test]
    fn test_dst() {
        dst_concepts();
        assert_eq!(size_of::<&[u8]>(), size_of::<usize>() * 2);
    }

    #[test]
    fn test_padding_needed() {
        assert_eq!(padding_needed(0, 8), 0);
        assert_eq!(padding_needed(1, 8), 7);
        assert_eq!(padding_needed(8, 8), 0);
        assert_eq!(padding_needed(9, 4), 3);
    }
}
