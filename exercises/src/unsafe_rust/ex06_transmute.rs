//! # 练习 6: `mem::transmute` 与类型双关
//!
//! **难度**: Medium  
//! **考点**: `std::mem::transmute`、`std::mem::transmute_copy`、大小与对齐约束、union
//!
//! ## 题目描述
//!
//! `transmute` 是 Rust 中最强大的类型转换工具，也是最容易出错的。
//! 它可以将一个值按位重新解释为另一种类型，**不执行任何运行时检查**。
//!
//! 本练习要求你在**保证安全前提**下使用 `transmute`，
//! 并对比 safe 的替代方案（如 `to_be_bytes`）。
//!
//! ## 要求
//!
//! - 使用 `transmute` 实现 `u32` 与 `[u8; 4]` 的转换
//! - 使用 `transmute_copy` 处理引用场景
//! - 使用 `union` 实现安全的类型双关（type punning）
//! - 理解为什么 `transmute` 要求 `size_of::<Src>() == size_of::<Dst>()`

/// 将 `u32` 按大端序（Big-Endian）转换为字节数组
///
/// 使用 **unsafe `transmute`** 实现，以练习底层语义。
/// 生产代码应优先使用 `u32::to_be_bytes()`。
///
/// # Safety
///
/// 此函数内部是 safe 的，因为 `u32` 和 `[u8; 4]` 的大小
/// 在编译期保证相同（均为 4 字节）。
pub fn u32_to_be_bytes_unsafe(value: u32) -> [u8; 4] {
    // SAFETY: u32 和 [u8; 4] 大小相同（均为 4 字节），
    // 且两者都是 POD（Plain Old Data）类型，按位重解释是安全的。
    unsafe { std::mem::transmute::<u32, [u8; 4]>(value.to_be()) }
}

/// 将字节数组按大端序（Big-Endian）转换为 `u32`
///
/// 使用 **unsafe `transmute`** 实现。
/// 生产代码应优先使用 `u32::from_be_bytes()`。
pub fn be_bytes_to_u32_unsafe(bytes: [u8; 4]) -> u32 {
    // SAFETY: [u8; 4] 和 u32 大小相同（均为 4 字节），
    // 按位重解释为 u32 后再调用 from_be() 还原主机字节序。
    let native: u32 = unsafe { std::mem::transmute::<[u8; 4], u32>(bytes) };
    u32::from_be(native)
}

/// 使用 `union` 实现安全的类型双关（type punning）
///
/// Union 是 C 兼容的类型，允许同一内存位置存储不同类型的值。
/// 在 Rust 中，读取 union 的非当前活跃字段是 **unsafe** 的。
#[repr(C)]
pub union FloatIntUnion {
    pub f: f32,
    pub i: u32,
}

/// 将 `f32` 的底层位模式提取为 `u32`
///
/// # Safety
///
/// 调用者必须确保 union 的 `f` 字段是最后写入的活跃字段。
/// 本函数内部是 safe 的，因为我们控制 union 的写入顺序。
pub fn f32_bits_via_union(value: f32) -> u32 {
    let u = FloatIntUnion { f: value };
    // SAFETY: 我们刚刚写入了 `f` 字段，因此读取 `i` 字段是合法的。
    // 这等价于 `value.to_bits()` 的底层实现。
    unsafe { u.i }
}

/// 使用 `transmute_copy` 获取 `&f32` 的位模式视图
///
/// `transmute_copy` 与 `transmute` 的区别在于：
/// - `transmute` 按值移动输入，消耗所有权
/// - `transmute_copy` 从引用处按位复制，不消耗所有权
///
/// # Safety
///
/// 调用者必须确保 `Src` 和 `Dst` 的大小相同。
pub unsafe fn f32_ref_bits_via_transmute_copy(value: &f32) -> u32 {
    // SAFETY: f32 和 u32 大小相同（4 字节），对齐也兼容。
    unsafe { std::mem::transmute_copy::<f32, u32>(value) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_u32_to_be_bytes_unsafe() {
        assert_eq!(u32_to_be_bytes_unsafe(0x12345678), [0x12, 0x34, 0x56, 0x78]);
        assert_eq!(u32_to_be_bytes_unsafe(0x00000000), [0x00; 4]);
        assert_eq!(u32_to_be_bytes_unsafe(0xFFFFFFFF), [0xFF; 4]);
    }

    #[test]
    fn test_be_bytes_to_u32_unsafe() {
        assert_eq!(be_bytes_to_u32_unsafe([0x12, 0x34, 0x56, 0x78]), 0x12345678);
        assert_eq!(be_bytes_to_u32_unsafe([0x00; 4]), 0x00000000);
        assert_eq!(be_bytes_to_u32_unsafe([0xFF; 4]), 0xFFFFFFFF);
    }

    #[test]
    fn test_roundtrip_unsafe() {
        let original: u32 = 0xDEADBEEF;
        let bytes = u32_to_be_bytes_unsafe(original);
        let recovered = be_bytes_to_u32_unsafe(bytes);
        assert_eq!(original, recovered);
    }

    #[test]
    fn test_f32_bits_via_union() {
        // 0.0 的位模式是 0x00000000
        assert_eq!(f32_bits_via_union(0.0f32), 0x00000000);
        // 1.0 的位模式是 0x3F800000
        assert_eq!(f32_bits_via_union(1.0f32), 0x3F800000);
        // -0.0 的位模式是 0x80000000
        assert_eq!(f32_bits_via_union(-0.0f32), 0x80000000);
        // NaN 的位模式最高位是 0x7FC00000（quiet NaN）
        let nan_bits = f32_bits_via_union(f32::NAN);
        assert!(nan_bits & 0x7F800000 == 0x7F800000);
    }

    #[test]
    fn test_f32_bits_matches_std() {
        let values = [
            0.0f32,
            -0.0,
            1.0,
            -1.0,
            3.14159,
            f32::NAN,
            f32::INFINITY,
            f32::NEG_INFINITY,
        ];
        for &v in &values {
            assert_eq!(f32_bits_via_union(v), v.to_bits(), "mismatch for {v}");
        }
    }

    #[test]
    fn test_f32_ref_bits_via_transmute_copy() {
        let value = 2.5f32;
        // SAFETY: f32 和 u32 大小相同，这是调用者保证的。
        let bits = unsafe { f32_ref_bits_via_transmute_copy(&value) };
        assert_eq!(bits, value.to_bits());
    }
}
