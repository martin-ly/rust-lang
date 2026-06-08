//! # 练习 8: `&raw const` / `&raw mut` — 原始引用操作符 (Rust 1.95) / Exercise 8: Raw Reference Operators
//!
//! **难度 / Difficulty**: Medium  
//! **考点 / Focus**: 原始引用操作符、避免中间引用 UB、`addr_of!` 替代、packed struct / union 安全访问
//!   Avoiding intermediate reference UB, `addr_of!` alternative, safe packed struct/union access
//!
//! ## 背景 / Background
//!
//! 在 Rust 1.95 之前，获取一个值的原始指针通常使用 `&expr as *const _`。
//! Before Rust 1.95, getting a raw pointer to a value usually used `&expr as *const _`.
//! 这种方式有一个隐藏问题：它会**先创建一个中间引用**，再将其强制转换为原始指针。
//! This has a hidden issue: it **first creates an intermediate reference**, then coerces to raw pointer.
//! 如果 `expr` 是未对齐的（如 `#[repr(packed)]` struct 的字段），
//! If `expr` is unaligned (e.g., field of `#[repr(packed)]` struct),
//! 创建这个中间引用本身就是 **Undefined Behavior (UB)**。
//! creating this intermediate reference itself is **Undefined Behavior (UB)**.
//!
//! Rust 1.95 稳定了原始引用操作符 `&raw const expr` 和 `&raw mut expr`，
//! Rust 1.95 stabilized raw reference operators `&raw const expr` and `&raw mut expr`,
//! 它们**直接创建原始指针**，不会经过中间引用，从而彻底避免了这个问题。
//! which **directly create raw pointers** without intermediate references, completely avoiding this issue.
//!
//! ## 要求 / Requirements
//!
//! - 使用 `&raw const` / `&raw mut` 替代 `&expr as *const/mut _`
//!   Use `&raw const` / `&raw mut` instead of `&expr as *const/mut _`
//! - 在 `#[repr(packed)]` struct 和 `union` 中安全地获取字段指针
//!   Safely get field pointers in `#[repr(packed)]` structs and `union`s
//! - 对比 `std::ptr::addr_of!` 宏与原始引用操作符
//!   Compare `std::ptr::addr_of!` macro with raw reference operators

/// 一个 packed 结构体，其 `value` 字段可能未按 `u32` 对齐
/// A packed struct whose `value` field may not be aligned for `u32`
#[repr(C, packed)]
pub struct PackedData {
    pub flag: u8,
    pub value: u32,
}

/// 使用 `&raw const` 安全地获取 packed struct 字段的原始指针
/// Safely gets raw pointer to packed struct field using `&raw const`
///
/// # 对比 / Comparison
///
/// 旧写法（Rust 2021 及之前）是 UB：
/// Old style (Rust 2021 and earlier) is UB:
/// ```ignore
/// let ptr = &data.value as *const u32; // UB! 创建了未对齐引用 / UB! Creates unaligned reference
/// ```
///
/// 新写法（Rust 1.95+）是安全的：
/// New style (Rust 1.95+) is safe:
/// ```ignore
/// let ptr = &raw const data.value;     // 正确！直接创建原始指针 / Correct! Directly creates raw pointer
/// ```
pub fn packed_field_ptr(data: &PackedData) -> *const u32 {
    &raw const data.value
}

/// 使用 `&raw mut` 安全地获取 packed struct 字段的可变原始指针
/// Safely gets mutable raw pointer to packed struct field using `&raw mut`
pub fn packed_field_ptr_mut(data: &mut PackedData) -> *mut u32 {
    &raw mut data.value
}

/// 一个用于类型双关的 union
/// A union for type punning
#[repr(C)]
pub union IntBytes {
    pub int: u32,
    pub bytes: [u8; 4],
}

/// 使用 `&raw const` 获取 union 字段的原始指针
/// Gets raw pointer to union field using `&raw const`
///
/// Union 的字段共享同一内存，读取非活跃字段是 unsafe 的。
/// Union fields share the same memory, reading non-active field is unsafe.
/// 但获取字段的**指针**是 safe 的——只要不解引用。
/// But getting the **pointer** to a field is safe — as long as you don't dereference.
pub fn union_field_ptr(union_data: &IntBytes) -> *const [u8; 4] {
    &raw const union_data.bytes
}

/// 对比：`addr_of!` 宏与 `&raw const` 操作符
/// Comparison: `addr_of!` macro vs `&raw const` operator
///
/// `std::ptr::addr_of!` 是 Rust 1.51 引入的宏，功能与 `&raw const` 相同。
/// `std::ptr::addr_of!` is a macro introduced in Rust 1.51 with same functionality as `&raw const`.
/// 在 Rust 1.95+ 中，`&raw const` 是原生语法，更简洁、更易读。
/// In Rust 1.95+, `&raw const` is native syntax, more concise and readable.
///
/// 两者在语义上完全等价：
/// Both are semantically equivalent:
/// - `addr_of!(expr)`  ≡  `&raw const expr`
/// - `addr_of_mut!(expr)` ≡ `&raw mut expr`
///
/// 本函数返回 `true`，表示两者等价。
/// This function returns `true`, indicating equivalence.
pub fn addr_of_equivalent_to_raw_const() -> bool {
    let x = 42u32;
    let p1: *const u32 = std::ptr::addr_of!(x);
    let p2: *const u32 = &raw const x;
    std::ptr::eq(p1, p2)
}

/// 安全地读取 packed struct 的未对齐字段
/// Safely reads unaligned field from packed struct
///
/// 使用 `&raw const` 获取指针后，通过 `read_unaligned` 读取值。
/// After getting pointer via `&raw const`, read value via `read_unaligned`.
/// 整个过程没有任何未对齐引用的创建。
/// No unaligned references are created throughout.
pub fn read_packed_value(data: &PackedData) -> u32 {
    // SAFETY: 我们通过 &raw const 获取了指针，没有创建未对齐引用。
    // SAFETY: We got pointer via &raw const, no unaligned reference created.
    // read_unaligned 不要求指针对齐。
    // read_unaligned does not require pointer alignment.
    unsafe { std::ptr::read_unaligned(packed_field_ptr(data)) }
}

/// 安全地写入 packed struct 的未对齐字段
/// Safely writes unaligned field to packed struct
pub fn write_packed_value(data: &mut PackedData, value: u32) {
    // SAFETY: 我们通过 &raw mut 获取了指针，没有创建未对齐引用。
    // SAFETY: We got pointer via &raw mut, no unaligned reference created.
    // write_unaligned 不要求指针对齐。
    // write_unaligned does not require pointer alignment.
    unsafe { std::ptr::write_unaligned(packed_field_ptr_mut(data), value) };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_packed_field_ptr_not_null() {
        let data = PackedData {
            flag: 1,
            value: 0x12345678,
        };
        let ptr = packed_field_ptr(&data);
        assert!(!ptr.is_null());
    }

    #[test]
    fn test_packed_field_ptr_mut_not_null() {
        let mut data = PackedData { flag: 1, value: 0 };
        let ptr = packed_field_ptr_mut(&mut data);
        assert!(!ptr.is_null());
    }

    #[test]
    fn test_read_packed_value() {
        let data = PackedData {
            flag: 0xAB,
            value: 0xDEADBEEF,
        };
        assert_eq!(read_packed_value(&data), 0xDEADBEEF);
    }

    #[test]
    fn test_write_packed_value() {
        let mut data = PackedData { flag: 0, value: 0 };
        write_packed_value(&mut data, 0xCAFEBABE);
        assert_eq!(read_packed_value(&data), 0xCAFEBABE);
    }

    #[test]
    fn test_union_field_ptr() {
        let data = IntBytes { int: 0x12345678 };
        let ptr = union_field_ptr(&data);
        assert!(!ptr.is_null());
        // SAFETY: union 当前活跃字段是 int，bytes 与之共享内存，读取 bytes 是合法的。
        // SAFETY: Union's active field is int, bytes shares memory, reading bytes is valid.
        let bytes = unsafe { *ptr };
        // 小端序下，0x12345678 的字节表示为 [0x78, 0x56, 0x34, 0x12]
        assert_eq!(bytes, 0x12345678u32.to_ne_bytes());
    }

    #[test]
    fn test_addr_of_equivalent_to_raw_const() {
        assert!(addr_of_equivalent_to_raw_const());
    }

    #[test]
    fn test_raw_const_vs_as_cast() {
        let x = 42u32;
        let p1 = &raw const x;
        let p2: *const u32 = &x as *const u32;
        // 两者指向同一地址（但 &raw const 更安全，不经过中间引用）
        // Both point to same address (but &raw const is safer, no intermediate reference)
        assert_eq!(p1, p2);
        // SAFETY: 两个指针都指向有效的 x
        // SAFETY: Both pointers point to valid x
        unsafe {
            assert_eq!(*p1, 42);
            assert_eq!(*p2, 42);
        }
    }
}
