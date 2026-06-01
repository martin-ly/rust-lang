//! Rust 192.0 新特性实现模块 —— c02_type_system
//! - `raw_ref_union`: `&raw [mut|const]` 对联合体字段在 safe 代码中允许
//! # 版本信息
//! # this
//! - Rust 版本: 192.0
//! - Rust this : 192.0
//! - Rust 版this: 192.0
//! - 稳定日期: 2025-12-11
//! - date : 2025-12-11
//! - 稳定date: 2025-12-11
//! - date: 2025-12-11

// ============================================================================
// 1. `MaybeUninit` 表示和有效性文档化
// ============================================================================

/// ## 对现有代码的影响
/// ## to impact
/// ## to现有代码impact
/// ## toimpact
/// 已经广泛存在。1.92 只是将这些已有保证正式写入文档。
/// in 。1.92 will 。
/// ## 实践意义
/// ##
use std::mem::MaybeUninit;

/// 利用 1.92 文档化 layout Guarantee。
///
/// 调用者必须确保  中的每个元素都已被正确初始化。
/// must in element is 。
/// 如果数组包含未初始化的元素，调用此函数将导致未定义行为。
/// if element ，this function will definition as 。
pub unsafe fn assume_init_array<T, const N: usize>(arr: [MaybeUninit<T>; N]) -> [T; N] {
    // SAFETY: [MaybeUninit<T>; N] 与 [T; N] layout 相同（1.92+ 文档保证）
    unsafe { std::mem::transmute_copy(&arr) }
}

#[test]
fn test_maybe_uninit_docs() {
    let arr: [MaybeUninit<i32>; 3] = std::array::from_fn(|i| MaybeUninit::new(i as i32 * 10));
    let initialized = unsafe { assume_init_array(arr) };
    assert_eq!(initialized, [0, 10, 20]);
}

// ============================================================================
// 2. `&raw [mut|const]` 对联合体字段在 safe 代码中允许
// ============================================================================

/// # Safe 代码in `&raw` unionvolumefieldreference
/// Rust 1.92.0 允许在 safe 代码中使用 `&raw const` 和 `&raw mut`
/// ## 背景
/// ## background
/// 因为编译器无法确定哪个变体是活跃的。
/// because volume 。
/// ## 现在
/// ## present
/// `&raw mut union.field` 直接产生原始指针（不创建引用），
/// `&raw mut union.field` raw pointer （reference ），
/// `&raw mut union.field` 直接Generateraw pointer（不Createreference），
/// ## 限制
/// ##
/// - 只能使用 `&raw`（原始指针），不能创建 `&union.field`（引用）
/// - `&raw`（raw pointer ），cannot `&union.field`（reference ）
/// - 解引用原始指针仍然需要 `unsafe`
/// - reference raw pointer `unsafe`
#[repr(C)]
pub union Value {
    pub int: i32,
    pub float: f32,
    pub bytes: [u8; 4],
}

pub fn get_union_raw_ptr(u: &mut Value) -> *mut i32 {
    &raw mut u.int
}

/// 在 safe 代码中读取联合体字节表示
/// in safe in union volume represent
pub fn get_union_bytes(u: &Value) -> *const [u8; 4] {
    &raw const u.bytes
}

#[test]
fn test_raw_ref_union() {
    let mut v = Value { int: 0x12345678 };
    let int_ptr = get_union_raw_ptr(&mut v);
    let bytes_ptr = get_union_bytes(&v);
    unsafe {
        assert_eq!(*int_ptr, 0x12345678);
        // 字节表示取决于平台字节序
        let _ = *bytes_ptr;
    }
}
