//! Rust 192.0 新特性实现模块 —— c13_embedded
//!
//! 本模块展示了 Rust 192.0 (2025-12-11) 的关键语言特性和工具链改进。
//!
//! - `maybe_uninit_docs`: `MaybeUninit` 表示和有效性文档化
//! - `raw_ref_union`: `&raw [mut|const]` 对联合体字段在 safe 代码中允许
//!
//! # 版本信息
//! - Rust 版本: 192.0
//! - 稳定日期: 2025-12-11
//! - Edition: 2024

// ============================================================================
// 1. `MaybeUninit` 表示和有效性文档化
// ============================================================================

/// # `MaybeUninit` 文档化保证
///
/// Rust 1.92.0 正式文档化了 `MaybeUninit` 的内存表示保证：
/// - `MaybeUninit<T>` 与 `T` 具有相同的内存布局和对齐方式
/// - `[MaybeUninit<T>; N]` 与 `[T; N]` 保证 layout 相同
/// - `MaybeUninit<T>` 的未初始化状态是明确定义的（不是 UB）
///
/// ## 对现有代码的影响
/// 之前版本中，`transmute_copy` 和 `ptr::read` 在 `MaybeUninit` 上的使用
/// 已经广泛存在。1.92 只是将这些已有保证正式写入文档。
///
/// ## 实践意义
/// 这使得以下模式成为官方认可的 safe/unsafe 边界：
/// - 从 `[MaybeUninit<T>; N]` 到 `[T; N]` 的转换
/// - 在结构体字段中使用 `MaybeUninit` 来避免不必要的初始化
use std::mem::MaybeUninit;

/// 安全地转换已初始化的 MaybeUninit 数组
///
/// 利用 1.92 文档化的 layout 保证。
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

/// # Safe 代码中的 `&raw` 联合体字段引用
///
/// Rust 1.92.0 允许在 safe 代码中使用 `&raw const` 和 `&raw mut`
/// 获取联合体字段的原始指针，而无需 `unsafe` 块。
///
/// ## 背景
/// 联合体（union）字段的引用创建之前需要 `unsafe`，
/// 因为编译器无法确定哪个变体是活跃的。
///
/// ## 现在
/// `&raw mut union.field` 直接产生原始指针（不创建引用），
/// 因此不涉及 Rust 的引用规则，可以在 safe 代码中使用。
///
/// ## 限制
/// - 只能使用 `&raw`（原始指针），不能创建 `&union.field`（引用）
/// - 解引用原始指针仍然需要 `unsafe`
#[repr(C)]
pub union Value {
    pub int: i32,
    pub float: f32,
    pub bytes: [u8; 4],
}

/// 在 safe 代码中获取联合体字段的原始指针
pub fn get_union_raw_ptr(u: &mut Value) -> *mut i32 {
    &raw mut u.int
}

/// 在 safe 代码中读取联合体字节表示
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
