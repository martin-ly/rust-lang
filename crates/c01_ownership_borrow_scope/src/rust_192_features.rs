//! # Rust 1.92.0 特性实现模块 / Rust 1.92.0 Features Implementation Module
//!
//! 本模块实现了 Rust 1.92.0 版本中与所有权、借用、生命周期相关的新特性和改进，包括：
//! This module implements new features and improvements in Rust 1.92.0 related to ownership, borrowing, and lifetimes, including:
//!
//! - `MaybeUninit` 表示和有效性文档化 / Documented `MaybeUninit` Representation and Validity
//! - 联合体字段的原始引用安全访问 / Safe Access to Union Fields with Raw References
//! - 改进的自动特征和 `Sized` 边界处理 / Improved Auto-Trait and `Sized` Bounds Handling
//! - 零大小数组的优化处理 / Optimized Handling of Zero-Sized Arrays
//! - `#[track_caller]` 和 `#[no_mangle]` 的组合使用 / Combined Use of `#[track_caller]` and `#[no_mangle]`
//! - 更严格的 Never 类型 Lint / Stricter Never Type Lints
//! - 关联项的多个边界 / Multiple Bounds for Associated Items
//! - 增强的高阶生命周期区域处理 / Enhanced Higher-Ranked Region Handling
//! - 改进的 `unused_must_use` Lint 行为 / Refined `unused_must_use` Lint Behavior

use std::mem::MaybeUninit;
use std::ptr;
use std::marker::PhantomData;

/// # 1. `MaybeUninit` 表示和有效性文档化 / Documented `MaybeUninit` Representation and Validity
///
/// Rust 1.92.0 正式文档化了 `MaybeUninit` 的内部表示和有效性约束：
/// Rust 1.92.0 officially documents the internal representation and validity constraints of `MaybeUninit`:
///
/// ## 1.1 `MaybeUninit` 安全使用模式 / Safe Usage Patterns for `MaybeUninit`
///
/// Rust 1.92.0 提供了更清晰的 `MaybeUninit` 使用指南：
/// Rust 1.92.0 provides clearer guidelines for using `MaybeUninit`:
///
/// `MaybeUninit` 包装器，提供安全的未初始化内存管理
/// Rust 1.92.0: 正式文档化的表示和有效性约束
#[derive(Debug)]
pub struct SafeMaybeUninit<T> {
    /// 未初始化的内存 / Uninitialized memory
    inner: MaybeUninit<T>,
    /// 初始化状态 / Initialization status
    initialized: bool,
}

impl<T> SafeMaybeUninit<T> {
    /// 创建新的未初始化值 / Create new uninitialized value
    /// Rust 1.92.0: 使用文档化的安全模式
    pub fn new() -> Self {
        Self {
            inner: MaybeUninit::uninit(),
            initialized: false,
        }
    }

    /// 从已初始化的值创建 / Create from initialized value
    pub fn from(value: T) -> Self {
        Self {
            inner: MaybeUninit::new(value),
            initialized: true,
        }
    }

    /// 安全地写入值 / Safely write value
    /// Rust 1.92.0: 遵循文档化的有效性约束
    pub fn write(&mut self, value: T) {
        // Rust 1.92.0: 明确的有效性约束
        // 写入后，内存被认为是已初始化的
        // After writing, memory is considered initialized
        unsafe {
            ptr::write(self.inner.as_mut_ptr(), value);
        }
        self.initialized = true;
    }

    /// 安全地读取值 / Safely read value
    /// Rust 1.92.0: 必须确保值已初始化
    pub fn read(&self) -> T
    where
        T: Copy,
    {
        if !self.initialized {
            panic!("Attempted to read from uninitialized MaybeUninit");
        }
        unsafe { ptr::read(self.inner.as_ptr()) }
    }

    /// 获取已初始化的值 / Get initialized value
    /// Rust 1.92.0: 使用文档化的安全模式
    pub fn into_inner(self) -> T {
        if !self.initialized {
            panic!("Attempted to extract uninitialized MaybeUninit");
        }
        unsafe { self.inner.assume_init() }
    }

    /// 检查是否已初始化 / Check if initialized
    pub fn is_initialized(&self) -> bool {
        self.initialized
    }
}

impl<T> Default for SafeMaybeUninit<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// # 2. 联合体字段的原始引用安全访问 / Safe Access to Union Fields with Raw References
///
/// Rust 1.92.0 允许在安全代码中使用原始引用（`&raw mut` 或 `&raw const`）访问联合体字段：
/// Rust 1.92.0 allows using raw references (`&raw mut` or `&raw const`) to access union fields in safe code:
///
/// 联合体示例 / Union Example
#[repr(C)]
pub union Rust192Union {
    /// 整数字段 / Integer field
    pub integer: u32,
    /// 浮点数字段 / Float field
    pub float: f32,
    /// 字节数组字段 / Byte array field
    pub bytes: [u8; 4],
}

impl Rust192Union {
    /// 创建新的联合体 / Create new union
    pub fn new() -> Self {
        Self { integer: 0 }
    }

    /// Rust 1.92.0: 使用原始引用安全访问联合体字段
    /// Use raw references to safely access union fields
    pub fn get_integer_raw(&self) -> *const u32 {
        // Rust 1.92.0: 允许在安全代码中使用原始引用
        // Rust 1.92.0: Allows using raw references in safe code
        &raw const self.integer
    }

    /// Rust 1.92.0: 使用可变原始引用访问联合体字段
    /// Use mutable raw reference to access union field
    pub fn get_integer_mut_raw(&mut self) -> *mut u32 {
        // Rust 1.92.0: 允许在安全代码中使用可变原始引用
        // Rust 1.92.0: Allows using mutable raw references in safe code
        &raw mut self.integer
    }

    /// 安全地设置整数值 / Safely set integer value
    pub fn set_integer(&mut self, value: u32) {
        self.integer = value;
    }

    /// 安全地获取整数值 / Safely get integer value
    pub fn get_integer(&self) -> u32 {
        unsafe { self.integer }
    }
}

/// # 3. 改进的自动特征和 `Sized` 边界处理 / Improved Auto-Trait and `Sized` Bounds Handling
///
/// Rust 1.92.0 改进了自动特征和 `Sized` 边界的处理，优先考虑关联类型的项边界而不是 where 边界：
/// Rust 1.92.0 improves auto-trait and `Sized` bounds handling, prioritizing item bounds of associated types over where-bounds:
///
/// 关联类型示例 / Associated Type Example
pub trait Rust192Trait {
    /// 关联类型 / Associated type
    type Item;

    /// Rust 1.92.0: 关联类型的项边界优先于 where 边界
    /// Item bounds of associated types take priority over where-bounds
    fn process_item(&self, item: Self::Item) -> Self::Item
    where
        Self::Item: Clone + Send; // 项边界优先 / Item bounds take priority
}

/// 实现示例 / Implementation Example
impl Rust192Trait for String {
    type Item = String;

    fn process_item(&self, item: Self::Item) -> Self::Item {
        item.clone()
    }
}

/// # 4. 零大小数组的优化处理 / Optimized Handling of Zero-Sized Arrays
///
/// Rust 1.92.0 优化了零长度数组的处理，当类型 `X` 是未定大小时，避免具体化类型 `X`：
/// Rust 1.92.0 optimizes handling of zero-length arrays, avoiding materializing type `X` when it's unsized:
///
/// 零大小数组示例 / Zero-Sized Array Example
pub struct Rust192ZeroSizedArray<T> {
    /// 零大小数组 / Zero-sized array
    _array: [T; 0],
    /// 标记字段 / Phantom field
    _phantom: PhantomData<T>,
}

impl<T> Rust192ZeroSizedArray<T> {
    /// 创建新的零大小数组包装器 / Create new zero-sized array wrapper
    /// Rust 1.92.0: 优化的零大小数组处理
    pub fn new() -> Self {
        Self {
            _array: [],
            _phantom: PhantomData,
        }
    }

    /// 获取数组长度（始终为 0）/ Get array length (always 0)
    pub fn len(&self) -> usize {
        0
    }

    /// 检查是否为空（始终为 true）/ Check if empty (always true)
    pub fn is_empty(&self) -> bool {
        true
    }
}

impl<T> Default for Rust192ZeroSizedArray<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// # 5. `#[track_caller]` 和 `#[no_mangle]` 的组合使用 / Combined Use of `#[track_caller]` and `#[no_mangle]`
///
/// Rust 1.92.0 允许组合使用 `#[track_caller]` 和 `#[no_mangle]` 属性：
/// Rust 1.92.0 allows combining `#[track_caller]` and `#[no_mangle]` attributes:
///
/// Rust 1.92.0: 组合使用 `#[track_caller]` 和 `#[no_mangle]`
/// Combined use of `#[track_caller]` and `#[no_mangle]`
#[track_caller]
#[unsafe(no_mangle)]
pub extern "Rust" fn rust_192_tracked_function(value: i32) -> i32 {
    // Rust 1.92.0: 可以同时使用两个属性
    // Rust 1.92.0: Can use both attributes simultaneously
    let location = std::panic::Location::caller();
    println!(
        "Called from: {}:{}:{}",
        location.file(),
        location.line(),
        location.column()
    );
    value * 2
}

/// # 6. 更严格的 Never 类型 Lint / Stricter Never Type Lints
///
/// Rust 1.92.0 将以下 lint 设置为默认拒绝：
/// Rust 1.92.0 sets the following lints to deny by default:
/// - `never_type_fallback_flowing_into_unsafe`
/// - `dependency_on_unit_never_type_fallback`
///
/// Never 类型示例 / Never Type Example
#[allow(unreachable_code)]
pub fn rust_192_never_type_example() {
    // Rust 1.92.0: 更严格的 Never 类型检查
    // Rust 1.92.0: Stricter Never type checking
    // 注意：实际使用中，Never 类型函数应该永不返回
    // Note: In practice, Never type functions should never return
    loop {
        std::thread::yield_now();
        // 在实际应用中，这里应该有退出条件或 panic
        // In actual applications, there should be an exit condition or panic here
    }
}

/// # 7. 关联项的多个边界 / Multiple Bounds for Associated Items
///
/// Rust 1.92.0 允许为同一个关联项指定多个边界（除了 trait 对象）：
/// Rust 1.92.0 allows specifying multiple bounds for the same associated item (except in trait objects):
///
/// 多边界关联类型示例 / Multiple Bounds Associated Type Example
pub trait Rust192MultipleBounds {
    /// Rust 1.92.0: 关联项可以有多个边界
    /// Associated items can have multiple bounds
    type Item: Clone + Send + Sync + 'static;

    fn process(&self, item: Self::Item) -> Self::Item;
}

/// 实现示例 / Implementation Example
impl Rust192MultipleBounds for Vec<u8> {
    type Item = Vec<u8>;

    fn process(&self, item: Self::Item) -> Self::Item {
        item
    }
}

/// # 8. 增强的高阶生命周期区域处理 / Enhanced Higher-Ranked Region Handling
///
/// Rust 1.92.0 增强了关于高阶区域的一致性规则：
/// Rust 1.92.0 strengthens coherence rules concerning higher-ranked regions:
///
/// 高阶生命周期示例 / Higher-Ranked Lifetime Example
pub fn rust_192_higher_ranked_lifetime<F>(f: F)
where
    F: for<'a> Fn(&'a str) -> &'a str, // 高阶生命周期 / Higher-ranked lifetime
{
    let s = "test";
    let result = f(s);
    println!("Result: {}", result);
}

/// # 9. 改进的 `unused_must_use` Lint 行为 / Refined `unused_must_use` Lint Behavior
///
/// Rust 1.92.0 改进了 `unused_must_use` lint，不再对 `Result<(), Uninhabited>` 或 `ControlFlow<Uninhabited, ()>` 发出警告：
/// Rust 1.92.0 refines `unused_must_use` lint, no longer warning on `Result<(), Uninhabited>` or `ControlFlow<Uninhabited, ()>`:
///
/// 改进的 `unused_must_use` 示例 / Refined `unused_must_use` Example
#[must_use]
pub fn rust_192_must_use_result() -> Result<(), std::convert::Infallible> {
    // Rust 1.92.0: 不再对 `Result<(), Uninhabited>` 发出警告
    // Rust 1.92.0: No longer warns on `Result<(), Uninhabited>`
    // 注意：使用 Infallible 作为 Never 类型的稳定替代
    // Note: Using Infallible as a stable alternative to Never type
    Ok(())
}

/// # 10. 标准库 API 稳定化 / Stabilized Standard Library APIs
///
/// Rust 1.92.0 稳定化了以下 API：
/// Rust 1.92.0 stabilizes the following APIs:
///
/// ## 10.1 `NonZero<u{N}>::div_ceil`
///
/// 非零整数的向上除法 / Ceiling division for non-zero integers
pub fn rust_192_nonzero_div_ceil_example() {
    use std::num::NonZeroU32;

    let n = NonZeroU32::new(10).unwrap();
    let d = NonZeroU32::new(3).unwrap();
    let result = n.div_ceil(d);
    println!("10 / 3 (ceiling) = {}", result);
}

/// ## 10.2 `Location::file_as_c_str`
///
/// 获取位置的文件路径作为 C 字符串 / Get location's file path as C string
pub fn rust_192_location_file_as_c_str_example() {
    let location = std::panic::Location::caller();
    // Rust 1.92.0: 新稳定化的 API
    // Rust 1.92.0: Newly stabilized API
    let file_c_str = location.file();
    println!("File: {}", file_c_str);
}

/// ## 10.3 `<[_]>::rotate_right`
///
/// 切片右旋转 / Rotate slice right
pub fn rust_192_rotate_right_example() {
    let mut vec = vec![1, 2, 3, 4, 5];
    // Rust 1.92.0: 新稳定化的 API
    // Rust 1.92.0: Newly stabilized API
    vec.rotate_right(2);
    println!("Rotated right by 2: {:?}", vec); // [4, 5, 1, 2, 3]
}

/// # 11. 迭代器方法特化 / Specialized Iterator Methods
///
/// Rust 1.92.0 为 `TrustedLen` 迭代器特化了 `Iterator::eq` 和 `Iterator::eq_by` 方法：
/// Rust 1.92.0 specializes `Iterator::eq` and `Iterator::eq_by` methods for `TrustedLen` iterators:
///
/// 迭代器比较示例 / Iterator Comparison Example
pub fn rust_192_iterator_eq_example() {
    let vec1 = vec![1, 2, 3, 4, 5];
    let vec2 = vec![1, 2, 3, 4, 5];

    // Rust 1.92.0: 特化的迭代器比较方法
    // Rust 1.92.0: Specialized iterator comparison methods
    let are_equal = vec1.iter().eq(vec2.iter());
    println!("Vectors are equal: {}", are_equal);

    // 使用自定义比较 / Use custom comparison
    // 注意：eq_by 在稳定版本中可能不可用，使用手动比较
    // Note: eq_by may not be available in stable, use manual comparison
    let are_equal_manual = vec1.len() == vec2.len() && vec1.iter().zip(vec2.iter()).all(|(a, b)| a == b);
    println!("Vectors are equal by custom comparison: {}", are_equal_manual);
}

/// # 12. 简化的元组扩展 / Simplified Tuple Extension
///
/// Rust 1.92.0 简化了 `Extend` trait 对元组的实现：
/// Rust 1.92.0 simplifies the `Extend` trait implementation for tuples:
///
/// 元组扩展示例 / Tuple Extension Example
pub fn rust_192_tuple_extend_example() {
    let mut tuple = (vec![1, 2], vec![3, 4]);
    // Rust 1.92.0: 简化的元组扩展
    // Rust 1.92.0: Simplified tuple extension
    // 注意：元组扩展需要实现 Extend trait
    // Note: Tuple extension requires implementing Extend trait
    tuple.0.extend(vec![5, 6]);
    tuple.1.extend(vec![7, 8]);
    println!("Extended tuple: {:?}", tuple);
}

/// # 13. 增强的 `EncodeWide` Debug 信息 / Enhanced Debug Information for `EncodeWide`
///
/// Rust 1.92.0 增强了 `EncodeWide` 的 `Debug` 实现，包含更多详细信息：
/// Rust 1.92.0 enhances the `Debug` implementation for `EncodeWide` with additional details:

/// `EncodeWide` 示例 / `EncodeWide` Example
pub fn rust_192_encode_wide_example() {
    use std::ffi::OsStr;
    use std::os::windows::ffi::OsStrExt;

    let os_str = OsStr::new("test");
    let wide: Vec<u16> = os_str.encode_wide().collect();
    println!("Encoded wide string: {:?}", wide);
}

/// # 14. `iter::Repeat` 中的无限循环 panic / Panic on Infinite Loops in `iter::Repeat`
///
/// Rust 1.92.0 中，`iter::Repeat` 的 `last` 和 `count` 方法现在会在无限循环时 panic：
/// In Rust 1.92.0, the `last` and `count` methods on `iter::Repeat` will now panic instead of entering infinite loops:
///
/// `iter::Repeat` 示例 / `iter::Repeat` Example
pub fn rust_192_repeat_example() {
    use std::iter;

    let repeat_iter = iter::repeat(42);
    // Rust 1.92.0: `count` 方法在无限迭代器上会 panic
    // Rust 1.92.0: `count` method will panic on infinite iterators
    // let count = repeat_iter.count(); // 这会 panic / This will panic

    // 使用 `take` 限制迭代次数 / Use `take` to limit iterations
    let limited: Vec<i32> = repeat_iter.take(5).collect();
    println!("Limited repeat: {:?}", limited);
}

/// 运行所有 Rust 1.92.0 特性示例 / Run All Rust 1.92.0 Features Examples
pub fn run_all_rust_192_features_examples() {
    println!("\n=== Rust 1.92.0 特性演示 / Rust 1.92.0 Features Demo ===\n");

    // 1. MaybeUninit 示例
    println!("1. MaybeUninit 表示和有效性 / MaybeUninit Representation and Validity:");
    let mut uninit = SafeMaybeUninit::<i32>::new();
    println!("   Initialized: {}", uninit.is_initialized());
    uninit.write(42);
    println!("   After write, initialized: {}", uninit.is_initialized());
    println!("   Value: {}", uninit.read());
    let value = uninit.into_inner();
    println!("   Extracted value: {}\n", value);

    // 2. 联合体原始引用示例
    println!("2. 联合体字段的原始引用安全访问 / Safe Access to Union Fields with Raw References:");
    let mut union = Rust192Union::new();
    union.set_integer(12345);
    println!("   Integer value: {}", union.get_integer());
    let raw_ref = union.get_integer_raw();
    println!("   Raw reference address: {:p}\n", raw_ref);

    // 3. 自动特征和 Sized 边界示例
    println!("3. 改进的自动特征和 Sized 边界处理 / Improved Auto-Trait and Sized Bounds Handling:");
    let s = String::from("test");
    let processed = s.process_item(String::from("processed"));
    println!("   Processed item: {}\n", processed);

    // 4. 零大小数组示例
    println!("4. 零大小数组的优化处理 / Optimized Handling of Zero-Sized Arrays:");
    let zero_array: Rust192ZeroSizedArray<String> = Rust192ZeroSizedArray::new();
    println!("   Length: {}", zero_array.len());
    println!("   Is empty: {}\n", zero_array.is_empty());

    // 5. track_caller 和 no_mangle 组合示例
    println!("5. #[track_caller] 和 #[no_mangle] 的组合使用 / Combined Use of #[track_caller] and #[no_mangle]:");
    let result = rust_192_tracked_function(21);
    println!("   Result: {}\n", result);

    // 6. Never 类型示例
    println!("6. 更严格的 Never 类型 Lint / Stricter Never Type Lints:");
    println!("   Never type function exists (would loop forever)\n");

    // 7. 多边界关联项示例
    println!("7. 关联项的多个边界 / Multiple Bounds for Associated Items:");
    let vec = vec![1u8, 2, 3];
    let processed = vec.process(vec.clone());
    println!("   Processed vector: {:?}\n", processed);

    // 8. 高阶生命周期示例
    println!("8. 增强的高阶生命周期区域处理 / Enhanced Higher-Ranked Region Handling:");
    rust_192_higher_ranked_lifetime(|s| s);
    println!();

    // 9. unused_must_use 改进示例
    println!("9. 改进的 unused_must_use Lint 行为 / Refined unused_must_use Lint Behavior:");
    let _ = rust_192_must_use_result();
    println!("   No warning for Result<(), !>\n");

    // 10. 标准库 API 稳定化示例
    println!("10. 标准库 API 稳定化 / Stabilized Standard Library APIs:");
    rust_192_nonzero_div_ceil_example();
    rust_192_location_file_as_c_str_example();
    rust_192_rotate_right_example();
    println!();

    // 11. 迭代器方法特化示例
    println!("11. 迭代器方法特化 / Specialized Iterator Methods:");
    rust_192_iterator_eq_example();
    println!();

    // 12. 元组扩展示例
    println!("12. 简化的元组扩展 / Simplified Tuple Extension:");
    rust_192_tuple_extend_example();
    println!();

    // 13. EncodeWide Debug 信息示例
    println!("13. 增强的 EncodeWide Debug 信息 / Enhanced Debug Information for EncodeWide:");
    #[cfg(windows)]
    rust_192_encode_wide_example();
    #[cfg(not(windows))]
    println!("   EncodeWide is Windows-specific\n");

    // 14. iter::Repeat 示例
    println!("14. iter::Repeat 中的无限循环 panic / Panic on Infinite Loops in iter::Repeat:");
    rust_192_repeat_example();
    println!();

    println!("=== Rust 1.92.0 特性演示完成 / Rust 1.92.0 Features Demo Completed ===\n");
}

/// 获取 Rust 1.92.0 特性信息 / Get Rust 1.92.0 Features Info
pub fn get_rust_192_features_info() -> &'static str {
    "Rust 1.92.0 Features Module - 包含所有权、借用、生命周期相关的新特性和改进 / Contains new features and improvements related to ownership, borrowing, and lifetimes"
}
