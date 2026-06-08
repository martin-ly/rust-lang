//! # 练习 11: `const {}` 块与 `&raw const` 在 const 上下文中的应用 (Rust 1.95) / Exercise 11: const Blocks and Raw References
//!
//! **难度 / Difficulty**: Hard  
//! **考点 / Focus**: `const {}` 块、const 上下文中的原始指针、`const fn` 安全边界
//!   Raw pointers in const context, const fn safety boundaries
//!
//! ## 背景 / Background
//!
//! Rust 1.95 扩展了 `const {}` 块的可用上下文，允许在类型位置、数组长度、
//! Rust 1.95 expanded `const {}` block contexts, allowing type positions, array lengths,
//! 枚举判别式等更多地方使用 `const { expr }`。
//! enum discriminants, and more places to use `const { expr }`.
//!
//! 同时，`&raw const` 操作符也可以在 `const fn` 中使用，
//! Meanwhile, `&raw const` operator can also be used in `const fn`,
//! 使得在编译期安全地获取原始指针成为可能。
//! making it possible to safely obtain raw pointers at compile time.
//!
//! 本练习结合这两个特性，展示 Rust 在编译期计算能力的增强。
//! This exercise combines both features, demonstrating Rust's enhanced compile-time computation.
//!
//! ## 要求 / Requirements
//!
//! - 使用 `const {}` 块在类型位置和运行时上下文中进行编译期计算
//!   Use `const {}` blocks for compile-time computation in type positions and runtime contexts
//! - 在 `const fn` 中使用 `&raw const` 获取原始指针
//!   Use `&raw const` in `const fn` to get raw pointers
//! - 理解 const 上下文中 unsafe 操作的安全边界
//!   Understand safety boundaries of unsafe operations in const contexts

/// 使用 `const {}` 块计算数组大小
/// Calculates array size using `const {}` block
///
/// `const { 4 + 4 }` 在编译期求值为 `8`，因此数组类型为 `[u8; 8]`。
/// `const { 4 + 4 }` evaluates to `8` at compile time, so array type is `[u8; 8]`.
pub fn const_block_array() -> [u8; const { 4 + 4 }] {
    [0; const { 4 + 4 }]
}

/// 使用 `const {}` 块进行编译期字符串长度计算
/// Compile-time string length calculation using `const {}` block
///
/// `const { b"hello".len() }` 在编译期求值为 `5`。
/// `const { b"hello".len() }` evaluates to `5` at compile time.
pub fn const_block_string_len() -> usize {
    const { b"hello".len() }
}

/// 在 `const fn` 中使用 `&raw const` 获取原始指针
/// Gets raw pointer in `const fn` using `&raw const`
///
/// 这是安全的，因为 `&raw const` 不会创建中间引用，
/// This is safe because `&raw const` does not create intermediate references,
/// 不会触发借用检查器的运行时约束。
/// not triggering borrow checker runtime constraints.
pub const fn const_raw_ptr<T>(value: &T) -> *const T {
    &raw const *value
}

/// 在 `const fn` 中读取原始指针指向的值
/// Reads value pointed to by raw pointer in `const fn`
///
/// # Safety
///
/// 调用者必须确保 `ptr` 指向有效的 `T`。
/// Caller must ensure `ptr` points to valid `T`.
/// 本函数在 const 上下文中使用 `unsafe` 块读取指针。
/// This function uses `unsafe` block to read pointer in const context.
pub const unsafe fn const_deref<T: Copy>(ptr: *const T) -> T {
    // SAFETY: 调用者保证 ptr 指向有效的 T
    // SAFETY: Caller guarantees ptr points to valid T
    unsafe { *ptr }
}

/// 使用 `const {}` 块实现编译期类型大小查询
/// Compile-time type size query using `const {}` block
///
/// `const { std::mem::size_of::<u64>() }` 在编译期求值为 `8`。
/// `const { std::mem::size_of::<u64>() }` evaluates to `8` at compile time.
pub fn const_block_size_of() -> usize {
    const { std::mem::size_of::<u64>() }
}

/// 一个演示 `const {}` 块在复杂表达式中使用的函数
/// Demonstrates `const {}` block in complex expressions
///
/// 计算一个缓冲区的大小：`header_size + payload_size * count`，
/// Calculates buffer size: `header_size + payload_size * count`,
/// 其中所有值都在编译期确定。
/// where all values are determined at compile time.
pub fn const_block_buffer_size() -> usize {
    const HEADER_SIZE: usize = 4;
    const PAYLOAD_SIZE: usize = 16;
    const COUNT: usize = 3;
    const { HEADER_SIZE + PAYLOAD_SIZE * COUNT }
}

/// 判断题：const 上下文中的 unsafe
/// True/false: unsafe in const context
///
/// 1. "`const fn` 中不能包含任何 `unsafe` 操作。" → false
///    "`const fn` cannot contain any `unsafe` operations."
/// 2. "`&raw const` 可以在 `const fn` 中使用。" → true
///    "`&raw const` can be used in `const fn`."
/// 3. "`const {}` 块中的代码在运行时才执行。" → false
///    "Code in `const {}` blocks executes at runtime."
/// 4. "`unsafe { *ptr }` 在 `const fn` 中需要 unsafe 块包裹。" → true
///    "`unsafe { *ptr }` needs unsafe block wrapping in `const fn`."
pub fn const_unsafe_quiz() -> [bool; 4] {
    [false, true, false, true]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_const_block_array() {
        let arr = const_block_array();
        assert_eq!(arr.len(), 8);
        assert!(arr.iter().all(|&x| x == 0));
    }

    #[test]
    fn test_const_block_string_len() {
        assert_eq!(const_block_string_len(), 5);
    }

    #[test]
    fn test_const_raw_ptr() {
        let x = 42u32;
        let ptr = const_raw_ptr(&x);
        // SAFETY: ptr 指向有效的 x
        // SAFETY: ptr points to valid x
        unsafe {
            assert_eq!(*ptr, 42);
        }
    }

    #[test]
    fn test_const_deref() {
        let x = 100i64;
        let ptr = const_raw_ptr(&x);
        // SAFETY: ptr 指向有效的 x
        // SAFETY: ptr points to valid x
        unsafe {
            assert_eq!(const_deref(ptr), 100);
        }
    }

    #[test]
    fn test_const_block_size_of() {
        assert_eq!(const_block_size_of(), 8);
    }

    #[test]
    fn test_const_block_buffer_size() {
        assert_eq!(const_block_buffer_size(), 4 + 16 * 3);
    }

    #[test]
    fn test_const_unsafe_quiz() {
        assert_eq!(const_unsafe_quiz(), [false, true, false, true]);
    }

    #[test]
    fn test_const_block_in_type_position() {
        // 使用 const {} 在类型位置
        // Using const {} in type position
        let arr: [u8; const { 2 + 3 }] = [1, 2, 3, 4, 5];
        assert_eq!(arr.len(), 5);
    }
}
