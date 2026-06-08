//! # 练习 1: 原始指针与安全的数组分割 / Exercise 1: Raw Pointers and Safe Array Splitting
//!
//! **难度 / Difficulty**: Medium  
//! **考点 / Focus**: 原始指针的创建、偏移、解引用；与借用检查器的交互
//!   Raw pointer creation, offset, dereference; interaction with borrow checker
//!
//! ## 题目描述 / Problem Description
//!
//! 标准库中的 `slice::split_at_mut` 可以在编译期 borrow checker 无法通过的场景下，
//! 安全地将一个可变切片分成两个不重叠的部分。
//! Standard library's `slice::split_at_mut` safely splits a mutable slice into two
//! non-overlapping parts in scenarios where the compile-time borrow checker cannot verify safety.
//!
//! 请使用**原始指针** (`*mut T`) 实现一个等价的 `safe_split_at_mut` 函数。
//! Please implement an equivalent `safe_split_at_mut` function using **raw pointers** (`*mut T`).
//!
//! ## 要求 / Requirements
//!
//! - 使用 `as_mut_ptr()` 获取切片的原始指针
//!   Use `as_mut_ptr()` to get the slice's raw pointer
//! - 使用 `pointer::add` 进行指针偏移
//!   Use `pointer::add` for pointer offset
//! - 使用 `slice::from_raw_parts_mut` 将原始指针转回切片
//!   Use `slice::from_raw_parts_mut` to convert raw pointer back to slice
//! - 确保所有 unsafe 操作都被包裹在 `unsafe` 块中
//!   Ensure all unsafe operations are wrapped in `unsafe` blocks
//! - 函数本身是 safe 的，调用者无需写 `unsafe`
//!   Function itself is safe, callers don't need `unsafe`
//!
//! ## 提示 / Hints
//!
//! - 原始指针不受到借用检查器的约束，因此可以同时存在指向同一数组不同位置的多个原始指针
//!   Raw pointers are not constrained by the borrow checker, so multiple raw pointers to different
//!   positions of the same array can coexist
//! - 你需要用断言确保 `mid <= slice.len()`，否则触发 panic（这是 safe API 的契约）
//!   Use assertions to ensure `mid <= slice.len()`, otherwise panic (this is the safe API contract)

/// 将一个可变切片在指定位置分割为两个不重叠的可变切片
/// Splits a mutable slice at a specified position into two non-overlapping mutable slices
///
/// # Panics
///
/// 当 `mid > slice.len()` 时 panic / Panics when `mid > slice.len()`
pub fn safe_split_at_mut<T>(slice: &mut [T], mid: usize) -> (&mut [T], &mut [T]) {
    assert!(mid <= slice.len(), "mid 索引越界 / mid index out of bounds");

    // 获取切片的原始指针 / Get the slice's raw pointer
    let ptr = slice.as_mut_ptr();
    let len = slice.len();

    unsafe {
        // 从原始指针重建两个不重叠的切片
        // Reconstruct two non-overlapping slices from raw pointers
        // 第一个切片: [0, mid) / First slice: [0, mid)
        // 第二个切片: [mid, len) / Second slice: [mid, len)
        let first = std::slice::from_raw_parts_mut(ptr, mid);
        let second = std::slice::from_raw_parts_mut(ptr.add(mid), len - mid);
        (first, second)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_split_at_mut_basic() {
        let mut arr = [1, 2, 3, 4, 5];
        let (left, right) = safe_split_at_mut(&mut arr, 2);
        assert_eq!(left, &[1, 2]);
        assert_eq!(right, &[3, 4, 5]);
    }

    #[test]
    fn test_split_at_mut_boundary_start() {
        let mut arr = [10, 20, 30];
        let (left, right) = safe_split_at_mut(&mut arr, 0);
        assert_eq!(left, &[]);
        assert_eq!(right, &[10, 20, 30]);
    }

    #[test]
    fn test_split_at_mut_boundary_end() {
        let mut arr = [10, 20, 30];
        let (left, right) = safe_split_at_mut(&mut arr, 3);
        assert_eq!(left, &[10, 20, 30]);
        assert_eq!(right, &[]);
    }

    #[test]
    fn test_split_at_mut_mutability() {
        let mut arr = [1, 2, 3, 4];
        let (left, right) = safe_split_at_mut(&mut arr, 2);
        left[0] = 100;
        right[0] = 200;
        assert_eq!(arr, [100, 2, 200, 4]);
    }

    #[test]
    #[should_panic(expected = "mid 索引越界")]
    fn test_split_at_mut_panic_on_oob() {
        let mut arr = [1, 2, 3];
        let _ = safe_split_at_mut(&mut arr, 4);
    }
}
