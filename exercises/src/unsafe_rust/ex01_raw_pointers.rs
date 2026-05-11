//! # 练习 1: 原始指针与安全的数组分割
//!
//! **难度**: Medium  
//! **考点**: 原始指针的创建、偏移、解引用；与借用检查器的交互
//!
//! ## 题目描述
//!
//! 标准库中的 `slice::split_at_mut` 可以在编译期 borrow checker 无法通过的场景下，
//! 安全地将一个可变切片分成两个不重叠的部分。
//!
//! 请使用**原始指针** (`*mut T`) 实现一个等价的 `safe_split_at_mut` 函数。
//!
//! ## 要求
//!
//! - 使用 `as_mut_ptr()` 获取切片的原始指针
//! - 使用 `pointer::add` 进行指针偏移
//! - 使用 `slice::from_raw_parts_mut` 将原始指针转回切片
//! - 确保所有 unsafe 操作都被包裹在 `unsafe` 块中
//! - 函数本身是 safe 的，调用者无需写 `unsafe`
//!
//! ## 提示
//!
//! - 原始指针不受到借用检查器的约束，因此可以同时存在指向同一数组不同位置的多个原始指针
//! - 你需要用断言确保 `mid <= slice.len()`，否则触发 panic（这是 safe API 的契约）

/// 将一个可变切片在指定位置分割为两个不重叠的可变切片
///
/// # Panics
///
/// 当 `mid > slice.len()` 时 panic
pub fn safe_split_at_mut<T>(slice: &mut [T], mid: usize) -> (&mut [T], &mut [T]) {
    assert!(mid <= slice.len(), "mid 索引越界");

    // 获取切片的原始指针
    let ptr = slice.as_mut_ptr();
    let len = slice.len();

    unsafe {
        // 从原始指针重建两个不重叠的切片
        // 第一个切片: [0, mid)
        // 第二个切片: [mid, len)
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
