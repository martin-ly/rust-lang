//! # Brown University CRP Ownership Inventory — Program 06
//!
//! **来源 / Source**: Brown University CRP Ownership Inventory 样题
//! **主题 / Topic**: 借用检查器错误修复 / Fixing Borrow Checker Errors
//!
//! ## 学习目标 / Learning Goal
//!
//! 在涉及集合（Vec）和可变借用的场景中，通过限制借用范围或使用索引来修复借用冲突。
//! Fix borrow-checker conflicts in collection (Vec) code by limiting borrow scope
//! or using indices.
//!
//! ## TODO
//!
//! 1. 下面的 `double_first_even` 需要同时读取和修改 Vec。当前实现会导致编译错误。
//! 2. 使用临时变量或缩小借用范围来修复它。
//! 3. 解释为什么不能同时持有 `&vec[0]` 和 `&mut vec`。

/// 找到第一个偶数，将其翻倍，并返回原值。
/// Finds the first even number, doubles it in place, and returns the original value.
///
/// TODO: 修复借用冲突，使代码编译并通过测试。
pub fn double_first_even(numbers: &mut [i32]) -> Option<i32> {
    // 需要先不可变地查找第一个偶数的位置或值
    let first_even = numbers.iter().copied().find(|&n| n % 2 == 0);

    // TODO: 如果存在偶数，需要可变地修改它。这里不能直接写 &mut numbers[...]
    // 因为 first_even 可能借用了 numbers。
    // 提示：使用 if let Some(value) = first_even 后再获取可变借用，
    // 或者使用索引 + 重新查找。
    if let Some(value) = first_even {
        // 重新查找索引，然后修改
        if let Some(idx) = numbers.iter().position(|&n| n == value) {
            numbers[idx] *= 2;
            return Some(value);
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_double_first_even() {
        let mut v = vec![1, 3, 4, 5];
        let original = double_first_even(&mut v);
        assert_eq!(original, Some(4));
        assert_eq!(v, vec![1, 3, 8, 5]);
    }

    #[test]
    fn test_no_even() {
        let mut v = vec![1, 3, 5];
        assert_eq!(double_first_even(&mut v), None);
        assert_eq!(v, vec![1, 3, 5]);
    }
}
