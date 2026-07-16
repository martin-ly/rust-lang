//! # Brown University CRP Ownership Inventory — Program 06
//!
//! **EN**: Fixing Borrow Checker Errors with Vec
//! **Summary**: Resolve borrow-checker conflicts in collection code by limiting borrow scope
//! or using indices.
//! **Key Terms**: 借用检查器 (borrow checker), 可变借用 (mutable borrow), 不可变借用
//! (immutable borrow), 索引 (index), 作用域 (scope), 临时变量 (temporary variable).
//! **Related Concepts**:
//! [`concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md`](../../../../../concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md),
//! [`concept/01_foundation/05_collections/01_collections.md`](../../../../../concept/01_foundation/05_collections/01_collections.md),
//! [`concept/01_foundation/01_ownership_borrow_lifetime/06_ownership_inventories_brown_book.md`](../../../../../concept/01_foundation/01_ownership_borrow_lifetime/06_ownership_inventories_brown_book.md).
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
//! ## TODO / Tasks
//!
//! 1. 下面的 `double_first_even` 需要同时读取和修改 Vec。当前实现会导致编译错误。
//!    `double_first_even` below needs to read and mutate a Vec at the same time. The current
//!    implementation causes a compile error.
//! 2. 使用临时变量或缩小借用范围来修复它。
//!    Fix it by using a temporary variable or narrowing the borrow scope.
//! 3. 解释为什么不能同时持有 `&vec[0]` 和 `&mut vec`。
//!    Explain why `&vec[0]` and `&mut vec` cannot coexist.

/// 找到第一个偶数，将其翻倍，并返回原值。
/// Finds the first even number, doubles it in place, and returns the original value.
///
/// TODO: 修复借用冲突，使代码编译并通过测试。
/// TODO: Fix the borrow conflict so the code compiles and passes the tests.
pub fn double_first_even(numbers: &mut [i32]) -> Option<i32> {
    // 需要先不可变地查找第一个偶数的位置或值
    let first_even = numbers.iter().copied().find(|&n| n % 2 == 0);

    // TODO: 如果存在偶数，需要可变地修改它。这里不能直接写 &mut numbers[...]
    // TODO: If an even number exists, mutate it. You cannot write `&mut numbers[...]` directly.
    // 因为 first_even 可能借用了 numbers。
    // because `first_even` may borrow from `numbers`.
    // 提示：使用 if let Some(value) = first_even 后再获取可变借用，
    // Hint: obtain the mutable borrow inside `if let Some(value) = first_even`,
    // 或者使用索引 + 重新查找。
    // or use an index plus a second lookup.
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
