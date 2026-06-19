//! # 练习 7: Vec 与切片借用 / Exercise 7: Vec and Slice Borrowing
//!
//! **难度 / Difficulty**: Medium  
//! **考点 / Focus**: 不可变借用与可变借用的互斥、切片生命周期
//!   Mutual exclusion of immutable and mutable borrows; slice lifetimes
//!
//! ## 题目描述 / Problem Description
//!
//! 实现 `first_n`，返回 `Vec<i32>` 前 `n` 个元素的切片。
//! 同时实现 `sum_and_push`，先计算切片和，再向原 Vec 追加元素。
//!
//! 注意：`sum_and_push` 必须正确处理「持有切片时不能修改 Vec」的限制。
//!
//! ## 提示 / Hints
//!
//! - `first_n` 返回 `&[i32]` 时不应阻止调用者后续修改 Vec，但调用者不能同时持有切片又修改 Vec
//! - 在 `sum_and_push` 中，先结束对切片的引用，再调用 `push`

/// 返回 Vec 前 n 个元素的切片
/// Returns a slice of the first n elements of a Vec
pub fn first_n(v: &[i32], n: usize) -> &[i32] {
    let end = n.min(v.len());
    &v[..end]
}

/// 先计算前 n 个元素之和，再向 Vec 追加一个元素
/// First sums the first n elements, then appends an element to the Vec
pub fn sum_and_push(v: &mut Vec<i32>, n: usize, extra: i32) -> i32 {
    // 先计算和，此时对 v 的借用在此表达式结束后立即释放
    let sum: i32 = first_n(v, n).iter().sum();
    // 然后才能获取可变借用
    v.push(extra);
    sum
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_first_n() {
        let v = vec![1, 2, 3, 4, 5];
        let s = first_n(&v, 3);
        assert_eq!(s, &[1, 2, 3]);
        // v 仍可用（只读）/ v is still usable for read-only access
        assert_eq!(v.len(), 5);
    }

    #[test]
    fn test_first_n_beyond_length() {
        let v = vec![1, 2];
        let s = first_n(&v, 10);
        assert_eq!(s, &[1, 2]);
    }

    #[test]
    fn test_sum_and_push() {
        let mut v = vec![1, 2, 3, 4, 5];
        let sum = sum_and_push(&mut v, 3, 10);
        assert_eq!(sum, 6); // 1 + 2 + 3
        assert_eq!(v, vec![1, 2, 3, 4, 5, 10]);
    }
}
