//! # Brown University CRP Ownership Inventory — Program 07
//!
//! **来源 / Source**: Brown University CRP Ownership Inventory 样题
//! **主题 / Topic**: Vec 重新分配与切片失效 / Vec Reallocation and Slice Invalidation
//!
//! ## 学习目标 / Learning Goal
//!
//! 理解为什么持有 Vec 切片的同时 push 元素是危险的：Vec 可能重新分配堆内存，导致原有切片悬垂。
//! Understand why holding a slice into a Vec while pushing is dangerous:
//! the Vec may reallocate, leaving the original slice dangling.
//!
//! ## TODO
//!
//! 1. 解释为什么 `slice` 在 `items.push(...)` 之后可能失效。
//! 2. 修复 `sum_before_push`，使其在 push 之前完成所有切片的使用。
//! 3. 思考：如果必须保留旧切片，有哪些替代方案？

/// 计算 Vec 当前内容的和，然后追加一个新元素。
/// Sums the current contents of a Vec, then appends a new element.
///
/// TODO: 当前实现的问题在于先获取了切片，然后在切片仍然存活时 push。
/// 请在 push 之前完成所有对切片的读取。
pub fn sum_before_push(items: &mut Vec<i32>, new_item: i32) -> i32 {
    // 先完成所有读取操作
    let sum: i32 = items.iter().sum();

    // TODO: 下面这行如果放在切片获取之前会怎样？请说明原因。
    items.push(new_item);

    sum
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sum_before_push() {
        let mut v = vec![1, 2, 3];
        let sum = sum_before_push(&mut v, 4);
        assert_eq!(sum, 6);
        assert_eq!(v, vec![1, 2, 3, 4]);
    }

    #[test]
    fn test_empty_vec() {
        let mut v = Vec::new();
        let sum = sum_before_push(&mut v, 10);
        assert_eq!(sum, 0);
        assert_eq!(v, vec![10]);
    }
}
