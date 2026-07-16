//! # Brown University CRP Ownership Inventory — Program 07
//!
//! **EN**: Vec Reallocation and Slice Invalidation
//! **Summary**: Understand why holding a slice into a Vec while pushing can leave the slice
//! dangling if the Vec reallocates its backing storage.
//! **Key Terms**: Vec 重新分配 (Vec reallocation), 切片 (slice), 悬垂指针 (dangling pointer),
//! 容量 (capacity), 内存重新分配 (reallocation), 可变借用 (mutable borrow).
//! **Related Concepts**:
//! [`concept/01_foundation/05_collections/01_collections.md`](../../../../../concept/01_foundation/05_collections/01_collections.md),
//! [`concept/01_foundation/05_collections/02_collections_advanced.md`](../../../../../concept/01_foundation/05_collections/02_collections_advanced.md),
//! [`concept/01_foundation/01_ownership_borrow_lifetime/06_ownership_inventories_brown_book.md`](../../../../../concept/01_foundation/01_ownership_borrow_lifetime/06_ownership_inventories_brown_book.md).
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
//! ## TODO / Tasks
//!
//! 1. 解释为什么 `slice` 在 `items.push(...)` 之后可能失效。
//!    Explain why a slice into `items` may become invalid after `items.push(...)`.
//! 2. 修复 `sum_before_push`，使其在 push 之前完成所有切片的使用。
//!    Fix `sum_before_push` so all slice usage finishes before the push.
//! 3. 思考：如果必须保留旧切片，有哪些替代方案？
//!    Consider alternatives if you really need to keep the old slice alive.

/// 计算 Vec 当前内容的和，然后追加一个新元素。
/// Sums the current contents of a Vec, then appends a new element.
///
/// TODO: 当前实现的问题在于先获取了切片，然后在切片仍然存活时 push。
/// TODO: The current implementation takes a slice and then pushes while the slice is still alive.
/// 请在 push 之前完成所有对切片的读取。
/// Finish all reads from the slice before pushing.
pub fn sum_before_push(items: &mut Vec<i32>, new_item: i32) -> i32 {
    // 先完成所有读取操作
    let sum: i32 = items.iter().sum();

    // TODO: 下面这行如果放在切片获取之前会怎样？请说明原因。
    // TODO: What would happen if the next line were placed before the slice was taken? Explain.
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
