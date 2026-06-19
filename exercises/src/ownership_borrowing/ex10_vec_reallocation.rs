//! # 练习 10: Vec 重新分配与引用失效 / Exercise 10: Vec Reallocation and Reference Invalidation
//!
//! **难度 / Difficulty**: Medium  
//! **考点 / Focus**: `Vec` 容量不足时重新分配内存会使旧引用失效
//!   Old references become invalid when a `Vec` reallocates due to growth
//!
//! ## 题目描述 / Problem Description
//!
//! 实现 `push_without_losing`：向 `Vec<i32>` 追加元素，并返回追加前最后一个元素的引用。
//!
//! 注意：如果先获取引用再 `push`，当 `Vec` 重新分配时该引用会失效。
//! 必须先 `push`，再获取引用。
//!
//! ## 提示 / Hints
//!
//! - `Vec::push` 可能导致重新分配，使之前获取的引用悬垂
//! - 调整操作顺序：先修改 Vec，再获取不可变引用

/// 向 Vec 追加元素，并返回追加前最后一个元素的引用
/// Appends an element to the Vec and returns a reference to the previous last element
pub fn push_without_losing(v: &mut Vec<i32>, new_elem: i32) -> Option<&i32> {
    let len = v.len();
    v.push(new_elem);
    if len == 0 {
        None
    } else {
        // push 之后，索引 len - 1 指向的是原来的最后一个元素
        // After push, index len - 1 points to the previous last element
        v.get(len - 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_push_without_losing() {
        let mut v = vec![1, 2, 3];
        let prev = push_without_losing(&mut v, 4);
        assert_eq!(prev, Some(&3));
        assert_eq!(v, vec![1, 2, 3, 4]);
    }

    #[test]
    fn test_push_empty_vec() {
        let mut v = Vec::new();
        let prev = push_without_losing(&mut v, 42);
        assert_eq!(prev, None);
        assert_eq!(v, vec![42]);
    }

    #[test]
    fn test_push_causes_reallocation() {
        // 预先分配小容量，强制触发重新分配
        // Pre-allocate small capacity to force reallocation
        let mut v = Vec::with_capacity(1);
        v.push(1);
        let prev = push_without_losing(&mut v, 2);
        assert_eq!(prev, Some(&1));
        assert!(v.capacity() >= 2);
    }
}
