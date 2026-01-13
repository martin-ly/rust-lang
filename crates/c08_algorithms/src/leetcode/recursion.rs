//! LeetCode 递归类算法（结合 Rust 1.92 特性）
//!
//! 本模块实现经典的递归类 LeetCode 题目，充分利用 Rust 1.92 的新特性。
//!
//! ## Rust 1.92 特性应用
//!
//! 1. **性能优化**: 尾递归优化
//! 2. **内存优化**: 递归栈优化

use crate::leetcode::{ComplexityInfo, LeetCodeProblem, LeetCodeTag};

// ==================== 数据结构定义 ====================

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct ListNode {
    pub val: i32,
    pub next: Option<Box<ListNode>>,
}

impl ListNode {
    pub fn new(val: i32) -> Self {
        ListNode { next: None, val }
    }
}

// ==================== 经典题目实现 ====================

/// 21. Merge Two Sorted Lists（合并两个有序链表）- 递归版本
pub fn merge_two_lists_recursive(
    list1: Option<Box<ListNode>>,
    list2: Option<Box<ListNode>>,
) -> Option<Box<ListNode>> {
    match (list1, list2) {
        (None, None) => None,
        (Some(l), None) | (None, Some(l)) => Some(l),
        (Some(mut l1), Some(mut l2)) => {
            if l1.val <= l2.val {
                l1.next = merge_two_lists_recursive(l1.next.take(), Some(l2));
                Some(l1)
            } else {
                l2.next = merge_two_lists_recursive(Some(l1), l2.next.take());
                Some(l2)
            }
        }
    }
}

/// 24. Swap Nodes in Pairs（两两交换链表中的节点）
pub fn swap_pairs(head: Option<Box<ListNode>>) -> Option<Box<ListNode>> {
    if head.is_none() || head.as_ref().unwrap().next.is_none() {
        return head;
    }

    let mut head = head;
    let mut next = head.as_mut().unwrap().next.take();
    let next_next = next.as_mut().unwrap().next.take();

    head.as_mut().unwrap().next = swap_pairs(next_next);
    next.as_mut().unwrap().next = head;

    next
}

/// 50. Pow(x, n) - 递归版本
pub fn my_pow_recursive(x: f64, n: i32) -> f64 {
    if n == 0 {
        return 1.0;
    }

    if n < 0 {
        return 1.0 / my_pow_recursive(x, -n);
    }

    if n % 2 == 0 {
        let half = my_pow_recursive(x, n / 2);
        half * half
    } else {
        x * my_pow_recursive(x, n - 1)
    }
}

/// 206. Reverse Linked List（反转链表）- 递归版本
pub fn reverse_list_recursive(head: Option<Box<ListNode>>) -> Option<Box<ListNode>> {
    fn reverse(
        head: Option<Box<ListNode>>,
        prev: Option<Box<ListNode>>,
    ) -> Option<Box<ListNode>> {
        match head {
            None => prev,
            Some(mut node) => {
                let next = node.next.take();
                node.next = prev;
                reverse(next, Some(node))
            }
        }
    }

    reverse(head, None)
}

/// 509. Fibonacci Number（斐波那契数）- 递归版本
pub fn fib_recursive(n: i32) -> i32 {
    if n < 2 {
        return n;
    }
    fib_recursive(n - 1) + fib_recursive(n - 2)
}

// ==================== 问题信息注册 ====================

/// 获取所有递归类问题
pub fn get_all_problems() -> Vec<LeetCodeProblem> {
    vec![
        LeetCodeProblem {
            problem_id: 21,
            title: "合并两个有序链表".to_string(),
            title_en: "Merge Two Sorted Lists".to_string(),
            difficulty: "Easy".to_string(),
            tags: vec![LeetCodeTag::LinkedList, LeetCodeTag::Recursion],
            description: "将两个升序链表合并为一个新的 升序 链表并返回。新链表是通过拼接给定的两个链表的所有节点组成的。".to_string(),
            examples: vec!["输入：l1 = [1,2,4], l2 = [1,3,4]\n输出：[1,1,2,3,4,4]".to_string()],
            constraints: vec!["两个链表的节点数目范围是 [0, 50]".to_string()],
            rust_191_features: vec!["使用递归，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(m+n)".to_string(),
                space_complexity: "O(m+n)".to_string(),
                explanation: Some("递归栈深度为 m+n".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 24,
            title: "两两交换链表中的节点".to_string(),
            title_en: "Swap Nodes in Pairs".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::LinkedList, LeetCodeTag::Recursion],
            description: "给你一个链表，两两交换其中相邻的节点，并返回交换后链表的头节点。你必须在不修改节点内部的值的情况下完成本题（即，只能进行节点交换）。".to_string(),
            examples: vec!["输入：head = [1,2,3,4]\n输出：[2,1,4,3]".to_string()],
            constraints: vec!["链表中节点的数目在范围 [0, 100] 内".to_string()],
            rust_191_features: vec!["使用递归，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("递归栈深度为 n/2".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 50,
            title: "Pow(x, n)".to_string(),
            title_en: "Pow(x, n)".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::Math, LeetCodeTag::Recursion],
            description: "实现 pow(x, n) ，即计算 x 的 n 次幂函数（即，x^n）。".to_string(),
            examples: vec!["输入：x = 2.00000, n = 10\n输出：1024.00000".to_string()],
            constraints: vec!["-100.0 < x < 100.0".to_string()],
            rust_191_features: vec!["使用快速幂递归，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(log n)".to_string(),
                space_complexity: "O(log n)".to_string(),
                explanation: Some("递归深度为 log(n)".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 206,
            title: "反转链表".to_string(),
            title_en: "Reverse Linked List".to_string(),
            difficulty: "Easy".to_string(),
            tags: vec![LeetCodeTag::LinkedList, LeetCodeTag::Recursion],
            description: "给你单链表的头节点 head ，请你反转链表，并返回反转后的链表。".to_string(),
            examples: vec!["输入：head = [1,2,3,4,5]\n输出：[5,4,3,2,1]".to_string()],
            constraints: vec!["链表中节点的数目范围是 [0, 5000]".to_string()],
            rust_191_features: vec!["使用递归，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("递归栈深度为 n".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 509,
            title: "斐波那契数".to_string(),
            title_en: "Fibonacci Number".to_string(),
            difficulty: "Easy".to_string(),
            tags: vec![LeetCodeTag::Math, LeetCodeTag::DynamicProgramming, LeetCodeTag::Recursion],
            description: "斐波那契数 （通常用 F(n) 表示）形成的序列称为 斐波那契数列 。该数列由 0 和 1 开始，后面的每一项数字都是前面两项数字的和。".to_string(),
            examples: vec!["输入：n = 2\n输出：1".to_string()],
            constraints: vec!["0 <= n <= 30".to_string()],
            rust_191_features: vec!["使用递归或动态规划，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(2^n)".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("朴素递归的时间复杂度".to_string()),
            },
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    fn list_from_vec(v: Vec<i32>) -> Option<Box<ListNode>> {
        let mut head = None;
        for &val in v.iter().rev() {
            let mut node = Box::new(ListNode::new(val));
            node.next = head;
            head = Some(node);
        }
        head
    }

    fn vec_from_list(head: Option<Box<ListNode>>) -> Vec<i32> {
        let mut result = Vec::new();
        let mut current = head;
        while let Some(node) = current {
            result.push(node.val);
            current = node.next;
        }
        result
    }

    #[test]
    fn test_merge_two_lists_recursive() {
        let l1 = list_from_vec(vec![1, 2, 4]);
        let l2 = list_from_vec(vec![1, 3, 4]);
        let result = merge_two_lists_recursive(l1, l2);
        assert_eq!(vec_from_list(result), vec![1, 1, 2, 3, 4, 4]);
    }

    #[test]
    fn test_swap_pairs() {
        let head = list_from_vec(vec![1, 2, 3, 4]);
        let result = swap_pairs(head);
        assert_eq!(vec_from_list(result), vec![2, 1, 4, 3]);
    }

    #[test]
    fn test_my_pow_recursive() {
        assert!((my_pow_recursive(2.0, 10) - 1024.0).abs() < 1e-5);
    }

    #[test]
    fn test_reverse_list_recursive() {
        let head = list_from_vec(vec![1, 2, 3, 4, 5]);
        let result = reverse_list_recursive(head);
        assert_eq!(vec_from_list(result), vec![5, 4, 3, 2, 1]);
    }

    #[test]
    fn test_fib_recursive() {
        assert_eq!(fib_recursive(2), 1);
        assert_eq!(fib_recursive(4), 3);
    }
}
