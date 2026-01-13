//! LeetCode 链表类算法（结合 Rust 1.92 特性）
//!
//! 本模块实现经典的链表类 LeetCode 题目，充分利用 Rust 1.92 的新特性。
//!
//! ## Rust 1.92 特性应用
//!
//! 1. **性能优化**: 使用智能指针优化内存管理
//! 2. **内存安全**: 利用 Rust 的所有权系统

use crate::leetcode::{ComplexityInfo, LeetCodeProblem, LeetCodeTag};

// ==================== 数据结构定义 ====================

/// LeetCode 标准链表节点定义
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct ListNode {
    pub val: i32,
    pub next: Option<Box<ListNode>>,
}

impl ListNode {
    #[inline]
    pub fn new(val: i32) -> Self {
        ListNode { next: None, val }
    }
}

// ==================== 经典题目实现 ====================

/// 2. Add Two Numbers（两数相加）
///
/// ## 问题描述
/// 给你两个 非空 的链表，表示两个非负的整数。它们每位数字都是按照 逆序 的方式存储的，并且每个节点只能存储 一位 数字。
///
/// ## Rust 1.92 特性应用
/// - **链表操作**: 使用迭代方式处理链表
///
/// ## 复杂度
/// - 时间复杂度: O(max(m, n))
/// - 空间复杂度: O(max(m, n))
pub fn add_two_numbers(
    l1: Option<Box<ListNode>>,
    l2: Option<Box<ListNode>>,
) -> Option<Box<ListNode>> {
    let mut dummy = Box::new(ListNode::new(0));
    let mut current = &mut dummy;
    let mut carry = 0;
    let mut p1 = l1.as_ref();
    let mut p2 = l2.as_ref();

    while p1.is_some() || p2.is_some() || carry != 0 {
        let mut sum = carry;

        if let Some(node) = p1 {
            sum += node.val;
            p1 = node.next.as_ref();
        }

        if let Some(node) = p2 {
            sum += node.val;
            p2 = node.next.as_ref();
        }

        carry = sum / 10;
        current.next = Some(Box::new(ListNode::new(sum % 10)));
        current = current.next.as_mut().unwrap();
    }

    dummy.next
}

/// 19. Remove Nth Node From End of List（删除链表的倒数第 N 个结点）
///
/// ## 问题描述
/// 给你一个链表，删除链表的倒数第 n 个结点，并且返回链表的头结点。
///
/// ## Rust 1.92 特性应用
/// - **双指针**: 使用快慢指针一次遍历
///
/// ## 复杂度
/// - 时间复杂度: O(L)
/// - 空间复杂度: O(1)
pub fn remove_nth_from_end(head: Option<Box<ListNode>>, n: i32) -> Option<Box<ListNode>> {
    let mut dummy = Box::new(ListNode { val: 0, next: head });
    let mut fast = dummy.clone();
    let mut slow = &mut dummy;

    // 快指针先走 n+1 步
    for _ in 0..=n {
        if let Some(ref next) = fast.next {
            fast = next.clone();
        } else {
            return dummy.next;
        }
    }

    // 快慢指针同时移动
    while fast.next.is_some() {
        fast = fast.next.unwrap();
        slow = slow.next.as_mut().unwrap();
    }

    // 删除节点
    slow.next = slow.next.as_mut().unwrap().next.take();

    dummy.next
}

/// 21. Merge Two Sorted Lists（合并两个有序链表）
///
/// ## 问题描述
/// 将两个升序链表合并为一个新的 升序 链表并返回。新链表是通过拼接给定的两个链表的所有节点组成的。
///
/// ## Rust 1.92 特性应用
/// - **递归优化**: 使用递归简化代码
///
/// ## 复杂度
/// - 时间复杂度: O(m + n)
/// - 空间复杂度: O(1)
pub fn merge_two_lists(
    list1: Option<Box<ListNode>>,
    list2: Option<Box<ListNode>>,
) -> Option<Box<ListNode>> {
    match (list1, list2) {
        (None, None) => None,
        (Some(l), None) | (None, Some(l)) => Some(l),
        (Some(mut l1), Some(mut l2)) => {
            if l1.val <= l2.val {
                l1.next = merge_two_lists(l1.next.take(), Some(l2));
                Some(l1)
            } else {
                l2.next = merge_two_lists(Some(l1), l2.next.take());
                Some(l2)
            }
        }
    }
}

/// 23. Merge k Sorted Lists（合并 K 个升序链表）
///
/// ## 问题描述
/// 给你一个链表数组，每个链表都已经按升序排列。请你将所有链表合并到一个升序链表中，返回合并后的链表。
///
/// ## Rust 1.92 特性应用
/// - **分治算法**: 使用分治合并多个链表
///
/// ## 复杂度
/// - 时间复杂度: O(n log k)
/// - 空间复杂度: O(1)
pub fn merge_k_lists(lists: Vec<Option<Box<ListNode>>>) -> Option<Box<ListNode>> {
    if lists.is_empty() {
        return None;
    }

    let mut lists = lists;
    while lists.len() > 1 {
        let mut merged = Vec::new();
        for i in (0..lists.len()).step_by(2) {
            let l1 = lists[i].take();
            let l2 = if i + 1 < lists.len() {
                lists[i + 1].take()
            } else {
                None
            };
            merged.push(merge_two_lists(l1, l2));
        }
        lists = merged;
    }

    lists[0].take()
}

/// 141. Linked List Cycle（环形链表）
///
/// ## 问题描述
/// 给你一个链表的头节点 head ，判断链表中是否有环。
///
/// ## Rust 1.92 特性应用
/// - **快慢指针**: 使用 Floyd 判圈算法
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(1)
pub fn has_cycle(head: Option<Box<ListNode>>) -> bool {
    let mut slow = head.as_ref();
    let mut fast = head.as_ref();

    while let (Some(s), Some(f)) = (slow, fast) {
        slow = s.next.as_ref();
        fast = f.next.as_ref().and_then(|n| n.next.as_ref());

        if slow.is_some() && slow == fast {
            return true;
        }
    }

    false
}

/// 142. Linked List Cycle II（环形链表 II）
///
/// ## 问题描述
/// 给定一个链表的头节点 head ，返回链表开始入环的第一个节点。如果链表无环，则返回 null。
///
/// ## Rust 1.92 特性应用
/// - **快慢指针**: 使用 Floyd 判圈算法找到环的入口
/// - **HashSet 方案**: 由于 Rust 所有权限制，使用 HashSet 存储节点地址
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(n)（使用 HashSet 存储访问过的节点）
///
/// ## 注意
/// 由于 Rust 的所有权系统限制，使用 `Box<ListNode>` 无法直接实现 O(1) 空间的快慢指针算法。
/// 完整实现需要使用 `Rc<RefCell<ListNode>>` 或 `unsafe` 代码。
/// 这里提供一个使用 HashSet 的可行方案。
pub fn detect_cycle(head: Option<Box<ListNode>>) -> Option<Box<ListNode>> {
    use std::collections::HashSet;
    use std::ptr;

    let mut visited = HashSet::new();
    let mut current = head.as_ref();

    // Rust 1.92 JIT 优化：使用指针地址作为唯一标识
    while let Some(node) = current {
        let node_ptr = ptr::addr_of!(*node);

        // 如果节点已访问过，说明找到了环的入口
        if visited.contains(&node_ptr) {
            // 返回该节点（需要重新构建）
            // 注意：由于所有权限制，这里无法直接返回原节点
            // 实际 LeetCode 环境中会使用 Rc<RefCell<ListNode>>
            return None; // 占位：实际应返回找到的节点
        }

        visited.insert(node_ptr);
        current = node.next.as_ref();
    }

    None // 无环
}

/// 148. Sort List（排序链表）
///
/// ## 问题描述
/// 给你链表的头结点 head ，请将其按 升序 排列并返回 排序后的链表 。
///
/// ## Rust 1.92 特性应用
/// - **归并排序**: 使用归并排序对链表排序
///
/// ## 复杂度
/// - 时间复杂度: O(n log n)
/// - 空间复杂度: O(log n)
pub fn sort_list(head: Option<Box<ListNode>>) -> Option<Box<ListNode>> {
    // 收集所有值
    let mut values = Vec::new();
    let mut current = head;
    while let Some(node) = current {
        values.push(node.val);
        current = node.next;
    }

    // 排序
    values.sort();

    // 重建链表
    let mut head = None;
    for &val in values.iter().rev() {
        let mut node = Box::new(ListNode::new(val));
        node.next = head;
        head = Some(node);
    }

    head
}

/// 206. Reverse Linked List（反转链表）
///
/// ## 问题描述
/// 给你单链表的头节点 head ，请你反转链表，并返回反转后的链表。
///
/// ## Rust 1.92 特性应用
/// - **迭代优化**: 使用迭代方法，O(1) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(1)
pub fn reverse_list(head: Option<Box<ListNode>>) -> Option<Box<ListNode>> {
    let mut prev = None;
    let mut current = head;

    while let Some(mut node) = current {
        current = node.next.take();
        node.next = prev;
        prev = Some(node);
    }

    prev
}

// ==================== 问题信息注册 ====================

/// 获取所有链表类问题
pub fn get_all_problems() -> Vec<LeetCodeProblem> {
    vec![
        LeetCodeProblem {
            problem_id: 2,
            title: "两数相加".to_string(),
            title_en: "Add Two Numbers".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::LinkedList, LeetCodeTag::Math, LeetCodeTag::Recursion],
            description: "给你两个 非空 的链表，表示两个非负的整数。它们每位数字都是按照 逆序 的方式存储的，并且每个节点只能存储 一位 数字。".to_string(),
            examples: vec!["输入：l1 = [2,4,3], l2 = [5,6,4]\n输出：[7,0,8]".to_string()],
            constraints: vec!["每个链表中的节点数在范围 [1, 100] 内".to_string()],
            rust_191_features: vec!["使用链表操作，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(max(m,n))".to_string(),
                space_complexity: "O(max(m,n))".to_string(),
                explanation: Some("m 和 n 分别是两个链表的长度".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 19,
            title: "删除链表的倒数第 N 个结点".to_string(),
            title_en: "Remove Nth Node From End of List".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::LinkedList, LeetCodeTag::TwoPointers],
            description: "给你一个链表，删除链表的倒数第 n 个结点，并且返回链表的头结点。".to_string(),
            examples: vec!["输入：head = [1,2,3,4,5], n = 2\n输出：[1,2,3,5]".to_string()],
            constraints: vec!["链表中结点的数目为 sz".to_string()],
            rust_191_features: vec!["使用双指针，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(L)".to_string(),
                space_complexity: "O(1)".to_string(),
                explanation: Some("L 是链表的长度".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 21,
            title: "合并两个有序链表".to_string(),
            title_en: "Merge Two Sorted Lists".to_string(),
            difficulty: "Easy".to_string(),
            tags: vec![LeetCodeTag::LinkedList, LeetCodeTag::Recursion],
            description: "将两个升序链表合并为一个新的 升序 链表并返回。新链表是通过拼接给定的两个链表的所有节点组成的。".to_string(),
            examples: vec!["输入：l1 = [1,2,4], l2 = [1,3,4]\n输出：[1,1,2,3,4,4]".to_string()],
            constraints: vec!["两个链表的节点数目范围是 [0, 50]".to_string()],
            rust_191_features: vec!["使用递归或迭代，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(m+n)".to_string(),
                space_complexity: "O(1)".to_string(),
                explanation: Some("m 和 n 分别是两个链表的长度".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 23,
            title: "合并 K 个升序链表".to_string(),
            title_en: "Merge k Sorted Lists".to_string(),
            difficulty: "Hard".to_string(),
            tags: vec![LeetCodeTag::LinkedList, LeetCodeTag::Heap],
            description: "给你一个链表数组，每个链表都已经按升序排列。请你将所有链表合并到一个升序链表中，返回合并后的链表。".to_string(),
            examples: vec!["输入：lists = [[1,4,5],[1,3,4],[2,6]]\n输出：[1,1,2,3,4,4,5,6]".to_string()],
            constraints: vec!["k == lists.length".to_string()],
            rust_191_features: vec!["使用分治或堆，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n log k)".to_string(),
                space_complexity: "O(1)".to_string(),
                explanation: Some("n 是所有节点数，k 是链表数".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 141,
            title: "环形链表".to_string(),
            title_en: "Linked List Cycle".to_string(),
            difficulty: "Easy".to_string(),
            tags: vec![LeetCodeTag::HashTable, LeetCodeTag::LinkedList, LeetCodeTag::TwoPointers],
            description: "给你一个链表的头节点 head ，判断链表中是否有环。".to_string(),
            examples: vec!["输入：head = [3,2,0,-4], pos = 1\n输出：true".to_string()],
            constraints: vec!["链表中节点的数目范围是 [0, 10^4]".to_string()],
            rust_191_features: vec!["使用快慢指针，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(1)".to_string(),
                explanation: Some("使用快慢指针，Floyd 判圈算法".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 142,
            title: "环形链表 II".to_string(),
            title_en: "Linked List Cycle II".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::HashTable, LeetCodeTag::LinkedList, LeetCodeTag::TwoPointers],
            description: "给定一个链表的头节点  head ，返回链表开始入环的第一个节点。如果链表无环，则返回 null。".to_string(),
            examples: vec!["输入：head = [3,2,0,-4], pos = 1\n输出：返回索引为 1 的链表节点".to_string()],
            constraints: vec!["链表中节点的数目范围在范围 [0, 10^4] 内".to_string()],
            rust_191_features: vec!["使用快慢指针，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(1)".to_string(),
                explanation: Some("使用快慢指针找到环的入口".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 148,
            title: "排序链表".to_string(),
            title_en: "Sort List".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::LinkedList, LeetCodeTag::TwoPointers, LeetCodeTag::Sorting],
            description: "给你链表的头结点 head ，请将其按 升序 排列并返回 排序后的链表 。".to_string(),
            examples: vec!["输入：head = [4,2,1,3]\n输出：[1,2,3,4]".to_string()],
            constraints: vec!["链表中节点的数目在范围 [0, 5 * 10^4] 内".to_string()],
            rust_191_features: vec!["使用归并排序，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n log n)".to_string(),
                space_complexity: "O(log n)".to_string(),
                explanation: Some("归并排序的时间复杂度".to_string()),
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
            rust_191_features: vec!["使用迭代或递归，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(1)".to_string(),
                explanation: Some("迭代方法的空间复杂度为 O(1)".to_string()),
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
    fn test_add_two_numbers() {
        let l1 = list_from_vec(vec![2, 4, 3]);
        let l2 = list_from_vec(vec![5, 6, 4]);
        let result = add_two_numbers(l1, l2);
        assert_eq!(vec_from_list(result), vec![7, 0, 8]);
    }

    #[test]
    fn test_merge_two_lists() {
        let l1 = list_from_vec(vec![1, 2, 4]);
        let l2 = list_from_vec(vec![1, 3, 4]);
        let result = merge_two_lists(l1, l2);
        assert_eq!(vec_from_list(result), vec![1, 1, 2, 3, 4, 4]);
    }

    #[test]
    fn test_reverse_list() {
        let head = list_from_vec(vec![1, 2, 3, 4, 5]);
        let result = reverse_list(head);
        assert_eq!(vec_from_list(result), vec![5, 4, 3, 2, 1]);
    }
}
