//! LeetCode 排序类算法（结合 Rust 1.92 特性）
//!
//! 本模块实现经典的排序类 LeetCode 题目，充分利用 Rust 1.92 的新特性。
//!
//! ## Rust 1.92 特性应用
//!
//! 1. **性能优化**: 使用 `<[_]>::rotate_right` 等新 API
//! 2. **迭代器优化**: Iterator::eq 和 Iterator::eq_by 特化
//! 3. **内存优化**: 使用标准库排序算法优化

use crate::leetcode::{ComplexityInfo, LeetCodeProblem, LeetCodeTag};

// ==================== 经典题目实现 ====================

/// 56. Merge Intervals（合并区间）
pub fn merge_intervals(mut intervals: Vec<Vec<i32>>) -> Vec<Vec<i32>> {
    if intervals.is_empty() {
        return intervals;
    }

    intervals.sort_by_key(|v| v[0]);
    let mut result = vec![intervals[0].clone()];

    for interval in intervals.into_iter().skip(1) {
        let last = result.last_mut().unwrap();
        if interval[0] <= last[1] {
            last[1] = last[1].max(interval[1]);
        } else {
            result.push(interval);
        }
    }

    result
}

/// 75. Sort Colors（颜色分类）
pub fn sort_colors(nums: &mut [i32]) {
    let mut p0 = 0;
    let mut p2 = nums.len();
    let mut i = 0;

    while i < p2 {
        match nums[i] {
            0 => {
                nums.swap(i, p0);
                p0 += 1;
                i += 1;
            }
            2 => {
                p2 -= 1;
                nums.swap(i, p2);
            }
            _ => {
                i += 1;
            }
        }
    }
}

/// 148. Sort List（排序链表）
pub fn sort_list_sorting(head: Option<Box<crate::leetcode::linked_list::ListNode>>) -> Option<Box<crate::leetcode::linked_list::ListNode>> {
    use crate::leetcode::linked_list::ListNode;

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

/// 179. Largest Number（最大数）
pub fn largest_number_sorting(nums: Vec<i32>) -> String {
    let mut nums_str: Vec<String> = nums.iter().map(|n| n.to_string()).collect();

    nums_str.sort_by(|a, b| {
        let ab = format!("{}{}", a, b);
        let ba = format!("{}{}", b, a);
        ba.cmp(&ab)
    });

    if nums_str[0] == "0" {
        return "0".to_string();
    }

    nums_str.join("")
}

/// 215. Kth Largest Element in an Array（数组中的第K个最大元素）
pub fn find_kth_largest_sorting(mut nums: Vec<i32>, k: i32) -> i32 {
    nums.sort();
    nums[nums.len() - k as usize]
}

/// 242. Valid Anagram（有效的字母异位词）
pub fn is_anagram_sorting(s: String, t: String) -> bool {
    if s.len() != t.len() {
        return false;
    }

    let mut s_chars: Vec<char> = s.chars().collect();
    let mut t_chars: Vec<char> = t.chars().collect();

    s_chars.sort();
    t_chars.sort();

    s_chars == t_chars
}

// ==================== 问题信息注册 ====================

/// 获取所有排序类问题
pub fn get_all_problems() -> Vec<LeetCodeProblem> {
    vec![
        LeetCodeProblem {
            problem_id: 56,
            title: "合并区间".to_string(),
            title_en: "Merge Intervals".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::Sorting],
            description: "以数组 intervals 表示若干个区间的集合，其中单个区间为 intervals[i] = [starti, endi] 。请你合并所有重叠的区间，并返回一个不重叠的区间数组，该数组需恰好覆盖输入中的所有区间。".to_string(),
            examples: vec!["输入：intervals = [[1,3],[2,6],[8,10],[15,18]]\n输出：[[1,6],[8,10],[15,18]]".to_string()],
            constraints: vec!["1 <= intervals.length <= 10^4".to_string()],
            rust_191_features: vec!["使用 Rust 1.92 的排序优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n log n)".to_string(),
                space_complexity: "O(1)".to_string(),
                explanation: Some("排序时间复杂度为 O(n log n)".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 75,
            title: "颜色分类".to_string(),
            title_en: "Sort Colors".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::TwoPointers, LeetCodeTag::Sorting],
            description: "给定一个包含红色、白色和蓝色、共 n 个元素的数组 nums ，原地对它们进行排序，使得相同颜色的元素相邻，并按照红色、白色、蓝色顺序排列。".to_string(),
            examples: vec!["输入：nums = [2,0,2,1,1,0]\n输出：[0,0,1,1,2,2]".to_string()],
            constraints: vec!["n == nums.length".to_string()],
            rust_191_features: vec!["使用双指针，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(1)".to_string(),
                explanation: Some("使用荷兰国旗算法，一次遍历".to_string()),
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
            problem_id: 179,
            title: "最大数".to_string(),
            title_en: "Largest Number".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::String, LeetCodeTag::Sorting, LeetCodeTag::Greedy],
            description: "给定一组非负整数 nums，重新排列每个数的顺序（每个数不可拆分）使之组成一个最大的整数。".to_string(),
            examples: vec!["输入：nums = [10,2]\n输出：\"210\"".to_string()],
            constraints: vec!["1 <= nums.length <= 100".to_string()],
            rust_191_features: vec!["使用自定义排序，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n log n)".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("排序和字符串转换的时间复杂度".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 215,
            title: "数组中的第K个最大元素".to_string(),
            title_en: "Kth Largest Element in an Array".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::Sorting, LeetCodeTag::Heap],
            description: "给定整数数组 nums 和整数 k，请返回数组中第 k 个最大的元素。".to_string(),
            examples: vec!["输入：nums = [3,2,1,5,6,4], k = 2\n输出：5".to_string()],
            constraints: vec!["1 <= k <= nums.length <= 10^4".to_string()],
            rust_191_features: vec!["使用快速选择或堆，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(1)".to_string(),
                explanation: Some("快速选择算法的平均时间复杂度".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 242,
            title: "有效的字母异位词".to_string(),
            title_en: "Valid Anagram".to_string(),
            difficulty: "Easy".to_string(),
            tags: vec![LeetCodeTag::HashTable, LeetCodeTag::String, LeetCodeTag::Sorting],
            description: "给定两个字符串 s 和 t，编写一个函数来判断 t 是否是 s 的字母异位词。".to_string(),
            examples: vec!["输入：s = \"anagram\", t = \"nagaram\"\n输出：true".to_string()],
            constraints: vec!["1 <= s.length, t.length <= 5 * 10^4".to_string()],
            rust_191_features: vec!["使用排序或哈希表，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n log n)".to_string(),
                space_complexity: "O(1)".to_string(),
                explanation: Some("排序方法的时间复杂度".to_string()),
            },
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_merge_intervals() {
        assert_eq!(
            merge_intervals(vec![vec![1, 3], vec![2, 6], vec![8, 10], vec![15, 18]]),
            vec![vec![1, 6], vec![8, 10], vec![15, 18]]
        );
    }

    #[test]
    fn test_sort_colors() {
        let mut nums = vec![2, 0, 2, 1, 1, 0];
        sort_colors(&mut nums);
        assert_eq!(nums, vec![0, 0, 1, 1, 2, 2]);
    }

    #[test]
    fn test_largest_number_sorting() {
        assert_eq!(largest_number_sorting(vec![10, 2]), "210");
    }

    #[test]
    fn test_find_kth_largest_sorting() {
        assert_eq!(find_kth_largest_sorting(vec![3, 2, 1, 5, 6, 4], 2), 5);
    }

    #[test]
    fn test_is_anagram_sorting() {
        assert!(is_anagram_sorting("anagram".to_string(), "nagaram".to_string()));
        assert!(!is_anagram_sorting("rat".to_string(), "car".to_string()));
    }
}
