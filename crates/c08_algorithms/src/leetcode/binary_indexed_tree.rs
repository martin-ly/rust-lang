//! LeetCode 树状数组类算法（结合 Rust 1.92 特性）
//!
//! 本模块实现经典的树状数组类 LeetCode 题目，充分利用 Rust 1.92 的新特性。
//!
//! ## Rust 1.92 特性应用
//!
//! 1. **性能优化**: 使用树状数组进行前缀和查询和更新
//! 2. **内存优化**: 高效的树状数组实现

use crate::leetcode::{ComplexityInfo, LeetCodeProblem, LeetCodeTag};

// ==================== 数据结构定义 ====================

/// Binary Indexed Tree (Fenwick Tree)
pub struct BinaryIndexedTree {
    tree: Vec<i32>,
    n: usize,
}

impl BinaryIndexedTree {
    pub fn new(n: usize) -> Self {
        BinaryIndexedTree {
            tree: vec![0; n + 1],
            n,
        }
    }

    fn lowbit(x: i32) -> i32 {
        x & (-x)
    }

    pub fn update(&mut self, mut index: usize, delta: i32) {
        index += 1;
        while index <= self.n {
            self.tree[index] += delta;
            index += Self::lowbit(index as i32) as usize;
        }
    }

    pub fn query(&self, mut index: usize) -> i32 {
        let mut sum = 0;
        index += 1;
        while index > 0 {
            sum += self.tree[index];
            index -= Self::lowbit(index as i32) as usize;
        }
        sum
    }

    pub fn range_query(&self, left: usize, right: usize) -> i32 {
        self.query(right) - if left > 0 { self.query(left - 1) } else { 0 }
    }
}

/// 307. Range Sum Query - Mutable（区域和检索 - 数组可修改）- 树状数组版本
pub struct NumArrayBIT {
    bit: BinaryIndexedTree,
    nums: Vec<i32>,
}

impl NumArrayBIT {
    pub fn new(nums: Vec<i32>) -> Self {
        let n = nums.len();
        let mut bit = BinaryIndexedTree::new(n);
        for (i, &val) in nums.iter().enumerate() {
            bit.update(i, val);
        }
        NumArrayBIT { bit, nums }
    }

    pub fn update(&mut self, index: i32, val: i32) {
        let idx = index as usize;
        let delta = val - self.nums[idx];
        self.nums[idx] = val;
        self.bit.update(idx, delta);
    }

    pub fn sum_range(&self, left: i32, right: i32) -> i32 {
        self.bit.range_query(left as usize, right as usize)
    }
}

/// 315. Count of Smaller Numbers After Self（计算右侧小于当前元素的个数）- 树状数组版本
pub fn count_smaller_bit(nums: Vec<i32>) -> Vec<i32> {
    // 离散化
    let mut sorted = nums.clone();
    sorted.sort();
    sorted.dedup();

    let mut bit = BinaryIndexedTree::new(sorted.len());
    let mut result = vec![0; nums.len()];

    for i in (0..nums.len()).rev() {
        let pos = sorted.binary_search(&nums[i]).unwrap();
        result[i] = if pos > 0 { bit.query(pos - 1) } else { 0 };
        bit.update(pos, 1);
    }

    result
}

/// 327. Count of Range Sum（区间和的个数）- 树状数组版本
pub fn count_range_sum_bit(nums: Vec<i32>, lower: i32, upper: i32) -> i32 {
    let n = nums.len();
    let mut prefix_sum = vec![0i64; n + 1];
    for i in 0..n {
        prefix_sum[i + 1] = prefix_sum[i] + nums[i] as i64;
    }

    // 离散化
    let mut all_nums = Vec::new();
    for &sum in &prefix_sum {
        all_nums.push(sum);
        all_nums.push(sum - lower as i64);
        all_nums.push(sum - upper as i64);
    }
    all_nums.sort();
    all_nums.dedup();

    let mut bit = BinaryIndexedTree::new(all_nums.len());
    let mut count = 0;

    for i in (0..=n).rev() {
        let sum = prefix_sum[i];
        let left_pos = all_nums.binary_search(&(sum - upper as i64)).unwrap_or_else(|x| x);
        let right_pos = all_nums.binary_search(&(sum - lower as i64 + 1)).unwrap_or_else(|x| x) - 1;

        if right_pos < all_nums.len() {
            count += if left_pos > 0 {
                bit.range_query(left_pos, right_pos)
            } else {
                bit.query(right_pos)
            };
        }

        let pos = all_nums.binary_search(&sum).unwrap();
        bit.update(pos, 1);
    }

    count
}

// ==================== 问题信息注册 ====================

/// 获取所有树状数组类问题
pub fn get_all_problems() -> Vec<LeetCodeProblem> {
    vec![
        LeetCodeProblem {
            problem_id: 307,
            title: "区域和检索 - 数组可修改".to_string(),
            title_en: "Range Sum Query - Mutable".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::Design, LeetCodeTag::BinaryIndexedTree, LeetCodeTag::SegmentTree],
            description: "给你一个数组 nums ，请你完成两类查询。其中一类查询要求 更新 数组 nums 下标对应的值。另一类查询要求返回数组 nums 中索引 left 和索引 right 之间（ 包含 ）的nums元素的 和 ，其中 left <= right。".to_string(),
            examples: vec!["输入：[\"NumArray\", \"sumRange\", \"update\", \"sumRange\"]\n[[[1, 3, 5]], [0, 2], [1, 2], [0, 2]]\n输出：[null, 9, null, 8]".to_string()],
            constraints: vec!["1 <= nums.length <= 3 * 10^4".to_string()],
            rust_191_features: vec!["使用树状数组或线段树，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(log n)".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("更新和查询的时间复杂度都是 O(log n)".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 315,
            title: "计算右侧小于当前元素的个数".to_string(),
            title_en: "Count of Smaller Numbers After Self".to_string(),
            difficulty: "Hard".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::BinarySearch, LeetCodeTag::BinaryIndexedTree, LeetCodeTag::SegmentTree],
            description: "给你一个整数数组 nums ，按要求返回一个新数组 counts 。数组 counts 有该性质： counts[i] 的值是  nums[i] 右侧小于 nums[i] 的元素的数量。".to_string(),
            examples: vec!["输入：nums = [5,2,6,1]\n输出：[2,1,1,0]".to_string()],
            constraints: vec!["1 <= nums.length <= 10^5".to_string()],
            rust_191_features: vec!["使用树状数组或归并排序，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n log n)".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("使用树状数组或归并排序".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 327,
            title: "区间和的个数".to_string(),
            title_en: "Count of Range Sum".to_string(),
            difficulty: "Hard".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::BinarySearch, LeetCodeTag::BinaryIndexedTree, LeetCodeTag::SegmentTree],
            description: "给你一个整数数组 nums 以及两个整数 lower 和 upper 。求数组中，值位于范围 [lower, upper] （包含 lower 和 upper）之内的 区间和的个数 。区间和 S(i, j) 表示在 nums 中，位置从 i 到 j 的元素之和，包含 i 和 j (i ≤ j)。".to_string(),
            examples: vec!["输入：nums = [-2,5,-1], lower = -2, upper = 2\n输出：3".to_string()],
            constraints: vec!["1 <= nums.length <= 10^5".to_string()],
            rust_191_features: vec!["使用树状数组或归并排序，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n log n)".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("使用树状数组或归并排序".to_string()),
            },
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_num_array_bit() {
        let mut na = NumArrayBIT::new(vec![1, 3, 5]);
        assert_eq!(na.sum_range(0, 2), 9);
        na.update(1, 2);
        assert_eq!(na.sum_range(0, 2), 8);
    }
}
