//! LeetCode 线段树类算法（结合 Rust 1.92 特性）
//!
//! 本模块实现经典的线段树类 LeetCode 题目，充分利用 Rust 1.92 的新特性。
//!
//! ## Rust 1.92 特性应用
//!
//! 1. **性能优化**: 使用线段树进行区间查询和更新
//! 2. **内存优化**: 高效的线段树实现

use crate::leetcode::{ComplexityInfo, LeetCodeProblem, LeetCodeTag};

// ==================== 数据结构定义 ====================

/// 307. Range Sum Query - Mutable（区域和检索 - 数组可修改）
pub struct NumArray {
    tree: Vec<i32>,
    n: usize,
}

impl NumArray {
    pub fn new(nums: Vec<i32>) -> Self {
        let n = nums.len();
        let mut tree = vec![0; n * 4];

        fn build_tree(nums: &[i32], tree: &mut [i32], node: usize, start: usize, end: usize) {
            if start == end {
                tree[node] = nums[start];
            } else {
                let mid = (start + end) / 2;
                build_tree(nums, tree, node * 2 + 1, start, mid);
                build_tree(nums, tree, node * 2 + 2, mid + 1, end);
                tree[node] = tree[node * 2 + 1] + tree[node * 2 + 2];
            }
        }

        if n > 0 {
            build_tree(&nums, &mut tree, 0, 0, n - 1);
        }

        NumArray { tree, n }
    }

    pub fn update(&mut self, index: i32, val: i32) {
        fn update_tree(
            tree: &mut [i32],
            node: usize,
            start: usize,
            end: usize,
            idx: usize,
            val: i32,
        ) {
            if start == end {
                tree[node] = val;
            } else {
                let mid = (start + end) / 2;
                if idx <= mid {
                    update_tree(tree, node * 2 + 1, start, mid, idx, val);
                } else {
                    update_tree(tree, node * 2 + 2, mid + 1, end, idx, val);
                }
                tree[node] = tree[node * 2 + 1] + tree[node * 2 + 2];
            }
        }

        if self.n > 0 {
            update_tree(&mut self.tree, 0, 0, self.n - 1, index as usize, val);
        }
    }

    pub fn sum_range(&self, left: i32, right: i32) -> i32 {
        fn query_tree(
            tree: &[i32],
            node: usize,
            start: usize,
            end: usize,
            l: usize,
            r: usize,
        ) -> i32 {
            if r < start || l > end {
                return 0;
            }
            if l <= start && end <= r {
                return tree[node];
            }
            let mid = (start + end) / 2;
            query_tree(tree, node * 2 + 1, start, mid, l, r)
                + query_tree(tree, node * 2 + 2, mid + 1, end, l, r)
        }

        if self.n == 0 {
            return 0;
        }
        query_tree(&self.tree, 0, 0, self.n - 1, left as usize, right as usize)
    }
}

/// 315. Count of Smaller Numbers After Self（计算右侧小于当前元素的个数）
pub fn count_smaller(nums: Vec<i32>) -> Vec<i32> {
    // 使用归并排序的方法
    let n = nums.len();
    let mut result = vec![0; n];
    let mut indices: Vec<usize> = (0..n).collect();
    let mut temp = vec![0; n];
    let mut temp_indices = vec![0; n];

    fn merge_sort(
        nums: &[i32],
        indices: &mut [usize],
        temp: &mut [usize],
        temp_indices: &mut [usize],
        result: &mut [i32],
        left: usize,
        right: usize,
    ) {
        if left >= right {
            return;
        }
        let mid = (left + right) / 2;
        merge_sort(nums, indices, temp, temp_indices, result, left, mid);
        merge_sort(nums, indices, temp, temp_indices, result, mid + 1, right);

        let mut i = left;
        let mut j = mid + 1;
        let mut k = left;
        let mut right_count = 0;

        while i <= mid && j <= right {
            if nums[indices[i]] <= nums[indices[j]] {
                result[indices[i]] += right_count;
                temp_indices[k] = indices[i];
                i += 1;
            } else {
                right_count += 1;
                temp_indices[k] = indices[j];
                j += 1;
            }
            k += 1;
        }

        while i <= mid {
            result[indices[i]] += right_count;
            temp_indices[k] = indices[i];
            i += 1;
            k += 1;
        }

        while j <= right {
            temp_indices[k] = indices[j];
            j += 1;
            k += 1;
        }

        for i in left..=right {
            indices[i] = temp_indices[i];
        }
    }

    merge_sort(&nums, &mut indices, &mut temp, &mut temp_indices, &mut result, 0, n - 1);
    result
}

/// 327. Count of Range Sum（区间和的个数）
pub fn count_range_sum(nums: Vec<i32>, lower: i32, upper: i32) -> i32 {
    let n = nums.len();
    let mut prefix_sum = vec![0i64; n + 1];
    for i in 0..n {
        prefix_sum[i + 1] = prefix_sum[i] + nums[i] as i64;
    }

    fn merge_count(
        prefix: &mut [i64],
        temp: &mut [i64],
        lower: i64,
        upper: i64,
        left: usize,
        right: usize,
    ) -> i32 {
        if left >= right {
            return 0;
        }

        let mid = (left + right) / 2;
        let mut count = merge_count(prefix, temp, lower, upper, left, mid)
            + merge_count(prefix, temp, lower, upper, mid + 1, right);

        let mut j = mid + 1;
        let mut k = mid + 1;

        for idx in left..=mid {
            while j <= right && prefix[j] - prefix[idx] < lower {
                j += 1;
            }
            while k <= right && prefix[k] - prefix[idx] <= upper {
                k += 1;
            }
            count += (k - j) as i32;
        }

        let mut i = left;
        let mut j = mid + 1;
        let mut t = left;

        while i <= mid && j <= right {
            if prefix[i] <= prefix[j] {
                temp[t] = prefix[i];
                i += 1;
            } else {
                temp[t] = prefix[j];
                j += 1;
            }
            t += 1;
        }

        while i <= mid {
            temp[t] = prefix[i];
            i += 1;
            t += 1;
        }

        while j <= right {
            temp[t] = prefix[j];
            j += 1;
            t += 1;
        }

        for i in left..=right {
            prefix[i] = temp[i];
        }

        count
    }

    let mut temp = vec![0i64; n + 1];
    merge_count(&mut prefix_sum, &mut temp, lower as i64, upper as i64, 0, n)
}

/// 699. Falling Squares（掉落的方块）
pub fn falling_squares(positions: Vec<Vec<i32>>) -> Vec<i32> {
    use std::collections::BTreeMap;

    let mut heights = BTreeMap::new();
    let mut result = Vec::new();
    let mut max_height = 0;

    for pos in positions {
        let left = pos[0];
        let side = pos[1];
        let right = left + side;

        let mut max_h = 0;
        for (_, &height) in heights.range(left..right) {
            max_h = max_h.max(height);
        }

        let new_height = max_h + side;
        heights.insert(left, new_height);
        heights.insert(right, max_h);

        // 移除中间的点
        let keys_to_remove: Vec<i32> = heights
            .range((left + 1)..right)
            .map(|(&k, _)| k)
            .collect();
        for key in keys_to_remove {
            heights.remove(&key);
        }

        max_height = max_height.max(new_height);
        result.push(max_height);
    }

    result
}

// ==================== 问题信息注册 ====================

/// 获取所有线段树类问题
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
            rust_191_features: vec!["使用线段树或树状数组，Rust 1.92 性能优化".to_string()],
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
            rust_191_features: vec!["使用线段树或归并排序，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n log n)".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("使用线段树或归并排序".to_string()),
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
            rust_191_features: vec!["使用线段树或归并排序，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n log n)".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("使用线段树或归并排序".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 699,
            title: "掉落的方块".to_string(),
            title_en: "Falling Squares".to_string(),
            difficulty: "Hard".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::SegmentTree, LeetCodeTag::OrderedMap],
            description: "在二维平面上的 x 轴上，放置着一些方块。给你一个二维整数数组 positions ，其中 positions[i] = [lefti, sideLengthi] 表示：第 i 个方块边长为 sideLengthi ，其左侧边与 x 轴上坐标点 lefti 对齐。每个方块都从一个比目前所有的落地方块更高的高度掉落而下。方块沿 y 轴负方向下落，直到着陆到 另一个方块的顶面 或者是 x 轴上 。一个方块「擦过」另一个方块的左侧边或右侧边不算着陆。一旦着陆，它就会固定在原地，无法移动。在每个方块掉落后，你必须记录目前所有已经落稳的 方块堆叠的最高高度 。返回一个整数数组 ans ，其中 ans[i] 表示在第 i 块方块掉落后堆叠的最高高度。".to_string(),
            examples: vec!["输入：positions = [[1,2],[2,3],[6,1]]\n输出：[2,5,5]".to_string()],
            constraints: vec!["1 <= positions.length <= 1000".to_string()],
            rust_191_features: vec!["使用线段树，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n log n)".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("n 是方块数量".to_string()),
            },
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_num_array() {
        let mut na = NumArray::new(vec![1, 3, 5]);
        assert_eq!(na.sum_range(0, 2), 9);
        na.update(1, 2);
        assert_eq!(na.sum_range(0, 2), 8);
    }

    #[test]
    fn test_count_smaller() {
        assert_eq!(count_smaller(vec![5, 2, 6, 1]), vec![2, 1, 1, 0]);
    }
}
