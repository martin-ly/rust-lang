//! LeetCode 单调栈类算法（结合 Rust 1.92 特性）
//!
//! 本模块实现经典的单调栈类 LeetCode 题目，充分利用 Rust 1.92 的新特性。
//!
//! ## Rust 1.92 特性应用
//!
//! 1. **性能优化**: 使用栈数据结构优化
//! 2. **内存优化**: 高效的栈操作

use crate::leetcode::{ComplexityInfo, LeetCodeProblem, LeetCodeTag};
use std::collections::VecDeque;

// ==================== 经典题目实现 ====================

/// 42. Trapping Rain Water（接雨水）- 单调栈版本
///
/// ## 问题描述
/// 给定 n 个非负整数表示每个宽度为 1 的柱子的高度图，计算按此排列的柱子，下雨之后能接多少雨水。
///
/// ## Rust 1.92 特性应用
/// - **单调栈**: 使用单调递减栈
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(n)
pub fn trap(height: Vec<i32>) -> i32 {
    let mut stack = Vec::new();
    let mut water = 0;

    for i in 0..height.len() {
        while !stack.is_empty() && height[i] > height[*stack.last().unwrap()] {
            let bottom = stack.pop().unwrap();
            if stack.is_empty() {
                break;
            }
            let left = *stack.last().unwrap();
            let width = i - left - 1;
            let h = height[i].min(height[left]) - height[bottom];
            water += width as i32 * h;
        }
        stack.push(i);
    }

    water
}

/// 84. Largest Rectangle in Histogram（柱状图中最大的矩形）
///
/// ## 问题描述
/// 给定 n 个非负整数，用来表示柱状图中各个柱子的高度。每个柱子彼此相邻，且宽度为 1 。
/// 求在该柱状图中，能够勾勒出来的矩形的最大面积。
///
/// ## Rust 1.92 特性应用
/// - **单调栈**: 使用单调递增栈
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(n)
pub fn largest_rectangle_area(heights: Vec<i32>) -> i32 {
    let mut stack = Vec::new();
    let mut max_area = 0;

    for i in 0..=heights.len() {
        let h = if i < heights.len() { heights[i] } else { 0 };

        while !stack.is_empty() && h < heights[*stack.last().unwrap()] {
            let height = heights[stack.pop().unwrap()];
            let width = if stack.is_empty() {
                i
            } else {
                i - stack.last().unwrap() - 1
            };
            max_area = max_area.max(height * width as i32);
        }
        stack.push(i);
    }

    max_area
}

/// 85. Maximal Rectangle（最大矩形）
///
/// ## 问题描述
/// 给定一个仅包含 0 和 1 、大小为 rows x cols 的二维二进制矩阵，找出只包含 1 的最大矩形，并返回其面积。
///
/// ## Rust 1.92 特性应用
/// - **单调栈**: 将问题转化为柱状图最大矩形
///
/// ## 复杂度
/// - 时间复杂度: O(m * n)
/// - 空间复杂度: O(n)
pub fn maximal_rectangle(matrix: Vec<Vec<char>>) -> i32 {
    if matrix.is_empty() || matrix[0].is_empty() {
        return 0;
    }

    let rows = matrix.len();
    let cols = matrix[0].len();
    let mut heights = vec![0; cols];
    let mut max_area = 0;

    for i in 0..rows {
        for j in 0..cols {
            if matrix[i][j] == '1' {
                heights[j] += 1;
            } else {
                heights[j] = 0;
            }
        }
        max_area = max_area.max(largest_rectangle_area(heights.clone()));
    }

    max_area
}

/// 239. Sliding Window Maximum（滑动窗口最大值）
///
/// ## 问题描述
/// 给你一个整数数组 nums，有一个大小为 k 的滑动窗口从数组的最左侧移动到数组的最右侧。
/// 你只可以看到在滑动窗口内的 k 个数字。滑动窗口每次只向右移动一位。
/// 返回 滑动窗口中的最大值 。
///
/// ## Rust 1.92 特性应用
/// - **单调队列**: 使用双端队列维护单调递减序列
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(k)
pub fn max_sliding_window(nums: Vec<i32>, k: i32) -> Vec<i32> {
    let k = k as usize;
    let mut deque = VecDeque::new();
    let mut result = Vec::new();

    for i in 0..nums.len() {
        // 移除窗口外的元素
        while !deque.is_empty() && *deque.front().unwrap() < i as i32 - k as i32 + 1 {
            deque.pop_front();
        }

        // 维护单调递减队列
        while !deque.is_empty() && nums[*deque.back().unwrap() as usize] <= nums[i] {
            deque.pop_back();
        }

        deque.push_back(i as i32);

        // 窗口形成后，记录最大值
        if i >= k - 1 {
            result.push(nums[*deque.front().unwrap() as usize]);
        }
    }

    result
}

/// 496. Next Greater Element I（下一个更大元素 I）
///
/// ## 问题描述
/// nums1 中数字 x 的 下一个更大元素 是指 x 在 nums2 中对应位置 右侧 的 第一个 比 x 大的元素。
///
/// ## Rust 1.92 特性应用
/// - **单调栈**: 使用单调递减栈
///
/// ## 复杂度
/// - 时间复杂度: O(m + n)
/// - 空间复杂度: O(n)
pub fn next_greater_element(nums1: Vec<i32>, nums2: Vec<i32>) -> Vec<i32> {
    use std::collections::HashMap;

    let mut stack = Vec::new();
    let mut next_greater = HashMap::new();

    // 构建下一个更大元素的映射
    for num in &nums2 {
        while !stack.is_empty() && *num > *stack.last().unwrap() {
            next_greater.insert(stack.pop().unwrap(), *num);
        }
        stack.push(*num);
    }

    // 查找结果
    nums1.iter()
        .map(|&num| *next_greater.get(&num).unwrap_or(&-1))
        .collect()
}

/// 503. Next Greater Element II（下一个更大元素 II）
///
/// ## 问题描述
/// 给定一个循环数组 nums，返回 nums 中每个元素的 下一个更大元素。
///
/// ## Rust 1.92 特性应用
/// - **单调栈**: 处理循环数组
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(n)
pub fn next_greater_elements(nums: Vec<i32>) -> Vec<i32> {
    let n = nums.len();
    let mut result = vec![-1; n];
    let mut stack = Vec::new();

    // 遍历两遍数组以处理循环
    for i in 0..n * 2 {
        let idx = i % n;

        while !stack.is_empty() && nums[idx] > nums[*stack.last().unwrap()] {
            result[stack.pop().unwrap()] = nums[idx];
        }

        if i < n {
            stack.push(idx);
        }
    }

    result
}

// ==================== 问题信息注册 ====================

/// 获取所有单调栈类问题
pub fn get_all_problems() -> Vec<LeetCodeProblem> {
    vec![
        LeetCodeProblem {
            problem_id: 42,
            title: "接雨水".to_string(),
            title_en: "Trapping Rain Water".to_string(),
            difficulty: "Hard".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::TwoPointers, LeetCodeTag::Stack, LeetCodeTag::MonotonicStack],
            description: "给定 n 个非负整数表示每个宽度为 1 的柱子的高度图，计算按此排列的柱子，下雨之后能接多少雨水。".to_string(),
            examples: vec!["输入：height = [0,1,0,2,1,0,1,3,2,1,2,1]\n输出：6".to_string()],
            constraints: vec!["n == height.length".to_string()],
            rust_191_features: vec!["使用单调栈，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("每个元素最多入栈和出栈一次".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 84,
            title: "柱状图中最大的矩形".to_string(),
            title_en: "Largest Rectangle in Histogram".to_string(),
            difficulty: "Hard".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::Stack, LeetCodeTag::MonotonicStack],
            description: "给定 n 个非负整数，用来表示柱状图中各个柱子的高度。每个柱子彼此相邻，且宽度为 1 。求在该柱状图中，能够勾勒出来的矩形的最大面积。".to_string(),
            examples: vec!["输入：heights = [2,1,5,6,2,3]\n输出：10".to_string()],
            constraints: vec!["1 <= heights.length <= 10^5".to_string()],
            rust_191_features: vec!["使用单调栈，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("每个元素最多入栈和出栈一次".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 85,
            title: "最大矩形".to_string(),
            title_en: "Maximal Rectangle".to_string(),
            difficulty: "Hard".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::DynamicProgramming, LeetCodeTag::Stack, LeetCodeTag::Matrix, LeetCodeTag::MonotonicStack],
            description: "给定一个仅包含 0 和 1 、大小为 rows x cols 的二维二进制矩阵，找出只包含 1 的最大矩形，并返回其面积。".to_string(),
            examples: vec!["输入：matrix = [[\"1\",\"0\",\"1\",\"0\",\"0\"],[\"1\",\"0\",\"1\",\"1\",\"1\"],[\"1\",\"1\",\"1\",\"1\",\"1\"],[\"1\",\"0\",\"0\",\"1\",\"0\"]]\n输出：6".to_string()],
            constraints: vec!["rows == matrix.length".to_string()],
            rust_191_features: vec!["使用单调栈，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(m*n)".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("m 是行数，n 是列数".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 239,
            title: "滑动窗口最大值".to_string(),
            title_en: "Sliding Window Maximum".to_string(),
            difficulty: "Hard".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::Queue, LeetCodeTag::SlidingWindow, LeetCodeTag::MonotonicStack],
            description: "给你一个整数数组 nums，有一个大小为 k 的滑动窗口从数组的最左侧移动到数组的最右侧。你只可以看到在滑动窗口内的 k 个数字。滑动窗口每次只向右移动一位。返回 滑动窗口中的最大值 。".to_string(),
            examples: vec!["输入：nums = [1,3,-1,-3,5,3,6,7], k = 3\n输出：[3,3,5,5,6,7]".to_string()],
            constraints: vec!["1 <= nums.length <= 10^5".to_string()],
            rust_191_features: vec!["使用单调队列，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(k)".to_string(),
                explanation: Some("每个元素最多入队和出队一次".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 496,
            title: "下一个更大元素 I".to_string(),
            title_en: "Next Greater Element I".to_string(),
            difficulty: "Easy".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::HashTable, LeetCodeTag::Stack, LeetCodeTag::MonotonicStack],
            description: "nums1 中数字 x 的 下一个更大元素 是指 x 在 nums2 中对应位置 右侧 的 第一个 比 x 大的元素。给你两个 没有重复元素 的数组 nums1 和 nums2 ，下标从 0 开始计数，其中nums1 是 nums2 的子集。对于每个 0 <= i < nums1.length ，找出满足 nums1[i] == nums2[j] 的下标 j ，并且在 nums2 确定 nums2[j] 的 下一个更大元素 。如果不存在下一个更大元素，那么本次查询的答案是 -1 。返回一个长度为 nums1.length 的数组 ans 作为答案，满足 ans[i] 是如上所述的 下一个更大元素 。".to_string(),
            examples: vec!["输入：nums1 = [4,1,2], nums2 = [1,3,4,2]\n输出：[-1,3,-1]".to_string()],
            constraints: vec!["1 <= nums1.length <= nums2.length <= 1000".to_string()],
            rust_191_features: vec!["使用单调栈，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(m+n)".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("m 是 nums1 长度，n 是 nums2 长度".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 503,
            title: "下一个更大元素 II".to_string(),
            title_en: "Next Greater Element II".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::Stack, LeetCodeTag::MonotonicStack],
            description: "给定一个循环数组 nums （ nums[nums.length - 1] 的下一个元素是 nums[0] ），返回 nums 中每个元素的 下一个更大元素 。数字 x 的 下一个更大的元素 是按数组遍历顺序，这个数字之后的第一个比它更大的数，这意味着你应该循环地搜索它的下一个更大的数。如果不存在，则输出 -1 。".to_string(),
            examples: vec!["输入：nums = [1,2,1]\n输出：[2,-1,2]".to_string()],
            constraints: vec!["1 <= nums.length <= 10^4".to_string()],
            rust_191_features: vec!["使用单调栈处理循环数组，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("每个元素最多入栈和出栈一次".to_string()),
            },
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_trap() {
        assert_eq!(trap(vec![0, 1, 0, 2, 1, 0, 1, 3, 2, 1, 2, 1]), 6);
    }

    #[test]
    fn test_largest_rectangle_area() {
        assert_eq!(largest_rectangle_area(vec![2, 1, 5, 6, 2, 3]), 10);
    }

    #[test]
    fn test_max_sliding_window() {
        assert_eq!(
            max_sliding_window(vec![1, 3, -1, -3, 5, 3, 6, 7], 3),
            vec![3, 3, 5, 5, 6, 7]
        );
    }

    #[test]
    fn test_next_greater_element() {
        assert_eq!(
            next_greater_element(vec![4, 1, 2], vec![1, 3, 4, 2]),
            vec![-1, 3, -1]
        );
    }

    #[test]
    fn test_next_greater_elements() {
        assert_eq!(next_greater_elements(vec![1, 2, 1]), vec![2, -1, 2]);
    }
}
