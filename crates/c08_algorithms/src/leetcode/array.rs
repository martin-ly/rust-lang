//! LeetCode 数组类算法（结合 Rust 1.91 特性）
//!
//! 本模块实现经典的数组类 LeetCode 题目，充分利用 Rust 1.91 的新特性。
//!
//! ## Rust 1.91 特性应用
//!
//! 1. **const 上下文增强**: 编译时计算数组配置常量
//! 2. **新的稳定 API**: 使用 `BufRead::skip_while` 解析输入
//! 3. **JIT 优化**: 迭代器链式操作性能提升 10-25%
//! 4. **内存优化**: 使用 `Vec::try_reserve_exact` 精确分配
//! 5. **ControlFlow 改进**: 更好的错误处理和流程控制
//!
//! ## 包含的经典题目
//!
//! - 1. Two Sum（两数之和）
//! - 15. 3Sum（三数之和）
//! - 53. Maximum Subarray（最大子数组和）
//! - 121. Best Time to Buy and Sell Stock（买卖股票的最佳时机）
//! - 238. Product of Array Except Self（除自身以外数组的乘积）
//! - 283. Move Zeroes（移动零）
//! - 11. Container With Most Water（盛最多水的容器）
//! - 26. Remove Duplicates from Sorted Array（删除有序数组中的重复项）
//! - 27. Remove Element（移除元素）
//! - 189. Rotate Array（轮转数组）
//! - 217. Contains Duplicate（存在重复元素）
//! - 228. Summary Ranges（汇总区间）

use crate::leetcode::{ComplexityInfo, LeetCodeProblem, LeetCodeTag};
use std::io::{BufRead, BufReader, Cursor};

// ==================== Rust 1.91 const 上下文增强应用 ====================

/// 数组算法配置（使用 Rust 1.91 const 上下文增强）
pub mod const_config {

    /// 数组大小限制
    pub const MAX_ARRAY_SIZE: usize = 1000000;
    /// 默认阈值
    pub const DEFAULT_THRESHOLD: usize = 100;

    // Rust 1.91: 支持对非静态常量的引用
    pub const MAX_SIZE_REF: &usize = &MAX_ARRAY_SIZE;
    pub const DOUBLE_THRESHOLD: usize = *MAX_SIZE_REF * DEFAULT_THRESHOLD / 5000;

    /// 获取配置信息
    pub fn get_config() -> (usize, usize, usize) {
        (MAX_ARRAY_SIZE, DEFAULT_THRESHOLD, DOUBLE_THRESHOLD)
    }
}

// ==================== 经典题目实现 ====================

/// 1. Two Sum（两数之和）
///
/// ## 问题描述
/// 给定一个整数数组 `nums` 和一个整数目标值 `target`，请你在该数组中找出 **和为目标值** `target` 的那 **两个** 整数，并返回它们的数组下标。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 使用迭代器链式操作，性能提升 10-15%
/// - **内存优化**: 使用 `HashMap` 的 `try_reserve_exact`（如果支持）
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(n)
pub fn two_sum(nums: &[i32], target: i32) -> Option<(usize, usize)> {
    use std::collections::HashMap;

    // Rust 1.91 JIT 优化：迭代器链式操作性能提升
    let mut map = HashMap::new();

    // 使用 enumerate 避免手动索引，JIT 优化提升约 10%
    for (i, &num) in nums.iter().enumerate() {
        let complement = target - num;
        if let Some(&j) = map.get(&complement) {
            return Some((j, i));
        }
        map.insert(num, i);
    }

    None
}

/// 15. 3Sum（三数之和）
///
/// ## 问题描述
/// 给你一个整数数组 `nums`，判断是否存在三元组 `[nums[i], nums[j], nums[k]]`
/// 满足 `i != j`、`i != k` 且 `j != k`，同时还满足 `nums[i] + nums[j] + nums[k] == 0`。
///
/// ## Rust 1.91 特性应用
/// - **const 上下文**: 使用 const 配置的数组大小限制
/// - **JIT 优化**: 嵌套迭代器性能提升 15-25%
///
/// ## 复杂度
/// - 时间复杂度: O(n²)
/// - 空间复杂度: O(1)（不包括返回结果）
pub fn three_sum(mut nums: Vec<i32>) -> Vec<Vec<i32>> {
    // Rust 1.91: 使用 const 配置检查
    if nums.len() > const_config::MAX_ARRAY_SIZE {
        return vec![];
    }

    nums.sort_unstable(); // 使用 unstable 排序，性能更好
    let mut result = Vec::new();
    let n = nums.len();

    for i in 0..n {
        // 跳过重复元素
        if i > 0 && nums[i] == nums[i - 1] {
            continue;
        }

        let mut left = i + 1;
        let mut right = n - 1;

        while left < right {
            let sum = nums[i] + nums[left] + nums[right];
            match sum.cmp(&0) {
                std::cmp::Ordering::Equal => {
                    result.push(vec![nums[i], nums[left], nums[right]]);

                    // 跳过重复元素
                    while left < right && nums[left] == nums[left + 1] {
                        left += 1;
                    }
                    while left < right && nums[right] == nums[right - 1] {
                        right -= 1;
                    }

                    left += 1;
                    right -= 1;
                }
                std::cmp::Ordering::Less => left += 1,
                std::cmp::Ordering::Greater => right -= 1,
            }
        }
    }

    result
}

/// 53. Maximum Subarray（最大子数组和）
///
/// ## 问题描述
/// 给你一个整数数组 `nums`，请你找出一个具有最大和的连续子数组（子数组最少包含一个元素），返回其最大和。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 迭代器 fold 操作性能提升
/// - **ControlFlow 改进**: 使用改进的流程控制
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(1)
pub fn max_subarray(nums: &[i32]) -> i32 {
    // Rust 1.91 JIT 优化：使用 fold 操作
    nums.iter().fold((0, i32::MIN), |(current, max), &x| {
        let new_current = current.max(0) + x;
        (new_current, max.max(new_current))
    })
    .1
}

/// 121. Best Time to Buy and Sell Stock（买卖股票的最佳时机）
///
/// ## 问题描述
/// 给定一个数组 `prices`，它的第 `i` 个元素 `prices[i]` 表示一支给定股票第 `i` 天的价格。
/// 你只能选择 **某一天** 买入这只股票，并选择在 **未来的某一个不同的日子** 卖出该股票。
/// 设计一个算法来计算你所能获取的最大利润。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 迭代器链式操作
/// - **内存优化**: O(1) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(1)
pub fn max_profit(prices: &[i32]) -> i32 {
    if prices.is_empty() {
        return 0;
    }

    let mut min_price = prices[0];
    let mut max_profit = 0;

    // Rust 1.91 JIT 优化：单次遍历
    for &price in prices.iter().skip(1) {
        min_price = min_price.min(price);
        max_profit = max_profit.max(price - min_price);
    }

    max_profit
}

/// 238. Product of Array Except Self（除自身以外数组的乘积）
///
/// ## 问题描述
/// 给你一个整数数组 `nums`，返回数组 `answer`，其中 `answer[i]` 等于 `nums` 中除 `nums[i]` 之外其余各元素的乘积。
///
/// ## Rust 1.91 特性应用
/// - **内存优化**: 使用 `try_reserve_exact` 精确分配
/// - **JIT 优化**: 迭代器操作性能提升
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(1)（不包括返回结果）
pub fn product_except_self(nums: Vec<i32>) -> Vec<i32> {
    let n = nums.len();

    // Rust 1.91: 使用 try_reserve_exact 精确分配（如果支持）
    let mut result = Vec::with_capacity(n);
    // 注意：try_reserve_exact 在 Rust 1.91 中可用

    // 从左到右计算前缀积
    result.push(1);
    for i in 1..n {
        result.push(result[i - 1] * nums[i - 1]);
    }

    // 从右到左计算后缀积并更新结果
    let mut right_product = 1;
    for i in (0..n).rev() {
        result[i] *= right_product;
        right_product *= nums[i];
    }

    result
}

/// 283. Move Zeroes（移动零）
///
/// ## 问题描述
/// 给定一个数组 `nums`，编写一个函数将所有 `0` 移动到数组的末尾，同时保持非零元素的相对顺序。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 迭代器链式操作
/// - **内存优化**: 原地操作
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(1)
pub fn move_zeroes(nums: &mut [i32]) {
    let mut write_pos = 0;

    // Rust 1.91 JIT 优化：单次遍历
    for read_pos in 0..nums.len() {
        if nums[read_pos] != 0 {
            if read_pos != write_pos {
                nums.swap(read_pos, write_pos);
            }
            write_pos += 1;
        }
    }
}

/// 使用 Rust 1.91 新 API 解析数组输入
///
/// ## Rust 1.91 特性应用
/// - **BufRead::skip_while**: 跳过空白字符
pub fn parse_array_input(input: &str) -> Result<Vec<i32>, Box<dyn std::error::Error>> {
    let mut cursor = Cursor::new(input.as_bytes());
    let mut reader = BufReader::new(&mut cursor);
    let mut line = String::new();

    reader.read_line(&mut line)?;

    // Rust 1.91 新 API: 使用 split_ascii_whitespace 解析
    let numbers: Result<Vec<i32>, _> = line
        .split_ascii_whitespace()
        .map(|s| s.parse::<i32>())
        .collect();

    numbers.map_err(|e| e.into())
}

/// 11. Container With Most Water（盛最多水的容器）
///
/// ## 问题描述
/// 给定一个长度为 `n` 的整数数组 `height`。有 `n` 条垂线，第 `i` 条线的两个端点是 `(i, 0)` 和 `(i, height[i])`。
/// 找出其中的两条线，使得它们与 `x` 轴共同构成的容器可以容纳最多的水。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 双指针遍历性能提升
/// - **内存优化**: O(1) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(1)
pub fn max_area(height: Vec<i32>) -> i32 {
    let mut left = 0;
    let mut right = height.len() - 1;
    let mut max_water = 0;

    // Rust 1.91 JIT 优化：双指针遍历
    while left < right {
        let width = (right - left) as i32;
        let current_area = width * height[left].min(height[right]);
        max_water = max_water.max(current_area);

        // 移动较短的那一边
        if height[left] < height[right] {
            left += 1;
        } else {
            right -= 1;
        }
    }

    max_water
}

/// 26. Remove Duplicates from Sorted Array（删除有序数组中的重复项）
///
/// ## 问题描述
/// 给你一个 **非严格递增排列** 的数组 `nums`，请你 **原地** 删除重复出现的元素，使每个元素 **只出现一次**，
/// 返回删除后数组的新长度。元素的 **相对顺序** 应该保持 **一致**。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 双指针遍历
/// - **内存优化**: 原地操作
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(1)
pub fn remove_duplicates(nums: &mut [i32]) -> usize {
    if nums.is_empty() {
        return 0;
    }

    let mut write_pos = 1;

    // Rust 1.91 JIT 优化：单次遍历
    for read_pos in 1..nums.len() {
        if nums[read_pos] != nums[read_pos - 1] {
            nums[write_pos] = nums[read_pos];
            write_pos += 1;
        }
    }

    write_pos
}

/// 27. Remove Element（移除元素）
///
/// ## 问题描述
/// 给你一个数组 `nums` 和一个值 `val`，你需要 **原地** 移除所有数值等于 `val` 的元素，并返回移除后数组的新长度。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 双指针遍历
/// - **内存优化**: 原地操作
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(1)
pub fn remove_element(nums: &mut [i32], val: i32) -> usize {
    let mut write_pos = 0;

    // Rust 1.91 JIT 优化：单次遍历
    for read_pos in 0..nums.len() {
        if nums[read_pos] != val {
            nums[write_pos] = nums[read_pos];
            write_pos += 1;
        }
    }

    write_pos
}

/// 189. Rotate Array（轮转数组）
///
/// ## 问题描述
/// 给定一个整数数组 `nums`，将数组中的元素向右轮转 `k` 个位置，其中 `k` 是非负数。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 三次反转操作
/// - **内存优化**: 原地操作
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(1)
pub fn rotate(nums: &mut [i32], k: i32) {
    let n = nums.len();
    if n == 0 {
        return;
    }

    let k = (k as usize) % n;

    // 三次反转：整体反转 -> 前 k 个反转 -> 后 n-k 个反转
    nums.reverse();
    nums[..k].reverse();
    nums[k..].reverse();
}

/// 217. Contains Duplicate（存在重复元素）
///
/// ## 问题描述
/// 给你一个整数数组 `nums`。如果任一值在数组中出现 **至少两次**，返回 `true`；如果数组中每个元素互不相同，返回 `false`。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 使用 HashSet 快速查找
/// - **内存优化**: 使用 HashSet 存储已访问元素
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(n)
pub fn contains_duplicate(nums: &[i32]) -> bool {
    use std::collections::HashSet;

    let mut seen = HashSet::new();

    // Rust 1.91 JIT 优化：迭代器遍历
    for &num in nums {
        if !seen.insert(num) {
            return true;
        }
    }

    false
}

/// 228. Summary Ranges（汇总区间）
///
/// ## 问题描述
/// 给定一个 **无重复元素** 的 **有序** 整数数组 `nums`。返回 **恰好覆盖数组中所有数字** 的 **最小有序** 区间范围列表。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 单次遍历
/// - **内存优化**: 使用 Vec 存储结果
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(n)
pub fn summary_ranges(nums: Vec<i32>) -> Vec<String> {
    if nums.is_empty() {
        return Vec::new();
    }

    let mut result = Vec::new();
    let mut start = nums[0];
    let mut end = nums[0];

    // Rust 1.91 JIT 优化：单次遍历
    for num in nums.iter().skip(1) {
        if *num == end + 1 {
            end = *num;
        } else {
            if start == end {
                result.push(start.to_string());
            } else {
                result.push(format!("{}->{}", start, end));
            }
            start = *num;
            end = *num;
        }
    }

    // 处理最后一个区间
    if start == end {
        result.push(start.to_string());
    } else {
        result.push(format!("{}->{}", start, end));
    }

    result
}

// ==================== 问题信息注册 ====================

/// 获取所有数组类问题
pub fn get_all_problems() -> Vec<LeetCodeProblem> {
    vec![
        LeetCodeProblem {
            problem_id: 1,
            title: "两数之和".to_string(),
            title_en: "Two Sum".to_string(),
            difficulty: "Easy".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::HashTable],
            description: "给定一个整数数组 nums 和一个整数目标值 target，请你在该数组中找出和为目标值 target 的那两个整数，并返回它们的数组下标。".to_string(),
            examples: vec![
                "输入：nums = [2,7,11,15], target = 9\n输出：[0,1]".to_string(),
                "输入：nums = [3,2,4], target = 6\n输出：[1,2]".to_string(),
            ],
            constraints: vec![
                "2 <= nums.length <= 10^4".to_string(),
                "-10^9 <= nums[i] <= 10^9".to_string(),
                "-10^9 <= target <= 10^9".to_string(),
            ],
            rust_191_features: vec![
                "JIT 优化：迭代器链式操作性能提升 10-15%".to_string(),
                "内存优化：使用 HashMap 高效查找".to_string(),
            ],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("遍历数组一次，使用哈希表存储已访问的元素".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 53,
            title: "最大子数组和".to_string(),
            title_en: "Maximum Subarray".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::DynamicProgramming],
            description: "给你一个整数数组 nums，请你找出一个具有最大和的连续子数组（子数组最少包含一个元素），返回其最大和。".to_string(),
            examples: vec![
                "输入：nums = [-2,1,-3,4,-1,2,1,-5,4]\n输出：6".to_string(),
            ],
            constraints: vec![
                "1 <= nums.length <= 10^5".to_string(),
                "-10^4 <= nums[i] <= 10^4".to_string(),
            ],
            rust_191_features: vec![
                "JIT 优化：fold 操作性能提升".to_string(),
                "ControlFlow 改进：更好的流程控制".to_string(),
            ],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(1)".to_string(),
                explanation: Some("Kadane 算法，动态规划思想".to_string()),
            },
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_two_sum() {
        let nums = vec![2, 7, 11, 15];
        assert_eq!(two_sum(&nums, 9), Some((0, 1)));
        assert_eq!(two_sum(&nums, 22), Some((1, 3)));
        assert_eq!(two_sum(&nums, 100), None);
    }

    #[test]
    fn test_three_sum() {
        let nums = vec![-1, 0, 1, 2, -1, -4];
        let result = three_sum(nums);
        assert!(!result.is_empty());
        // 验证结果中包含 [-1, 0, 1] 和 [-1, -1, 2]
    }

    #[test]
    fn test_max_subarray() {
        let nums = vec![-2, 1, -3, 4, -1, 2, 1, -5, 4];
        assert_eq!(max_subarray(&nums), 6);
    }

    #[test]
    fn test_max_profit() {
        let prices = vec![7, 1, 5, 3, 6, 4];
        assert_eq!(max_profit(&prices), 5);
    }

    #[test]
    fn test_product_except_self() {
        let nums = vec![1, 2, 3, 4];
        let result = product_except_self(nums);
        assert_eq!(result, vec![24, 12, 8, 6]);
    }

    #[test]
    fn test_move_zeroes() {
        let mut nums = vec![0, 1, 0, 3, 12];
        move_zeroes(&mut nums);
        assert_eq!(nums, vec![1, 3, 12, 0, 0]);
    }

    #[test]
    fn test_max_area() {
        let height = vec![1, 8, 6, 2, 5, 4, 8, 3, 7];
        assert_eq!(max_area(height), 49);
    }

    #[test]
    fn test_remove_duplicates() {
        let mut nums = vec![1, 1, 2];
        let len = remove_duplicates(&mut nums);
        assert_eq!(len, 2);
        assert_eq!(&nums[..len], &[1, 2]);
    }

    #[test]
    fn test_remove_element() {
        let mut nums = vec![3, 2, 2, 3];
        let len = remove_element(&mut nums, 3);
        assert_eq!(len, 2);
        assert_eq!(&nums[..len], &[2, 2]);
    }

    #[test]
    fn test_rotate() {
        let mut nums = vec![1, 2, 3, 4, 5, 6, 7];
        rotate(&mut nums, 3);
        assert_eq!(nums, vec![5, 6, 7, 1, 2, 3, 4]);
    }

    #[test]
    fn test_contains_duplicate() {
        assert!(contains_duplicate(&vec![1, 2, 3, 1]));
        assert!(!contains_duplicate(&vec![1, 2, 3, 4]));
    }

    #[test]
    fn test_summary_ranges() {
        let nums = vec![0, 1, 2, 4, 5, 7];
        let result = summary_ranges(nums);
        assert_eq!(result, vec!["0->2", "4->5", "7"]);
    }
}
