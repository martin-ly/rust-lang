//! LeetCode 贪心类算法（结合 Rust 1.92 特性）
//!
//! 本模块实现经典的贪心类 LeetCode 题目，充分利用 Rust 1.92 的新特性。
//!
//! ## Rust 1.92 特性应用
//!
//! 1. **性能优化**: 迭代器操作性能提升
//! 2. **内存优化**: 使用标准库高效数据结构

use crate::leetcode::{ComplexityInfo, LeetCodeProblem, LeetCodeTag};

// ==================== 经典题目实现 ====================

/// 45. Jump Game II（跳跃游戏 II）
///
/// ## 问题描述
/// 给你一个非负整数数组 nums ，你最初位于数组的第一个位置。
/// 数组中的每个元素代表你在该位置可以跳跃的最大长度。
/// 你的目标是使用最少的跳跃次数到达数组的最后一个位置。
///
/// ## Rust 1.92 特性应用
/// - **贪心算法**: 一次遍历，贪心选择最远可达位置
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(1)
pub fn jump(nums: Vec<i32>) -> i32 {
    let n = nums.len();
    if n < 2 {
        return 0;
    }

    let mut jumps = 0;
    let mut current_end = 0;
    let mut farthest = 0;

    for i in 0..n - 1 {
        farthest = farthest.max(i + nums[i] as usize);

        if i == current_end {
            jumps += 1;
            current_end = farthest;

            if current_end >= n - 1 {
                break;
            }
        }
    }

    jumps
}

/// 55. Jump Game（跳跃游戏）
///
/// ## 问题描述
/// 给定一个非负整数数组 nums ，你最初位于数组的 第一个下标 。
/// 数组中的每个元素代表你在该位置可以跳跃的最大长度。
/// 判断你是否能够到达最后一个下标。
///
/// ## Rust 1.92 特性应用
/// - **贪心算法**: 一次遍历，贪心选择最远可达位置
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(1)
pub fn can_jump(nums: Vec<i32>) -> bool {
    let n = nums.len();
    let mut farthest = 0;

    for i in 0..n {
        if i > farthest {
            return false;
        }
        farthest = farthest.max(i + nums[i] as usize);
        if farthest >= n - 1 {
            return true;
        }
    }

    true
}

/// 122. Best Time to Buy and Sell Stock II（买卖股票的最佳时机 II）
///
/// ## 问题描述
/// 给你一个整数数组 prices ，其中 prices[i] 表示某支股票第 i 天的价格。
/// 在每一天，你可以决定是否购买和/或出售股票。你在任何时候 最多 只能持有 一股 股票。
/// 你也可以先购买，然后在 同一天 出售。返回 你能获得的 最大 利润 。
///
/// ## Rust 1.92 特性应用
/// - **贪心算法**: 贪心选择所有正收益
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(1)
pub fn max_profit_ii(prices: Vec<i32>) -> i32 {
    let mut profit = 0;

    for i in 1..prices.len() {
        if prices[i] > prices[i - 1] {
            profit += prices[i] - prices[i - 1];
        }
    }

    profit
}

/// 134. Gas Station（加油站）
///
/// ## 问题描述
/// 在一条环路上有 n 个加油站，其中第 i 个加油站有汽油 gas[i] 升。
/// 你有一辆油箱容量无限的的汽车，从第 i 个加油站开往第 i+1 个加油站需要消耗汽油 cost[i] 升。
/// 你从其中的一个加油站出发，开始时油箱为空。
/// 给定两个整数数组 gas 和 cost ，如果你可以绕环路行驶一周，则返回出发时加油站的编号，否则返回 -1 。
///
/// ## Rust 1.92 特性应用
/// - **贪心算法**: 贪心选择起始点
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(1)
pub fn can_complete_circuit(gas: Vec<i32>, cost: Vec<i32>) -> i32 {
    let n = gas.len();
    let mut total_tank = 0;
    let mut curr_tank = 0;
    let mut start = 0;

    for i in 0..n {
        total_tank += gas[i] - cost[i];
        curr_tank += gas[i] - cost[i];

        if curr_tank < 0 {
            start = i + 1;
            curr_tank = 0;
        }
    }

    if total_tank >= 0 {
        start as i32
    } else {
        -1
    }
}

/// 179. Largest Number（最大数）
///
/// ## 问题描述
/// 给定一组非负整数 nums，重新排列每个数的顺序（每个数不可拆分）使之组成一个最大的整数。
///
/// ## Rust 1.92 特性应用
/// - **贪心排序**: 使用自定义比较函数排序
///
/// ## 复杂度
/// - 时间复杂度: O(n log n)
/// - 空间复杂度: O(n)
pub fn largest_number(nums: Vec<i32>) -> String {
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

// ==================== 问题信息注册 ====================

/// 获取所有贪心类问题
pub fn get_all_problems() -> Vec<LeetCodeProblem> {
    vec![
        LeetCodeProblem {
            problem_id: 45,
            title: "跳跃游戏 II".to_string(),
            title_en: "Jump Game II".to_string(),
            difficulty: "Hard".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::Greedy, LeetCodeTag::DynamicProgramming],
            description: "给你一个非负整数数组 nums ，你最初位于数组的第一个位置。数组中的每个元素代表你在该位置可以跳跃的最大长度。你的目标是使用最少的跳跃次数到达数组的最后一个位置。".to_string(),
            examples: vec!["输入：nums = [2,3,1,1,4]\n输出：2".to_string()],
            constraints: vec!["1 <= nums.length <= 10^4".to_string()],
            rust_191_features: vec!["使用贪心算法，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(1)".to_string(),
                explanation: Some("一次遍历，贪心选择".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 55,
            title: "跳跃游戏".to_string(),
            title_en: "Jump Game".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::Greedy, LeetCodeTag::DynamicProgramming],
            description: "给定一个非负整数数组 nums ，你最初位于数组的 第一个下标 。数组中的每个元素代表你在该位置可以跳跃的最大长度。判断你是否能够到达最后一个下标。".to_string(),
            examples: vec!["输入：nums = [2,3,1,1,4]\n输出：true".to_string()],
            constraints: vec!["1 <= nums.length <= 3 * 10^4".to_string()],
            rust_191_features: vec!["使用贪心算法，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(1)".to_string(),
                explanation: Some("一次遍历，贪心选择".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 122,
            title: "买卖股票的最佳时机 II".to_string(),
            title_en: "Best Time to Buy and Sell Stock II".to_string(),
            difficulty: "Easy".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::Greedy, LeetCodeTag::DynamicProgramming],
            description: "给你一个整数数组 prices ，其中 prices[i] 表示某支股票第 i 天的价格。在每一天，你可以决定是否购买和/或出售股票。你在任何时候 最多 只能持有 一股 股票。你也可以先购买，然后在 同一天 出售。返回 你能获得的 最大 利润 。".to_string(),
            examples: vec!["输入：prices = [7,1,5,3,6,4]\n输出：7".to_string()],
            constraints: vec!["1 <= prices.length <= 3 * 10^4".to_string()],
            rust_191_features: vec!["使用贪心算法，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(1)".to_string(),
                explanation: Some("一次遍历，贪心选择所有正收益".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 134,
            title: "加油站".to_string(),
            title_en: "Gas Station".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::Greedy],
            description: "在一条环路上有 n 个加油站，其中第 i 个加油站有汽油 gas[i] 升。你有一辆油箱容量无限的的汽车，从第 i 个加油站开往第 i+1 个加油站需要消耗汽油 cost[i] 升。你从其中的一个加油站出发，开始时油箱为空。给定两个整数数组 gas 和 cost ，如果你可以绕环路行驶一周，则返回出发时加油站的编号，否则返回 -1 。".to_string(),
            examples: vec!["输入：gas = [1,2,3,4,5], cost = [3,4,5,1,2]\n输出：3".to_string()],
            constraints: vec!["gas.length == n".to_string()],
            rust_191_features: vec!["使用贪心算法，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(1)".to_string(),
                explanation: Some("一次遍历，贪心选择起始点".to_string()),
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
            rust_191_features: vec!["使用贪心排序，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n log n)".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("排序和字符串转换的时间复杂度".to_string()),
            },
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_jump() {
        assert_eq!(jump(vec![2, 3, 1, 1, 4]), 2);
        assert_eq!(jump(vec![2, 3, 0, 1, 4]), 2);
    }

    #[test]
    fn test_can_jump() {
        assert!(can_jump(vec![2, 3, 1, 1, 4]));
        assert!(!can_jump(vec![3, 2, 1, 0, 4]));
    }

    #[test]
    fn test_max_profit_ii() {
        assert_eq!(max_profit_ii(vec![7, 1, 5, 3, 6, 4]), 7);
        assert_eq!(max_profit_ii(vec![1, 2, 3, 4, 5]), 4);
        assert_eq!(max_profit_ii(vec![7, 6, 4, 3, 1]), 0);
    }

    #[test]
    fn test_can_complete_circuit() {
        assert_eq!(can_complete_circuit(vec![1, 2, 3, 4, 5], vec![3, 4, 5, 1, 2]), 3);
        assert_eq!(can_complete_circuit(vec![2, 3, 4], vec![3, 4, 3]), -1);
    }

    #[test]
    fn test_largest_number() {
        assert_eq!(largest_number(vec![10, 2]), "210");
        assert_eq!(largest_number(vec![3, 30, 34, 5, 9]), "9534330");
        assert_eq!(largest_number(vec![0, 0]), "0");
    }
}
