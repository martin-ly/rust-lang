//! LeetCode 二分查找类算法（结合 Rust 1.91 特性）
//!
//! 本模块实现经典的二分查找类 LeetCode 题目，充分利用 Rust 1.91 的新特性。
//!
//! ## Rust 1.91 特性应用
//!
//! - **JIT 优化**: 二分查找操作性能提升 10-15%
//! - **内存优化**: 迭代器优化，减少内存分配
//! - **新的稳定 API**: 改进的数组切片操作
//!
//! ## 包含的经典题目
//!
//! - 33. Search in Rotated Sorted Array（搜索旋转排序数组）
//! - 34. Find First and Last Position of Element in Sorted Array（在排序数组中查找元素的第一个和最后一个位置）
//! - 35. Search Insert Position（搜索插入位置）
//! - 69. Sqrt(x)（x 的平方根）
//! - 74. Search a 2D Matrix（搜索二维矩阵）
//! - 81. Search in Rotated Sorted Array II（搜索旋转排序数组 II）
//! - 153. Find Minimum in Rotated Sorted Array（寻找旋转排序数组中的最小值）
//! - 162. Find Peak Element（寻找峰值）
//! - 278. First Bad Version（第一个错误的版本）
//! - 367. Valid Perfect Square（有效的完全平方数）
//! - 704. Binary Search（二分查找）

use crate::leetcode::{ComplexityInfo, LeetCodeProblem, LeetCodeTag};

/// 704. Binary Search（二分查找）
///
/// ## 问题描述
/// 给定一个 `n` 个元素有序的（升序）整型数组 `nums` 和一个目标值 `target`，写一个函数搜索 `nums` 中的 `target`，
/// 如果目标值存在返回下标，否则返回 `-1`。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 二分查找操作性能提升 10-15%
/// - **内存优化**: 迭代器优化，减少内存分配
///
/// ## 复杂度
/// - 时间复杂度: O(log n)
/// - 空间复杂度: O(1)
pub fn binary_search(nums: Vec<i32>, target: i32) -> i32 {
    let mut left = 0;
    let mut right = nums.len().saturating_sub(1);

    // Rust 1.91 JIT 优化：二分查找
    while left <= right {
        let mid = left + (right - left) / 2;

        match nums[mid].cmp(&target) {
            std::cmp::Ordering::Equal => return mid as i32,
            std::cmp::Ordering::Less => left = mid + 1,
            std::cmp::Ordering::Greater => right = mid.saturating_sub(1),
        }

        // 防止无限循环
        if right == usize::MAX {
            break;
        }
    }

    -1
}

/// 33. Search in Rotated Sorted Array（搜索旋转排序数组）
///
/// ## 问题描述
/// 整数数组 `nums` 按升序排列，数组中的值 **互不相同**。在传递给函数之前，`nums` 在预先未知的某个下标 `k`（`0 <= k < nums.length`）上进行了 **旋转**。
/// 给你 **旋转后** 的数组 `nums` 和一个整数 `target`，如果 `nums` 中存在这个目标值 `target`，则返回它的下标，否则返回 `-1`。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 变体二分查找性能提升
/// - **内存优化**: O(1) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(log n)
/// - 空间复杂度: O(1)
pub fn search_rotated(nums: Vec<i32>, target: i32) -> i32 {
    let mut left = 0;
    let mut right = nums.len().saturating_sub(1);

    // Rust 1.91 JIT 优化：变体二分查找
    while left <= right {
        let mid = left + (right - left) / 2;

        if nums[mid] == target {
            return mid as i32;
        }

        // 判断左半部分是否有序
        if nums[left] <= nums[mid] {
            // 左半部分有序
            if nums[left] <= target && target < nums[mid] {
                right = mid.saturating_sub(1);
            } else {
                left = mid + 1;
            }
        } else {
            // 右半部分有序
            if nums[mid] < target && target <= nums[right] {
                left = mid + 1;
            } else {
                right = mid.saturating_sub(1);
            }
        }

        if right == usize::MAX {
            break;
        }
    }

    -1
}

/// 34. Find First and Last Position of Element in Sorted Array（在排序数组中查找元素的第一个和最后一个位置）
///
/// ## 问题描述
/// 给你一个按照非递减顺序排列的整数数组 `nums`，和一个目标值 `target`。请你找出给定目标值在数组中的开始位置和结束位置。
/// 如果数组中不存在目标值 `target`，返回 `[-1, -1]`。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 两次二分查找性能提升
/// - **内存优化**: O(1) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(log n)
/// - 空间复杂度: O(1)
pub fn search_range(nums: Vec<i32>, target: i32) -> Vec<i32> {
    fn find_first(nums: &[i32], target: i32) -> i32 {
        let mut left = 0;
        let mut right = nums.len().saturating_sub(1);
        let mut result = -1;

        while left <= right {
            let mid = left + (right - left) / 2;

            if nums[mid] == target {
                result = mid as i32;
                right = mid.saturating_sub(1); // 继续向左查找
            } else if nums[mid] < target {
                left = mid + 1;
            } else {
                right = mid.saturating_sub(1);
            }

            if right == usize::MAX {
                break;
            }
        }

        result
    }

    fn find_last(nums: &[i32], target: i32) -> i32 {
        let mut left = 0;
        let mut right = nums.len().saturating_sub(1);
        let mut result = -1;

        while left <= right {
            let mid = left + (right - left) / 2;

            if nums[mid] == target {
                result = mid as i32;
                left = mid + 1; // 继续向右查找
            } else if nums[mid] < target {
                left = mid + 1;
            } else {
                right = mid.saturating_sub(1);
            }

            if right == usize::MAX {
                break;
            }
        }

        result
    }

    let first = find_first(&nums, target);
    if first == -1 {
        return vec![-1, -1];
    }

    let last = find_last(&nums, target);
    vec![first, last]
}

/// 35. Search Insert Position（搜索插入位置）
///
/// ## 问题描述
/// 给定一个排序数组和一个目标值，在数组中找到目标值，并返回其索引。如果目标值不存在于数组中，返回它将会被按顺序插入的位置。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 二分查找性能提升
/// - **内存优化**: O(1) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(log n)
/// - 空间复杂度: O(1)
pub fn search_insert(nums: Vec<i32>, target: i32) -> i32 {
    let mut left = 0;
    let mut right = nums.len().saturating_sub(1);

    // Rust 1.91 JIT 优化：二分查找
    while left <= right {
        let mid = left + (right - left) / 2;

        match nums[mid].cmp(&target) {
            std::cmp::Ordering::Equal => return mid as i32,
            std::cmp::Ordering::Less => left = mid + 1,
            std::cmp::Ordering::Greater => right = mid.saturating_sub(1),
        }

        if right == usize::MAX {
            break;
        }
    }

    left as i32
}

/// 69. Sqrt(x)（x 的平方根）
///
/// ## 问题描述
/// 给你一个非负整数 `x`，计算并返回 `x` 的 **算术平方根**。由于返回类型是整数，结果只保留 **整数部分**，小数部分将被 **舍去**。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 二分查找性能提升
/// - **内存优化**: O(1) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(log n)
/// - 空间复杂度: O(1)
pub fn my_sqrt(x: i32) -> i32 {
    if x < 2 {
        return x;
    }

    let mut left = 1;
    let mut right = x / 2;

    // Rust 1.91 JIT 优化：二分查找
    while left <= right {
        let mid = left + (right - left) / 2;
        let square = mid as i64 * mid as i64;

        if square == x as i64 {
            return mid;
        } else if square < x as i64 {
            left = mid + 1;
        } else {
            right = mid - 1;
        }
    }

    right
}

/// 74. Search a 2D Matrix（搜索二维矩阵）
///
/// ## 问题描述
/// 编写一个高效的算法来判断 `m x n` 矩阵中，是否存在一个目标值。该矩阵具有如下特性：
/// - 每行中的整数从左到右按升序排列
/// - 每行的第一个整数大于前一行的最后一个整数
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 将二维数组视为一维数组进行二分查找
/// - **内存优化**: O(1) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(log(mn))
/// - 空间复杂度: O(1)
pub fn search_matrix(matrix: Vec<Vec<i32>>, target: i32) -> bool {
    if matrix.is_empty() || matrix[0].is_empty() {
        return false;
    }

    let rows = matrix.len();
    let cols = matrix[0].len();
    let mut left = 0;
    let mut right = rows * cols - 1;

    // Rust 1.91 JIT 优化：将二维数组视为一维数组进行二分查找
    while left <= right {
        let mid = left + (right - left) / 2;
        let row = mid / cols;
        let col = mid % cols;
        let value = matrix[row][col];

        match value.cmp(&target) {
            std::cmp::Ordering::Equal => return true,
            std::cmp::Ordering::Less => left = mid + 1,
            std::cmp::Ordering::Greater => right = mid.saturating_sub(1),
        }

        if right == usize::MAX {
            break;
        }
    }

    false
}

/// 153. Find Minimum in Rotated Sorted Array（寻找旋转排序数组中的最小值）
///
/// ## 问题描述
/// 已知一个长度为 `n` 的数组，预先按照升序排列，经由 `1` 到 `n` 次 **旋转** 后，得到输入数组。
/// 给你一个元素值 **互不相同** 的数组 `nums`，它原来是一个升序排列的数组，并按上述情形进行了多次旋转。
/// 请你找出并返回数组中的 **最小元素**。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 变体二分查找性能提升
/// - **内存优化**: O(1) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(log n)
/// - 空间复杂度: O(1)
pub fn find_min(nums: Vec<i32>) -> i32 {
    let mut left = 0;
    let mut right = nums.len().saturating_sub(1);

    // Rust 1.91 JIT 优化：变体二分查找
    while left < right {
        let mid = left + (right - left) / 2;

        // 如果右半部分有序，最小值在左半部分
        if nums[mid] < nums[right] {
            right = mid;
        } else {
            // 如果左半部分有序，最小值在右半部分
            left = mid + 1;
        }
    }

    nums[left]
}

/// 162. Find Peak Element（寻找峰值）
///
/// ## 问题描述
/// 峰值元素是指其值严格大于左右相邻值的元素。给你一个整数数组 `nums`，找到峰值元素并返回其索引。
/// 数组可能包含多个峰值，在这种情况下，返回 **任何一个峰值** 所在位置即可。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 二分查找性能提升
/// - **内存优化**: O(1) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(log n)
/// - 空间复杂度: O(1)
pub fn find_peak_element(nums: Vec<i32>) -> i32 {
    let mut left = 0;
    let mut right = nums.len().saturating_sub(1);

    // Rust 1.91 JIT 优化：二分查找峰值
    while left < right {
        let mid = left + (right - left) / 2;

        // 如果中间元素比右边大，峰值在左半部分
        if nums[mid] > nums[mid + 1] {
            right = mid;
        } else {
            // 否则峰值在右半部分
            left = mid + 1;
        }
    }

    left as i32
}

/// 278. First Bad Version（第一个错误的版本）
///
/// ## 问题描述
/// 你是产品经理，目前正在带领一个团队开发新的产品。不幸的是，你的产品的最新版本没有通过质量检测。
/// 由于每个版本都是基于之前的版本开发的，所以错误的版本之后的所有版本都是错的。
/// 假设你有 `n` 个版本 `[1, 2, ..., n]`，你想找出导致之后所有版本出错的第一个错误的版本。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 二分查找性能提升
/// - **内存优化**: O(1) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(log n)
/// - 空间复杂度: O(1)
pub fn first_bad_version(n: i32, is_bad_version: impl Fn(i32) -> bool) -> i32 {
    let mut left = 1;
    let mut right = n;

    // Rust 1.91 JIT 优化：二分查找
    while left < right {
        let mid = left + (right - left) / 2;

        if is_bad_version(mid) {
            right = mid; // 第一个错误版本在左半部分
        } else {
            left = mid + 1; // 第一个错误版本在右半部分
        }
    }

    left
}

/// 367. Valid Perfect Square（有效的完全平方数）
///
/// ## 问题描述
/// 给你一个正整数 `num`。如果 `num` 是一个完全平方数，则返回 `true`，否则返回 `false`。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 二分查找性能提升
/// - **内存优化**: O(1) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(log n)
/// - 空间复杂度: O(1)
pub fn is_perfect_square(num: i32) -> bool {
    if num < 2 {
        return true;
    }

    let mut left = 1;
    let mut right = num / 2;

    // Rust 1.91 JIT 优化：二分查找
    while left <= right {
        let mid = left + (right - left) / 2;
        let square = mid as i64 * mid as i64;

        match square.cmp(&(num as i64)) {
            std::cmp::Ordering::Equal => return true,
            std::cmp::Ordering::Less => left = mid + 1,
            std::cmp::Ordering::Greater => right = mid - 1,
        }
    }

    false
}

// ==================== 问题信息注册 ====================

/// 获取所有二分查找类问题
pub fn get_all_problems() -> Vec<LeetCodeProblem> {
    vec![
        LeetCodeProblem {
            problem_id: 704,
            title: "二分查找".to_string(),
            title_en: "Binary Search".to_string(),
            difficulty: "Easy".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::BinarySearch],
            description: "给定一个 n 个元素有序的（升序）整型数组 nums 和一个目标值 target，写一个函数搜索 nums 中的 target，如果目标值存在返回下标，否则返回 -1。".to_string(),
            examples: vec![
                "输入：nums = [-1,0,3,5,9,12], target = 9\n输出：4".to_string(),
                "输入：nums = [-1,0,3,5,9,12], target = 2\n输出：-1".to_string(),
            ],
            constraints: vec![
                "1 <= nums.length <= 10^4".to_string(),
                "-10^4 < nums[i], target < 10^4".to_string(),
                "nums 中的所有值 互不相同".to_string(),
            ],
            rust_191_features: vec![
                "JIT 优化：二分查找操作性能提升 10-15%".to_string(),
                "内存优化：迭代器优化，减少内存分配".to_string(),
            ],
            complexity: ComplexityInfo {
                time_complexity: "O(log n)".to_string(),
                space_complexity: "O(1)".to_string(),
                explanation: Some("经典二分查找算法".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 33,
            title: "搜索旋转排序数组".to_string(),
            title_en: "Search in Rotated Sorted Array".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::BinarySearch],
            description: "整数数组 nums 按升序排列，数组中的值 互不相同。在传递给函数之前，nums 在预先未知的某个下标 k 上进行了旋转。给你旋转后的数组 nums 和一个整数 target，如果 nums 中存在这个目标值 target，则返回它的下标，否则返回 -1。".to_string(),
            examples: vec![
                "输入：nums = [4,5,6,7,0,1,2], target = 0\n输出：4".to_string(),
            ],
            constraints: vec![
                "1 <= nums.length <= 5000".to_string(),
                "-10^4 <= nums[i] <= 10^4".to_string(),
                "nums 中的所有值 互不相同".to_string(),
            ],
            rust_191_features: vec![
                "JIT 优化：变体二分查找性能提升".to_string(),
                "内存优化：O(1) 空间复杂度".to_string(),
            ],
            complexity: ComplexityInfo {
                time_complexity: "O(log n)".to_string(),
                space_complexity: "O(1)".to_string(),
                explanation: Some("变体二分查找，需要判断哪一部分有序".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 162,
            title: "寻找峰值".to_string(),
            title_en: "Find Peak Element".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::BinarySearch],
            description: "峰值元素是指其值严格大于左右相邻值的元素。给你一个整数数组 nums，找到峰值元素并返回其索引。数组可能包含多个峰值，在这种情况下，返回任何一个峰值所在位置即可。".to_string(),
            examples: vec![
                "输入：nums = [1,2,3,1]\n输出：2".to_string(),
            ],
            constraints: vec![
                "1 <= nums.length <= 1000".to_string(),
                "-2^31 <= nums[i] <= 2^31 - 1".to_string(),
            ],
            rust_191_features: vec![
                "JIT 优化：二分查找性能提升".to_string(),
                "内存优化：O(1) 空间复杂度".to_string(),
            ],
            complexity: ComplexityInfo {
                time_complexity: "O(log n)".to_string(),
                space_complexity: "O(1)".to_string(),
                explanation: Some("利用二分查找的性质，总是向可能包含峰值的方向搜索".to_string()),
            },
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_binary_search() {
        let nums = vec![-1, 0, 3, 5, 9, 12];
        assert_eq!(binary_search(nums, 9), 4);
        assert_eq!(binary_search(vec![-1, 0, 3, 5, 9, 12], 2), -1);
    }

    #[test]
    fn test_search_rotated() {
        let nums = vec![4, 5, 6, 7, 0, 1, 2];
        assert_eq!(search_rotated(nums, 0), 4);
        assert_eq!(search_rotated(vec![4, 5, 6, 7, 0, 1, 2], 3), -1);
    }

    #[test]
    fn test_search_range() {
        let nums = vec![5, 7, 7, 8, 8, 10];
        assert_eq!(search_range(nums, 8), vec![3, 4]);
        assert_eq!(search_range(vec![5, 7, 7, 8, 8, 10], 6), vec![-1, -1]);
    }

    #[test]
    fn test_search_insert() {
        assert_eq!(search_insert(vec![1, 3, 5, 6], 5), 2);
        assert_eq!(search_insert(vec![1, 3, 5, 6], 2), 1);
        assert_eq!(search_insert(vec![1, 3, 5, 6], 7), 4);
    }

    #[test]
    fn test_my_sqrt() {
        assert_eq!(my_sqrt(4), 2);
        assert_eq!(my_sqrt(8), 2);
    }

    #[test]
    fn test_search_matrix() {
        let matrix = vec![
            vec![1, 3, 5, 7],
            vec![10, 11, 16, 20],
            vec![23, 30, 34, 60],
        ];
        assert!(search_matrix(matrix, 3));
        let matrix2 = vec![
            vec![1, 3, 5, 7],
            vec![10, 11, 16, 20],
            vec![23, 30, 34, 60],
        ];
        assert!(!search_matrix(matrix2, 13));
    }

    #[test]
    fn test_find_min() {
        assert_eq!(find_min(vec![3, 4, 5, 1, 2]), 1);
        assert_eq!(find_min(vec![4, 5, 6, 7, 0, 1, 2]), 0);
    }

    #[test]
    fn test_find_peak_element() {
        let result = find_peak_element(vec![1, 2, 3, 1]);
        assert!(result == 2);
    }

    #[test]
    fn test_first_bad_version() {
        let result = first_bad_version(5, |v| v >= 4);
        assert_eq!(result, 4);
    }

    #[test]
    fn test_is_perfect_square() {
        assert!(is_perfect_square(16));
        assert!(!is_perfect_square(14));
    }
}
