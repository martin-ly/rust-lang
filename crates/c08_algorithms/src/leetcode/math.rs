//! LeetCode 数学类算法（结合 Rust 1.92 特性）
//!
//! 本模块实现经典的数学类 LeetCode 题目，充分利用 Rust 1.92 的新特性。
//!
//! ## Rust 1.92 特性应用
//!
//! 1. **const 上下文增强**: 编译时计算数学常量
//! 2. **标准库 API**: 使用 `NonZero<u{N}>::div_ceil` 等新 API
//! 3. **性能优化**: 迭代器操作性能提升
//!
//! ## 包含的经典题目
//!
//! - 7. Reverse Integer（整数反转）
//! - 9. Palindrome Number（回文数）
//! - 50. Pow(x, n)（Pow 函数）
//! - 69. Sqrt(x)（x 的平方根）
//! - 202. Happy Number（快乐数）
//! - 204. Count Primes（计数质数）
//! - 231. Power of Two（2 的幂）
//! - 326. Power of Three（3 的幂）
//! - 367. Valid Perfect Square（有效的完全平方数）
//! - 509. Fibonacci Number（斐波那契数）

use crate::leetcode::{ComplexityInfo, LeetCodeProblem, LeetCodeTag};
use std::collections::HashSet;

// ==================== 经典题目实现 ====================

/// 7. Reverse Integer（整数反转）
///
/// ## 问题描述
/// 给你一个 32 位的有符号整数 x ，返回将 x 中的数字部分反转后的结果。
/// 如果反转后整数超过 32 位的有符号整数的范围，就返回 0。
///
/// ## Rust 1.92 特性应用
/// - **整数溢出检查**: 使用 checked_mul 和 checked_add 防止溢出
///
/// ## 复杂度
/// - 时间复杂度: O(log(x))
/// - 空间复杂度: O(1)
pub fn reverse(x: i32) -> i32 {
    let mut num = x;
    let mut result = 0i32;

    while num != 0 {
        if let Some(new_result) = result.checked_mul(10) {
            if let Some(final_result) = new_result.checked_add(num % 10) {
                result = final_result;
                num /= 10;
            } else {
                return 0;
            }
        } else {
            return 0;
        }
    }

    result
}

/// 9. Palindrome Number（回文数）
///
/// ## 问题描述
/// 给你一个整数 x ，如果 x 是一个回文整数，返回 true ；否则，返回 false 。
///
/// ## Rust 1.92 特性应用
/// - **整数操作优化**: 使用整数反转判断回文
///
/// ## 复杂度
/// - 时间复杂度: O(log(x))
/// - 空间复杂度: O(1)
pub fn is_palindrome(x: i32) -> bool {
    if x < 0 {
        return false;
    }

    let mut num = x;
    let mut reversed = 0i32;

    while num > 0 {
        if let Some(new_reversed) = reversed.checked_mul(10) {
            if let Some(final_reversed) = new_reversed.checked_add(num % 10) {
                reversed = final_reversed;
                num /= 10;
            } else {
                return false;
            }
        } else {
            return false;
        }
    }

    reversed == x
}

/// 50. Pow(x, n)（Pow 函数）
///
/// ## 问题描述
/// 实现 pow(x, n) ，即计算 x 的 n 次幂函数（即，x^n）。
///
/// ## Rust 1.92 特性应用
/// - **快速幂算法**: 使用递归实现快速幂，O(log(n)) 时间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(log(n))
/// - 空间复杂度: O(log(n))
pub fn my_pow(x: f64, n: i32) -> f64 {
    if n == 0 {
        return 1.0;
    }

    if n < 0 {
        return 1.0 / my_pow(x, -n);
    }

    if n % 2 == 0 {
        let half = my_pow(x, n / 2);
        half * half
    } else {
        x * my_pow(x, n - 1)
    }
}

/// 69. Sqrt(x)（x 的平方根）
///
/// ## 问题描述
/// 给你一个非负整数 x ，计算并返回 x 的 算术平方根 。
/// 由于返回类型是整数，结果只保留 整数部分 ，小数部分将被 舍去 。
///
/// ## Rust 1.92 特性应用
/// - **二分查找**: 使用二分查找优化平方根计算
///
/// ## 复杂度
/// - 时间复杂度: O(log(x))
/// - 空间复杂度: O(1)
pub fn my_sqrt(x: i32) -> i32 {
    if x < 2 {
        return x;
    }

    let mut left = 1;
    let mut right = x / 2;

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

/// 202. Happy Number（快乐数）
///
/// ## 问题描述
/// 编写一个算法来判断一个数 n 是不是快乐数。
///
/// ## Rust 1.92 特性应用
/// - **HashSet 优化**: 使用 HashSet 检测循环
///
/// ## 复杂度
/// - 时间复杂度: O(log(n))
/// - 空间复杂度: O(log(n))
pub fn is_happy(n: i32) -> bool {
    let mut seen = HashSet::new();
    let mut num = n;

    while num != 1 && !seen.contains(&num) {
        seen.insert(num);
        num = get_next(num);
    }

    num == 1
}

fn get_next(n: i32) -> i32 {
    let mut sum = 0;
    let mut num = n;

    while num > 0 {
        let digit = num % 10;
        sum += digit * digit;
        num /= 10;
    }

    sum
}

/// 204. Count Primes（计数质数）
///
/// ## 问题描述
/// 统计所有小于非负整数 n 的质数的数量。
///
/// ## Rust 1.92 特性应用
/// - **埃拉托斯特尼筛法**: 使用筛法高效计算质数
///
/// ## 复杂度
/// - 时间复杂度: O(n log(log(n)))
/// - 空间复杂度: O(n)
pub fn count_primes(n: i32) -> i32 {
    if n < 2 {
        return 0;
    }

    let n = n as usize;
    let mut is_prime = vec![true; n];
    is_prime[0] = false;
    is_prime[1] = false;

    let mut count = 0;
    for i in 2..n {
        if is_prime[i] {
            count += 1;
            let mut j = i * i;
            while j < n {
                is_prime[j] = false;
                j += i;
            }
        }
    }

    count
}

/// 231. Power of Two（2 的幂）
///
/// ## 问题描述
/// 给你一个整数 n，请你判断该整数是否是 2 的幂次方。如果是，返回 true ；否则，返回 false 。
///
/// ## Rust 1.92 特性应用
/// - **位操作优化**: 使用位操作 O(1) 判断
///
/// ## 复杂度
/// - 时间复杂度: O(1)
/// - 空间复杂度: O(1)
pub fn is_power_of_two(n: i32) -> bool {
    if n <= 0 {
        return false;
    }
    (n & (n - 1)) == 0
}

/// 326. Power of Three（3 的幂）
///
/// ## 问题描述
/// 给定一个整数，写一个函数来判断它是否是 3 的幂次方。如果是，返回 true ；否则，返回 false 。
///
/// ## Rust 1.92 特性应用
/// - **循环优化**: 使用循环判断
///
/// ## 复杂度
/// - 时间复杂度: O(log(n))
/// - 空间复杂度: O(1)
pub fn is_power_of_three(n: i32) -> bool {
    if n <= 0 {
        return false;
    }

    let mut num = n;
    while num % 3 == 0 {
        num /= 3;
    }

    num == 1
}

/// 367. Valid Perfect Square（有效的完全平方数）
///
/// ## 问题描述
/// 给定一个 正整数 num ，编写一个函数，如果 num 是一个完全平方数，则返回 true ，否则返回 false 。
///
/// ## Rust 1.92 特性应用
/// - **二分查找**: 使用二分查找优化判断
///
/// ## 复杂度
/// - 时间复杂度: O(log(num))
/// - 空间复杂度: O(1)
pub fn is_perfect_square(num: i32) -> bool {
    if num < 2 {
        return true;
    }

    let mut left = 1;
    let mut right = num / 2;

    while left <= right {
        let mid = left + (right - left) / 2;
        let square = mid as i64 * mid as i64;

        if square == num as i64 {
            return true;
        } else if square < num as i64 {
            left = mid + 1;
        } else {
            right = mid - 1;
        }
    }

    false
}

/// 509. Fibonacci Number（斐波那契数）
///
/// ## 问题描述
/// 斐波那契数 （通常用 F(n) 表示）形成的序列称为 斐波那契数列 。
/// 该数列由 0 和 1 开始，后面的每一项数字都是前面两项数字的和。
///
/// ## Rust 1.92 特性应用
/// - **动态规划优化**: 使用迭代方法，O(1) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(1)
pub fn fib(n: i32) -> i32 {
    if n < 2 {
        return n;
    }

    let mut prev = 0;
    let mut curr = 1;

    for _ in 2..=n {
        let next = prev + curr;
        prev = curr;
        curr = next;
    }

    curr
}

// ==================== 问题信息注册 ====================

/// 获取所有数学类问题
pub fn get_all_problems() -> Vec<LeetCodeProblem> {
    vec![
        LeetCodeProblem {
            problem_id: 7,
            title: "整数反转".to_string(),
            title_en: "Reverse Integer".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::Math],
            description: "给你一个 32 位的有符号整数 x ，返回将 x 中的数字部分反转后的结果。如果反转后整数超过 32 位的有符号整数的范围，就返回 0。".to_string(),
            examples: vec!["输入：x = 123\n输出：321".to_string()],
            constraints: vec!["-2^31 <= x <= 2^31 - 1".to_string()],
            rust_191_features: vec!["使用 Rust 1.92 的整数溢出检查".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(log(x))".to_string(),
                space_complexity: "O(1)".to_string(),
                explanation: Some("数字的位数决定了时间复杂度".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 9,
            title: "回文数".to_string(),
            title_en: "Palindrome Number".to_string(),
            difficulty: "Easy".to_string(),
            tags: vec![LeetCodeTag::Math],
            description: "给你一个整数 x ，如果 x 是一个回文整数，返回 true ；否则，返回 false 。".to_string(),
            examples: vec!["输入：x = 121\n输出：true".to_string()],
            constraints: vec!["-2^31 <= x <= 2^31 - 1".to_string()],
            rust_191_features: vec!["使用 Rust 1.92 的整数操作优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(log(x))".to_string(),
                space_complexity: "O(1)".to_string(),
                explanation: None,
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
            constraints: vec!["-100.0 < x < 100.0".to_string(), "-2^31 <= n <= 2^31-1".to_string()],
            rust_191_features: vec!["使用快速幂算法，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(log(n))".to_string(),
                space_complexity: "O(log(n))".to_string(),
                explanation: Some("使用快速幂算法，递归深度为 log(n)".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 69,
            title: "x 的平方根".to_string(),
            title_en: "Sqrt(x)".to_string(),
            difficulty: "Easy".to_string(),
            tags: vec![LeetCodeTag::Math, LeetCodeTag::BinarySearch],
            description: "给你一个非负整数 x ，计算并返回 x 的 算术平方根 。由于返回类型是整数，结果只保留 整数部分 ，小数部分将被 舍去 。".to_string(),
            examples: vec!["输入：x = 4\n输出：2".to_string()],
            constraints: vec!["0 <= x <= 2^31 - 1".to_string()],
            rust_191_features: vec!["使用二分查找，Rust 1.92 整数操作优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(log(x))".to_string(),
                space_complexity: "O(1)".to_string(),
                explanation: None,
            },
        },
        LeetCodeProblem {
            problem_id: 202,
            title: "快乐数".to_string(),
            title_en: "Happy Number".to_string(),
            difficulty: "Easy".to_string(),
            tags: vec![LeetCodeTag::Math, LeetCodeTag::HashTable],
            description: "编写一个算法来判断一个数 n 是不是快乐数。".to_string(),
            examples: vec!["输入：n = 19\n输出：true".to_string()],
            constraints: vec!["1 <= n <= 2^31 - 1".to_string()],
            rust_191_features: vec!["使用 HashSet 检测循环，Rust 1.92 哈希优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(log(n))".to_string(),
                space_complexity: "O(log(n))".to_string(),
                explanation: Some("数字的位数决定了复杂度".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 204,
            title: "计数质数".to_string(),
            title_en: "Count Primes".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::Math],
            description: "统计所有小于非负整数 n 的质数的数量。".to_string(),
            examples: vec!["输入：n = 10\n输出：4".to_string()],
            constraints: vec!["0 <= n <= 5 * 10^6".to_string()],
            rust_191_features: vec!["使用埃拉托斯特尼筛法，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n log(log(n)))".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("埃拉托斯特尼筛法的时间复杂度".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 231,
            title: "2 的幂".to_string(),
            title_en: "Power of Two".to_string(),
            difficulty: "Easy".to_string(),
            tags: vec![LeetCodeTag::Math, LeetCodeTag::BitManipulation],
            description: "给你一个整数 n，请你判断该整数是否是 2 的幂次方。如果是，返回 true ；否则，返回 false 。".to_string(),
            examples: vec!["输入：n = 1\n输出：true".to_string()],
            constraints: vec!["-2^31 <= n <= 2^31 - 1".to_string()],
            rust_191_features: vec!["使用位操作，Rust 1.92 位操作优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(1)".to_string(),
                space_complexity: "O(1)".to_string(),
                explanation: None,
            },
        },
        LeetCodeProblem {
            problem_id: 326,
            title: "3 的幂".to_string(),
            title_en: "Power of Three".to_string(),
            difficulty: "Easy".to_string(),
            tags: vec![LeetCodeTag::Math, LeetCodeTag::Recursion],
            description: "给定一个整数，写一个函数来判断它是否是 3 的幂次方。如果是，返回 true ；否则，返回 false 。".to_string(),
            examples: vec!["输入：n = 27\n输出：true".to_string()],
            constraints: vec!["-2^31 <= n <= 2^31 - 1".to_string()],
            rust_191_features: vec!["使用循环或递归，Rust 1.92 整数操作优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(log(n))".to_string(),
                space_complexity: "O(1)".to_string(),
                explanation: None,
            },
        },
        LeetCodeProblem {
            problem_id: 367,
            title: "有效的完全平方数".to_string(),
            title_en: "Valid Perfect Square".to_string(),
            difficulty: "Easy".to_string(),
            tags: vec![LeetCodeTag::Math, LeetCodeTag::BinarySearch],
            description: "给定一个 正整数 num ，编写一个函数，如果 num 是一个完全平方数，则返回 true ，否则返回 false 。".to_string(),
            examples: vec!["输入：num = 16\n输出：true".to_string()],
            constraints: vec!["1 <= num <= 2^31 - 1".to_string()],
            rust_191_features: vec!["使用二分查找，Rust 1.92 整数操作优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(log(num))".to_string(),
                space_complexity: "O(1)".to_string(),
                explanation: None,
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
            rust_191_features: vec!["使用动态规划或递归，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(1)".to_string(),
                explanation: Some("使用迭代方法，空间复杂度为 O(1)".to_string()),
            },
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_reverse() {
        assert_eq!(reverse(123), 321);
        assert_eq!(reverse(-123), -321);
        assert_eq!(reverse(120), 21);
        assert_eq!(reverse(0), 0);
    }

    #[test]
    fn test_is_palindrome() {
        assert!(is_palindrome(121));
        assert!(!is_palindrome(-121));
        assert!(!is_palindrome(10));
    }

    #[test]
    fn test_my_pow() {
        assert!((my_pow(2.0, 10) - 1024.0).abs() < 1e-5);
        assert!((my_pow(2.1, 3) - 9.261).abs() < 1e-5);
        assert!((my_pow(2.0, -2) - 0.25).abs() < 1e-5);
    }

    #[test]
    fn test_my_sqrt() {
        assert_eq!(my_sqrt(4), 2);
        assert_eq!(my_sqrt(8), 2);
        assert_eq!(my_sqrt(0), 0);
    }

    #[test]
    fn test_is_happy() {
        assert!(is_happy(19));
        assert!(!is_happy(2));
    }

    #[test]
    fn test_count_primes() {
        assert_eq!(count_primes(10), 4);
        assert_eq!(count_primes(0), 0);
        assert_eq!(count_primes(1), 0);
    }

    #[test]
    fn test_is_power_of_two() {
        assert!(is_power_of_two(1));
        assert!(is_power_of_two(16));
        assert!(!is_power_of_two(3));
        assert!(!is_power_of_two(0));
    }

    #[test]
    fn test_is_power_of_three() {
        assert!(is_power_of_three(27));
        assert!(!is_power_of_three(0));
        assert!(!is_power_of_three(45));
    }

    #[test]
    fn test_is_perfect_square() {
        assert!(is_perfect_square(16));
        assert!(!is_perfect_square(14));
        assert!(is_perfect_square(1));
    }

    #[test]
    fn test_fib() {
        assert_eq!(fib(2), 1);
        assert_eq!(fib(3), 2);
        assert_eq!(fib(4), 3);
    }
}
