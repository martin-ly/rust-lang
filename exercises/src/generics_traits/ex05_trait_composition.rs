//! # 练习 5: 特质组合
//!
//! **难度**: Hard  
//! **考点**: trait bound 组合、supertrait
//!
//! ## 题目描述
//!
//! 定义一个 PrintableComparable 特质，它要求类型同时实现
//! Display 和 PartialOrd，并在此基础上添加新方法。

use std::fmt::Display;

/// 可打印且可比较的特质
pub trait PrintableComparable: Display + PartialOrd {
    /// 返回自我描述，包含当前值和与其他值的比较结果
    fn describe_cmp(&self, other: &Self) -> String;

    /// 判断自身是否在指定范围内（包含边界）
    fn in_range(&self, low: &Self, high: &Self) -> bool;
}

impl<T: Display + PartialOrd> PrintableComparable for T {
    fn describe_cmp(&self, other: &Self) -> String {
        if self > other {
            format!("{} 大于 {}", self, other)
        } else if self < other {
            format!("{} 小于 {}", self, other)
        } else {
            format!("{} 等于 {}", self, other)
        }
    }

    fn in_range(&self, low: &Self, high: &Self) -> bool {
        self >= low && self <= high
    }
}

/// 接受任何实现了 PrintableComparable 的类型
pub fn print_comparison<T: PrintableComparable>(a: &T, b: &T) {
    println!("{}", a.describe_cmp(b));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_describe_cmp() {
        assert_eq!(10.describe_cmp(&5), "10 大于 5");
        assert_eq!(3.describe_cmp(&7), "3 小于 7");
        assert_eq!(4.describe_cmp(&4), "4 等于 4");
    }

    #[test]
    fn test_in_range() {
        assert!(10i32.in_range(&5, &15));
        assert!(!20i32.in_range(&5, &15));
        assert!(5i32.in_range(&5, &15));
    }

    #[test]
    fn test_with_f64() {
        let a = 3.14;
        assert_eq!(a.describe_cmp(&2.71), "3.14 大于 2.71");
        assert!(a.in_range(&3.0, &4.0));
    }
}
