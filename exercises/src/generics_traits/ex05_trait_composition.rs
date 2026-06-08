//! # 练习 5: 特质组合 / Exercise 5: Trait Composition
//!
//! **难度 / Difficulty**: Hard  
//! **考点 / Focus**: trait bound 组合、supertrait
//!   Trait bound composition, supertraits
//!
//! ## 题目描述 / Problem Description
//!
//! 定义一个 PrintableComparable 特质，它要求类型同时实现
//! Display 和 PartialOrd，并在此基础上添加新方法。
//! Define a PrintableComparable trait requiring Display + PartialOrd,
//! adding new methods on top of those bounds.

#![allow(clippy::approx_constant)]
use std::fmt::Display;

/// 可打印且可比较的特质 / Printable and comparable trait
pub trait PrintableComparable: Display + PartialOrd {
    /// 返回自我描述，包含当前值和与其他值的比较结果
    /// Returns self-description with current value and comparison result
    fn describe_cmp(&self, other: &Self) -> String;

    /// 判断自身是否在指定范围内（包含边界）
    /// Checks whether self is within the specified range (inclusive)
    fn in_range(&self, low: &Self, high: &Self) -> bool;
}

impl<T: Display + PartialOrd> PrintableComparable for T {
    fn describe_cmp(&self, other: &Self) -> String {
        if self > other {
            format!(
                "{} 大于 {} / {} is greater than {}",
                self, other, self, other
            )
        } else if self < other {
            format!("{} 小于 {} / {} is less than {}", self, other, self, other)
        } else {
            format!("{} 等于 {} / {} equals {}", self, other, self, other)
        }
    }

    fn in_range(&self, low: &Self, high: &Self) -> bool {
        self >= low && self <= high
    }
}

/// 接受任何实现了 PrintableComparable 的类型
/// Accepts any type implementing PrintableComparable
pub fn print_comparison<T: PrintableComparable>(a: &T, b: &T) {
    println!("{}", a.describe_cmp(b));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_describe_cmp() {
        assert_eq!(10.describe_cmp(&5), "10 大于 5 / 10 is greater than 5");
        assert_eq!(3.describe_cmp(&7), "3 小于 7 / 3 is less than 7");
        assert_eq!(4.describe_cmp(&4), "4 等于 4 / 4 equals 4");
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
        assert_eq!(
            a.describe_cmp(&2.71),
            "3.14 大于 2.71 / 3.14 is greater than 2.71"
        );
        assert!(a.in_range(&3.0, &4.0));
    }
}
