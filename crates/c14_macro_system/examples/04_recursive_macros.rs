//! # 示例04: 递归宏
//!
//! 演示递归宏的使用

use c14_macro_system::{count, max};

/// 递归反转
#[allow(unused_macros)]
macro_rules! reverse {
    () => { () };
    ($head:expr) => { ($head,) };
    ($head:expr, $($tail:expr),+ $(,)?) => {
        (reverse!($($tail),+), $head)
    };
}

/// 列表求和
macro_rules! sum {
    () => { 0 };
    ($x:expr) => { $x };
    ($x:expr, $($rest:expr),+ $(,)?) => {
        $x + sum!($($rest),+)
    };
}

/// 找最小值
macro_rules! min {
    ($x:expr) => { $x };
    ($x:expr, $($rest:expr),+ $(,)?) => {
        {
            let rest_min = min!($($rest),+);
            if $x < rest_min { $x } else { rest_min }
        }
    };
}

fn main() {
    println!("=== 递归宏示例 ===\n");

    // 1. 计数
    println!("1. 递归计数:");
    println!("count!() = {}", count!());
    println!("count!(1) = {}", count!(1));
    println!("count!(1, 2, 3) = {}", count!(1, 2, 3));
    println!("count!(1, 2, 3, 4, 5, 6, 7, 8, 9, 10) = {}",
        count!(1, 2, 3, 4, 5, 6, 7, 8, 9, 10));
    println!();

    // 2. 找最大值
    println!("2. 递归找最大值:");
    println!("max!(42) = {}", max!(42));
    println!("max!(10, 25, 15) = {}", max!(10, 25, 15));
    println!("max!(100, 50, 200, 75, 150) = {}",
        max!(100, 50, 200, 75, 150));
    println!();

    // 3. 列表求和
    println!("3. 递归求和:");
    println!("sum!() = {}", sum!());
    println!("sum!(5) = {}", sum!(5));
    println!("sum!(1, 2, 3, 4, 5) = {}", sum!(1, 2, 3, 4, 5));
    println!("sum!(10, 20, 30, 40, 50) = {}", sum!(10, 20, 30, 40, 50));
    println!();

    // 4. 找最小值
    println!("4. 递归找最小值:");
    println!("min!(42) = {}", min!(42));
    println!("min!(10, 25, 15) = {}", min!(10, 25, 15));
    println!("min!(100, 50, 200, 75, 150) = {}",
        min!(100, 50, 200, 75, 150));
    println!();

    println!("=== 示例完成 ===");
}

