//! # 示例02: 宏模式匹配
//!
//! 演示宏中的模式匹配功能

/// 支持多种模式的计算宏
macro_rules! calc {
    // 加法
    (add $a:expr, $b:expr) => {
        $a + $b
    };
    // 减法
    (sub $a:expr, $b:expr) => {
        $a - $b
    };
    // 乘法
    (mul $a:expr, $b:expr) => {
        $a * $b
    };
    // 除法
    (div $a:expr, $b:expr) => {
        $a / $b
    };
    // 求值
    (eval $e:expr) => {
        $e
    };
}

/// 类型转换宏
macro_rules! cast {
    ($val:expr => $ty:ty) => {
        $val as $ty
    };
}

fn main() {
    println!("=== 宏模式匹配示例 ===\n");

    // 1. 四则运算
    println!("1. 四则运算:");
    println!("add 10, 5 = {}", calc!(add 10, 5));
    println!("sub 10, 5 = {}", calc!(sub 10, 5));
    println!("mul 10, 5 = {}", calc!(mul 10, 5));
    println!("div 10, 5 = {}", calc!(div 10, 5));
    println!();

    // 2. 表达式求值
    println!("2. 表达式求值:");
    println!("eval (2 + 3) * 4 = {}", calc!(eval (2 + 3) * 4));
    println!();

    // 3. 类型转换
    println!("3. 类型转换:");
    let int_val = 42;
    let float_val = cast!(int_val => f64);
    println!("{} (i32) => {} (f64)", int_val, float_val);
    println!();

    println!("=== 示例完成 ===");
}
