// 宏与元编程：macro_rules! 基本用法示例 Macro & Metaprogramming: macro_rules! Example
macro_rules! add {
    ($a:expr, $b:expr) => { $a + $b };
}

fn main() {
    let sum = add!(3, 4);
    println!("Sum: {}", sum);
} 