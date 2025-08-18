/// 计算两个数之和
/// Calculate the sum of two numbers
///
/// # Example
/// ```
/// assert_eq!(add(2, 3), 5);
/// ```
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

fn main() {
    println!("2 + 3 = {}", add(2, 3));
} 