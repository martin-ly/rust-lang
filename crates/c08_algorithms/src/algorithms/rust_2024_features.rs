//! Rust 2024 / Rust 1.90 语言特性精选示例
//!
//! 本模块演示在算法场景中使用 2024 edition 成熟语法：
//! - let-else 早返回
//! - try 块聚合 `Result`
//! - `Option::is_some_and`/`bool::then_some`
//! - 返回位置 `impl Trait`（RPITIT）
//! - 从不返回类型 `!`

use anyhow::{anyhow, Result};

/// let-else：从切片中取首元素并早返回
pub fn first_or_error(data: &[i32]) -> Result<i32> {
    let Some(&first) = data.first() else { return Err(anyhow!("empty")); };
    Ok(first)
}

/// try 块：将多步计算聚合为一个 Result
pub fn sum_three_try(a: Result<i32>, b: Result<i32>, c: Result<i32>) -> Result<i32> {
    let x = a?;
    let y = b?;
    let z = c?;
    Ok(x + y + z)
}

/// `is_some_and`：更直观的 Option 条件判断
pub fn has_even(option: Option<i32>) -> bool {
    option.is_some_and(|v| v % 2 == 0)
}

/// 返回位置 impl Trait（RPITIT）：返回迭代器隐藏具体类型
pub fn range_even_iter(start: i32, end: i32) -> impl Iterator<Item = i32> {
    (start..end).filter(|x| x % 2 == 0)
}

/// 从不返回类型 `!`：用于致命错误的不可返回函数
#[allow(dead_code)]
pub fn abort_with(message: &str) -> ! {
    panic!("fatal: {}", message)
}


