//! Prusti 合约验证示例。
//!
//! 使用 `#[cfg(prusti)]` 包裹 Prusti 注解；普通 `cargo check` 会跳过这些注解，
//! 仅编译安全占位实现。
#![allow(dead_code, unexpected_cfgs)]

#[cfg(prusti)]
mod verified {
    //! 带 Prusti 合约的函数。

    use prusti_contracts::*;

    /// 绝对值。
    ///
    /// 前置条件排除 `i32::MIN`，避免 `-i32::MIN` 溢出。
    #[requires(x != i32::MIN)]
    #[ensures(result >= 0)]
    pub fn abs(x: i32) -> i32 {
        if x < 0 { -x } else { x }
    }

    /// 最大值。
    #[requires(true)]
    #[ensures(result >= a && result >= b)]
    #[ensures(result == a || result == b)]
    pub fn max(a: i32, b: i32) -> i32 {
        if a > b { a } else { b }
    }

    /// 两数之和。
    #[requires(true)]
    #[ensures(result == a + b)]
    pub fn sum(a: i32, b: i32) -> i32 {
        a + b
    }
}

#[cfg(not(prusti))]
mod verified {
    //! 普通编译时使用的占位实现。

    /// 绝对值。
    pub fn abs(x: i32) -> i32 {
        if x < 0 { -x } else { x }
    }

    /// 最大值。
    pub fn max(a: i32, b: i32) -> i32 {
        if a > b { a } else { b }
    }

    /// 两数之和。
    pub fn sum(a: i32, b: i32) -> i32 {
        a + b
    }
}

fn main() {
    println!(
        "Run with Prusti to verify contracts; normal cargo check uses the stub implementations."
    );
    let _ = verified::abs(-5);
    let _ = verified::max(3, 7);
    let _ = verified::sum(2, 3);
}
