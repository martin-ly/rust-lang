//! # 练习 1: 基础 async/await
//!
//! **难度**: Easy  
//! **考点**: async fn、.await、异步函数组合
//!
//! ## 题目描述
//!
//! 实现简单的异步函数，理解 async/await 的基本用法。

/// 异步返回一个数字的平方
pub async fn async_square(n: i32) -> i32 {
    n * n
}

/// 异步计算两个数字的和
pub async fn async_add(a: i32, b: i32) -> i32 {
    a + b
}

/// 顺序执行两个异步操作并返回结果之和
pub async fn sequential_sum(a: i32, b: i32) -> i32 {
    let x = async_square(a).await;
    let y = async_square(b).await;
    x + y
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_async_square() {
        assert_eq!(async_square(5).await, 25);
        assert_eq!(async_square(-3).await, 9);
    }

    #[tokio::test]
    async fn test_async_add() {
        assert_eq!(async_add(2, 3).await, 5);
    }

    #[tokio::test]
    async fn test_sequential_sum() {
        assert_eq!(sequential_sum(3, 4).await, 25); // 9 + 16
    }
}
