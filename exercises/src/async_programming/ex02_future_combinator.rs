//! # 练习 2: Future 组合
//!
//! **难度**: Medium  
//! **考点**: futures::future::join、并发执行
//!
//! ## 题目描述
//!
//! 使用 Future 组合子并发执行多个异步任务。

use std::future::Future;

/// 并发执行两个 Future，返回结果元组
pub async fn run_two<T1, T2, F1, F2>(f1: F1, f2: F2) -> (T1, T2)
where
    F1: Future<Output = T1>,
    F2: Future<Output = T2>,
{
    futures::future::join(f1, f2).await
}

/// 并发计算多个数字的平方
pub async fn concurrent_squares(values: Vec<i32>) -> Vec<i32> {
    let futures: Vec<_> = values.into_iter().map(|v| async_square(v)).collect();
    futures::future::join_all(futures).await
}

async fn async_square(n: i32) -> i32 {
    n * n
}

/// 返回先完成的 Future 的结果
pub async fn race_futures<T, F1, F2>(f1: F1, f2: F2) -> T
where
    F1: Future<Output = T> + Unpin,
    F2: Future<Output = T> + Unpin,
{
    futures::future::select(f1, f2).await.factor_first().0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_run_two() {
        let f1 = async { 1 };
        let f2 = async { "hello" };
        let (a, b) = run_two(f1, f2).await;
        assert_eq!(a, 1);
        assert_eq!(b, "hello");
    }

    #[tokio::test]
    async fn test_concurrent_squares() {
        let values = vec![1, 2, 3, 4, 5];
        let result = concurrent_squares(values).await;
        assert_eq!(result, vec![1, 4, 9, 16, 25]);
    }
}
