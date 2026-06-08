//! # 练习 5: 超时与重试 / Exercise 5: Timeout and Retry
//!
//! **难度 / Difficulty**: Hard  
//! **考点 / Focus**: tokio::time::timeout、重试策略
//!   tokio::time::timeout, retry strategies
//!
//! ## 题目描述 / Problem Description
//!
//! 实现带有超时和重试机制的异步操作。
//! Implement async operations with timeout and retry mechanisms.

use std::future::Future;
use std::time::Duration;

/// 带超时的异步操作
/// Async operation with timeout
pub async fn with_timeout<T, F>(duration: Duration, f: F) -> Result<T, &'static str>
where
    F: Future<Output = T>,
{
    match tokio::time::timeout(duration, f).await {
        Ok(result) => Ok(result),
        Err(_) => Err("操作超时 / Operation timed out"),
    }
}

/// 简单重试：如果失败则重试指定次数
/// Simple retry: retries up to max_attempts on failure
pub async fn retry<F, Fut, T>(mut f: F, max_attempts: usize) -> Result<T, &'static str>
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<T, &'static str>>,
{
    for _ in 0..max_attempts {
        match f().await {
            Ok(val) => return Ok(val),
            Err(_) => continue,
        }
    }
    Err("所有重试均失败 / All retries failed")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_with_timeout_ok() {
        let result = with_timeout(Duration::from_secs(1), async { 42 }).await;
        assert_eq!(result, Ok(42));
    }

    #[tokio::test]
    async fn test_with_timeout_fail() {
        let result = with_timeout(Duration::from_millis(10), async {
            tokio::time::sleep(Duration::from_millis(100)).await;
            42
        })
        .await;
        assert_eq!(result, Err("操作超时 / Operation timed out"));
    }

    #[tokio::test]
    async fn test_retry_success() {
        let mut counter = 0;
        let result = retry(
            || {
                counter += 1;
                async move {
                    if counter >= 3 {
                        Ok("success")
                    } else {
                        Err("not yet")
                    }
                }
            },
            5,
        )
        .await;
        assert_eq!(result, Ok("success"));
    }

    #[tokio::test]
    async fn test_retry_exhausted() {
        let result = retry(|| async { Err::<i32, _>("always fails") }, 3).await;
        assert_eq!(result, Err("所有重试均失败 / All retries failed"));
    }
}
