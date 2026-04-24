//! # 练习 3: Tokio 任务
//!
//! **难度**: Medium  
//! **考点**: tokio::spawn、JoinHandle、任务并发
//!
//! ## 题目描述
//!
//! 使用 Tokio 的任务系统并发执行异步操作。

use tokio::task::JoinHandle;

/// 生成多个 Tokio 任务并发计算
pub async fn spawn_computations(values: Vec<i32>) -> Vec<i32> {
    let mut handles: Vec<JoinHandle<i32>> = Vec::new();

    for v in values {
        let handle = tokio::spawn(async move { v * v });
        handles.push(handle);
    }

    let mut results = Vec::new();
    for handle in handles {
        results.push(handle.await.unwrap());
    }
    results
}

/// 生成任务并收集结果（使用 try_join）
pub async fn spawn_with_retry(values: Vec<i32>) -> Result<Vec<i32>, String> {
    let mut handles = Vec::new();

    for v in values {
        let handle = tokio::spawn(async move {
            if v < 0 {
                Err("负数不允许".to_string())
            } else {
                Ok(v * 2)
            }
        });
        handles.push(handle);
    }

    let mut results = Vec::new();
    for handle in handles {
        match handle.await.unwrap() {
            Ok(val) => results.push(val),
            Err(e) => return Err(e),
        }
    }
    Ok(results)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_spawn_computations() {
        let values = vec![1, 2, 3, 4];
        let mut result = spawn_computations(values).await;
        result.sort();
        assert_eq!(result, vec![1, 4, 9, 16]);
    }

    #[tokio::test]
    async fn test_spawn_with_retry_ok() {
        let values = vec![1, 2, 3];
        let result = spawn_with_retry(values).await;
        assert_eq!(result.unwrap(), vec![2, 4, 6]);
    }

    #[tokio::test]
    async fn test_spawn_with_retry_err() {
        let values = vec![1, -1, 3];
        let result = spawn_with_retry(values).await;
        assert!(result.is_err());
    }
}
