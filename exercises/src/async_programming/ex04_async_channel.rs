//! # 练习 4: 异步通道
//!
//! **难度**: Medium  
//! **考点**: tokio::sync::mpsc、异步消息传递
//!
//! ## 题目描述
//!
//! 使用 Tokio 的异步通道进行任务间通信。

use tokio::sync::mpsc;

/// 使用异步通道发送和接收消息
pub async fn async_channel_example(items: Vec<i32>) -> Vec<i32> {
    let (tx, mut rx) = mpsc::channel::<i32>(16);

    tokio::spawn(async move {
        for item in items {
            if tx.send(item * 2).await.is_err() {
                break;
            }
        }
    });

    let mut results = Vec::new();
    while let Some(v) = rx.recv().await {
        results.push(v);
    }
    results
}

/// 多生产者单消费者
pub async fn multi_producer(values: Vec<Vec<i32>>) -> Vec<i32> {
    let (tx, mut rx) = mpsc::channel::<i32>(32);

    for batch in values {
        let tx = tx.clone();
        tokio::spawn(async move {
            for v in batch {
                let _ = tx.send(v).await;
            }
        });
    }

    // 关闭原始发送端，当所有克隆都结束时通道会关闭
    drop(tx);

    let mut results = Vec::new();
    while let Some(v) = rx.recv().await {
        results.push(v);
    }
    results.sort();
    results
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_async_channel() {
        let items = vec![1, 2, 3, 4, 5];
        let result = async_channel_example(items).await;
        assert_eq!(result, vec![2, 4, 6, 8, 10]);
    }

    #[tokio::test]
    async fn test_multi_producer() {
        let batches = vec![vec![1, 2], vec![3, 4], vec![5, 6]];
        let result = multi_producer(batches).await;
        assert_eq!(result, vec![1, 2, 3, 4, 5, 6]);
    }
}
