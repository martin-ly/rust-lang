//! 异步编程集成测试
//! 
//! 测试Rust异步编程的各种特性

use c06_async::*;
use tokio::time::{sleep, Duration};

#[tokio::test]
async fn test_async_functions() {
    let result = async_add(5, 3).await;
    assert_eq!(result, 8);
}

#[tokio::test]
async fn test_async_error_handling() {
    let success_result = async_divide(10, 2).await;
    assert!(success_result.is_ok());
    assert_eq!(success_result.unwrap(), 5);
    
    let error_result = async_divide(10, 0).await;
    assert!(error_result.is_err());
}

#[tokio::test]
async fn test_concurrent_execution() {
    let start = std::time::Instant::now();
    
    let (result1, result2) = tokio::join!(
        async_task("task1", 100),
        async_task("task2", 150)
    );
    
    let duration = start.elapsed();
    
    assert_eq!(result1, "task1 completed");
    assert_eq!(result2, "task2 completed");
    
    // 并发执行应该比串行执行快
    assert!(duration < Duration::from_millis(300));
}

#[tokio::test]
async fn test_stream_processing() {
    let mut stream = create_number_stream(5);
    let mut results = Vec::new();
    
    while let Some(value) = stream.next().await {
        results.push(value);
    }
    
    assert_eq!(results, vec![0, 1, 2, 3, 4]);
}

#[tokio::test]
async fn test_timeout_handling() {
    let result = with_timeout(
        async {
            sleep(Duration::from_millis(50)).await;
            "completed"
        },
        Duration::from_millis(100)
    ).await;
    
    assert_eq!(result, Some("completed"));
    
    let timeout_result = with_timeout(
        async {
            sleep(Duration::from_millis(200)).await;
            "completed"
        },
        Duration::from_millis(100)
    ).await;
    
    assert_eq!(timeout_result, None);
}

#[tokio::test]
async fn test_channel_communication() {
    let (tx, mut rx) = tokio::sync::mpsc::channel(10);
    
    // 发送任务
    tokio::spawn(async move {
        for i in 0..5 {
            tx.send(i).await.unwrap();
            sleep(Duration::from_millis(10)).await;
        }
    });
    
    // 接收任务
    let mut received = Vec::new();
    while let Some(value) = rx.recv().await {
        received.push(value);
    }
    
    assert_eq!(received, vec![0, 1, 2, 3, 4]);
}

#[tokio::test]
async fn test_mutex_usage() {
    let counter = std::sync::Arc::new(tokio::sync::Mutex::new(0));
    let mut handles = Vec::new();
    
    // 创建多个异步任务
    for _ in 0..10 {
        let counter = std::sync::Arc::clone(&counter);
        let handle = tokio::spawn(async move {
            let mut count = counter.lock().await;
            *count += 1;
        });
        handles.push(handle);
    }
    
    // 等待所有任务完成
    for handle in handles {
        handle.await.unwrap();
    }
    
    let final_count = *counter.lock().await;
    assert_eq!(final_count, 10);
}

// 辅助函数
async fn async_add(a: i32, b: i32) -> i32 {
    sleep(Duration::from_millis(10)).await;
    a + b
}

async fn async_divide(a: i32, b: i32) -> Result<i32, String> {
    sleep(Duration::from_millis(10)).await;
    if b == 0 {
        Err("Division by zero".to_string())
    } else {
        Ok(a / b)
    }
}

async fn async_task(name: &str, delay_ms: u64) -> String {
    sleep(Duration::from_millis(delay_ms)).await;
    format!("{} completed", name)
}

async fn create_number_stream(count: usize) -> impl futures::Stream<Item = usize> {
    futures::stream::iter(0..count)
}

async fn with_timeout<F, T>(
    future: F,
    timeout: Duration,
) -> Option<T>
where
    F: std::future::Future<Output = T>,
{
    match tokio::time::timeout(timeout, future).await {
        Ok(result) => Some(result),
        Err(_) => None,
    }
}
