//! 异步编程模块集成测试套件 / Async Programming Module Integration Test Suite

use std::sync::Arc;

/// 测试异步函数集成
#[test]
fn test_async_function_integration() {
    async fn async_add(a: i32, b: i32) -> i32 {
        a + b
    }

    let rt = tokio::runtime::Runtime::new().unwrap();
    let result = rt.block_on(async_add(3, 4));
    assert_eq!(result, 7);
}

/// 测试Future集成
#[test]
fn test_future_integration() {
    use std::future::Future;
    use std::pin::Pin;
    use std::task::{Context, Poll};

    struct SimpleFuture {
        value: i32,
    }

    impl Future for SimpleFuture {
        type Output = i32;

        fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
            Poll::Ready(self.value)
        }
    }

    let rt = tokio::runtime::Runtime::new().unwrap();
    let future = SimpleFuture { value: 42 };
    let result = rt.block_on(future);
    assert_eq!(result, 42);
}

/// 测试异步并发集成
#[test]
fn test_async_concurrency_integration() {
    async fn async_task(id: i32) -> i32 {
        id * 2
    }

    let rt = tokio::runtime::Runtime::new().unwrap();
    let result = rt.block_on(async {
        let task1 = async_task(1);
        let task2 = async_task(2);

        let (r1, r2) = tokio::join!(task1, task2);
        r1 + r2
    });

    assert_eq!(result, 6);
}

/// 测试异步错误处理集成
#[test]
fn test_async_error_handling_integration() {
    async fn async_divide(a: i32, b: i32) -> Result<i32, String> {
        if b == 0 {
            Err("Division by zero".to_string())
        } else {
            Ok(a / b)
        }
    }

    let rt = tokio::runtime::Runtime::new().unwrap();
    assert_eq!(rt.block_on(async_divide(10, 2)), Ok(5));
    assert!(rt.block_on(async_divide(10, 0)).is_err());
}

/// 测试异步流集成
#[test]
fn test_async_stream_integration() {
    use futures::stream::{self, StreamExt};

    let rt = tokio::runtime::Runtime::new().unwrap();
    let result = rt.block_on(async {
        let stream = stream::iter(vec![1, 2, 3, 4, 5]);
        stream.fold(0i32, |acc, x| async move { acc + x }).await
    });

    assert_eq!(result, 15);
}

/// 测试异步同步原语集成
#[test]
fn test_async_sync_primitives_integration() {
    use tokio::sync::Mutex;

    let rt = tokio::runtime::Runtime::new().unwrap();
    let result = rt.block_on(async {
        let mutex = Arc::new(Mutex::new(0));
        let mutex_clone = Arc::clone(&mutex);

        tokio::spawn(async move {
            let mut value = mutex_clone.lock().await;
            *value += 1;
        }).await.unwrap();

        let value = mutex.lock().await;
        *value
    });

    assert_eq!(result, 1);
}
