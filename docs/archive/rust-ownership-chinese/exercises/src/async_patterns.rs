//! 异步所有权模式
//!
//! async/await与所有权系统的交互

use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

// ============================================
// Future基础
// ============================================

/// 自定义Future实现（使用Tokio的sleep）
pub async fn delay(duration: std::time::Duration) {
    tokio::time::sleep(duration).await;
}

// ============================================
// async/await所有权模式
// ============================================

/// 模式1: 跨await持有引用
/// 
/// async函数被编译为状态机，所有跨await的变量必须被存储
pub async fn holding_across_await() {
    let data = String::from("hello");
    
    // data被存储在生成的Future中
    let future = async {
        println!("Before await: {}", data);
        delay(std::time::Duration::from_millis(10)).await;
        println!("After await: {}", data);
    };
    
    future.await;
}

/// 模式2: 选择正确的持有方式
pub async fn ownership_strategies() {
    let data = vec![1, 2, 3];
    
    // 策略1: 移动所有权
    let fut1 = async move {
        println!("{:?}", data);
    };
    
    // 策略2: 共享所有权
    let data = Arc::new(vec![1, 2, 3]);
    let data2 = Arc::clone(&data);
    let fut2 = async move {
        println!("{:?}", data2);
    };
    
    fut1.await;
    fut2.await;
    println!("{:?}", data);
}

use std::sync::Arc;

/// 模式3: Pin与Unpin在异步中的重要性
pub async fn pin_requirement() {
    let fut = async {
        let local = String::from("pinned");
        delay(std::time::Duration::from_millis(10)).await;
        println!("{}", local);
    };
    
    // fut.await 自动处理Pin
    fut.await;
}

// ============================================
// Stream模式
// ============================================

/// 自定义Stream
pub struct Counter {
    count: u32,
    max: u32,
}

impl Counter {
    pub fn new(max: u32) -> Self {
        Self { count: 0, max }
    }
}

impl Future for Counter {
    type Output = Option<u32>;
    
    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        if self.count < self.max {
            self.count += 1;
            Poll::Ready(Some(self.count))
        } else {
            Poll::Ready(None)
        }
    }
}

// ============================================
// 并发异步模式
// ============================================

/// select!模式 - 等待多个Future
pub async fn select_pattern() {
    let fut1 = delay(std::time::Duration::from_millis(50));
    let fut2 = delay(std::time::Duration::from_millis(100));
    
    // 简化的select实现
    tokio::select! {
        _ = fut1 => println!("First completed"),
        _ = fut2 => println!("Second completed"),
    }
}

/// join!模式 - 等待所有Future
pub async fn join_pattern() {
    let fut1 = async { 1 };
    let fut2 = async { 2 };
    
    let (a, b) = tokio::join!(fut1, fut2);
    println!("Results: {}, {}", a, b);
}

// ============================================
// 测试
// ============================================

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_delay() {
        let start = std::time::Instant::now();
        delay(std::time::Duration::from_millis(10)).await;
        assert!(start.elapsed() >= std::time::Duration::from_millis(10));
    }
    
    #[tokio::test]
    async fn test_holding_across_await() {
        holding_across_await().await;
    }
    
    #[tokio::test]
    async fn test_counter() {
        let mut counter = Counter::new(3);
        let mut results = vec![];
        
        while let Poll::Ready(Some(v)) = 
            Pin::new(&mut counter).poll(&mut Context::from_waker(
                &std::task::Waker::noop()
            )) {
            results.push(v);
        }
        
        assert_eq!(results, vec![1, 2, 3]);
    }
}
