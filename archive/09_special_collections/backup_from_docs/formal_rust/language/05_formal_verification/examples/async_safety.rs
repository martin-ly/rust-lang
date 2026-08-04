// 异步/并发安全性示例
// 工程意义：演示Rust async/await 任务调度下的Send/Sync安全约束，适用于Kani/Prusti等工具验证
use std::sync::Arc;
use tokio::sync::Mutex;

#[tokio::main]
async fn main() {
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];
    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = tokio::spawn(async move {
            let mut num = counter.lock().await;
            *num += 1;
        });
        handles.push(handle);
    }
    for handle in handles {
        handle.await.unwrap();
    }
    assert_eq!(*counter.lock().await, 10);
}

// 形式化注释：
// ∀future. Send/Sync trait 保证跨任务安全
// TypeCheck(p) = ✓ ⇒ NoDataRaces(p) in async context
// 工具建议：Kani/Prusti 可验证异步并发安全 