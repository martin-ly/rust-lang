use tokio::sync::Semaphore;
use tokio::time::{sleep, Duration};
use std::sync::Arc;

async fn limited_task(id: u32, semaphore: Arc<Semaphore>) {
    let _permit = semaphore.acquire().await.unwrap(); // 获取许可
    println!("任务 {} 开始", id);
    sleep(Duration::from_secs(2)).await;
    println!("任务 {} 完成", id);
}

#[tokio::main]
async fn main() {
    let semaphore = Arc::new(Semaphore::new(2)); // 限制并发为2

    let tasks: Vec<_> = (1..=5)
        .map(|id| {
            let semaphore = Arc::clone(&semaphore);
            tokio::spawn(limited_task(id, semaphore))
        })
        .collect();

    for task in tasks {
        let _ = task.await; // 等待所有任务完成
    }
}
