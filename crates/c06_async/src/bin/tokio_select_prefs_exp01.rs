use std::time::Duration;

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn main() {
    let mut fast = tokio::time::interval(Duration::from_millis(50));
    let mut slow = tokio::time::interval(Duration::from_millis(80));

    // 带偏好：在分支前放置 `biased;`，让上方分支优先
    for _ in 0..10 {
        tokio::select! {
            biased;
            _ = fast.tick() => println!("fast"),
            _ = slow.tick() => println!("slow"),
        }
    }
}


