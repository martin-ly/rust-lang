// 事件驱动：mpsc通道事件分发示例 Event Driven: mpsc Channel Example
use tokio::sync::mpsc;

#[tokio::main]
async fn main() {
    let (tx, mut rx) = mpsc::channel(8);
    tokio::spawn(async move {
        tx.send("event: user_login").await.unwrap();
    });
    if let Some(event) = rx.recv().await {
        println!("Received: {}", event);
    }
} 