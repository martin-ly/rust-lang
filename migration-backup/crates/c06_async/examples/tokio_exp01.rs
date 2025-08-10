use tokio::sync::mpsc;
//use tokio_stream::StreamExt; // 导入 StreamExt trait
use tokio::time::{Duration, sleep};

#[tokio::main]
async fn main() {
    // 创建一个通道
    let (tx, mut rx) = mpsc::channel(32);

    // 发送者任务
    tokio::spawn(async move {
        for i in 0..5 {
            // 发送消息
            if tx.send(i).await.is_err() {
                println!("接收者已关闭");
                return;
            }
            println!("发送: {}", i);
            sleep(Duration::from_secs(1)).await; // 异步等待
        }
    });

    // 接收者任务
    while let Some(value) = rx.recv().await {
        println!("接收: {}", value);
    }
}
