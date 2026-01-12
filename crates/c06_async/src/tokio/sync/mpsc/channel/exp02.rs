use tokio::sync::mpsc;
use tokio::time::{self, Duration, Instant};

//使用 tokio::select! 宏来监听多个异步操作，包括取消信号。

#[allow(unused)]
pub async fn channel_exp11() {
    println!("channel_exp11");
    let (tx, mut rx) = mpsc::channel(32);

    // 启动一个任务
    tokio::spawn(async move {
        for i in 0..5 {
            if tx.send(i).await.is_err() {
                println!("Receiver dropped");
                return;
            }
            time::sleep(Duration::from_secs(1)).await;
        }
    });

    // 监听接收和超时
    loop {
        tokio::select! {
            Some(message) = rx.recv() => {
                println!("Received: {}", message);
            }
            _ = time::sleep(Duration::from_secs(3)) => {
                println!("Timeout, cancelling operation.");
                break;
            }
        }
    }
}

#[allow(unused)]
pub async fn channel_exp12() {
    println!("channel_exp12");
    let (tx, mut rx) = mpsc::channel(32);

    // 启动一个任务来发送消息
    tokio::spawn(async move {
        for i in 0..5 {
            if tx.send(i).await.is_err() {
                println!("Receiver dropped");
                return;
            }
            println!("Sent: {}", i);
            time::sleep(Duration::from_secs(1)).await; // 模拟工作
        }
    });

    // 启动一个任务来监听超时和接收消息
    let timeout_duration = Duration::from_secs(3);
    let start_time = Instant::now();

    loop {
        tokio::select! {
            Some(message) = rx.recv() => {
                println!("Received: {}", message);
            }
            _ = time::sleep(timeout_duration) => {
                println!("Timeout reached, exiting...");
                break; // 超时，退出循环
            }
            // Check elapsed time in a separate branch
            _ = time::sleep(Duration::from_millis(100)) => {
                if start_time.elapsed() >= timeout_duration {
                    println!("Total timeout reached, exiting...");
                    break; // 总超时，退出循环
                }
            }
        }
    }

    println!("Exiting gracefully...");
}
