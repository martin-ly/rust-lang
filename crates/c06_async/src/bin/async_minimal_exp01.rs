// 最小可运行的 Rust 1.90 异步示例
// 目标：演示 async/await、tokio 运行时、spawn 并发与非阻塞 sleep

use std::time::Duration;

#[tokio::main(flavor = "multi_thread")] // 创建多线程 Tokio 运行时
async fn main() {
    // 1) 基本 async/await：非阻塞延迟 100ms
    hello().await;

    // 2) 并发执行两个任务：分别延迟 50ms 与 80ms
    let handle_fast = tokio::spawn(async {
        tokio::time::sleep(Duration::from_millis(50)).await;
        "fast"
    });

    let handle_slow = tokio::spawn(async {
        tokio::time::sleep(Duration::from_millis(80)).await;
        "slow"
    });

    // 3) 等待两个任务完成（并发执行，整体耗时约 ~80ms 而非 130ms）
    let (fast, slow) = tokio::join!(handle_fast, handle_slow);
    println!("hello async, results = ({:?}, {:?})", fast.unwrap(), slow.unwrap());
}

// 简单的异步函数：演示 await
async fn hello() {
    tokio::time::sleep(Duration::from_millis(100)).await;
    println!("hello async world");
}


