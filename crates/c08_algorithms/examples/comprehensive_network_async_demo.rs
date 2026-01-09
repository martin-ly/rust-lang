//! 综合网络异步编程演示程序
//!
//! 本示例展示如何结合网络编程（C10）和异步编程（C06）构建高性能网络应用。
//!
//! ## 📐 知识结构
//!
//! ### 核心概念
//!
//! - **异步网络编程**: 结合异步编程和网络编程的编程范式
//!   - **属性**: 非阻塞 I/O、高并发、事件驱动
//!   - **关系**: 与异步编程、网络编程相关
//!
//! - **异步服务器**: 使用异步运行时处理网络请求的服务器
//!   - **属性**: 高并发、低资源占用、事件驱动
//!   - **关系**: 与异步编程、网络协议相关
//!
//! ### 思维导图
//!
//! ```text
//! 网络异步演示
//! │
//! ├── 异步网络服务器
//! │   ├── TCP 监听
//! │   ├── 异步接受连接
//! │   └── 并发处理请求
//! ├── 异步 I/O
//! │   ├── 异步读取
//! │   └── 异步写入
//! └── 错误处理
//!     ├── 错误传播
//!     └── 错误恢复
//! ```

use std::time::Duration;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpListener;
use tokio::time::{sleep, Instant};

/// 异步 TCP 服务器
///
/// 注意：此函数用于演示目的，在实际运行中会阻塞主线程
/// 如需使用，请单独启动服务器线程
#[allow(dead_code)]
async fn async_tcp_server() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 启动异步 TCP 服务器...");

    let listener = TcpListener::bind("127.0.0.1:8080").await?;
    println!("✅ 服务器监听在 127.0.0.1:8080");

    loop {
        let (mut socket, addr) = listener.accept().await?;
        println!("📥 新连接: {}", addr);

        tokio::spawn(async move {
            let mut buf = [0; 1024];

            loop {
                match socket.read(&mut buf).await {
                    Ok(0) => {
                        println!("🔌 连接关闭: {}", addr);
                        break;
                    }
                    Ok(n) => {
                        let message = String::from_utf8_lossy(&buf[0..n]);
                        println!("📨 收到消息: {}", message);

                        // 回显消息
                        if socket.write_all(&buf[0..n]).await.is_err() {
                            break;
                        }
                    }
                    Err(e) => {
                        eprintln!("❌ 读取错误: {}", e);
                        break;
                    }
                }
            }
        });
    }
}

/// 异步 HTTP 客户端（简化版）
async fn async_http_client(url: &str) -> Result<String, Box<dyn std::error::Error>> {
    println!("🌐 发送 HTTP 请求到: {}", url);

    // 模拟 HTTP 请求
    sleep(Duration::from_millis(100)).await;

    Ok(format!("响应来自: {}", url))
}

/// 并发处理多个请求
async fn concurrent_requests() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n⚡ 并发处理多个请求...");

    let urls = vec![
        "https://api1.example.com",
        "https://api2.example.com",
        "https://api3.example.com",
        "https://api4.example.com",
        "https://api5.example.com",
    ];

    let start = Instant::now();

    // 使用 join_all 并发执行
    let futures: Vec<_> = urls.iter()
        .map(|url| async_http_client(url))
        .collect();

    let results = futures::future::join_all(futures).await;

    let elapsed = start.elapsed();

    for (i, result) in results.iter().enumerate() {
        match result {
            Ok(response) => println!("  ✅ 请求 {}: {}", i + 1, response),
            Err(e) => println!("  ❌ 请求 {} 失败: {}", i + 1, e),
        }
    }

    println!("⏱️  总耗时: {:?} (并发执行)", elapsed);

    Ok(())
}

/// 使用 select! 处理多个异步任务
async fn select_example() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🎯 使用 select! 处理多个任务...");

    let task1 = async {
        sleep(Duration::from_secs(2)).await;
        "任务1完成"
    };

    let task2 = async {
        sleep(Duration::from_secs(1)).await;
        "任务2完成"
    };

    tokio::select! {
        result = task1 => {
            println!("  ✅ {}", result);
        }
        result = task2 => {
            println!("  ✅ {}", result);
        }
    }

    Ok(())
}

/// 流式处理数据
async fn stream_processing() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🌊 流式处理数据...");

    use tokio_stream::StreamExt;

    let mut stream = tokio_stream::iter(1..=10)
        .map(|x| x * 2)
        .filter(|&x| x > 5);

    while let Some(value) = stream.next().await {
        println!("  📊 处理值: {}", value);
        sleep(Duration::from_millis(100)).await;
    }

    Ok(())
}

/// 异步任务池
async fn task_pool_example() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🏊 异步任务池示例...");

    use tokio::sync::mpsc;

    let (tx, mut rx) = mpsc::channel(10);

    // 生产者
    for i in 0..20 {
        let tx = tx.clone();
        tokio::spawn(async move {
            sleep(Duration::from_millis(50)).await;
            tx.send(format!("任务 {}", i)).await.unwrap();
        });
    }

    drop(tx); // 关闭发送端

    // 消费者
    let mut count = 0;
    while let Some(task) = rx.recv().await {
        println!("  ✅ 完成: {}", task);
        count += 1;
    }

    println!("📊 总共完成 {} 个任务", count);

    Ok(())
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 综合网络异步编程演示");
    println!("========================\n");

    // 注意：实际运行服务器会阻塞，这里只演示其他功能
    println!("💡 提示: TCP 服务器示例代码已提供，实际运行需要单独启动\n");

    // 1. 并发请求示例
    concurrent_requests().await?;

    // 2. select! 示例
    select_example().await?;

    // 3. 流式处理示例
    stream_processing().await?;

    // 4. 任务池示例
    task_pool_example().await?;

    println!("\n✅ 演示完成！");
    println!("\n📚 相关文档:");
    println!("  - 异步编程指南: docs/ASYNC_PROGRAMMING_USAGE_GUIDE.md");
    println!("  - 网络编程速查卡: docs/quick_reference/network_programming_cheatsheet.md");

    Ok(())
}
