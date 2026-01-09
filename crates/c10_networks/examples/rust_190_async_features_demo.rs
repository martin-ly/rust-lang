//! Rust 1.90 异步特性演示示例
//!
//! 本示例展示了如何使用Rust 1.90的新异步特性来改进网络编程

use c10_networks::error::{NetworkError, NetworkResult};
use c10_networks::unified_api::NetClient;
use std::time::{Duration, Instant};
use tokio::time::timeout;
use futures::StreamExt;

/// Rust 1.90 异步特性演示
#[tokio::main]
async fn main() -> NetworkResult<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("🚀 Rust 1.90 异步特性演示开始...");

    // 演示1: 异步trait优化
    demo_async_traits().await?;

    // 演示2: 异步闭包改进
    demo_async_closures().await?;

    // 演示3: 常量泛型推断
    demo_const_generics().await?;

    // 演示4: 异步迭代器增强
    demo_async_iterators().await?;

    // 演示5: 生命周期语法检查
    demo_lifetime_syntax().await?;

    println!("✅ 所有演示完成！");
    Ok(())
}

/// 演示1: 异步trait优化
async fn demo_async_traits() -> NetworkResult<()> {
    println!("\n📡 演示1: 异步trait优化");

    let client = NetClient::new();

    // Rust 1.90的异步trait改进
    let start = Instant::now();

    // 使用改进的异步trait语法
    let results = futures::future::try_join_all(vec![
        async_network_operation(&client, "example.com", 1),
        async_network_operation(&client, "google.com", 2),
        async_network_operation(&client, "github.com", 3),
    ]).await?;

    let duration = start.elapsed();
    println!("   并发操作完成，耗时: {:?}", duration);
    println!("   结果数量: {}", results.len());

    Ok(())
}

/// 异步网络操作（展示改进的异步trait）
async fn async_network_operation(
    client: &NetClient,
    host: &str,
    operation_id: u32,
) -> NetworkResult<String> {
    println!("   操作 {}: 开始处理 {}", operation_id, host);

    // 模拟异步网络操作
    tokio::time::sleep(Duration::from_millis(100)).await;

    // 使用改进的错误处理
    let result = client.dns_lookup_ips(host).await
        .map_err(|e| {
            NetworkError::Other(format!("DNS lookup failed for {}: {}", host, e))
        })?;

    println!("   操作 {}: 完成，找到 {} 个IP", operation_id, result.len());
    Ok(format!("{}: {} IPs", host, result.len()))
}

/// 演示2: 异步闭包改进
async fn demo_async_closures() -> NetworkResult<()> {
    println!("\n🔄 演示2: 异步闭包改进");

    let client = NetClient::new();

    // Rust 1.90的异步闭包改进
    let operations = vec![
        "httpbin.org",
        "jsonplaceholder.typicode.com",
        "reqres.in",
    ];

    // 使用改进的异步闭包语法
    let results = futures::future::try_join_all(
        operations.into_iter().map(|host| {
            let client = client.clone();
            // 异步闭包捕获优化
            async move {
                let start = Instant::now();
                let result = client.dns_lookup_ips(host).await?;
                let duration = start.elapsed();
                Ok::<String, NetworkError>(format!("{}: {} IPs in {:?}", host, result.len(), duration))
            }
        })
    ).await?;

    for result in results {
        println!("   {}", result);
    }

    Ok(())
}

/// 演示3: 常量泛型推断
async fn demo_const_generics() -> NetworkResult<()> {
    println!("\n🔢 演示3: 常量泛型推断");

    // Rust 1.90的常量泛型推断改进
    let packet1 = [1u8, 2, 3, 4, 5];
    let packet2 = [10u8, 20, 30, 40, 50];
    let packet3 = [100u8, 200, 255];

    // 使用改进的常量泛型推断
    let result1 = process_packet_improved(packet1).await?;
    let result2 = process_packet_improved(packet2).await?;
    let result3 = process_packet_improved(packet3).await?;

    println!("   数据包 1: 处理结果 = {}", result1);
    println!("   数据包 2: 处理结果 = {}", result2);
    println!("   数据包 3: 处理结果 = {}", result3);

    Ok(())
}

/// 改进的数据包处理函数（使用Rust 1.90的常量泛型推断）
async fn process_packet_improved<const N: usize>(data: [u8; N]) -> NetworkResult<u32> {
    // Rust 1.90: 编译器自动推断数组长度
    let _len = data.len();

    // 模拟异步处理
    tokio::time::sleep(Duration::from_millis(50)).await;

    // 计算校验和
    let checksum = data.iter().fold(0u32, |acc, &byte| acc.wrapping_add(byte as u32));

    Ok(checksum)
}

/// 演示4: 异步迭代器增强
async fn demo_async_iterators() -> NetworkResult<()> {
    println!("\n🔄 演示4: 异步迭代器增强");

    let client = NetClient::new();
    let hosts = vec![
        "example.com",
        "google.com",
        "github.com",
        "rust-lang.org",
        "tokio.rs",
    ];

    // 使用改进的异步迭代器
    let mut stream = futures::stream::iter(hosts)
        .map(|host| {
            let client = client.clone();
            async move {
                let start = Instant::now();
                let result = client.dns_lookup_ips(host).await;
                let duration = start.elapsed();
                (host, result, duration)
            }
        })
        .buffer_unordered(3); // 并发度为3

    let mut results = Vec::new();
    while let Some((host, result, duration)) = stream.next().await {
        match result {
            Ok(ips) => {
                println!("   {}: {} IPs in {:?}", host, ips.len(), duration);
                results.push((host.to_string(), ips.len()));
            }
            Err(e) => {
                println!("   {}: 错误 - {}", host, e);
            }
        }
    }

    println!("   总共处理了 {} 个主机", results.len());

    Ok(())
}

/// 演示5: 生命周期语法检查
async fn demo_lifetime_syntax() -> NetworkResult<()> {
    println!("\n🔗 演示5: 生命周期语法检查");

    let client = NetClient::new();

    // Rust 1.90的改进生命周期语法
    let result = with_improved_lifetimes(&client, "example.com").await?;
    println!("   生命周期改进结果: {}", result);

    // 演示生命周期一致性检查
    let data = b"Hello, Rust 1.90!";
    let processed = process_with_lifetime_check(data).await?;
    println!("   生命周期检查结果: {}", processed);

    Ok(())
}

/// 改进的生命周期处理
async fn with_improved_lifetimes<'a>(
    client: &'a NetClient,
    host: &'a str,
) -> NetworkResult<String> {
    // Rust 1.90: 更好的生命周期推断
    let start = Instant::now();

    // 使用timeout包装异步操作
    let result = timeout(Duration::from_secs(5), async {
        client.dns_lookup_ips(host).await
    }).await
    .map_err(|_| NetworkError::Timeout(Duration::from_secs(5)))?
    .map_err(|e| NetworkError::Other(format!("DNS error: {}", e)))?;

    let duration = start.elapsed();
    Ok(format!("{}: {} IPs in {:?}", host, result.len(), duration))
}

/// 生命周期检查示例
async fn process_with_lifetime_check(data: &[u8]) -> NetworkResult<String> {
    // 模拟异步处理
    tokio::time::sleep(Duration::from_millis(30)).await;

    // 计算哈希值
    let hash = data.iter().fold(0u32, |acc, &byte| acc.wrapping_mul(31).wrapping_add(byte as u32));

    Ok(format!("Hash: 0x{:08x}", hash))
}

/// 性能基准测试
#[allow(dead_code)]
async fn benchmark_async_performance() -> NetworkResult<()> {
    println!("\n📊 异步性能基准测试");

    let client = NetClient::new();
    let iterations = 100;

    // 测试1: 顺序执行
    let start = Instant::now();
    for i in 0..iterations {
        let _ = client.dns_lookup_ips("example.com").await?;
        if i % 10 == 0 {
            println!("   顺序执行进度: {}/{}", i, iterations);
        }
    }
    let sequential_time = start.elapsed();

    // 测试2: 并发执行
    let start = Instant::now();
    let futures = (0..iterations).map(|_| {
        client.dns_lookup_ips("example.com")
    });

    let _results = futures::future::try_join_all(futures).await?;
    let concurrent_time = start.elapsed();

    println!("   顺序执行时间: {:?}", sequential_time);
    println!("   并发执行时间: {:?}", concurrent_time);
    println!("   性能提升: {:.2}x",
        sequential_time.as_secs_f64() / concurrent_time.as_secs_f64());

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_async_traits() -> NetworkResult<()> {
        demo_async_traits().await
    }

    #[tokio::test]
    async fn test_async_closures() -> NetworkResult<()> {
        demo_async_closures().await
    }

    #[tokio::test]
    async fn test_const_generics() -> NetworkResult<()> {
        demo_const_generics().await
    }

    #[tokio::test]
    async fn test_async_iterators() -> NetworkResult<()> {
        demo_async_iterators().await
    }

    #[tokio::test]
    async fn test_lifetime_syntax() -> NetworkResult<()> {
        demo_lifetime_syntax().await
    }
}
