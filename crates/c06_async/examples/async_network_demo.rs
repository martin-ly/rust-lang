//! 异步网络编程演示
//!
//! 本示例展示了异步网络编程的各种场景：
//! - HTTP 客户端并发请求
//! - TCP 服务器和客户端
//! - UDP 通信
//! - WebSocket 连接
//! - 网络超时和重试
//! - 连接池管理
//!
//! 运行方式：
//! ```bash
//! cargo run --example async_network_demo
//! ```
use anyhow::Result;
use reqwest::Client;
use serde::{Deserialize, Serialize};
use std::net::SocketAddr;
use std::sync::Arc;
use std::time::Duration;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::{TcpListener, TcpStream, UdpSocket};
use tokio::sync::Semaphore;
use tokio::time::{sleep, timeout};

#[derive(Debug, Serialize, Deserialize)]
struct HttpResponse {
    status: u16,
    body: String,
    duration: Duration,
}

struct NetworkDemo {
    client: Client,
    connection_pool: Arc<Semaphore>,
}

impl NetworkDemo {
    fn new() -> Self {
        let client = Client::builder()
            .timeout(Duration::from_secs(10))
            .build()
            .unwrap();

        Self {
            client,
            connection_pool: Arc::new(Semaphore::new(10)), // 最多10个并发连接
        }
    }

    async fn run(&self) -> Result<()> {
        println!("🌐 异步网络编程演示");
        println!("================================");

        // 1. HTTP 并发请求演示
        println!("\n📡 1. HTTP 并发请求演示");
        self.http_concurrent_requests().await?;

        // 2. HTTP 请求重试和超时演示
        println!("\n🔄 2. HTTP 请求重试和超时演示");
        self.http_retry_timeout().await?;

        // 3. TCP 服务器演示
        println!("\n🔌 3. TCP 服务器演示");
        self.tcp_server_demo().await?;

        // 4. UDP 通信演示
        println!("\n📨 4. UDP 通信演示");
        self.udp_communication_demo().await?;

        // 5. 连接池管理演示
        println!("\n🏊 5. 连接池管理演示");
        self.connection_pool_demo().await?;

        Ok(())
    }

    async fn http_concurrent_requests(&self) -> Result<()> {
        let urls = vec![
            "https://httpbin.org/get",
            "https://httpbin.org/json",
            "https://httpbin.org/uuid",
            "https://httpbin.org/headers",
            "https://httpbin.org/ip",
        ];

        println!("  发起 {} 个并发 HTTP 请求...", urls.len());

        let start = std::time::Instant::now();
        let semaphore = Arc::clone(&self.connection_pool);

        // 使用信号量限制并发数
        let futures = urls.clone().into_iter().map(|url| {
            let client = self.client.clone();
            let semaphore = Arc::clone(&semaphore);
            async move {
                let _permit = semaphore.acquire().await.unwrap();
                Self::fetch_url(client, url).await
            }
        });

        let results = futures::future::join_all(futures).await;
        let total_time = start.elapsed();

        let mut success_count = 0;
        let mut total_bytes = 0;

        for result in results {
            match result {
                Ok(response) => {
                    success_count += 1;
                    total_bytes += response.body.len();
                    println!(
                        "    ✅ 状态: {}, 大小: {} 字节, 耗时: {:?}",
                        response.status,
                        response.body.len(),
                        response.duration
                    );
                }
                Err(e) => {
                    println!("    ❌ 请求失败: {}", e);
                }
            }
        }

        println!("  并发请求完成:");
        println!("    总耗时: {:?}", total_time);
        println!("    成功请求: {}/{}", success_count, urls.len());
        println!("    总数据量: {} 字节", total_bytes);

        Ok(())
    }

    async fn http_retry_timeout(&self) -> Result<()> {
        let url = "https://httpbin.org/delay/2"; // 延迟2秒的端点

        println!("  测试超时处理...");

        // 测试超时
        match timeout(Duration::from_secs(1), self.client.get(url).send()).await {
            Ok(Ok(response)) => {
                println!("    ✅ 请求成功: {}", response.status());
            }
            Ok(Err(e)) => {
                println!("    ❌ 请求错误: {}", e);
            }
            Err(_) => {
                println!("    ⏰ 请求超时");
            }
        }

        println!("  测试重试机制...");

        // 测试重试
        let mut attempts = 0;
        let max_attempts = 3;

        loop {
            attempts += 1;
            match self
                .client
                .get("https://httpbin.org/status/500")
                .send()
                .await
            {
                Ok(response) if response.status().is_success() => {
                    println!("    ✅ 请求成功: {}", response.status());
                    break;
                }
                Ok(response) => {
                    println!("    ⚠️  尝试 {}: 状态码 {}", attempts, response.status());
                }
                Err(e) => {
                    println!("    ❌ 尝试 {}: 错误 {}", attempts, e);
                }
            }

            if attempts >= max_attempts {
                println!("    ❌ 达到最大重试次数");
                break;
            }

            // 指数退避
            let delay = Duration::from_millis(100 * (2_u64.pow(attempts)));
            println!("    ⏳ 等待 {:?} 后重试...", delay);
            sleep(delay).await;
        }

        Ok(())
    }

    async fn tcp_server_demo(&self) -> Result<()> {
        let addr = "127.0.0.1:0";
        let listener = TcpListener::bind(addr).await?;
        let server_addr = listener.local_addr()?;

        println!("  TCP 服务器启动在: {}", server_addr);

        // 启动服务器
        let server_handle = tokio::spawn(async move {
            Self::tcp_server(listener).await;
        });

        // 等待服务器启动
        sleep(Duration::from_millis(100)).await;

        // 启动多个客户端
        let mut client_handles = vec![];
        for i in 0..3 {
            let addr = server_addr;
            let handle = tokio::spawn(async move {
                Self::tcp_client(addr, i).await;
            });
            client_handles.push(handle);
        }

        // 等待客户端完成
        for handle in client_handles {
            handle.await?;
        }

        // 关闭服务器
        server_handle.abort();

        println!("  TCP 服务器演示完成");
        Ok(())
    }

    async fn tcp_server(listener: TcpListener) {
        let mut connection_count = 0;

        while let Ok((stream, addr)) = listener.accept().await {
            connection_count += 1;
            println!("    📥 接受连接 #{} 来自: {}", connection_count, addr);

            tokio::spawn(async move {
                Self::handle_tcp_connection(stream, connection_count).await;
            });
        }
    }

    async fn handle_tcp_connection(mut stream: TcpStream, connection_id: usize) {
        let mut buffer = [0; 1024];

        loop {
            match stream.read(&mut buffer).await {
                Ok(0) => {
                    println!("    📤 连接 #{} 关闭", connection_id);
                    break;
                }
                Ok(n) => {
                    let message = String::from_utf8_lossy(&buffer[..n]);
                    println!("    📨 连接 #{} 收到: {}", connection_id, message.trim());

                    let response = format!("服务器响应: {}", message.trim());
                    if let Err(e) = stream.write_all(response.as_bytes()).await {
                        println!("    ❌ 连接 #{} 写入错误: {}", connection_id, e);
                        break;
                    }
                }
                Err(e) => {
                    println!("    ❌ 连接 #{} 读取错误: {}", connection_id, e);
                    break;
                }
            }
        }
    }

    async fn tcp_client(addr: SocketAddr, client_id: usize) {
        match TcpStream::connect(addr).await {
            Ok(mut stream) => {
                println!("    🔗 客户端 {} 连接到服务器", client_id);

                for i in 0..3 {
                    let message = format!("客户端 {} 消息 {}", client_id, i);

                    if let Err(e) = stream.write_all(message.as_bytes()).await {
                        println!("    ❌ 客户端 {} 写入错误: {}", client_id, e);
                        break;
                    }

                    let mut buffer = [0; 1024];
                    match stream.read(&mut buffer).await {
                        Ok(n) => {
                            let response = String::from_utf8_lossy(&buffer[..n]);
                            println!("    📨 客户端 {} 收到响应: {}", client_id, response.trim());
                        }
                        Err(e) => {
                            println!("    ❌ 客户端 {} 读取错误: {}", client_id, e);
                            break;
                        }
                    }

                    sleep(Duration::from_millis(500)).await;
                }

                println!("    🔌 客户端 {} 断开连接", client_id);
            }
            Err(e) => {
                println!("    ❌ 客户端 {} 连接失败: {}", client_id, e);
            }
        }
    }

    async fn udp_communication_demo(&self) -> Result<()> {
        // 创建 UDP 套接字
        let server_addr = "127.0.0.1:0";
        let server_socket = UdpSocket::bind(server_addr).await?;
        let server_addr = server_socket.local_addr()?;

        println!("  UDP 服务器启动在: {}", server_addr);

        // 启动 UDP 服务器
        let server_handle = tokio::spawn(async move {
            Self::udp_server(server_socket).await;
        });

        // 等待服务器启动
        sleep(Duration::from_millis(100)).await;

        // 创建客户端套接字
        let client_socket = UdpSocket::bind("127.0.0.1:0").await?;

        // 发送消息
        let messages = vec!["Hello UDP Server!", "This is message 2", "Final message"];

        for (i, message) in messages.iter().enumerate() {
            println!("    📤 发送消息 {}: {}", i + 1, message);

            if let Err(e) = client_socket.send_to(message.as_bytes(), server_addr).await {
                println!("    ❌ 发送失败: {}", e);
                continue;
            }

            // 接收响应
            let mut buffer = [0; 1024];
            match timeout(Duration::from_secs(1), client_socket.recv_from(&mut buffer)).await {
                Ok(Ok((n, addr))) => {
                    let response = String::from_utf8_lossy(&buffer[..n]);
                    println!("    📨 收到响应: {} (来自: {})", response, addr);
                }
                Ok(Err(e)) => {
                    println!("    ❌ 接收错误: {}", e);
                }
                Err(_) => {
                    println!("    ⏰ 接收超时");
                }
            }

            sleep(Duration::from_millis(500)).await;
        }

        // 关闭服务器
        server_handle.abort();

        println!("  UDP 通信演示完成");
        Ok(())
    }

    async fn udp_server(socket: UdpSocket) {
        let mut buffer = [0; 1024];

        while let Ok((n, addr)) = socket.recv_from(&mut buffer).await {
            let message = String::from_utf8_lossy(&buffer[..n]);
            println!("    📥 UDP 服务器收到: {} (来自: {})", message, addr);

            let response = format!("UDP 服务器响应: {}", message);
            if let Err(e) = socket.send_to(response.as_bytes(), addr).await {
                println!("    ❌ UDP 服务器发送错误: {}", e);
            }
        }
    }

    async fn connection_pool_demo(&self) -> Result<()> {
        println!("  连接池管理演示...");

        let pool_size = 5;
        let semaphore = Arc::new(Semaphore::new(pool_size));
        let mut handles = vec![];

        // 模拟多个任务同时请求连接
        for i in 0..10 {
            let semaphore = Arc::clone(&semaphore);
            let client = self.client.clone();

            let handle = tokio::spawn(async move {
                println!("    🏊 任务 {} 请求连接", i);

                let _permit = semaphore.acquire().await.unwrap();
                println!("    ✅ 任务 {} 获得连接", i);

                // 模拟网络操作
                match Self::fetch_url(client, "https://httpbin.org/get").await {
                    Ok(response) => {
                        println!("    📡 任务 {} 完成，状态: {}", i, response.status);
                    }
                    Err(e) => {
                        println!("    ❌ 任务 {} 失败: {}", i, e);
                    }
                }

                sleep(Duration::from_millis(100)).await;
                println!("    🔓 任务 {} 释放连接", i);
            });

            handles.push(handle);
        }

        // 等待所有任务完成
        for handle in handles {
            handle.await?;
        }

        println!("  连接池演示完成");
        Ok(())
    }

    async fn fetch_url(client: Client, url: &str) -> Result<HttpResponse> {
        let start = std::time::Instant::now();

        let response = client.get(url).send().await?;
        let status = response.status().as_u16();
        let body = response.text().await?;
        let duration = start.elapsed();

        Ok(HttpResponse {
            status,
            body,
            duration,
        })
    }
}

struct NetworkPerformanceDemo;

impl NetworkPerformanceDemo {
    async fn run() -> Result<()> {
        println!("\n⚡ 网络性能测试");
        println!("================================");

        // 测试不同并发级别的性能
        let concurrency_levels = vec![1, 5, 10, 20];

        for level in concurrency_levels {
            println!("\n📊 测试并发级别: {}", level);
            Self::performance_test(level).await?;
        }

        Ok(())
    }

    async fn performance_test(concurrency: usize) -> Result<()> {
        let client = Client::new();
        let semaphore = Arc::new(Semaphore::new(concurrency));
        let start = std::time::Instant::now();

        let urls = vec![
            "https://httpbin.org/get",
            "https://httpbin.org/json",
            "https://httpbin.org/uuid",
        ];

        // 重复URL以达到足够的请求量
        let mut all_urls = Vec::new();
        for _ in 0..10 {
            all_urls.extend(urls.clone());
        }

        let futures = all_urls.into_iter().map(|url| {
            let client = client.clone();
            let semaphore = Arc::clone(&semaphore);
            async move {
                let _permit = semaphore.acquire().await.unwrap();
                client.get(url).send().await
            }
        });

        let results = futures::future::join_all(futures).await;
        let total_time = start.elapsed();

        let success_count = results.iter().filter(|r| r.is_ok()).count();
        let total_requests = results.len();
        let requests_per_second = total_requests as f64 / total_time.as_secs_f64();

        println!("    总请求数: {}", total_requests);
        println!("    成功请求数: {}", success_count);
        println!("    总耗时: {:?}", total_time);
        println!("    请求/秒: {:.2}", requests_per_second);
        println!(
            "    成功率: {:.1}%",
            (success_count as f64 / total_requests as f64) * 100.0
        );

        Ok(())
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    let demo = NetworkDemo::new();
    demo.run().await?;

    // 运行性能测试
    NetworkPerformanceDemo::run().await?;

    println!("\n🎉 异步网络编程演示完成！");
    Ok(())
}
