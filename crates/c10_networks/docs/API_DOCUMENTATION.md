# API 文档生成指南

> 适用范围：Rust 1.90+，Tokio 1.35+。文档风格遵循 [`STYLE.md`](STYLE.md)。

## 📋 目录

- [API 文档生成指南](#api-文档生成指南)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
  - [🚀 快速开始](#-快速开始)
  - [📚 文档生成](#-文档生成)
    - [基础文档生成](#基础文档生成)
    - [高级文档生成](#高级文档生成)
    - [API 文档发布](#api-文档发布)
  - [🔧 配置选项](#-配置选项)
    - [Cargo.toml 配置](#cargotoml-配置)
    - [文档属性配置](#文档属性配置)
    - [特性文档配置](#特性文档配置)
  - [📖 文档编写规范](#-文档编写规范)
    - [模块文档](#模块文档)
    - [函数文档](#函数文档)
    - [结构体文档](#结构体文档)
    - [枚举文档](#枚举文档)
    - [特性文档](#特性文档)
  - [🎨 文档样式](#-文档样式)
    - [代码示例](#代码示例)
    - [图表和流程图](#图表和流程图)
    - [数学公式](#数学公式)
    - [链接和引用](#链接和引用)
  - [🔍 文档质量检查](#-文档质量检查)
    - [文档覆盖率](#文档覆盖率)
    - [示例代码验证](#示例代码验证)
    - [链接有效性](#链接有效性)
  - [📦 文档发布](#-文档发布)
    - [本地文档服务](#本地文档服务)
    - [GitHub Pages](#github-pages)
    - [docs.rs 发布](#docsrs-发布)
  - [❓ 常见问题](#-常见问题)

## 🎯 概述

C10 Networks 提供了完整的 API 文档生成和发布流程。本文档介绍了如何生成、配置和发布高质量的 API 文档。

### 文档特性

- ✅ 自动 API 文档生成
- ✅ 交互式代码示例
- ✅ 特性文档支持
- ✅ 搜索和导航
- ✅ 主题定制
- ✅ 多平台发布

## 🚀 快速开始

### 生成基础文档

```bash
# 生成所有文档
cargo doc

# 生成特定包的文档
cargo doc -p c10_networks

# 生成并打开文档
cargo doc --open

# 生成文档但不构建依赖
cargo doc --no-deps
```

### 生成完整文档

```bash
# 生成包含所有特性的文档
cargo doc --all-features

# 生成包含私有项的文档
cargo doc --document-private-items

# 生成并保留源码链接
cargo doc --document-private-items --no-deps
```

## 📚 文档生成

### 基础文档生成

```bash
#!/bin/bash
# scripts/generate_docs.sh

set -e

echo "🚀 生成 C10 Networks API 文档..."

# 清理之前的文档
rm -rf target/doc

# 生成基础文档
echo "📚 生成基础文档..."
cargo doc --no-deps --document-private-items

# 生成特性文档
echo "🔧 生成特性文档..."
cargo doc --features "sniff,tls,offline,pcap_live" --no-deps --document-private-items

# 生成示例文档
echo "📖 生成示例文档..."
cargo doc --examples --no-deps

echo "✅ 文档生成完成！"
echo "📖 查看文档: file://$(pwd)/target/doc/c10_networks/index.html"
```

### 高级文档生成

```bash
#!/bin/bash
# scripts/generate_full_docs.sh

set -e

echo "🚀 生成完整 C10 Networks 文档..."

# 设置环境变量
export RUSTDOCFLAGS="--html-in-header docs/header.html --html-before-content docs/before.html --html-after-content docs/after.html"

# 清理之前的文档
rm -rf target/doc

# 生成完整文档
echo "📚 生成完整文档..."
cargo doc \
    --all-features \
    --document-private-items \
    --no-deps \
    --open

# 生成基准测试文档
echo "📊 生成基准测试文档..."
cargo doc --benches --no-deps

# 生成测试文档
echo "🧪 生成测试文档..."
cargo doc --tests --no-deps

echo "✅ 完整文档生成完成！"
```

### API 文档发布

```bash
#!/bin/bash
# scripts/publish_docs.sh

set -e

echo "🚀 发布 C10 Networks 文档..."

# 生成文档
cargo doc --all-features --document-private-items --no-deps

# 发布到 GitHub Pages
if [ "$GITHUB_ACTIONS" = "true" ]; then
    echo "📤 发布到 GitHub Pages..."
    
    # 配置 Git
    git config --global user.name "C10 Networks Bot"
    git config --global user.email "bot@c10networks.com"
    
    # 克隆 gh-pages 分支
    git clone --branch gh-pages https://github.com/your-org/c10_networks.git gh-pages
    
    # 复制文档
    cp -r target/doc/* gh-pages/
    
    # 提交更改
    cd gh-pages
    git add .
    git commit -m "Update API documentation"
    git push origin gh-pages
    
    echo "✅ 文档已发布到 GitHub Pages"
fi

echo "✅ 文档发布完成！"
```

## 🔧 配置选项

### Cargo.toml 配置

```toml
[package]
name = "c10_networks"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"

# 文档配置
documentation = "https://docs.rs/c10_networks"
homepage = "https://github.com/your-org/c10_networks"
repository = "https://github.com/your-org/c10_networks"
readme = "README.md"
license = "MIT"
keywords = ["network", "async", "tcp", "udp", "http", "websocket"]
categories = ["network-programming", "asynchronous"]
description = "High-performance network programming library for Rust"

[package.metadata.docs.rs]
# docs.rs 配置
features = ["sniff", "tls", "offline", "pcap_live"]
all-features = true
default-target = "x86_64-unknown-linux-gnu"
rustc-args = ["--cfg", "docsrs"]

[package.metadata.docs.rs.dependencies]
# 文档依赖
tokio = { version = "1.35", features = ["full"] }
bytes = "1.0"
serde = { version = "1.0", features = ["derive"] }
```

### 文档属性配置

```rust
//! # C10 Networks - Rust 网络编程库
//!
//! 本库提供了基于 Rust 1.90 的现代网络编程功能，包括：
//! - 异步网络通信
//! - 多种网络协议支持
//! - 高性能网络编程工具
//! - 安全的网络通信
//!
//! ## 特性
//!
//! - 🚀 基于 Rust 1.90 最新特性
//! - ⚡ 异步/await 支持
//! - 🔒 内置安全功能
//! - 📊 性能监控
//! - 🧪 完整的测试覆盖
//!
//! ## 快速开始
//!
//! ```rust
//! use c10_networks::{NetClient, NetworkResult};
//!
//! #[tokio::main]
//! async fn main() -> NetworkResult<()> {
//!     let client = NetClient::new();
//!     let response = client.get("https://example.com").await?;
//!     println!("Response: {}", response);
//!     Ok(())
//! }
//! ```
//!
//! ## 更多信息
//!
//! - [API 文档](https://docs.rs/c10_networks)
//! - [示例代码](../examples/)
//! - [GitHub 仓库](https://github.com/your-org/c10_networks)

#![doc(html_logo_url = "https://raw.githubusercontent.com/your-org/c10_networks/main/assets/logo.png")]
#![doc(html_favicon_url = "https://raw.githubusercontent.com/your-org/c10_networks/main/assets/favicon.ico")]
#![doc(html_root_url = "https://docs.rs/c10_networks")]
#![doc(html_playground_url = "https://play.rust-lang.org/")]
#![warn(missing_docs)]
#![warn(rustdoc::missing_crate_level_docs)]
```

### 特性文档配置

```rust
/// # 网络诊断工具
///
/// 提供网络连接诊断和性能分析功能。
///
/// ## 特性
///
/// 启用 `diagnostics` 特性后，可以使用以下功能：
/// - 网络延迟测试
/// - 带宽测量
/// - 连接质量分析
/// - 故障诊断
///
/// ## 示例
///
/// ```rust
/// use c10_networks::diagnostics::NetworkDiagnostics;
///
/// #[tokio::main]
/// async fn main() -> Result<(), Box<dyn std::error::Error>> {
///     let diagnostics = NetworkDiagnostics::new();
///     let latency = diagnostics.measure_latency("example.com").await?;
///     println!("延迟: {:?}", latency);
///     Ok(())
/// }
/// ```
#[cfg(feature = "diagnostics")]
pub mod diagnostics {
    //! 网络诊断模块
    //!
    //! 提供网络连接诊断和性能分析功能。

    /// 网络诊断工具
    ///
    /// 用于测试网络连接质量和性能。
    pub struct NetworkDiagnostics {
        // 实现细节
    }

    impl NetworkDiagnostics {
        /// 创建新的网络诊断工具
        ///
        /// # 示例
        ///
        /// ```rust
        /// use c10_networks::diagnostics::NetworkDiagnostics;
        ///
        /// let diagnostics = NetworkDiagnostics::new();
        /// ```
        pub fn new() -> Self {
            Self {
                // 初始化
            }
        }

        /// 测量网络延迟
        ///
        /// # 参数
        ///
        /// * `host` - 目标主机名或IP地址
        ///
        /// # 返回值
        ///
        /// 返回延迟测量结果
        ///
        /// # 示例
        ///
        /// ```rust
        /// use c10_networks::diagnostics::NetworkDiagnostics;
        ///
        /// #[tokio::main]
        /// async fn main() -> Result<(), Box<dyn std::error::Error>> {
        ///     let diagnostics = NetworkDiagnostics::new();
        ///     let latency = diagnostics.measure_latency("example.com").await?;
        ///     println!("延迟: {:?}", latency);
        ///     Ok(())
        /// }
        /// ```
        pub async fn measure_latency(&self, host: &str) -> Result<std::time::Duration, Box<dyn std::error::Error>> {
            // 实现延迟测量
            Ok(std::time::Duration::from_millis(100))
        }
    }
}
```

## 📖 文档编写规范

### 模块文档

```rust
//! # 网络协议模块
//!
//! 本模块提供了各种网络协议的实现，包括：
//! - HTTP/1.1 和 HTTP/2
//! - WebSocket
//! - TCP 和 UDP
//! - DNS
//! - TLS/SSL
//!
//! ## 使用示例
//!
//! ```rust
//! use c10_networks::protocol::http::HttpClient;
//!
//! #[tokio::main]
//! async fn main() -> Result<(), Box<dyn std::error::Error>> {
//!     let client = HttpClient::new();
//!     let response = client.get("https://example.com").await?;
//!     println!("Status: {}", response.status());
//!     Ok(())
//! }
//! ```
//!
//! ## 特性
//!
//! - `http` - HTTP 协议支持
//! - `websocket` - WebSocket 协议支持
//! - `tls` - TLS/SSL 加密支持
//! - `dns` - DNS 解析支持

pub mod http;
pub mod websocket;
pub mod tcp;
pub mod udp;
pub mod dns;
```

### 函数文档

```rust
/// 创建新的 HTTP 客户端
///
/// 创建一个配置了默认设置的 HTTP 客户端实例。
/// 客户端支持 HTTP/1.1 和 HTTP/2 协议。
///
/// # 参数
///
/// * `config` - 客户端配置选项
///
/// # 返回值
///
/// 返回配置好的 HTTP 客户端实例
///
/// # 错误
///
/// 如果配置无效，返回 `NetworkError::Configuration`
///
/// # 示例
///
/// ```rust
/// use c10_networks::protocol::http::{HttpClient, HttpClientConfig};
///
/// #[tokio::main]
/// async fn main() -> Result<(), Box<dyn std::error::Error>> {
///     let config = HttpClientConfig::default()
///         .with_timeout(std::time::Duration::from_secs(30))
///         .with_user_agent("MyApp/1.0");
///     
///     let client = HttpClient::new(config)?;
///     let response = client.get("https://example.com").await?;
///     println!("Response: {}", response.body());
///     Ok(())
/// }
/// ```
///
/// # 性能考虑
///
/// - 客户端使用连接池来复用连接
/// - 默认连接池大小为 10
/// - 支持 HTTP/2 多路复用
pub fn new(config: HttpClientConfig) -> NetworkResult<Self> {
    // 实现
}
```

### 结构体文档

```rust
/// HTTP 客户端配置
///
/// 用于配置 HTTP 客户端的各种选项，包括超时、重试、连接池等。
///
/// # 示例
///
/// ```rust
/// use c10_networks::protocol::http::HttpClientConfig;
/// use std::time::Duration;
///
/// let config = HttpClientConfig::default()
///     .with_timeout(Duration::from_secs(30))
///     .with_max_retries(3)
///     .with_user_agent("MyApp/1.0")
///     .with_connection_pool_size(20);
/// ```
///
/// # 默认值
///
/// - 超时时间: 30秒
/// - 最大重试次数: 3
/// - 连接池大小: 10
/// - 用户代理: "c10_networks/0.1.0"
#[derive(Debug, Clone)]
pub struct HttpClientConfig {
    /// 请求超时时间
    pub timeout: Duration,
    /// 最大重试次数
    pub max_retries: u32,
    /// 连接池大小
    pub connection_pool_size: usize,
    /// 用户代理字符串
    pub user_agent: String,
    /// 是否启用 HTTP/2
    pub enable_http2: bool,
}

impl Default for HttpClientConfig {
    fn default() -> Self {
        Self {
            timeout: Duration::from_secs(30),
            max_retries: 3,
            connection_pool_size: 10,
            user_agent: "c10_networks/0.1.0".to_string(),
            enable_http2: true,
        }
    }
}

impl HttpClientConfig {
    /// 设置超时时间
    ///
    /// # 参数
    ///
    /// * `timeout` - 超时时间
    ///
    /// # 示例
    ///
    /// ```rust
    /// use c10_networks::protocol::http::HttpClientConfig;
    /// use std::time::Duration;
    ///
    /// let config = HttpClientConfig::default()
    ///     .with_timeout(Duration::from_secs(60));
    /// ```
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = timeout;
        self
    }

    /// 设置最大重试次数
    ///
    /// # 参数
    ///
    /// * `max_retries` - 最大重试次数
    ///
    /// # 示例
    ///
    /// ```rust
    /// use c10_networks::protocol::http::HttpClientConfig;
    ///
    /// let config = HttpClientConfig::default()
    ///     .with_max_retries(5);
    /// ```
    pub fn with_max_retries(mut self, max_retries: u32) -> Self {
        self.max_retries = max_retries;
        self
    }
}
```

### 枚举文档

```rust
/// HTTP 状态码
///
/// 表示 HTTP 响应的状态码和相关信息。
///
/// # 示例
///
/// ```rust
/// use c10_networks::protocol::http::HttpStatusCode;
///
/// let status = HttpStatusCode::ok();
/// println!("状态码: {}", status.code);
/// println!("状态文本: {}", status.text);
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HttpStatusCode {
    /// 状态码数字
    pub code: u16,
    /// 状态文本
    pub text: &'static str,
}

impl HttpStatusCode {
    /// 创建新的状态码
    ///
    /// # 参数
    ///
    /// * `code` - 状态码数字
    /// * `text` - 状态文本
    ///
    /// # 示例
    ///
    /// ```rust
    /// use c10_networks::protocol::http::HttpStatusCode;
    ///
    /// let status = HttpStatusCode::new(200, "OK");
    /// ```
    pub fn new(code: u16, text: &'static str) -> Self {
        Self { code, text }
    }

    /// 200 OK
    ///
    /// 请求成功
    pub fn ok() -> Self {
        Self::new(200, "OK")
    }

    /// 201 Created
    ///
    /// 请求成功并创建了新资源
    pub fn created() -> Self {
        Self::new(201, "Created")
    }

    /// 400 Bad Request
    ///
    /// 请求语法错误
    pub fn bad_request() -> Self {
        Self::new(400, "Bad Request")
    }

    /// 401 Unauthorized
    ///
    /// 需要身份验证
    pub fn unauthorized() -> Self {
        Self::new(401, "Unauthorized")
    }

    /// 404 Not Found
    ///
    /// 请求的资源不存在
    pub fn not_found() -> Self {
        Self::new(404, "Not Found")
    }

    /// 500 Internal Server Error
    ///
    /// 服务器内部错误
    pub fn internal_server_error() -> Self {
        Self::new(500, "Internal Server Error")
    }

    /// 检查是否为成功状态码
    ///
    /// # 返回值
    ///
    /// 如果状态码在 200-299 范围内，返回 `true`
    ///
    /// # 示例
    ///
    /// ```rust
    /// use c10_networks::protocol::http::HttpStatusCode;
    ///
    /// let status = HttpStatusCode::ok();
    /// assert!(status.is_success());
    ///
    /// let status = HttpStatusCode::not_found();
    /// assert!(!status.is_success());
    /// ```
    pub fn is_success(&self) -> bool {
        self.code >= 200 && self.code < 300
    }

    /// 检查是否为客户端错误
    ///
    /// # 返回值
    ///
    /// 如果状态码在 400-499 范围内，返回 `true`
    pub fn is_client_error(&self) -> bool {
        self.code >= 400 && self.code < 500
    }

    /// 检查是否为服务器错误
    ///
    /// # 返回值
    ///
    /// 如果状态码在 500-599 范围内，返回 `true`
    pub fn is_server_error(&self) -> bool {
        self.code >= 500 && self.code < 600
    }
}
```

### 特性文档

```rust
/// 异步网络客户端特性
///
/// 定义了异步网络客户端的基本行为。
/// 所有网络客户端都应该实现这个特性。
///
/// # 示例
///
/// ```rust
/// use c10_networks::protocol::AsyncNetworkClient;
/// use std::time::Duration;
///
/// struct MyClient;
///
/// #[async_trait::async_trait]
/// impl AsyncNetworkClient for MyClient {
///     async fn connect(&mut self, address: &str) -> NetworkResult<()> {
///         // 实现连接逻辑
///         Ok(())
///     }
///
///     async fn send(&mut self, data: &[u8]) -> NetworkResult<()> {
///         // 实现发送逻辑
///         Ok(())
///     }
///
///     async fn receive(&mut self) -> NetworkResult<Vec<u8>> {
///         // 实现接收逻辑
///         Ok(vec![])
///     }
///
///     async fn disconnect(&mut self) -> NetworkResult<()> {
///         // 实现断开逻辑
///         Ok(())
///     }
/// }
/// ```
#[async_trait::async_trait]
pub trait AsyncNetworkClient: Send + Sync {
    /// 连接到远程服务器
    ///
    /// # 参数
    ///
    /// * `address` - 服务器地址
    ///
    /// # 返回值
    ///
    /// 连接成功返回 `Ok(())`，失败返回 `NetworkError`
    ///
    /// # 示例
    ///
    /// ```rust
    /// use c10_networks::protocol::AsyncNetworkClient;
    ///
    /// #[tokio::main]
    /// async fn main() -> NetworkResult<()> {
    ///     let mut client = MyClient::new();
    ///     client.connect("127.0.0.1:8080").await?;
    ///     Ok(())
    /// }
    /// ```
    async fn connect(&mut self, address: &str) -> NetworkResult<()>;

    /// 发送数据
    ///
    /// # 参数
    ///
    /// * `data` - 要发送的数据
    ///
    /// # 返回值
    ///
    /// 发送成功返回 `Ok(())`，失败返回 `NetworkError`
    async fn send(&mut self, data: &[u8]) -> NetworkResult<()>;

    /// 接收数据
    ///
    /// # 返回值
    /// 返回接收到的数据
    ///
    /// # 错误
    ///
    /// 如果接收失败，返回 `NetworkError`
    async fn receive(&mut self) -> NetworkResult<Vec<u8>>;

    /// 断开连接
    ///
    /// # 返回值
    ///
    /// 断开成功返回 `Ok(())`，失败返回 `NetworkError`
    async fn disconnect(&mut self) -> NetworkResult<()>;
}
```

## 🎨 文档样式

### 代码示例

```rust
/// 计算网络延迟
///
/// 通过发送 ping 包来测量网络延迟。
///
/// # 参数
///
/// * `host` - 目标主机
/// * `count` - ping 次数
///
/// # 返回值
///
/// 返回平均延迟时间
///
/// # 示例
///
/// ```rust
/// use c10_networks::diagnostics::ping;
/// use std::time::Duration;
///
/// #[tokio::main]
/// async fn main() -> Result<(), Box<dyn std::error::Error>> {
///     let latency = ping("example.com", 5).await?;
///     println!("平均延迟: {:?}", latency);
///     Ok(())
/// }
/// ```
///
/// # 错误处理
///
/// ```rust
/// use c10_networks::diagnostics::ping;
///
/// #[tokio::main]
/// async fn main() {
///     match ping("invalid-host", 1).await {
///         Ok(latency) => println!("延迟: {:?}", latency),
///         Err(e) => eprintln!("ping 失败: {}", e),
///     }
/// }
/// ```
///
/// # 性能考虑
///
/// ```rust
/// use c10_networks::diagnostics::ping;
/// use std::time::Instant;
///
/// #[tokio::main]
/// async fn main() -> Result<(), Box<dyn std::error::Error>> {
///     let start = Instant::now();
///     let latency = ping("example.com", 10).await?;
///     let duration = start.elapsed();
///     
///     println!("延迟: {:?}", latency);
///     println!("总耗时: {:?}", duration);
///     Ok(())
/// }
/// ```
pub async fn ping(host: &str, count: usize) -> NetworkResult<Duration> {
    // 实现
}
```

### 图表和流程图

```rust
/// 网络连接建立流程
///
/// 下图展示了网络连接建立的完整流程：
///
/// ```mermaid
/// sequenceDiagram
///     participant Client
///     participant Server
///     participant DNS
///     
///     Client->>DNS: 解析域名
///     DNS-->>Client: 返回IP地址
///     Client->>Server: TCP连接请求
///     Server-->>Client: 连接确认
///     Client->>Server: 发送数据
///     Server-->>Client: 响应数据
/// ```
///
/// # 状态转换
///
/// 连接状态转换图：
///
/// ```mermaid
/// stateDiagram-v2
///     [*] --> Closed
///     Closed --> Connecting : connect()
///     Connecting --> Connected : 连接成功
///     Connecting --> Closed : 连接失败
///     Connected --> Closed : disconnect()
///     Connected --> Closed : 连接错误
/// ```
pub struct NetworkConnection {
    // 实现
}
```

### 数学公式

```rust
/// 网络性能计算公式
///
/// 本函数实现了网络性能的数学计算模型。
///
/// # 公式
///
/// 网络延迟计算公式：
///
/// ```math
/// RTT = 2 \times \frac{distance}{speed\_of\_light} + processing\_time
/// ```
///
/// 吞吐量计算公式：
///
/// ```math
/// Throughput = \frac{data\_size}{RTT + transmission\_time}
/// ```
///
/// 其中：
/// - `RTT` 是往返时间
/// - `distance` 是网络距离
/// - `speed_of_light` 是光速
/// - `processing_time` 是处理时间
/// - `data_size` 是数据大小
/// - `transmission_time` 是传输时间
///
/// # 参数
///
/// * `distance` - 网络距离（公里）
/// * `data_size` - 数据大小（字节）
///
/// # 返回值
///
/// 返回性能指标结构体
///
/// # 示例
///
/// ```rust
/// use c10_networks::performance::calculate_metrics;
///
/// let metrics = calculate_metrics(1000.0, 1024);
/// println!("RTT: {:?}", metrics.rtt);
/// println!("吞吐量: {:.2} Mbps", metrics.throughput_mbps);
/// ```
pub fn calculate_metrics(distance: f64, data_size: usize) -> PerformanceMetrics {
    // 实现
}
```

### 链接和引用

```rust
/// 网络配置管理器
///
/// 用于管理网络连接的各种配置选项。
/// 支持从文件、环境变量和代码中加载配置。
///
/// # 相关类型
///
/// - [`NetworkConfig`] - 网络配置结构体
/// - [`ConfigError`] - 配置错误类型
/// - [`ConfigLoader`] - 配置加载器特性
///
/// # 相关模块
///
/// - [`crate::protocol`] - 协议实现模块
/// - [`crate::socket`] - 套接字模块
/// - [`crate::security`] - 安全模块
///
/// # 外部链接
///
/// - [Rust 网络编程指南](https://doc.rust-lang.org/book/)
/// - [Tokio 异步运行时](https://tokio.rs/)
/// - [HTTP/2 规范](https://tools.ietf.org/html/rfc7540)
///
/// # 示例
///
/// ```rust
/// use c10_networks::config::NetworkConfigManager;
/// use c10_networks::NetworkResult;
///
/// #[tokio::main]
/// async fn main() -> NetworkResult<()> {
///     let mut manager = NetworkConfigManager::new();
///     manager.load_from_file("config.toml").await?;
///     manager.load_from_env().await?;
///     
///     let config = manager.get_config();
///     println!("配置: {:?}", config);
///     Ok(())
/// }
/// ```
///
/// [`NetworkConfig`]: crate::config::NetworkConfig
/// [`ConfigError`]: crate::error::ConfigError
/// [`ConfigLoader`]: crate::config::ConfigLoader
pub struct NetworkConfigManager {
    // 实现
}
```

## 🔍 文档质量检查

### 文档覆盖率

```bash
#!/bin/bash
# scripts/check_docs.sh

set -e

echo "🔍 检查文档覆盖率..."

# 生成文档覆盖率报告
cargo doc --document-private-items --no-deps

# 检查缺失的文档
echo "📊 检查缺失的文档..."
cargo doc --document-private-items --no-deps 2>&1 | grep -E "warning.*missing.*docs" || true

# 检查文档链接
echo "🔗 检查文档链接..."
cargo doc --document-private-items --no-deps 2>&1 | grep -E "warning.*unresolved.*link" || true

echo "✅ 文档检查完成！"
```

### 示例代码验证

```bash
#!/bin/bash
# scripts/verify_examples.sh

set -e

echo "🧪 验证示例代码..."

# 编译所有示例
echo "📦 编译示例..."
cargo build --examples

# 运行示例测试
echo "🚀 运行示例测试..."
cargo test --examples

# 检查示例文档
echo "📖 检查示例文档..."
cargo doc --examples --no-deps

echo "✅ 示例验证完成！"
```

### 链接有效性

```bash
#!/bin/bash
# scripts/check_links.sh

set -e

echo "🔗 检查文档链接..."

# 生成文档
cargo doc --document-private-items --no-deps

# 检查内部链接
echo "📊 检查内部链接..."
cargo doc --document-private-items --no-deps 2>&1 | grep -E "warning.*unresolved.*link" || true

# 检查外部链接（需要额外工具）
if command -v linkchecker &> /dev/null; then
    echo "🌐 检查外部链接..."
    linkchecker target/doc/c10_networks/index.html
fi

echo "✅ 链接检查完成！"
```

## 📦 文档发布

### 本地文档服务

```bash
#!/bin/bash
# scripts/serve_docs.sh

set -e

echo "🚀 启动本地文档服务..."

# 生成文档
cargo doc --document-private-items --no-deps

# 启动本地服务器
echo "📖 文档服务地址: http://localhost:8000"
cd target/doc
python3 -m http.server 8000
```

### GitHub Pages

```yaml
# .github/workflows/docs.yml
name: Deploy Documentation

on:
  push:
    branches: [ main ]
  pull_request:
    branches: [ main ]

jobs:
  docs:
    runs-on: ubuntu-latest
    
    steps:
    - uses: actions/checkout@v4
    
    - name: Install Rust
      uses: actions-rs/toolchain@v1
      with:
        toolchain: stable
        components: rustfmt, clippy
        override: true
    
    - name: Generate Documentation
      run: |
        cargo doc --all-features --document-private-items --no-deps
    
    - name: Deploy to GitHub Pages
      if: github.ref == 'refs/heads/main'
      uses: peaceiris/actions-gh-pages@v3
      with:
        github_token: ${{ secrets.GITHUB_TOKEN }}
        publish_dir: ./target/doc
```

### docs.rs 发布

```toml
# Cargo.toml
[package.metadata.docs.rs]
# 启用所有特性
features = ["sniff", "tls", "offline", "pcap_live"]
all-features = true

# 默认目标平台
default-target = "x86_64-unknown-linux-gnu"

# Rust 编译器参数
rustc-args = ["--cfg", "docsrs"]

# 依赖配置
[dependencies]
# 文档依赖
tokio = { version = "1.35", features = ["full"] }
bytes = "1.0"
serde = { version = "1.0", features = ["derive"] }
```

## ❓ 常见问题

### Q: 如何生成包含私有项的文档？

A: 使用 `--document-private-items` 参数：

```bash
cargo doc --document-private-items
```

### Q: 如何生成特定特性的文档？

A: 使用 `--features` 参数：

```bash
cargo doc --features "sniff,tls"
```

### Q: 如何自定义文档样式？

A: 使用 `RUSTDOCFLAGS` 环境变量：

```bash
export RUSTDOCFLAGS="--html-in-header header.html --html-before-content before.html"
cargo doc
```

### Q: 如何验证示例代码？

A: 使用 `cargo test --examples` 命令：

```bash
cargo test --examples
```

### Q: 如何发布文档到 docs.rs？

A: 确保 `Cargo.toml` 中配置了 `[package.metadata.docs.rs]` 部分，然后发布到 crates.io。

### Q: 如何检查文档覆盖率？

A: 使用 `cargo doc` 命令并查看警告信息：

```bash
cargo doc --document-private-items 2>&1 | grep "missing.*docs"
```

---

**API 文档生成指南完成！** 🎉

现在您已经掌握了 C10 Networks 的完整文档生成和发布流程，可以创建高质量的 API 文档了。

*最后更新: 2025年1月*  
*文档版本: v1.0*  
*维护者: C10 Networks 开发团队*
