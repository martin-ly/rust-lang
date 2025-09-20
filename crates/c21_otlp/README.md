# OpenTelemetry Protocol (OTLP) Implementation for Rust 1.90

[![Rust](https://img.shields.io/badge/rust-1.90+-orange.svg)](https://www.rust-lang.org/)
[![License](https://img.shields.io/badge/license-MIT%20OR%20Apache--2.0-blue.svg)](LICENSE)
[![Crates.io](https://img.shields.io/crates/v/c21_otlp.svg)](https://crates.io/crates/c21_otlp)

一个基于Rust 1.90语言特性的OpenTelemetry协议(OTLP)完整实现，支持同步和异步结合的遥测数据收集、处理和传输。

## 🚀 核心特性

- **异步优先设计**: 利用Rust 1.90的async/await特性实现高性能异步处理
- **同步兼容**: 提供同步API接口，支持传统同步代码集成
- **多传输协议**: 支持gRPC和HTTP/JSON两种OTLP传输方式
- **类型安全**: 利用Rust类型系统确保编译时安全性
- **零拷贝优化**: 使用Rust 1.90的内存管理特性优化性能
- **并发安全**: 基于Rust的所有权系统实现无锁并发
- **完整错误处理**: 提供详细的错误类型和重试机制
- **性能监控**: 内置指标收集和性能分析功能

## 📋 系统要求

- Rust 1.90+
- 支持异步运行时的操作系统
- 网络连接（用于数据传输）

## 🛠️ 安装

在`Cargo.toml`中添加依赖：

```toml
[dependencies]
c21_otlp = "0.1.0"
tokio = { version = "1.0", features = ["full"] }
```

## 📖 快速开始

### 基本使用

```rust
use c21_otlp::{OtlpClient, OtlpConfig, TelemetryData};
use c21_otlp::data::{LogSeverity, StatusCode};
use c21_otlp::transport::TransportProtocol;
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建OTLP配置
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Grpc)
        .with_service("my-service", "1.0.0")
        .with_timeout(Duration::from_secs(10));
    
    // 创建并初始化客户端
    let client = OtlpClient::new(config).await?;
    client.initialize().await?;
    
    // 发送追踪数据
    let result = client.send_trace("example-operation").await?
        .with_attribute("service.name", "my-service")
        .with_attribute("service.version", "1.0.0")
        .with_numeric_attribute("duration", 150.0)
        .with_status(StatusCode::Ok, Some("操作成功".to_string()))
        .finish()
        .await?;
    
    println!("追踪数据发送结果: 成功 {} 条", result.success_count);
    
    // 发送指标数据
    let result = client.send_metric("request_count", 1.0).await?
        .with_label("method", "GET")
        .with_label("endpoint", "/api/health")
        .with_description("HTTP请求计数")
        .with_unit("count")
        .send()
        .await?;
    
    println!("指标数据发送结果: 成功 {} 条", result.success_count);
    
    // 发送日志数据
    let result = client.send_log("用户登录成功", LogSeverity::Info).await?
        .with_attribute("user_id", "12345")
        .with_attribute("ip_address", "192.168.1.100")
        .with_trace_context("trace-123", "span-456")
        .send()
        .await?;
    
    println!("日志数据发送结果: 成功 {} 条", result.success_count);
    
    // 关闭客户端
    client.shutdown().await?;
    
    Ok(())
}
```

### 批量发送

```rust
// 批量发送数据
let mut batch_data = Vec::new();

for i in 0..100 {
    let trace_data = TelemetryData::trace(format!("operation-{}", i))
        .with_attribute("batch_id", "batch-001")
        .with_attribute("operation_index", i.to_string());
    
    batch_data.push(trace_data);
}

let result = client.send_batch(batch_data).await?;
println!("批量发送结果: 成功 {} 条", result.success_count);
```

### 异步发送

```rust
// 异步并发发送
let mut futures = Vec::new();

for i in 0..10 {
    let client_clone = client.clone();
    let future = tokio::spawn(async move {
        client_clone.send_trace(format!("async-operation-{}", i)).await?
            .with_attribute("async", "true")
            .finish()
            .await
    });
    futures.push(future);
}

// 等待所有异步操作完成
for future in futures {
    let result = future.await??;
    println!("异步操作结果: 成功 {} 条", result.success_count);
}
```

## 🏗️ 架构设计

### 整体架构

```text
┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
│   数据收集层     │    │   数据处理层     │    │   数据传输层     │
│  (Collection)   │───▶│  (Processing)   │───▶│  (Transport)    │
│                 │    │                 │    │                 │
│ • Traces        │    │ • 过滤/聚合      │    │ • gRPC          │
│ • Metrics       │    │ • 批处理        │    │ • HTTP/JSON     │
│ • Logs          │    │ • 压缩          │    │ • 重试机制      │
└─────────────────┘    └─────────────────┘    └─────────────────┘
```

### 核心组件

1. **OtlpClient**: 高级客户端接口，提供完整的OTLP功能
2. **OtlpExporter**: 数据导出器，负责将数据发送到远程端点
3. **OtlpProcessor**: 数据处理器，支持过滤、聚合和批处理
4. **Transport**: 传输层，支持gRPC和HTTP两种协议
5. **Data Models**: 完整的数据模型，支持追踪、指标和日志

## 🔧 配置选项

### 基本配置

```rust
let config = OtlpConfig::default()
    .with_endpoint("http://localhost:4317")           // 服务端点
    .with_protocol(TransportProtocol::Grpc)           // 传输协议
    .with_service("my-service", "1.0.0")              // 服务信息
    .with_timeout(Duration::from_secs(10))            // 请求超时
    .with_debug(true);                                // 调试模式
```

### 高级配置

```rust
let config = OtlpConfig::default()
    .with_endpoint("https://api.example.com/otlp")
    .with_protocol(TransportProtocol::Http)
    .with_compression(Compression::Gzip)              // 压缩算法
    .with_api_key("your-api-key")                     // API密钥
    .with_bearer_token("your-bearer-token")           // Bearer令牌
    .with_tls(true)                                   // 启用TLS
    .with_sampling_ratio(0.1)                         // 采样率
    .with_resource_attribute("environment", "production")
    .with_resource_attribute("region", "us-west-2");
```

### 批处理配置

```rust
let batch_config = BatchConfig {
    max_export_batch_size: 512,                       // 批处理大小
    export_timeout: Duration::from_millis(5000),      // 批处理超时
    max_queue_size: 2048,                             // 最大队列大小
    scheduled_delay: Duration::from_millis(5000),     // 调度间隔
};

let config = OtlpConfig::default()
    .with_batch_config(batch_config);
```

### 重试配置

```rust
let retry_config = RetryConfig {
    max_retries: 5,                                   // 最大重试次数
    initial_retry_delay: Duration::from_millis(1000), // 初始重试延迟
    max_retry_delay: Duration::from_secs(30),         // 最大重试延迟
    retry_delay_multiplier: 2.0,                      // 重试延迟倍数
    randomize_retry_delay: true,                      // 随机化重试延迟
};

let config = OtlpConfig::default()
    .with_retry_config(retry_config);
```

## 📊 性能特性

### 异步处理

- 基于Tokio异步运行时
- 支持高并发数据处理
- 非阻塞I/O操作
- 异步批处理机制

### 内存优化

- 零拷贝数据传输
- 高效的内存管理
- 自动垃圾回收
- 内存池技术

### 网络优化

- 连接池管理
- 自动重连机制
- 压缩传输
- 负载均衡

## 🔍 监控和调试

### 指标收集

```rust
// 获取客户端指标
let metrics = client.get_metrics().await;
println!("总发送数据量: {}", metrics.total_data_sent);
println!("总接收数据量: {}", metrics.total_data_received);
println!("运行时间: {:?}", metrics.uptime);
println!("平均导出延迟: {:?}", metrics.exporter_metrics.average_export_latency);
```

### 调试模式

```rust
let config = OtlpConfig::default()
    .with_debug(true);  // 启用调试模式

// 调试信息将输出到控制台
```

### 日志记录

```rust
use tracing_subscriber;

// 初始化日志系统
tracing_subscriber::fmt::init();

// 日志将自动记录OTLP操作
```

## 🧪 测试

### 运行测试

```bash
# 运行所有测试
cargo test

# 运行特定测试
cargo test test_client_creation

# 运行性能测试
cargo bench
```

### 集成测试

```bash
# 启动测试服务器
docker run -p 4317:4317 -p 4318:4318 otel/opentelemetry-collector

# 运行集成测试
cargo test --test integration
```

## 📚 文档导航

### 2025年综合分析文档

- **[OTLP国际标准分析](docs/standards/OTLP_INTERNATIONAL_STANDARDS_2025.md)** - 协议标准、软件堆栈、云原生集成
- **[同步异步控制流分析](docs/sync_async/OTLP_SYNC_ASYNC_CONTROL_FLOW_2025.md)** - 控制流、执行流、数据流设计
- **[算法和设计模式](docs/algorithms/OTLP_ALGORITHMS_DESIGN_PATTERNS_2025.md)** - 核心算法、设计模式、架构组合
- **[采样控制和动态调整](docs/sampling/OTLP_SAMPLING_CONTROL_2025.md)** - 日志采集、采样策略、动态调整
- **[递归和调度组合](docs/advanced/OTLP_RECURSIVE_MIXED_SCHEDULING_2025.md)** - 递归处理、混合执行、智能调度
- **[执行流组织](docs/flow_organization/OTLP_EXECUTION_FLOW_ORGANIZATION_2025.md)** - 执行流、控制流、数据流组织
- **[综合使用示例](docs/examples/OTLP_COMPREHENSIVE_USAGE_EXAMPLES_2025.md)** - 基础用法、高级特性、实际应用
- **[文档索引](docs/OTLP_2025_COMPREHENSIVE_DOCUMENTATION_INDEX.md)** - 完整文档导航和使用指南

### API文档

#### 主要类型

- `OtlpClient`: OTLP客户端主接口
- `OtlpConfig`: 客户端配置
- `TelemetryData`: 遥测数据
- `ExportResult`: 导出结果
- `OtlpError`: 错误类型

#### 数据模型

- `TraceData`: 追踪数据
- `MetricData`: 指标数据
- `LogData`: 日志数据
- `AttributeValue`: 属性值
- `SpanStatus`: 跨度状态

#### 传输协议

- `TransportProtocol`: 传输协议枚举
- `GrpcTransport`: gRPC传输实现
- `HttpTransport`: HTTP传输实现
- `TransportPool`: 传输池管理

## 🤝 贡献指南

1. Fork 项目
2. 创建特性分支 (`git checkout -b feature/amazing-feature`)
3. 提交更改 (`git commit -m 'Add amazing feature'`)
4. 推送到分支 (`git push origin feature/amazing-feature`)
5. 打开 Pull Request

## 📄 许可证

本项目采用 MIT 或 Apache-2.0 双重许可证。详情请参阅 [LICENSE](LICENSE) 文件。

## 🙏 致谢

- [OpenTelemetry](https://opentelemetry.io/) - 提供OTLP协议标准
- [Rust社区](https://www.rust-lang.org/community) - 提供优秀的语言和工具
- [Tokio](https://tokio.rs/) - 提供异步运行时
- [Tonic](https://github.com/hyperium/tonic) - 提供gRPC实现

## 📞 支持

如果您遇到问题或有任何建议，请：

1. 查看 [Issues](https://github.com/your-repo/c21_otlp/issues)
2. 创建新的 Issue
3. 联系维护者

---

**注意**: 这是一个演示项目，展示了如何使用Rust 1.90的语言特性实现OTLP协议。
在生产环境中使用前，请进行充分的测试和性能评估。
