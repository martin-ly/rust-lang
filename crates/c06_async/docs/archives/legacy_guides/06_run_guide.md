# 运行指南

## 📊 目录

- [运行指南](#运行指南)
  - [📊 目录](#-目录)
  - [环境要求](#环境要求)
  - [基础命令](#基础命令)
    - [编译](#编译)
    - [检查语法](#检查语法)
  - [运行示例](#运行示例)
    - [基础异步示例](#基础异步示例)
    - [并发控制示例](#并发控制示例)
    - [高级模式示例](#高级模式示例)
    - [网络和服务器示例](#网络和服务器示例)
    - [工具和调试](#工具和调试)
  - [基准测试](#基准测试)
    - [编译基准测试](#编译基准测试)
    - [运行基准测试](#运行基准测试)
    - [基准测试结果](#基准测试结果)
  - [指标和监控](#指标和监控)
    - [Actix Web 指标端点](#actix-web-指标端点)
    - [可用指标](#可用指标)
    - [日志配置](#日志配置)
  - [故障排除](#故障排除)
    - [常见问题](#常见问题)
    - [调试技巧](#调试技巧)
  - [扩展开发](#扩展开发)
    - [添加新示例](#添加新示例)
    - [添加新基准测试](#添加新基准测试)
    - [添加新工具](#添加新工具)

## 环境要求

- Rust 1.89+
- Windows PowerShell 或 Linux/macOS 终端
- 网络访问（用于 HTTP 示例）

## 基础命令

### 编译

```powershell
cd .\crates\c06_async
cargo build
```

### 检查语法

```powershell
cargo check
```

## 运行示例

### 基础异步示例

```powershell
# 最小示例
cargo run --bin async_minimal_exp01

# Future 和 Stream 基础
cargo run --bin tokio_select_exp01
cargo run --bin tokio_try_join_exp01
cargo run --bin tokio_joinset_exp01

# 超时和取消
cargo run --bin tokio_timeout_cancel_exp01
cargo run --bin cancel_propagation_exp01
cargo run --bin select_timeout_fallback_exp01
```

### 并发控制示例

```powershell
# 限流和背压
cargo run --bin tokio_semaphore_limit_exp01
cargo run --bin tokio_mpsc_backpressure_exp01
cargo run --bin semaphore_mpsc_pipeline_exp01
cargo run --bin mpsc_backpressure_compare_exp01

# 结构化并发
cargo run --bin task_scope_structured_concurrency_exp01
cargo run --bin joinset_cancel_on_error_exp01
```

### 高级模式示例

```powershell
# 重试和错误处理
cargo run --bin retry_backoff_exp01
cargo run --bin concurrent_fetch_error_handling_exp01
cargo run --bin concurrent_fetch_reqwest_exp01

# 批处理和管道
cargo run --bin window_batch_semaphore_exp01
cargo run --bin mpsc_worker_pool_exp01
cargo run --bin stream_buffer_unordered_exp01
cargo run --bin pipeline_helper_exp01
cargo run --bin http_ingest_pipeline_exp01

# 配置驱动策略
cargo run --bin strategy_from_config_exp01
cargo run --bin advanced_strategy_exp01

# Prometheus 指标
cargo run --bin metrics_prometheus_exp01
# 端到端流水线指标导出
# pipeline_helper_exp01 暴露 http://127.0.0.1:9898/metrics
# http_ingest_pipeline_exp01 暴露 http://127.0.0.1:9899/metrics

# 状态同步
cargo run --bin tokio_watch_exp01
cargo run --bin tokio_broadcast_exp01

# !Send 与 LocalSet
cargo run --bin localset_nonsend_exp01

# 分布式模式
cargo run --bin distributed_lock_exp01
cargo run --bin stream_processing_exp01

# 微服务模式
cargo run --bin microservice_patterns_exp01

# 云原生特性
cargo run --bin cloud_native_exp01

# 事件溯源和一致性
cargo run --bin event_sourcing_exp01
cargo run --bin distributed_consensus_exp01

# 异步文件 I/O
cargo run --bin tokio_fs_async_io_exp01
```

### 网络和服务器示例

```powershell
# Actix Web 服务器
cargo run --bin actix_web_exp01

# 优雅关闭
cargo run --bin graceful_shutdown_exp01
```

### 工具和调试

```powershell
# 追踪和指标
cargo run --bin tracing_console_exp01

# 断路器模式
cargo run --bin circuit_breaker_exp01

# utils 组合演示
cargo run --bin utils_demo_exp01

# ExecHelper 增强示例（判定 + 截止时间）
cargo run --bin exec_helper_advanced_exp01
```

## 基准测试

### 编译基准测试

```powershell
cargo bench --no-run
```

### 运行基准测试

```powershell
# 运行所有基准测试
cargo bench

# 运行特定基准测试
cargo bench --bench async_benches -- mpsc_bounded
cargo bench --bench async_benches -- semaphore_limiter

# 生成详细报告
cargo bench --bench async_benches -- --verbose
```

### 基准测试结果

详细的性能对比结果请参考 `docs/benchmark_results.md`。

## 指标和监控

### Actix Web 指标端点

```powershell
# 启动服务器
cargo run --bin actix_web_exp01

# 访问指标端点（Prometheus 格式）
curl http://127.0.0.1:8080/metrics
```

### 可用指标

- `http_requests_total`: 总请求数
- `http_request_duration_nanoseconds_total`: 总延迟时间
- `http_requests_errors_total`: 错误请求数
- `http_slow_requests_total`: 慢速请求数（>1s）
- `http_request_duration_average_nanoseconds`: 平均延迟
- `http_error_rate_percentage`: 错误率百分比

### 日志配置

```powershell
# 设置日志级别
$env:RUST_LOG="info"
cargo run --bin actix_web_exp01
```

## 故障排除

### 常见问题

1. **PowerShell 执行策略**

   ```powershell
   Set-ExecutionPolicy -ExecutionPolicy RemoteSigned -Scope CurrentUser
   ```

2. **网络访问问题**
   - 确保防火墙允许本地连接
   - 检查端口 8080 是否被占用

3. **依赖下载失败**

   ```powershell
   cargo clean
   cargo update
   ```

### 调试技巧

1. **详细编译信息**

   ```powershell
   cargo build --verbose
   ```

2. **运行时日志**

   ```powershell
   $env:RUST_LOG="debug"
   cargo run --bin your_binary
   ```

3. **性能分析**

   ```powershell
   cargo bench --bench async_benches -- --verbose
   ```

## 扩展开发

### 添加新示例

1. 在 `src/bin/` 目录下创建新的 `.rs` 文件
2. 在 `Cargo.toml` 中添加必要的依赖
3. 更新本文档

### 添加新基准测试

1. 在 `benches/async_benches.rs` 中添加测试函数
2. 使用 `criterion` 的 `BenchmarkId` 进行参数化测试
3. 更新 `docs/benchmark_results.md`

### 添加新工具

1. 在 `src/utils/` 目录下创建新模块
2. 在 `src/utils/mod.rs` 中导出
3. 在 `src/lib.rs` 中声明为公共模块
