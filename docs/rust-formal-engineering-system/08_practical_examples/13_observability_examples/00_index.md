# 可观测性示例（Observability Examples）索引

> **创建日期**: 2025-10-31
> **最后更新**: 2025-11-10
> **Rust 版本**: 1.91.0 (Edition 2024) ✅
> **状态**: 已完善 ✅

---

## 📊 目录

- [可观测性示例（Observability Examples）索引](#可观测性示例observability-examples索引)
  - [📊 目录](#-目录)
  - [🎯 目的](#-目的)
    - [核心价值](#核心价值)
  - [📚 核心示例](#-核心示例)
    - [1. 日志记录（Logging）](#1-日志记录logging)
    - [2. 指标监控（Metrics）](#2-指标监控metrics)
    - [3. 分布式追踪（Distributed Tracing）](#3-分布式追踪distributed-tracing)
    - [4. 健康检查（Health Checks）](#4-健康检查health-checks)
  - [💻 实践与样例](#-实践与样例)
    - [代码示例位置](#代码示例位置)
    - [文件级清单（精选）](#文件级清单精选)
      - [`crates/c83_observability/src/`](#cratesc83_observabilitysrc)
      - [`crates/c84_monitoring/src/`](#cratesc84_monitoringsrc)
    - [快速开始示例](#快速开始示例)
  - [相关索引](#相关索引)
  - [导航](#导航)

## 🎯 目的

本模块提供 Rust 可观测性开发的实用示例，涵盖日志记录、指标监控、分布式追踪和健康检查等核心功能。
所有示例均基于 Rust 1.91.0 和当前最佳实践。

### 核心价值

- **实用性强**: 所有示例均可直接运行
- **最佳实践**: 基于 Rust 社区最新实践
- **完整覆盖**: 涵盖可观测性的各个方面
- **易于理解**: 提供详细注释和说明

## 📚 核心示例

### 1. 日志记录（Logging）

**推荐库**: `tracing`, `log`, `env_logger`, `slog`

- **结构化日志**: 使用 `tracing` 进行结构化日志记录
- **日志级别管理**: 动态调整日志级别
- **日志聚合**: 集成到 ELK、Loki 等日志系统
- **日志分析**: 日志查询和分析示例

**相关资源**:

- [tracing 官方文档](https://docs.rs/tracing/)
- [log crate 文档](https://docs.rs/log/)

### 2. 指标监控（Metrics）

**推荐库**: `prometheus`, `metrics`, `opentelemetry`

- **性能指标**: CPU、内存、网络等系统指标
- **业务指标**: 自定义业务指标收集
- **自定义指标**: 创建自定义指标类型
- **指标可视化**: 集成 Grafana 等可视化工具

**相关资源**:

- [prometheus 客户端库](https://docs.rs/prometheus/)
- [OpenTelemetry Rust](https://opentelemetry.io/docs/instrumentation/rust/)

### 3. 分布式追踪（Distributed Tracing）

**推荐库**: `opentelemetry`, `tracing-opentelemetry`, `jaeger`

- **请求追踪**: 跨服务请求追踪
- **服务依赖**: 服务依赖关系可视化
- **性能分析**: 性能瓶颈分析
- **错误追踪**: 错误传播和追踪

**相关资源**:

- [OpenTelemetry Rust](https://opentelemetry.io/docs/instrumentation/rust/)
- [Jaeger 文档](https://www.jaegertracing.io/docs/)

### 4. 健康检查（Health Checks）

**推荐库**: `axum`, `actix-web`, `warp`

- **服务健康检查**: HTTP 健康检查端点
- **依赖健康检查**: 数据库、缓存等依赖检查
- **自定义健康检查**: 实现自定义健康检查逻辑
- **健康状态报告**: 详细的健康状态报告

**相关资源**:

- [axum 健康检查示例](https://docs.rs/axum/)
- [actix-web 健康检查](https://actix.rs/)

## 💻 实践与样例

### 代码示例位置

- **可观测性示例**: [crates/c83_observability](../../../crates/c83_observability/)
- **监控系统**: [crates/c84_monitoring](../../../crates/c84_monitoring/)
- **日志系统**: [crates/c85_logging](../../../crates/c85_logging/)

### 文件级清单（精选）

#### `crates/c83_observability/src/`

- `logging_examples.rs` - 日志记录示例
  - 结构化日志
  - 日志级别管理
  - 日志格式化
- `metrics_examples.rs` - 指标监控示例
  - Prometheus 指标
  - 自定义指标
  - 指标导出
- `tracing_examples.rs` - 分布式追踪示例
  - OpenTelemetry 集成
  - 跨服务追踪
  - 性能分析
- `health_checks.rs` - 健康检查示例
  - HTTP 健康检查
  - 依赖健康检查
  - 健康状态报告

#### `crates/c84_monitoring/src/`

- `performance_monitoring.rs` - 性能监控示例
- `business_monitoring.rs` - 业务监控示例
- `alerting_system.rs` - 告警系统示例

### 快速开始示例

```rust
// 使用 tracing 进行日志记录
use tracing::{info, error, warn};

fn main() {
    tracing_subscriber::fmt::init();

    info!("应用启动");
    // ... 应用逻辑
    warn!("警告信息");
    error!("错误信息");
}
```

```rust
// 使用 prometheus 进行指标收集
use prometheus::{Counter, Registry};

let counter = Counter::new("requests_total", "Total requests").unwrap();
let registry = Registry::new();
registry.register(Box::new(counter.clone())).unwrap();

counter.inc();
```

## 相关索引

- 理论基础（并发模型）：[`../../01_theoretical_foundations/04_concurrency_models/00_index.md`](../../01_theoretical_foundations/04_concurrency_models/00_index.md)
- 编程范式（异步）：[`../../02_programming_paradigms/02_async/00_index.md`](../../02_programming_paradigms/02_async/00_index.md)
- 工具链生态（监控）：[`../../06_toolchain_ecosystem/10_monitoring/00_index.md`](../../06_toolchain_ecosystem/10_monitoring/00_index.md)

## 📚 内容文档

- **[追踪和日志](./01_tracing_and_logging.md)** - 追踪和日志实践示例 ✅

## 导航

- 返回实用示例：[`../00_index.md`](../00_index.md)
- 消息队列示例：[`../12_messaging_examples/00_index.md`](../12_messaging_examples/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
