# 可观测性示例（Observability Examples）索引

## 📊 目录

- [可观测性示例（Observability Examples）索引](#可观测性示例observability-examples索引)
  - [📊 目录](#-目录)
  - [目的](#目的)
  - [核心示例](#核心示例)
    - [日志记录](#日志记录)
    - [指标监控](#指标监控)
    - [分布式追踪](#分布式追踪)
    - [健康检查](#健康检查)
  - [实践与样例](#实践与样例)
    - [文件级清单（精选）](#文件级清单精选)
  - [相关索引](#相关索引)
  - [导航](#导航)

## 目的

- 提供 Rust 可观测性开发的实用示例。
- 展示如何构建可观测的系统。

## 核心示例

### 日志记录

- 结构化日志示例
- 日志级别管理
- 日志聚合示例
- 日志分析示例

### 指标监控

- 性能指标示例
- 业务指标示例
- 自定义指标示例
- 指标可视化示例

### 分布式追踪

- 请求追踪示例
- 服务依赖追踪
- 性能分析示例
- 错误追踪示例

### 健康检查

- 服务健康检查
- 依赖健康检查
- 自定义健康检查
- 健康状态报告

## 实践与样例

- 可观测性示例：参见 [crates/c83_observability](../../../crates/c83_observability/)
- 监控系统：[crates/c84_monitoring](../../../crates/c84_monitoring/)
- 日志系统：[crates/c85_logging](../../../crates/c85_logging/)

### 文件级清单（精选）

- `crates/c83_observability/src/`：
  - `logging_examples.rs`：日志记录示例
  - `metrics_examples.rs`：指标监控示例
  - `tracing_examples.rs`：分布式追踪示例
  - `health_checks.rs`：健康检查示例
- `crates/c84_monitoring/src/`：
  - `performance_monitoring.rs`：性能监控示例
  - `business_monitoring.rs`：业务监控示例
  - `alerting_system.rs`：告警系统示例

## 相关索引

- 理论基础（并发模型）：[`../../01_theoretical_foundations/04_concurrency_models/00_index.md`](../../01_theoretical_foundations/04_concurrency_models/00_index.md)
- 编程范式（异步）：[`../../02_programming_paradigms/02_async/00_index.md`](../../02_programming_paradigms/02_async/00_index.md)
- 工具链生态（监控）：[`../../06_toolchain_ecosystem/10_monitoring/00_index.md`](../../06_toolchain_ecosystem/10_monitoring/00_index.md)

## 导航

- 返回实用示例：[`../00_index.md`](../00_index.md)
- 消息队列示例：[`../12_messaging_examples/00_index.md`](../12_messaging_examples/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
