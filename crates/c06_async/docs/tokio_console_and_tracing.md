# Tokio Console 与 Tracing 指南（Rust 1.90）

## 0. 目录（严格编号）

1. 目标与范围
2. Tracing 基本用法与结构化日志
3. tokio-console 使用与注意事项
4. 生产环境建议（采样、过滤、负载）
5. 集成清单（本仓示例）
6. 参考资料

## 1. 目标与范围

提供开发/压测阶段的任务观测与结构化日志方案；生产环境采用轻量采样与分级输出，避免影响性能。

## 2. Tracing 基本用法与结构化日志

- 初始化：

  ```rust
  tracing_subscriber::fmt().with_env_filter("info").init();
  ```

- JSON 输出（生产更友好）：

  ```rust
  tracing_subscriber::fmt().json().with_env_filter("info").init();
  ```

- 语义化字段：`tracing::info!(%user_id, latency_ms, "done")`。

## 3. tokio-console 使用与注意事项

- 启用特性与运行：
  - 依赖：`tokio-console`（已在 workspace）
  - 运行时环境变量：
    - `RUSTFLAGS="--cfg tokio_unstable"`
    - `TOKIO_CONSOLE_BIND=127.0.0.1:6669`
    - `TOKIO_CONSOLE_RETENTION=60s`
- 适用场景：开发/压测阶段定位任务阻塞、资源竞争；生产谨慎开启。

## 4. 生产环境建议（采样、过滤、负载）

- 过滤级别按模块划分；敏感路径仅在告警时临时上调。
- 采样与限频：降低高 QPS 路径日志量；指标优先于详细日志。
- 指标导出配合 Prometheus：QPS、p50/p95/p99 延迟、队列长度、丢弃率。

## 5. 集成清单（本仓示例）

- `examples/tokio_patterns.rs`：结构化日志、并发限额、背压示例。
- `examples/tokio_axum_sqlx.rs`：HTTP + DB，演示超时边界与后续重试拓展。
- `docs/async_cookbook_tokio_smol.md`：可复制片段（Tokio/Smol）。

## 6. 参考资料

- Tokio 官方文档与 tokio-console 项目说明
- tracing 与 tracing-subscriber 文档
- OpenTelemetry 集成资料（可选）
