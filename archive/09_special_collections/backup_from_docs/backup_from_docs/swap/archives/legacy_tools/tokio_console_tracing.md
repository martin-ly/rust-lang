# Tokio Console 与 Tracing 指南（Rust 1.90）

## 目录

- [Tokio Console 与 Tracing 指南（Rust 1.90）](#tokio-console-与-tracing-指南rust-190)
  - [目录](#目录)
  - [1. 目标与范围](#1-目标与范围)
  - [2. Tracing 基本用法与结构化日志](#2-tracing-基本用法与结构化日志)
  - [3. tokio-console 使用与注意事项](#3-tokio-console-使用与注意事项)
  - [4. 生产环境建议（采样、过滤、负载）](#4-生产环境建议采样过滤负载)
  - [5. 集成清单（本仓示例）](#5-集成清单本仓示例)
    - [指标命名规范与仪表盘模板（新增）](#指标命名规范与仪表盘模板新增)
    - [给任意 demo 挂载指标（最小片段）](#给任意-demo-挂载指标最小片段)
    - [推荐 PromQL 与仪表盘（网关与混合样例）](#推荐-promql-与仪表盘网关与混合样例)
      - [基准（benchmarks，端口 9900）](#基准benchmarks端口-9900)
  - [6. 参考资料](#6-参考资料)
    - [Grafana 仪表盘模板与导入](#grafana-仪表盘模板与导入)
    - [一键启动本地观测栈（Prometheus + Grafana）](#一键启动本地观测栈prometheus--grafana)

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

### 指标命名规范与仪表盘模板（新增）

- 命名规范（建议）：
  - 前缀按域划分：`actor_*`、`mailbox_*`、`stage_*`、`pipeline_*`
  - 计数器：`*_total`；仪表：`*_current`/`*_inflight`；直方图：`*_seconds` / `*_duration_ms`
  - 标签：`actor`、`stage`、`tenant_id`、`msg_type`
- 最小集合：
  - `actor_mailbox_len_current{actor}`、`actor_restart_total{actor}`
  - `mailbox_inflight`、`stage_processed_total{stage}`、`stage_dropped_total{stage}`
  - `stage_process_seconds{stage}`（P50/P95/P99.9）
- 仪表盘区块：
  - 流量：总 QPS、各优先级入/出队速率
  - 延迟：`stage_process_seconds` 分位曲线（叠加版本/发布窗口）
  - 队列：各邮箱/通道长度、滞留时间
  - 可靠性：丢弃率、重启次数、错误类型 Top-N
  - 资源：任务数、RSS/堆外、FD、上下文切换

### 给任意 demo 挂载指标（最小片段）

```rust
use once_cell::sync::Lazy;
use prometheus::{Registry, IntCounter, Histogram, HistogramOpts, Opts};

static DEMO_EXEC_TOTAL: Lazy<IntCounter> = Lazy::new(|| IntCounter::with_opts(Opts::new("demo_exec_total", "demo 执行总次数")).unwrap());
static DEMO_EXEC_SECONDS: Lazy<Histogram> = Lazy::new(|| Histogram::with_opts(HistogramOpts::new("demo_exec_seconds", "demo 执行耗时(秒)")).unwrap());

// main 中：
let registry = Registry::new();
let _ = registry.register(Box::new(DEMO_EXEC_TOTAL.clone()));
let _ = registry.register(Box::new(DEMO_EXEC_SECONDS.clone()));
let metrics_handle = tokio::spawn(c06_async::utils::metrics::serve_metrics(registry.clone(), "127.0.0.1:9899"));

// demo 运行前后：
let t = std::time::Instant::now();
demo().await?;
DEMO_EXEC_TOTAL.inc();
DEMO_EXEC_SECONDS.observe(t.elapsed().as_secs_f64());
```

### 推荐 PromQL 与仪表盘（网关与混合样例）

- 网关请求漏斗：
  - QPS：`rate(gateway_request_total[1m])`
  - 耗时分位（近似）：`histogram_quantile(0.95, rate(gateway_request_seconds_bucket[5m]))`
  - 限流命中：`increase(gateway_rate_limited_total[5m]) by (reason)`
  - 后端状态分布：`increase(gateway_backend_status_total[5m]) by (status)`
  - 实例选择分布：`increase(gateway_instance_pick_total[5m]) by (instance)`

- Actor×CSP 混合（进阶样例）：
  - 处理吞吐：`rate(stage_processed_total[1m])`
  - 丢弃率：`rate(stage_dropped_total[1m])`
  - 阶段耗时分位：`histogram_quantile(0.99, rate(stage_process_seconds_bucket[5m]))`
  - 在途估算/邮箱：`mailbox_inflight`（或按场景替换为实际队列长度指标）

- 面板建议：
  - 概览：总体 QPS、P50/P95/P99、错误率、限流命中率
  - 网关：状态码堆叠图、实例选择 Top-N、路径级 P95
  - 混合样例：阶段吞吐与长尾、丢弃原因、在途与队列长度
- 资源：任务数、CPU/内存、上下文切换（结合节点级导出器）

#### 基准（benchmarks，端口 9900）

- 执行速率：`rate(bench_exec_total[1m])`
- 耗时分位（如 P95）：`histogram_quantile(0.95, rate(bench_exec_seconds_bucket[5m]))`

## 6. 参考资料

- Tokio 官方文档与 tokio-console 项目说明
- tracing 与 tracing-subscriber 文档
- OpenTelemetry 集成资料（可选）

### Grafana 仪表盘模板与导入

- 模板位置：
  - `docs/dashboard_templates/gateway_dashboard.json`
  - `docs/dashboard_templates/hybrid_dashboard.json`
- 导入步骤：
  1) 打开 Grafana → Dashboards → Import
  2) 上传 JSON 文件或粘贴内容
  3) 选择 Prometheus 数据源 → Import
  4) 调整时间范围与变量（若有）

### 一键启动本地观测栈（Prometheus + Grafana）

- 先启动示例以暴露 `/metrics`：
  - 混合样例：`cargo run --example actor_csp_hybrid_advanced`
  - 网关样例：`cargo run --example async_api_gateway_2025`
- 启动观测栈：

  ```bash
  docker compose -f deployment/docker-compose.observability.yml up -d
  # Prometheus: http://localhost:9090  Grafana: http://localhost:3000 (admin/admin)
  ```

- Prometheus 抓取配置：`configs/prometheus.yml`（已包含 9897/9898 两个目标）。
