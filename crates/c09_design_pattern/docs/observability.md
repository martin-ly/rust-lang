# 可观测性指南（tracing 快速上手）


## 📊 目录

- [可观测性指南（tracing 快速上手）](#可观测性指南tracing-快速上手)
  - [📊 目录](#-目录)
  - [目标](#目标)
  - [建议依赖](#建议依赖)
  - [初始化示例](#初始化示例)
  - [链式调用标注](#链式调用标注)
  - [示例](#示例)
  - [最佳实践清单](#最佳实践清单)


## 目标

- 为责任链、装饰器、代理等链式调用提供可观测追踪（span/事件）。
- 结合执行模型（Sync/Async/Hybrid）在不同路径上观测时延与错误传播。

## 建议依赖

```toml
[features]
obs-tracing = ["tracing", "tracing-subscriber"]

[dev-dependencies]
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["fmt", "env-filter"] }
```

## 初始化示例

```rust
use tracing_subscriber::{fmt, EnvFilter};

fn init_tracing() {
    let filter = EnvFilter::try_from_default_env()
        .unwrap_or_else(|_| EnvFilter::new("info"));
    let subscriber = fmt().with_env_filter(filter).finish();
    tracing::subscriber::set_global_default(subscriber).ok();
}
```

## 链式调用标注

- 在每个处理步骤创建子 span 或事件；
- 聚合入口创建顶层 span，串起链路；
- 异步步骤用 `.instrument(span)` 绑定上下文；
- 失败路径记录 `error!` 并携带上下文键值。

## 示例

参见 `examples/tracing_chain.rs`（需 `--features obs-tracing`）。

```bash
cargo run --example tracing_chain --features obs-tracing | cat
```

## 最佳实践清单

- 为公共 API 增加 `request_id`/`span_id` 字段参数或上下文入口。
- 在责任链/中间件链上统一记录输入/输出大小与耗时。
- 与 `criterion` 基准结合：在基准前后启停 subscriber，避免噪声。
- 生产环境使用结构化日志/导出到后端（如 OTLP）。
