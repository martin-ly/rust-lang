# c06_async 运行指南（Rust 1.89 对标）

## 准备

- 在工作区根目录执行命令时，先切换到本 crate：
  - Windows PowerShell: `cd .\\crates\\c06_async`

## 构建

```bash
cargo build
```

## 运行默认二进制

```bash
cargo run --bin c06_async
```

## 运行异步示例二进制

- select 多路复用：

```bash
cargo run --bin tokio_select_exp01
```

- try_join 并行等待：

```bash
cargo run --bin tokio_try_join_exp01
```

- JoinSet 动态任务集：

```bash
cargo run --bin tokio_joinset_exp01
```

- 超时与取消：

```bash
cargo run --bin tokio_timeout_cancel_exp01
```

- tracing 日志示例（配合 tokio 多任务）：

```bash
cargo run --bin tracing_console_exp01
```

- Actix Web 示例（含限流/超时/指标）：

```bash
cargo run --bin actix_web_exp01
# 访问：
# http://127.0.0.1:8080/greet/World
# http://127.0.0.1:8080/slow
# http://127.0.0.1:8080/metrics
```

- select 偏好/分支：

```bash
cargo run --bin tokio_select_prefs_exp01
```

- try_join、JoinSet、取消传播与降级：

```bash
cargo run --bin cancel_propagation_exp01
cargo run --bin select_timeout_fallback_exp01
```

- 限流与背压：

```bash
cargo run --bin tokio_semaphore_limit_exp01
cargo run --bin tokio_mpsc_backpressure_exp01
cargo run --bin semaphore_mpsc_pipeline_exp01
cargo run --bin mpsc_backpressure_compare_exp01
```

- 并发抓取与错误处理：

```bash
cargo run --bin concurrent_fetch_error_handling_exp01
```

- 窗口批处理与限速：

```bash
cargo run --bin window_batch_semaphore_exp01
```

- 重试与指数退避：

```bash
cargo run --bin retry_backoff_exp01
```

## 工具模块（utils）

- 重试器：`retry_with_backoff`
- 超时：`with_timeout`
- 限流器：`SemaphoreLimiter`

上述工具已接入部分示例（重试/降级/管道限速），可复用在你的业务代码中。

- 结构化并发（JoinSet）：

```bash
cargo run --bin task_scope_structured_concurrency_exp01
```

- 状态/事件发布：

```bash
cargo run --bin tokio_watch_exp01
cargo run --bin tokio_broadcast_exp01
```

- 优雅关闭：

```bash
cargo run --bin graceful_shutdown_exp01
```

- 工作池（有界队列）：

```bash
cargo run --bin mpsc_worker_pool_exp01
```

- 断路器（示例）：

```bash
cargo run --bin circuit_breaker_exp01
```

## 说明与注意事项

- Windows PowerShell 中不需要通过管道传给 `cat`，直接运行 `cargo run ...` 即可。
- tracing 示例默认使用 `INFO` 日志级别，可在代码中调整 `with_max_level`。
- 网络相关示例如 `streams::demo_buffer_unordered` 需外网访问权限，否则可能表现为空或报错。
- 若需要调度器差异对比，可在示例中切换 `#[tokio::main]` 的 flavor（`current_thread`/`multi_thread`）。
