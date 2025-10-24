# 工程范式：默认安全与可靠性栈


## 📊 目录

- [默认策略](#默认策略)
- [Tower 中间件矩阵](#tower-中间件矩阵)
- [验证与基准](#验证与基准)
  - [运行指南](#运行指南)


## 默认策略

- 所有对外异步入口：必须携带超时/取消/背压
- 通道：优先有界容量 + 明确溢出策略（丢弃/阻塞/最新优先）
- I/O：区分阻塞/非阻塞；提供 `spawn_blocking` 网关
- 观测：`tracing` 全链路 span + 指标与错误上下文

## Tower 中间件矩阵

- 限流、重试、熔断、缓冲、超时；组合次序建议与反模式
- 示例：`examples/tower_reliability.rs`（启用 `--features tower-examples,tokio-adapter`）

## 验证与基准

- `loom` 并发快测；`proptest` 属性不变量；`criterion` 微基准

### 运行指南

- 并发验证（loom）：`cargo test -p c18_model --test concurrency_loom`
- 微基准（criterion）：`cargo bench -p c18_model --bench concurrency_bench`
