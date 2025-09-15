# 并发与异步：Rust 1.89 对标与工程实践

本章节提供 Rust 1.89 语义与生态的并发/异步系统化对标，包含：

- 同步模型（线程、内存模型、同步原语、消息传递）
- 异步模型（Future/Pin/Waker、执行器、取消、背压、结构化并发）
- 统一运行时能力抽象（Spawner/Timer/Net/Channel/Cancellation/Observability）
- 验证与基准（loom、proptest、criterion、tracing）
- 国际资料对齐（Wiki/名校课程/论文/Rust 团队文档）

建议配合 `c20_distributed` 的示例一起阅读，理解可靠性与可观测性在分布式场景中的落地。

## 多运行时适配

- 可选特性：`tokio-adapter`、`async-std-adapter`
- 统一抽象：`src/runtime_abi.rs`
- 适配实现：`src/runtime_tokio.rs`、`src/runtime_async_std.rs`
- 示例运行：
  - Tokio：`--features tokio-adapter`
  - async-std：`--features async-std-adapter`

## 与 c20_distributed 的对接

- 可选特性：`c20-integration`
- 示例：`examples/c20_integration_demo.rs`
