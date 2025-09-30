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

## 进一步阅读（Rust 1.90 对齐）

- 同步与异步分类与等价关系：`./async-sync-classification.md`
- 消息队列与背压模型：`./backpressure-models.md`
- 递归异步与组合模式：`./async-recursion.md`

## 检查清单（快速自检）

- 异步路径是否包含阻塞调用？如有请改为异步替代或 `spawn_blocking`。
- 是否设置了队列容量与溢出策略？是否有度量丢弃率与p99延迟？
- 是否定义了取消/超时/重试策略并保证可观测性？