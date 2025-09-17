# 编程范式（Programming Paradigms）总索引

## 目的

- 汇总本项目中各类编程范式的最小索引与导航，统一返回根入口。

## 术语

- 范式（Paradigm）：对程序构造与推理方式的总体约束与风格。
- 模型（Model）：范式下的具体执行或并发语义（如 Actor、CSP、线程-锁）。
- 模式（Pattern）：在特定范式与上下文下可复用的设计解法。
- 抽象边界（Abstraction Boundary）：在模块/并发单元之间维持不变量的接口与契约。

## 核心概念分层

- 语言层：所有权/借用、生命周期、类型系统（参考类型系统与理论基础）。
- 执行层：同步/异步、并发/并行、阻塞/非阻塞、调度与背压。
- 架构层：事件驱动、响应式、Actor、数据导向。（与设计模式、质量保障交叉）
- 工程层：可观测性、可测试性、可演进性（与工具链、QA 交叉）。

## 子目录

- 同步范式：[`01_synchronous/00_index.md`](./01_synchronous/00_index.md)
- 异步范式：[`02_async/00_index.md`](./02_async/00_index.md)（`02_asynchronous` 为兼容别名，仅含跳转）
- 函数式：[`03_functional/00_index.md`](./03_functional/00_index.md)
- 面向对象：[`04_object_oriented/00_index.md`](./04_object_oriented/00_index.md)
- 并发：[`05_concurrent/00_index.md`](./05_concurrent/00_index.md)
- 并行：[`06_parallel/00_index.md`](./06_parallel/00_index.md)
- 响应式：[`07_reactive/00_index.md`](./07_reactive/00_index.md)
- 事件驱动：[`08_event_driven/00_index.md`](./08_event_driven/00_index.md)
- Actor 模型：[`09_actor_model/00_index.md`](./09_actor_model/00_index.md)
- 数据导向：[`10_data_oriented/00_index.md`](./10_data_oriented/00_index.md)

## 交叉链接

- 类型系统：[`../01_theoretical_foundations/01_type_system/00_index.md`](../01_theoretical_foundations/01_type_system/00_index.md)
- 设计模式：[`../03_design_patterns/00_index.md`](../03_design_patterns/00_index.md)
- 质量保障：[`../10_quality_assurance/00_index.md`](../10_quality_assurance/00_index.md)

## 示例与代码

- 同步并发示例：[`../../crates/c05_threads/`](../../crates/c05_threads/)
- 异步与网络：[`../../crates/c06_async/`](../../crates/c06_async/)、[`../../crates/c10_networks/`](../../crates/c10_networks/)
- 反压与背压：见异步子模块与网络 crate 中的限流、超时、重试示例。

### 关联基准

- 最小基准指南：[`11_benchmark_minimal_guide.md`](./11_benchmark_minimal_guide.md)
- 同步基准：[`../../crates/c05_threads/benches/`](../../crates/c05_threads/benches/)
- 异步基准：[`../../crates/c06_async/benches/`](../../crates/c06_async/benches/)

## 实践指引（最小决策树）

- I/O 密集 + 多连接：优先异步（`tokio`/`async-std`），结合超时/重试与限流。
- CPU 密集：优先并行（`rayon`/自建线程池），与异步解耦。
- 状态隔离需求强：Actor 或消息传递模型，最小化共享可变状态。
- 复杂变换管线：响应式/事件驱动，配合可观测性与反压策略。

### 选择与迁移（同步 ↔ 异步）

- 小规模/低 I/O：从同步开始；仅在观测到 I/O 等待显著后引入异步。
- 渐进式边界：优先在 I/O 适配层切换范式，保持领域核心同步可测试。
- 回退机制：提供同步降级路径，便于在运行时问题发生时切换。

## 参考与进一步阅读

- Rust Async Book、Tokio 文档、Rustonomicon（并发与不安全章节）
- 设计模式 Rust 实践（见 `../03_design_patterns/`）
- 可观测性与质量保障（见 `../10_quality_assurance/`）

## 导航

- 返回项目根：[`../README.md`](../README.md)
