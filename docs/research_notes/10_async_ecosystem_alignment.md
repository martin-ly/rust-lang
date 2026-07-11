# 异步生态权威来源对齐矩阵 {#异步生态权威来源对齐矩阵}

> **EN**: Async Ecosystem Alignment
> **Summary**: 异步生态权威来源对齐矩阵 Async Ecosystem Alignment.
> **概念族**: 权威来源对齐 / 异步（Async）生态
> **内容分级**: [核心级]
> **层级**: L0-L5
> **Bloom 层级**: L5-L6
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [异步生态权威来源对齐矩阵 {#异步生态权威来源对齐矩阵}](#异步生态权威来源对齐矩阵-异步生态权威来源对齐矩阵)
  - [目录 {#目录}](#目录-目录)
  - [一、对齐说明 {#一对齐说明}](#一对齐说明-一对齐说明)
  - [二、核心运行时 {#二核心运行时}](#二核心运行时-二核心运行时)
  - [三、并发原语 {#三并发原语}](#三并发原语-三并发原语)
  - [四、网络与 IO {#四网络与-io}](#四网络与-io-四网络与-io)
  - [五、流与通道 {#五流与通道}](#五流与通道-五流与通道)
  - [六、测试与调试 {#六测试与调试}](#六测试与调试-六测试与调试)
  - [七、与项目文档的映射 {#七与项目文档的映射}](#七与项目文档的映射-七与项目文档的映射)
  - [八、未覆盖缺口 {#八未覆盖缺口}](#八未覆盖缺口-八未覆盖缺口)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [学术权威参考 {#学术权威参考}](#学术权威参考-学术权威参考)

---

## 一、对齐说明 {#一对齐说明}

本文档将 `docs/research_notes/` 中的异步/并发内容与 Rust 异步生态的权威来源建立映射，包括 tokio、async-std、smol、futures 等运行时与库。

---

## 二、核心运行时 {#二核心运行时}

| 运行时（Runtime）/库 | 官方文档 | 项目文档 | 覆盖内容 |
|-----------|----------|----------|----------|
| Tokio | <https://tokio.rs/> | [crates/c06_async/](../../crates/c06_async/README.md) | 任务调度、IO、time、sync |
| async-std | <https://docs.rs/async-std/> | [crates/c06_async/](../../crates/c06_async/README.md) | 与 std 类似的异步 API |
| smol | <https://docs.rs/smol/> | [software_design_theory/03_execution_models/README.md](software_design_theory/03_execution_models/README.md) | 小型异步运行时 |
| futures-rs | <https://docs.rs/futures/> | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) | Stream、Sink、FutureExt |

---

## 三、并发原语 {#三并发原语}

| 原语 | 来源 | 项目文档 | 备注 |
|------|------|----------|------|
| `tokio::sync::Mutex` | [Tokio Docs](https://docs.rs/tokio/latest/tokio/sync/struct.Mutex.html) | [60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) §4 | 异步锁 |
| `tokio::sync::RwLock` | [Tokio Docs](https://docs.rs/tokio/latest/tokio/sync/struct.RwLock.html) | [60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) §4 | 异步读写锁 |
| `tokio::sync::oneshot` | [Tokio Docs](https://docs.rs/tokio/latest/tokio/sync/oneshot/index.html) | [60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) §7 | 单次通道 |
| `tokio::task` | [Tokio Docs](https://docs.rs/tokio/latest/tokio/task/index.html) | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) | spawn、JoinHandle |

---

## 四、网络与 IO {#四网络与-io}

| 库/框架 | 来源 | 项目文档 | 备注 |
|---------|------|----------|------|
| tokio::net | [Tokio Docs](https://docs.rs/tokio/latest/tokio/net/index.html) | [crates/c10_networks/](../../crates/c10_networks/README.md) | TCP/UDP 异步（Async） IO |
| hyper | [hyper.rs](https://hyper.rs/) | [crates/c10_networks/](../../crates/c10_networks/README.md) | HTTP 客户端/服务端 |
| axum | [axum docs](https://docs.rs/axum/) | [software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md](software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md) | Web 框架架构 |
| tonic | [tonic docs](https://docs.rs/tonic/) | [software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md](software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md) | gRPC |

---

## 五、流与通道 {#五流与通道}

| 概念/库 | 来源 | 项目文档 | 备注 |
|---------|------|----------|------|
| Stream trait | [futures-rs](https://docs.rs/futures/latest/futures/stream/trait.Stream.html) | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) | 异步迭代 |
| async_iter (gen blocks) | [RFC 3516 [已失效]]<!-- 原链接: https://github.com/rust-lang/rfcs/blob/master/text/3516-gen-blocks.md --> | [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) §3 | 不稳定 |
| channels (mpsc) | [Tokio Docs](https://docs.rs/tokio/latest/tokio/sync/mpsc/index.html) | [crates/c05_threads/](../../crates/c05_threads/README.md) | 消息传递 |

---

## 六、测试与调试 {#六测试与调试}

| 工具 | 来源 | 项目文档 | 备注 |
|------|------|----------|------|
| tokio::test | [Tokio Docs](https://docs.rs/tokio/latest/tokio/attr.test.html) | [crates/c06_async/](../../crates/c06_async/README.md) | 异步测试 |
| tokio-console | [Tokio Console](https://github.com/tokio-rs/console) | [experiments/10_concurrency_performance.md](experiments/10_concurrency_performance.md) | 异步任务调试 |

---

## 七、与项目文档的映射 {#七与项目文档的映射}

| 项目文档 | 生态覆盖 | 权威来源 |
|----------|----------|----------|
| [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) | Future、async/await、Pin、状态机 | Async Book、RFC 2394 |
| [formal_methods/60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) | 锁跨越 await、poll、Pin 契约 | Tokio Docs、Async Book |
| [crates/c06_async/README.md](../../crates/c06_async/README.md) | tokio 实战示例 | Tokio Docs |
| [software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md](software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md) | axum/tokio 架构分析 | 官方文档 |

---

## 八、未覆盖缺口 {#八未覆盖缺口}

1. `async-trait` crate 与原生 async fn in trait 的迁移映射。
2. `rayon` 数据并行与 async 的协作模式。
3. 异步运行时性能对比（tokio vs async-std vs smol）。
4. `Stream` trait 稳定化后的专门对齐文档。

> **权威来源**:
>
> [Tokio](https://tokio.rs/) |
> [async-std](https://async.rs/) |
> [smol](https://github.com/smol-rs/smol) |
> [futures-rs](https://github.com/rust-lang/futures-rs) |
> [hyper](https://hyper.rs/) |
> [axum](https://docs.rs/axum/) |
> [tonic](https://docs.rs/tonic/)
>

## 相关概念 {#相关概念}

- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [Async Book 对齐](10_async_book_alignment.md)
- [并发与异步反例](formal_methods/60_concurrency_async_counterexamples.md)
- [知识图谱索引](10_knowledge_graph_index.md)

---

## 学术权威参考 {#学术权威参考}

本对齐矩阵同时参考以下 P1 学术权威来源，以形成完整的官方-学术对照网络：

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)
- [Aeneas](https://aeneasverif.github.io/)
