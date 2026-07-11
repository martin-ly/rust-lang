# Async Book 对齐矩阵 {#async-book-对齐矩阵}

> **EN**: Async Book Alignment
> **Summary**: Async Book 对齐矩阵 Async Book Alignment.
> **概念族**: 权威来源对齐 / Async Book
> **内容分级**: [核心级]
> **层级**: L0-L6
> **Bloom 层级**: L5-L6
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [Async Book 对齐矩阵 {#async-book-对齐矩阵}](#async-book-对齐矩阵-async-book-对齐矩阵)
  - [目录 {#目录}](#目录-目录)
  - [一、对齐说明 {#一对齐说明}](#一对齐说明-一对齐说明)
  - [二、Future 与 async/await {#二future-与-asyncawait}](#二future-与-asyncawait-二future-与-asyncawait)
  - [三、Pin 与自引用 {#三pin-与自引用}](#三pin-与自引用-三pin-与自引用)
  - [四、执行器与 Waker {#四执行器与-waker}](#四执行器与-waker-四执行器与-waker)
  - [五、IO 与并发 {#五io-与并发}](#五io-与并发-五io-与并发)
  - [六、状态机与编译 {#六状态机与编译}](#六状态机与编译-六状态机与编译)
  - [七、常见误区 {#七常见误区}](#七常见误区-七常见误区)
  - [八、未覆盖缺口 {#八未覆盖缺口}](#八未覆盖缺口-八未覆盖缺口)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [学术权威参考 {#学术权威参考}](#学术权威参考-学术权威参考)
  - [社区权威参考 {#社区权威参考}](#社区权威参考-社区权威参考)

---

## 一、对齐说明 {#一对齐说明}

本文档将 `docs/research_notes/` 中关于异步（Async）编程、Future、Pin、执行器的内容与 [Asynchronous Programming in Rust](https://rust-lang.github.io/async-book/) 建立映射。

---

## 二、Future 与 async/await {#二future-与-asyncawait}

| Async Book 章节 | 项目文档 | 状态 | 备注 |
|-----------------|----------|------|------|
| [Why Async?](https://rust-lang.github.io/async-book/) | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) | ✅ | 异步动机 |
| [async/await Primer](https://rust-lang.github.io/async-book/) | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) | ✅ | async 块编译为 Future |
| [The Future Trait](https://rust-lang.github.io/async-book/) | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) | ✅ | Future::poll |

---

## 三、Pin 与自引用 {#三pin-与自引用}

| Async Book 章节 | 项目文档 | 状态 | 备注 |
|-----------------|----------|------|------|
| [Pinning [已失效]]<!-- 原链接: https://rust-lang.github.io/async-book/ --> | [formal_methods/10_pin_self_referential.md](formal_methods/10_pin_self_referential.md) | ✅ | Pin 保证不移动 |
| [Pin and Suffering [已失效]]<!-- 原链接: https://rust-lang.github.io/async-book/ --> | [formal_methods/60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) §5 | ✅ | Pin 契约破坏 |

---

## 四、执行器与 Waker {#四执行器与-waker}

| Async Book 章节 | 项目文档 | 状态 | 备注 |
|-----------------|----------|------|------|
| [Executors](https://rust-lang.github.io/async-book/) | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) | ✅ | 执行器调度 |
| [Waker](https://rust-lang.github.io/async-book/) | [formal_methods/60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) §7 | ✅ | 错误 poll 不注册 waker |

---

## 五、IO 与并发 {#五io-与并发}

| Async Book 章节 | 项目文档 | 状态 | 备注 |
|-----------------|----------|------|------|
| [Async IO](https://rust-lang.github.io/async-book/) | [crates/c06_async/](../../crates/c06_async/README.md) | ✅ | 异步 IO 示例 |
| [Shared State](https://rust-lang.github.io/async-book/) | [formal_methods/60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) §4 | ✅ | 异步中持同步锁 |

---

## 六、状态机与编译 {#六状态机与编译}

| Async Book 章节 | 项目文档 | 状态 | 备注 |
|-----------------|----------|------|------|
| [Under the Hood](https://rust-lang.github.io/async-book/) | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) | ✅ | async 状态机展开 |
| [Async Lifetimes [已失效]]<!-- 原链接: https://rust-lang.github.io/async-book/ --> | [formal_methods/60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) §6 | ✅ | async 析构限制 |

---

## 七、常见误区 {#七常见误区}

| 误区 | 项目反例 | Async Book 来源 |
|------|----------|-----------------|
| 在 `Drop` 中调用 `.await` | [formal_methods/60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) §6 | [Async Drop [已失效]]<!-- 原链接: https://rust-lang.github.io/async-book/ --> |
| 同步锁跨越 await | [formal_methods/60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) §4 | [Shared State](https://rust-lang.github.io/async-book/) |
| poll 不注册 waker | [formal_methods/60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) §7 | [Waker](https://rust-lang.github.io/async-book/) |

---

## 八、未覆盖缺口 {#八未覆盖缺口}

1. `Stream` trait（已不稳定 `async_iter`）的专门对齐待 Rust 1.97+ 稳定后补充。
2. 异步（Async） trait（`trait Foo { async fn bar(); }`）的 Rust 1.75+ 特性需更新。
3. 具体运行时（tokio/async-std）差异可单独成文。

> **权威来源**: [Asynchronous Programming in Rust](https://rust-lang.github.io/async-book/)

## 相关概念 {#相关概念}

- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [异步状态机形式化](formal_methods/10_async_state_machine.md)
- [Pin 与自引用](formal_methods/10_pin_self_referential.md)
- [并发与异步反例](formal_methods/60_concurrency_async_counterexamples.md)
- [知识图谱索引](10_knowledge_graph_index.md)

---

## 学术权威参考 {#学术权威参考}

本对齐矩阵同时参考以下 P1 学术权威来源，以形成完整的官方-学术对照网络：

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)
- [Aeneas](https://aeneas-verification.github.io/)

## 社区权威参考 {#社区权威参考}

- [This Week in Rust](https://this-week-in-rust.org/)
- [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/)
- [Rust 中文社区 [已失效]]<!-- 原链接: https://rustcc.cn/ -->
