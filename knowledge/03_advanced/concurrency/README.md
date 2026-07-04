# Concurrency 并发编程

> **EN**: Concurrency Index
> **Summary**: Concurrency 并发编程 Concurrency Index. (stub/archive redirect)
> **📎 交叉引用**
>
> 本主题在 concept 中有深度的概念分析：[并发](../../../concept/03_advanced/00_concurrency/01_concurrency.md)
> **层次定位**: L3 高级概念 / 并发子域索引
> **前置依赖**: [knowledge 泛型](../../02_intermediate/03_generics.md) · [knowledge Trait](../../02_intermediate/06_traits.md)
> **后置延伸**: [knowledge Async](../async/README.md) · [concept L3 并发](../../../concept/03_advanced/00_concurrency/01_concurrency.md)
> **跨层映射**: knowledge→concept 直觉映射 | L3 系统编程
> **定理链编号**: T-040 Send 类型安全 → T-041 Sync 数据竞争自由
>
> **受众**: [初学者] / [进阶]
> **内容分级**: [专家级]

## 📑 目录

- [Concurrency 并发编程](#concurrency-并发编程)
  - [📑 目录](#-目录)
  - [📚 内容](#-内容)
  - [🎯 学习路径](#-学习路径)
  - [🚀 相关层](#-相关层)
  - [相关概念](#相关概念)
  - [📚 模块 8: 国际化对齐](#-模块-8-国际化对齐)
    - [8.1 官方来源](#81-官方来源)
    - [8.2 学术/工业来源](#82-学术工业来源)
    - [8.3 社区资源](#83-社区资源)

> **Bloom 层级**: 理解
> **Rust 并发编程核心：线程、原子操作、同步原语**

## 📚 内容

> **[Rust Official Docs](https://doc.rust-lang.org/)**

| 文档 | 主题 | 难度 |
|------|------|------|
| [threads.md](03_threads.md) | 线程基础与 Send/Sync | ⭐⭐⭐ |
| [atomics.md](01_atomics.md) | 原子操作与内存序 | ⭐⭐⭐⭐ |
| [synchronization.md](02_synchronization.md) | 同步原语（Mutex、RwLock、Barrier）| ⭐⭐⭐⭐ |

## 🎯 学习路径
>
> **[Rust Official Docs](https://doc.rust-lang.org/)**

1. **线程基础** → [threads.md](03_threads.md)
2. **原子操作** → [atomics.md](01_atomics.md)
3. **高级同步** → [synchronization.md](02_synchronization.md)

## 🚀 相关层
>
> **[Rust Official Docs](https://doc.rust-lang.org/)**

- [03_advanced/async/](../async) - 异步编程
- [06_ecosystem/deep_dives/tokio_deep_dive.md](../../06_ecosystem/deep_dives/02_tokio_deep_dive.md) - Tokio 运行时

---

**维护者**: Rust 学习项目
**最后更新**: 2026-05-09

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/),
> [The Rust Programming Language](https://doc.rust-lang.org/book/),
> [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [Authority Source Sprint Batch 8](../../../concept/00_meta/02_sources/international_authority_index.md)

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.1+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 相关概念

- [NLL 与 Polonius (concept)](../../../concept/03_advanced/02_unsafe/08_nll_and_polonius.md) — Location-sensitive Polonius 与并发借用分析

## 📚 模块 8: 国际化对齐

> 本模块按项目模板补充国际化权威来源：官方文档、学术论文/工业报告、社区权威资源。

### 8.1 官方来源

| 来源 | 说明 |
|:---|:---|
| [TRPL Ch16 — Fearless Concurrency](https://doc.rust-lang.org/book/ch16-00-concurrency.html) | 并发基础 |
| [Rustonomicon — Concurrency](https://doc.rust-lang.org/nomicon/concurrency.html) | 并发高级话题 |
| [std::sync](https://doc.rust-lang.org/std/sync/) | 同步原语 API |

### 8.2 学术/工业来源

| 来源 | 说明 |
|:---|:---|
| [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) | Send / Sync 语义 |

### 8.3 社区资源

| 来源 | 说明 |
|:---|:---|
| [Rayon Documentation](https://docs.rs/rayon/latest/rayon/) | 数据并行 |
| [Crossbeam](https://github.com/crossbeam-rs/crossbeam) | 并发原语库 |
| [Rust Cookbook — Concurrency](https://rust-lang-nursery.github.io/rust-cookbook/concurrency.html) | 并发模式 |
