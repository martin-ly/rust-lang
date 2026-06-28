# Async 异步编程
>
> **📎 交叉引用**
>
> 本主题在 concept 中有深度的概念分析：[异步编程](../../../concept/03_advanced/02_async.md)
>
> **层次定位**: L3 高级概念 / 异步子域索引
> **前置依赖**: [knowledge 泛型](../../02_intermediate/03_generics.md) · [knowledge Trait](../../02_intermediate/06_traits.md)
> **后置延伸**: [knowledge Unsafe](../unsafe/README.md) · [concept L3 Async](../../../concept/03_advanced/02_async.md)
> **跨层映射**: knowledge→concept 直觉映射 | L3 系统编程
> **定理链编号**: T-050 Pin 安全性 → T-051 轮询一致性
>
> **受众**: [进阶] / [专家]
> **内容分级**: [专家级]

## 📑 目录

- [Async 异步编程](.#async-异步编程)
  - [📑 目录](.#-目录)
  - [📚 内容](.#-内容)
  - [🎯 学习路径](.#-学习路径)
  - [🚀 相关层](.#-相关层)
  - [📚 模块 8: 国际化对齐](.#-模块-8-国际化对齐)
    - [8.1 官方来源](.#81-官方来源)
    - [8.2 学术/工业来源](.#82-学术工业来源)
    - [8.3 社区资源](.#83-社区资源)

> **Bloom 层级**: 理解
> **Rust 异步编程核心：async/await、异步闭包、并发模式**

## 📚 内容

> **[来源: Rust Official Docs]**

| 文档 | 主题 | 难度 | 说明 |
|------|------|------|------|
| [async_await.md](01_async_await.md) | async/await 基础 | ⭐⭐⭐⭐ | 10 模块完整教学 |
| [async_closure.md](02_async_closure.md) | 异步闭包 | ⭐⭐⭐⭐ | 10 模块完整教学（Rust 1.85+）|
| [async_closures_2024.md](01_async_closures_2024.md) | 2024 Edition 异步闭包速览 | ⭐⭐⭐ | 快速参考 |

## 🎯 学习路径

> **[来源: Rust Official Docs]**

1. **async/await 基础** → 先学习 [async_await.md](01_async_await.md)
2. **异步闭包** → 再学习 [async_closure.md](02_async_closure.md)
3. **快速查阅** → 参考 [async_closures_2024.md](01_async_closures_2024.md)

## 🚀 相关层

> **[来源: Rust Official Docs]**

- [03_advanced/concurrency/](../concurrency) - 线程、原子操作、同步原语
- [06_ecosystem/deep_dives/tokio_deep_dive.md](../../06_ecosystem/deep_dives/02_tokio_deep_dive.md) - Tokio 运行时

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

## 📚 模块 8: 国际化对齐

> 本模块按项目模板补充国际化权威来源：官方文档、学术论文/工业报告、社区权威资源。

### 8.1 官方来源

| 来源 | 说明 |
|:---|:---|
| [The Rust Async Book](https://rust-lang.github.io/async-book/) | 异步编程官方教程 |
| [TRPL Ch17 — Async/Await](https://doc.rust-lang.org/book/ch17-00-async-await.html) | async/await 语法 |
| [Rust Reference — Async Functions](https://doc.rust-lang.org/reference/items/functions.html#async-functions) | async fn 规范 |

### 8.2 学术/工业来源

| 来源 | 说明 |
|:---|:---|
| [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) | Future / Pin 语义基础 |

### 8.3 社区资源

| 来源 | 说明 |
|:---|:---|
| [Tokio Documentation](https://tokio.rs/) | 主流异步运行时 |
| [smol](https://github.com/smol-rs/smol) | 轻量异步运行时 |
| [Embassy](https://embassy.dev/) | 嵌入式异步框架 |
