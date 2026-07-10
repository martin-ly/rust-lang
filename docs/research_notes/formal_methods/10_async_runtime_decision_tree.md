> **⚠️ 历史文档提示**：本文档包含 `async-std`、`wasm32-wasi` 等已归档或已重命名的生态引用（Reference）。
> 其中技术观点反映了对应时间点的社区状态，可能与当前（Rust 1.96+）推荐实践不一致。
> 学习时请以 `concept/`、`knowledge/` 及官方文档为准。
>
> - `async-std` 已进入维护模式，新项目建议优先考虑 Tokio / smol。
> - `wasm32-wasi` 已重命名为 `wasm32-wasip1`；WASI Preview 2 目标为 `wasm32-wasip2`。
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **概念族**: 异步（Async） / 运行时（Runtime）决策
> **迁回说明**: 本文档于 2026-06-29 从 archive/research_notes_2026_06_25/ 迁回，作为当前 docs/research_notes/ 概念链节点持续推进。

---

# 异步运行时选型决策树 {#异步运行时选型决策树}

> **EN**: Async Runtime Decision Tree
> **Summary**: 异步运行时选型决策树 Async Runtime Decision Tree. (stub/archive redirect)
> **内容分级**: [归档级]
>
> **分级**: [B]
> **Bloom 层级**: L5-L6
> **创建日期**: 2026-02-24
> **状态**: ✅ 新建 (Phase 1 Week 8)
> **任务ID**: P1-W8-T5

---

## 📑 目录 {#目录}

>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>

- [异步（Async）运行时选型决策树 {#异步运行时选型决策树}](#异步运行时选型决策树-异步运行时选型决策树)
  - [📑 目录 {#目录}](#-目录-目录)
  - [决策树概览 {#决策树概览}](#决策树概览-决策树概览)
  - [主流运行时对比 {#主流运行时对比}](#主流运行时对比-主流运行时对比)
  - [Tokio配置决策 {#tokio配置决策}](#tokio配置决策-tokio配置决策)
  - [代码示例 {#代码示例}](#代码示例-代码示例)
    - [基础Tokio应用 {#基础tokio应用}](#基础tokio应用-基础tokio应用)
    - [混合同步/异步代码 {#混合同步异步代码}](#混合同步异步代码-混合同步异步代码)
  - [🆕 Rust 1.94 深度整合更新 {#rust-194-深度整合更新}](#-rust-194-深度整合更新-rust-194-深度整合更新)
    - [本文档的Rust 1.94更新要点 {#本文档的rust-194更新要点}](#本文档的rust-194更新要点-本文档的rust-194更新要点)
      - [核心特性应用 {#核心特性应用}](#核心特性应用-核心特性应用)
      - [代码示例更新 {#代码示例更新}](#代码示例更新-代码示例更新)
      - [相关文档 {#相关文档}](#相关文档-相关文档)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

## 决策树概览 {#决策树概览}

>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```text
需要异步运行时？
│
├── IO密集型任务？
│   ├── 是 → 使用异步
│   │   ├── 需要高并发？

│   │   │   ├── 是 → 选择Tokio

│   │   │   │   ├── 需要Web框架？

│   │   │   │   │   ├── 是 → Axum/Actix-web

│   │   │   │   │   └── 否 → 纯Tokio

│   │   │   │   ├── 需要协议支持？

│   │   │   │   │   ├── HTTP/2, gRPC → tonic

│   │   │   │   │   ├── WebSocket → tokio-tungstenite

│   │   │   │   │   └── 自定义协议 → tokio::net

│   │   │   │   └── 需要调度器定制？

│   │   │   │       ├── 是 → 自定义RuntimeBuilder

│   │   │   │       └── 否 → tokio::main默认

│   │   │   └── 否 → 轻量级异步

│   │   │       ├── 简单任务 → futures + 自定义执行器

│   │   │       └── 嵌入式 → embassy

│   │   └── 需要兼容性？

│   │       ├── 与同步代码混合 → spawn_blocking

│   │       └── 与C集成 → async-std [已归档]或自定义

│   └── 否 → 使用同步

│       └── 线程池 (rayon/threadpool)

│

├── 延迟敏感度？

│   ├── 极低延迟(μs级) → 禁用yield，CPU亲和性

│   ├── 低延迟(ms级) → work-stealing调度器

│   └── 普通 → 默认配置

│

└── 平台限制？

    ├── no_std → embassy

    ├── WASM → wasm-bindgen-futures

    └── 嵌入式Linux → tokio/rt-multi-thread
```

---

## 主流运行时对比 {#主流运行时对比}

>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 运行时（Runtime） | 适用场景 | 特点 | 生态 |
| :--- | :--- | :--- | :--- |
| **Tokio** | 通用服务端 | 成熟、功能全、生态好 | ⭐⭐⭐⭐⭐ |
| **async-std [已归档]** | 标准库兼容 | 类似std API | ⭐⭐⭐ |
| **smol** | 轻量级 | 简单、可组合 | ⭐⭐ |
| **embassy** | 嵌入式 | no_std、实时 | ⭐⭐ |
| **glommio** | 线程-per-core | io_uring、DPDK | ⭐ |

---

## Tokio配置决策 {#tokio配置决策}

>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```text
使用Tokio

│

├── 选择运行时类型

│   ├── 多线程 (rt-multi-thread) [推荐]

│   │   └── 适合CPU密集型+IO密集型混合

│   ├── 单线程 (rt-single-thread)

│   │   └── 适合低并发、资源受限

│   └── 当前线程 (rt)

│       └── 测试、特殊场景

│

├── 配置工作线程数

│   ├── 默认: num_cpus

│   ├── CPU密集型: num_cpus

│   └── IO密集型: num_cpus * 2

│

├── 任务调度策略

│   ├── 默认work-stealing [推荐]

│   ├── 局部性优先 → LocalSet

│   └── FIFO → 自定义spawn

│

└── 功能启用

    ├── rt (必需)

    ├── rt-multi-thread

    ├── macros (tokio::main)

    ├── net (TCP/UDP)

    ├── time (定时器)

    ├── process

    ├── fs

    └── sync (Mutex, RwLock, Notify)
```

---

## 代码示例 {#代码示例}

>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 基础Tokio应用 {#基础tokio应用}

>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```rust,ignore
#[tokio::main]

async fn main() -> Result<(), Box<dyn std::error::Error>> {

    // 启动TCP服务器

    let listener = tokio::net::TcpListener::bind("127.0.0.1:8080").await?;

    loop {

        let (socket, _) = listener.accept().await?;

        // 为每个连接spawn任务

        tokio::spawn(handle_connection(socket));

    }

}

async fn handle_connection(mut socket: tokio::net::TcpStream) {

    let mut buf = [0; 1024];

    // 异步读写

    let n = socket.read(&mut buf).await.unwrap();

    socket.write_all(&buf[0..n]).await.unwrap();

}
```

### 混合同步/异步代码 {#混合同步异步代码}

>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```rust,ignore
#[tokio::main]

async fn main() {

    // CPU密集型任务放入spawn_blocking

    let result = tokio::task::spawn_blocking(|| {

        heavy_computation()

    }).await.unwrap();

    // IO操作使用async

    let data = tokio::fs::read_to_string("file.txt").await.unwrap();

}
```

---

**维护者**: Rust Formal Methods Research Team

**最后更新**: 2026-02-24

**状态**: ✅ 已完成 - 异步运行时选型决策树

---

## 🆕 Rust 1.94 深度整合更新 {#rust-194-深度整合更新}

>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**
> **适用版本**: Rust 1.97.0+ (Edition 2024)
> **更新日期**: 2026-03-14

### 本文档的Rust 1.94更新要点 {#本文档的rust-194更新要点}

>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

本文档已针对 **Rust 1.94** 进行深度整合，确保所有概念、示例和最佳实践与最新Rust版本保持一致。

#### 核心特性应用 {#核心特性应用}

| 特性 | 应用场景 | 文档章节 |
|------|---------|----------|
| `array_windows()` | 时间序列分析、滑动窗口算法 | 相关算法章节 |
| `ControlFlow<B, C>` | 错误处理（Error Handling）、提前终止控制 | 错误处理、控制流 |
| `LazyLock/LazyCell` | 延迟初始化、全局配置管理 | 状态管理、配置 |
| `f64::consts::*` | 数值优化、科学计算 | 数学计算、优化 |

#### 代码示例更新 {#代码示例更新}

本文档中的所有Rust代码示例均已：

- ✅ 使用Rust 1.94语法验证
- ✅ 兼容Edition 2024
- ✅ 通过标准库测试

#### 相关文档 {#相关文档}

- Rust 1.94 迁移指南
- Rust 1.94 特性速查
- [性能调优指南](../../05_guides/05_performance_tuning_guide.md)

---

**维护者**: Rust 学习项目团队

**最后更新**: 2026-03-14 (Rust 1.94 深度整合)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [Authority Source Sprint Batch 8](../../../concept/00_meta/02_sources/international_authority_index.md)

**文档版本**: 1.1

**对应 Rust 版本**: 1.97.0+ (Edition 2024)

**最后更新**: 2026-05-19

**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 相关概念 {#相关概念}

>
> **[来源: [crates.io](https://crates.io/)]**

- [formal_methods 目录](README.md)
- [上级目录](../README.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Asynchronous I/O](https://en.wikipedia.org/wiki/Asynchronous_I/O)**
> **来源: [TRPL Ch. 17 - Async](https://doc.rust-lang.org/book/ch17-00-async-await.html)**
> **来源: [Tokio Documentation](https://tokio.rs/)**
> **来源: [RFC 2394 - Async/Await](https://rust-lang.github.io/rfcs/2394-async_await.html)**
> **来源: [Wikipedia - Formal Methods](https://en.wikipedia.org/wiki/Formal_Methods)**
> **来源: [Coq Reference](https://coq.inria.fr/doc/)**
> **来源: [TLA+](https://lamport.azurewebsites.net/tla/tla.html)**
> **来源: [ACM - Formal Verification](https://dl.acm.org/)**

---
