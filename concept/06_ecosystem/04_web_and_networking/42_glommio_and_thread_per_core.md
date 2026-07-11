> **内容分级**: [专家级]

# Glommio 与 Thread-per-Core 异步运行时
>
> **EN**: Glommio and Thread-per-Core Async Runtimes
> **Summary**: High-performance Linux async runtime based on io_uring and thread-per-core architecture: design trade-offs, CPU pinning, NUMA awareness, and when to prefer Glommio over work-stealing runtimes like Tokio.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [专家]
> **Bloom 层级**: L4-L5
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **S+P** — Structure + Procedure
> **双维定位**: C×Eva — 评价异步（Async）运行时（Runtime）架构对目标场景的适配性
> **前置依赖**: [Async/Await](../../03_advanced/01_async/02_async.md) · [Async Patterns](../../03_advanced/01_async/26_async_patterns.md) · [执行模型同构](../../05_comparative/00_paradigms/05_execution_model_isomorphism.md)
> **后置概念**: [High-Performance Network Service Architecture](39_high_performance_network_service_architecture.md)
>
> **主要来源**: [Glommio Repository](https://github.com/DataDog/glommio) · [Linux io_uring](https://kernel.dk/io_uring.pdf) · [Async Rust Book](https://rust-lang.github.io/async-book/)

---

## 一、核心定位

**Glommio** 是由 DataDog 开发的、基于 Linux `io_uring` 的高性能异步（Async）运行时（Runtime），采用 **Thread-per-Core** 架构。它通过避免线程切换和跨核同步开销，追求极致的延迟与吞吐量。

| 特性 | 说明 |
|:---|:---|
| Thread-per-core | 每个 CPU 核心绑定一个执行器，任务不跨核迁移 |
| io_uring | Linux 5.1+ 提供的高性能异步 I/O 接口 |
| NUMA 感知 | 针对多 socket 系统优化内存与任务放置 |
| 零拷贝 I/O | 最小化数据复制 |

---

## 二、Thread-per-Core vs Work-Stealing

| 特性 | Thread-per-core (Glommio) | Work-stealing (Tokio) |
|:---|:---|:---|
| 线程切换 | 无 | 有 |
| 缓存友好 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ |
| 负载均衡 | 需手动处理 | 自动 |
| 编程复杂度 | 较高 | 较低 |
| 适用场景 | 高频交易、数据库引擎、高吞吐网络服务 | 通用 Web / 微服务 |

---

## 三、CPU 绑定与 NUMA 优化

```rust
use glommio::{LocalExecutorBuilder, Placement};

let handle = LocalExecutorBuilder::default()
    .pin_to_cpu(0)
    .name("worker-0")
    .spawn(|| async move {
        // 绑定到核心 0 的任务
    })
    .unwrap();
```

- 显式绑定核心可提升缓存命中率并降低延迟。
- NUMA 系统下应尽量让任务访问本地内存节点。

---

## 四、适用场景与不推荐场景

✅ **推荐**:

- 高频交易系统（HFT）
- 数据库 / 存储引擎
- 高 QPS 网络服务
- 实时数据流处理

❌ **不推荐**:

- 桌面 / GUI 应用
- 简单 Web 应用
- Windows / macOS 平台
- 大量阻塞 I/O 的场景

---

## 五、生态状态

- Glommio 主要面向 Linux 5.1+；需要 `liburing` 支持。
- 旧目标名 `wasm32-wasi` 已重命名为 `wasm32-wasip1`。
- 新项目若需跨平台，应优先评估 Tokio 或 smol。

---

## 六、Rust 异步运行时对比 2025

> 内容来源：`crates/c06_async/docs/tier_03_references/06_runtime_comparison_glommio_2025.md`，已按 AGENTS.md §6.4 迁移至此。

### 6.1 运行时特性概览

| 特性 | Glommio | Tokio | Smol | async-std（已归档） |
|:---|:---|:---|:---|:---|
| 架构模型 | Thread-per-core | Work-stealing | 单线程/多线程池 | Work-stealing |
| 平台支持 | Linux 5.1+ | 跨平台 | 跨平台 | 跨平台 |
| I/O 接口 | io_uring | epoll/kqueue | epoll/kqueue | epoll/kqueue |
| NUMA 优化 | ✅ | ⚠️ 有限 | ❌ | ❌ |
| 零拷贝 I/O | ✅ 原生 | ⚠️ 部分 | ⚠️ 部分 | ⚠️ 部分 |
| 学习曲线 | 陡峭 | 中等 | 平缓 | 平缓 |
| 生态系统 | 小 | 最大 | 中 | 中（维护模式） |

> ⚠️ `async-std` 已于 2025 年 3 月停止活跃维护，新项目建议优先评估 Tokio 或 smol。

### 6.2 架构对比

**Glommio: Thread-per-core**

- 每个任务固定在一个核心上，无线程切换开销。
- 极高的缓存命中率，但需要手动做负载均衡。
- 适合 Linux 5.1+ 的 `io_uring` 环境。

**Tokio: Work-stealing**

- 自动负载均衡，生态最成熟。
- 适用微服务、Web 应用、云原生场景。
- 跨平台，是多数项目的默认选择。

**Smol: 轻量级多模式**

- 极简设计，内存占用小。
- 可在单线程与多线程池之间切换。
- 适合嵌入式、CLI 工具、学习原型。

### 6.3 选择决策树

```text
开始选择运行时
│
├─ 需要极致性能？──Yes──> 只在 Linux 5.1+ 运行？──Yes──> Glommio ✅
│                                              └──No──> Tokio
│
├─ 需要跨平台？──Yes──> 需要丰富生态？──Yes──> Tokio ✅
│                              └──No──> Smol ✅
│
└─ 轻量级/学习用途？──Yes──> Smol / Tokio（按生态需求）
```

### 6.4 代码对比

**Glommio**

```rust
use glommio::{LocalExecutor, Task};

LocalExecutor::default().run(async {
    let task = Task::local(async { 42 });
    println!("Result: {}", task.await);
});
```

**Tokio**

```rust
#[tokio::main]
async fn main() {
    let task = tokio::spawn(async { 42 });
    println!("Result: {}", task.await.unwrap());
}
```

**Smol**

```rust
fn main() {
    smol::block_on(async {
        let task = smol::spawn(async { 42 });
        println!("Result: {}", task.await);
    });
}
```

### 6.5 迁移提示

从 Tokio 迁移到 Glommio 需要重构为 thread-per-core 模型：

```rust
// Tokio（Before）
#[tokio::main]
async fn main() {
    tokio::spawn(async { /* work */ }).await;
}

// Glommio（After）
use glommio::LocalExecutorBuilder;

fn main() {
    LocalExecutorBuilder::default()
        .pin_to_cpu(0)
        .spawn(|| async { /* work */ })
        .unwrap()
        .join()
        .unwrap();
}
```

> **关键洞察**: Glommio 提供极致延迟和吞吐量，但牺牲了跨平台能力和生态成熟度。除非明确需要 <100μs 延迟且部署环境固定为 Linux 5.1+，否则 Tokio 通常是更安全的选择。

---

## 权威来源索引

- [Glommio GitHub](https://github.com/DataDog/glommio)
- [Linux io_uring 论文](https://kernel.dk/io_uring.pdf)
- [Async Rust Book](https://rust-lang.github.io/async-book/)

## 过渡段

> **过渡**: 从传统线程池过渡到 thread-per-core，可以理解专用核心与缓存亲和性对尾延迟的影响。
>
> **过渡**: 从 io_uring 集成过渡到协作式调度，可以建立“避免抢占、减少抖动”的设计原则。
>
> **过渡**: 从低延迟设计过渡到运维复杂度，可以评估这种架构对部署与监控的要求。
>

## 定理链

| 定理 | 前提 | 结论 |
|:---|:---|:---|
| 专用核心 ⟹ 缓存亲和性 | 任务固定到特定 CPU | 减少缓存失效与上下文切换 |
| io_uring ⟹ 更少系统调用 | 批量处理 I/O 请求 | 降低内核态开销 |
| 协作式任务 ⟹ 可预测尾延迟 | 避免抢占式调度抖动 | 适合延迟敏感型服务 |


---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P1 学术/形式化**: [Hoare: Communicating Sequential Processes (CACM 1978)](https://dl.acm.org/doi/10.1145/359576.359585) · [RustBelt: Securing the Foundations of the Rust Programming Language (POPL 2018)](https://dl.acm.org/doi/10.1145/3158154)
- **P2 生态/社区**: [docs.rs/futures — 生态权威 API 文档](https://docs.rs/futures) · [docs.rs/hyper — 生态权威 API 文档](https://docs.rs/hyper)
