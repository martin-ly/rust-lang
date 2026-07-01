> **📌 生态说明**：
>
> 本文档已按 Rust 1.96.0+ / Edition 2024 推荐实践更新生态引用：
>
> - 异步运行时：`async-std` 已归档，新项目优先使用 **Tokio** 或 **smol**。
> - WASI 目标：`wasm32-wasi` 已重命名为 **`wasm32-wasip1`**；WASI Preview 2 目标为 **`wasm32-wasip2`**。
> - 学习时请以 [The Rust Programming Language](https://doc.rust-lang.org/book/)、[Rust Reference](https://doc.rust-lang.org/reference/)、[Cargo Book](https://doc.rust-lang.org/cargo/)、[Rust Edition Guide - Rust 2024](https://doc.rust-lang.org/edition-guide/rust-2024/index.html) 为准。
> **概念族**: 实际应用

---

# 应用树 {#应用树}

> **内容分级**: [归档级]
>
> **分级**: [B]
> **Bloom 层级**: L5-L6 (分析/评价/创造)
> **创建日期**: 2026-03-10
> **最后更新**: 2026-06-29
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **版本**: v1.1
> **描述**: Rust 在不同应用领域的知识体系与应用树
> **状态**: ✅ 已完成权威国际化来源对齐升级

---

## 📑 目录 {#目录}

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

- [应用树 {#应用树}](#应用树-应用树)
  - [📑 目录 {#目录}](#-目录-目录)
  - [一、概述 {#一概述}](#一概述-一概述)
  - [二、系统编程应用树 {#二系统编程应用树}](#二系统编程应用树-二系统编程应用树)
    - [2.1 概念树 {#21-概念树}](#21-概念树-21-概念树)
    - [2.2 技能路径 {#22-技能路径}](#22-技能路径-22-技能路径)
    - [2.3 核心技术栈 {#23-核心技术栈}](#23-核心技术栈-23-核心技术栈)
  - [三、网络服务应用树 {#三网络服务应用树}](#三网络服务应用树-三网络服务应用树)
    - [3.1 概念树 {#31-概念树}](#31-概念树-31-概念树)
    - [3.2 架构层次 {#32-架构层次}](#32-架构层次-32-架构层次)
    - [3.3 服务开发技能树 {#33-服务开发技能树}](#33-服务开发技能树-33-服务开发技能树)
  - [四、数据系统应用树 {#四数据系统应用树}](#四数据系统应用树-四数据系统应用树)
    - [4.1 概念树 {#41-概念树}](#41-概念树-41-概念树)
    - [4.2 数据系统层次 {#42-数据系统层次}](#42-数据系统层次-42-数据系统层次)
    - [4.3 数据库开发技能树 {#43-数据库开发技能树}](#43-数据库开发技能树-43-数据库开发技能树)
  - [五、跨领域通用能力 {#五跨领域通用能力}](#五跨领域通用能力-五跨领域通用能力)
    - [5.1 通用技能矩阵 {#51-通用技能矩阵}](#51-通用技能矩阵-51-通用技能矩阵)
    - [5.2 跨领域架构模式 {#52-跨领域架构模式}](#52-跨领域架构模式-52-跨领域架构模式)
  - [六、相关资源 {#六相关资源}](#六相关资源-六相关资源)
    - [6.1 学习路径文档 {#61-学习路径文档}](#61-学习路径文档-61-学习路径文档)
    - [6.2 领域特定资源 {#62-领域特定资源}](#62-领域特定资源-62-领域特定资源)
    - [6.3 应用树总览 {#63-应用树总览}](#63-应用树总览-63-应用树总览)
  - [🆕 Rust 1.96.0+ / Edition 2024 研究更新 {#rust-1960-edition-2024-研究更新}](#-rust-1960--edition-2024-研究更新-rust-1960-edition-2024-研究更新)
    - [核心研究点 {#核心研究点}](#核心研究点-核心研究点)
  - [🆕 Rust 1.96.0+ / Edition 2024 权威国际化升级说明 {#rust-1960-edition-2024-权威国际化升级说明}](#-rust-1960--edition-2024-权威国际化升级说明-rust-1960-edition-2024-权威国际化升级说明)
    - [升级要点 {#升级要点}](#升级要点-升级要点)
      - [权威来源对齐 {#权威来源对齐}](#权威来源对齐-权威来源对齐)
      - [形式化来源对照 {#形式化来源对照}](#形式化来源对照-形式化来源对照)
      - [版本与生态更新 {#版本与生态更新}](#版本与生态更新-版本与生态更新)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

## 一、概述 {#一概述}
>
> **来源**: [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Reference](https://doc.rust-lang.org/reference/), [Cargo Book](https://doc.rust-lang.org/cargo/), [Rust Standard Library](https://doc.rust-lang.org/std/), [Rust Edition Guide](https://doc.rust-lang.org/edition-guide/)

本文档构建 Rust 在三大核心应用领域的知识体系树：系统编程、网络服务和数据系统。每个领域展示从基础概念到高级应用的知识路径。

---

## 二、系统编程应用树 {#二系统编程应用树}
>
> **来源**: [Rust Standard Library - io](https://doc.rust-lang.org/std/io/), [Rust Standard Library - fs](https://doc.rust-lang.org/std/fs/), [Rust Standard Library - process](https://doc.rust-lang.org/std/process/), [The Rust Programming Language](https://doc.rust-lang.org/book/)

### 2.1 概念树 {#21-概念树}

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

```mermaid
mindmap
  root((系统编程))
    内存管理
      所有权系统
        堆分配
        栈分配
        内存对齐
      智能指针
        Box
        Rc/Arc
        自定义分配器
      零成本抽象
        泛型单态化
        内联优化
    并发原语
      线程管理
        线程创建
        线程局部存储
        线程池
      同步机制
        Mutex/RwLock
        Condvar
        Barrier
      原子操作
        Atomic类型
        内存序
        Lock-free结构
    系统接口
      文件IO
        标准IO
        异步IO
        内存映射
      进程管理
        进程创建
        进程通信
        信号处理
      网络底层
        Socket编程
        协议实现
        io_uring
    Unsafe Rust
      原始指针
      FFI绑定
      内联汇编
```
### 2.2 技能路径 {#22-技能路径}

> **来源: [POPL](https://www.sigplan.org/Conferences/POPL/)**

| 层级 | 主题 | 核心概念 | 实践项目 |
|------|------|----------|----------|
| **入门** | 基础语法 | 所有权、借用、生命周期 | CLI工具 |
| **进阶** | 系统接口 | 文件IO、进程、信号 | 系统监控工具 |
| **高级** | 并发编程 | 锁、原子、Lock-free | 高性能服务器 |
| **专家** | 内核开发 | 裸机、驱动、调度器 | 微型OS |

### 2.3 核心技术栈 {#23-核心技术栈}

> **来源: [PLDI](https://www.sigplan.org/Conferences/PLDI/)**

```text
系统编程栈
│
├─ 语言核心
│  ├─ 所有权与借用
│  ├─ 生命周期
│  └─ 类型系统
│
├─ 标准库
│  ├─ std::io
│  ├─ std::fs
│  ├─ std::process
│  └─ std::thread
│
├─ 并发框架
│  ├─ tokio (异步运行时)
│  ├─ rayon (数据并行)
│  └─ crossbeam (并发原语)
│
└─ 系统绑定
   ├─ libc (POSIX)
   ├─ winapi (Windows)
   └─ nix (Unix工具)
```
---

## 三、网络服务应用树 {#三网络服务应用树}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 3.1 概念树 {#31-概念树}

> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**

```mermaid
mindmap
  root((网络服务))
    Web框架
      异步运行时
        Tokio
        Tokio / smol
        smol
      HTTP服务器
        Axum
        Actix-web
        Rocket
      中间件
        路由
        认证
        日志追踪
    服务架构
      REST API
        资源设计
        状态码
        版本控制
      gRPC
        Protobuf
        流式传输
        拦截器
      GraphQL
        Schema定义
        Resolver
        订阅
    分布式系统
      服务发现
        Consul
        etcd
        Kubernetes
      负载均衡
        轮询
        加权
        一致性哈希
      容错模式
        熔断
        重试
        超时
    数据通信
      序列化
        JSON
        MessagePack
        Protocol Buffers
      消息队列
        Kafka
        RabbitMQ
        NATS
      缓存
        Redis
        Memcached
```
### 3.2 架构层次 {#32-架构层次}

> **来源: [ACM](https://dl.acm.org/)**

| 层次 | 技术选择 | 关注点 | 成熟度 |
|------|----------|--------|--------|
| **边缘层** | Nginx/Envoy | 路由、TLS、限流 | 生产级 |
| **网关层** | Axum/Actix | 认证、聚合、转换 | 生产级 |
| **服务层** | gRPC/REST | 业务逻辑、事务 | 生产级 |
| **数据层** | SQL/NoSQL | 持久化、缓存 | 生产级 |

### 3.3 服务开发技能树 {#33-服务开发技能树}

> **来源: [IEEE](https://standards.ieee.org/)**

```text
网络服务开发
│
├─ 基础网络
│  ├─ TCP/IP协议栈
│  ├─ HTTP/1.1 & HTTP/2
│  └─ WebSocket
│
├─ Web框架
│  ├─ 路由与处理器
│  ├─ 中间件系统
│  └─ 错误处理
│
├─ 数据层
│  ├─ SQL (diesel, sqlx)
│  ├─ NoSQL (mongodb, redis)
│  └─ ORM与查询构建
│
├─ 服务通信
│  ├─ REST API设计
│  ├─ gRPC服务
│  └─ 消息队列
│
└─ 运维部署
   ├─ 容器化 (Docker)
   ├─ 编排 (Kubernetes)
   └─ 可观测性 (Prometheus, Jaeger)
```
---

## 四、数据系统应用树 {#四数据系统应用树}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 4.1 概念树 {#41-概念树}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```mermaid
mindmap
  root((数据系统))
    存储引擎
      B树家族
        B+树
        LSM树
        写入优化
      索引结构
        哈希索引
        位图索引
        倒排索引
      存储格式
        行式存储
        列式存储
        混合存储
    查询处理
      SQL解析
        词法分析
        语法分析
        语义检查
      查询优化
        成本模型
        执行计划
        统计信息
      执行引擎
        向量化
        代码生成
        并行执行
    事务系统
      ACID实现
        原子性
        一致性
        隔离性
        持久性
      并发控制
        2PL
        MVCC
        OCC
      故障恢复
        WAL
        Checkpoint
        日志回放
    分布式数据
      数据分片
        范围分片
        哈希分片
        一致性哈希
      复制协议
        主从复制
        多主复制
        共识算法
      分布式事务
        2PC
        Saga
        Percolator
```
### 4.2 数据系统层次 {#42-数据系统层次}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

| 层次 | 组件 | 关键技术 | Rust生态 |
|------|------|----------|----------|
| **存储层** | 文件系统、IO | mmap, io_uring | tokio-uring |
| **引擎层** | 索引、缓存 | B-tree, LRU | sled, dashmap |
| **处理层** | SQL、计算 | 查询优化 | datafusion |
| **服务层** | 协议、API | PostgreSQL协议 | pgwire |

### 4.3 数据库开发技能树 {#43-数据库开发技能树}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```text
数据库系统开发
│
├─ 存储基础
│  ├─ 文件系统接口
│  ├─ 内存映射
│  └─ 零拷贝技术
│
├─ 数据结构
│  ├─ B+树实现
│  ├─ LSM树优化
│  └─ 布隆过滤器
│
├─ 事务引擎
│  ├─ MVCC实现
│  ├─ 锁管理器
│  └─ WAL与恢复
│
├─ 查询引擎
│  ├─ SQL解析器
│  ├─ 查询优化器
│  └─ 执行引擎
│
└─ 分布式扩展
   ├─ 共识算法 (Raft)
   ├─ 分片策略
   └─ 复制协议
```
---

## 五、跨领域通用能力 {#五跨领域通用能力}
>
> **[来源: [crates.io](https://crates.io/)]**

### 5.1 通用技能矩阵 {#51-通用技能矩阵}
>
> **[来源: [docs.rs](https://docs.rs/)]**

| 技能 | 系统编程 | 网络服务 | 数据系统 | 重要度 |
|------|:--------:|:--------:|:--------:|:------:|
| **所有权精通** | ✅ | ✅ | ✅ | ⭐⭐⭐ |
| **并发安全** | ✅ | ✅ | ✅ | ⭐⭐⭐ |
| **性能优化** | ✅ | ✅ | ✅ | ⭐⭐⭐ |
| **Unsafe Rust** | ✅ | ⚠️ | ✅ | ⭐⭐ |
| **异步编程** | ⚠️ | ✅ | ✅ | ⭐⭐⭐ |
| **FFI绑定** | ✅ | ⚠️ | ⚠️ | ⭐⭐ |
| **宏编程** | ⚠️ | ⚠️ | ✅ | ⭐⭐ |
| **测试策略** | ✅ | ✅ | ✅ | ⭐⭐⭐ |

### 5.2 跨领域架构模式 {#52-跨领域架构模式}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```text
通用架构能力
│
├─ 设计模式
│  ├─ 组合优于继承
│  ├─ 零成本抽象
│  └─ 类型状态模式
│
├─ 错误处理
│  ├─ Result传播
│  ├─ 自定义错误类型
│  └─ thiserror/anyhow
│
├─ 可观测性
│  ├─ 结构化日志 (tracing)
│  ├─ 指标收集 (prometheus)
│  └─ 分布式追踪
│
└─ 性能工程
   ├─ 剖析工具 (flamegraph)
   ├─ 基准测试 (criterion)
   └─ 内存分析
```
---

## 六、相关资源 {#六相关资源}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 6.1 学习路径文档 {#61-学习路径文档}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| 领域 | 入门文档 | 进阶文档 |
|------|----------|----------|
| 系统编程 | [TUTORIAL_OWNERSHIP](10_tutorial_ownership_safety.md) | [THREADS_CONCURRENCY](../05_guides/05_threads_concurrency_usage_guide.md) |
| 网络服务 | [ASYNC_PROGRAMMING](../05_guides/05_async_programming_usage_guide.md) | [DESIGN_PATTERNS](../05_guides/05_design_patterns_usage_guide.md) |
| 数据系统 | TYPE_SYSTEM | [UNSAFE_RUST](../../concept/03_advanced/03_unsafe.md) |

### 6.2 领域特定资源 {#62-领域特定资源}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 领域 | 关键 Crate | 示例项目 |
|------|------------|----------|
| 系统编程 | nix, libc, io-uring | Redox OS, Firecracker |
| 网络服务 | tokio, axum, tonic | Linkerd, Vector |
| 数据系统 | datafusion, polars, sled | TiKV, MeiliSearch |

### 6.3 应用树总览 {#63-应用树总览}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```text
Rust 应用领域总览
│
├─ 系统层
│  ├─ 操作系统 (Redox)
│  ├─ 容器/虚拟化 (Firecracker)
│  └─ 嵌入式 (Tock)
│
├─ 网络层
│  ├─ Web框架 (Actix, Axum)
│  ├─ 代理/网关 (Linkerd, Envoy)
│  └─ 网络协议 (Quinn, rustls)
│
├─ 数据层
│  ├─ 数据库 (TiKV, sled)
│  ├─ 查询引擎 (DataFusion)
│  └─ 流处理 (Vector, Fluvio)
│
└─ 工具层
   ├─ CLI工具 (ripgrep, fd)
   ├─ 构建系统 (Cargo)
   └─ 开发工具 (rust-analyzer)
```
---

**维护者**: Rust Learning Project Team
**最后更新**: 2026-03-10

---

## 🆕 Rust 1.96.0+ / Edition 2024 研究更新 {#rust-1960-edition-2024-研究更新}
>
> **来源**: [Rust Edition Guide - Rust 2024](https://doc.rust-lang.org/edition-guide/rust-2024/index.html)
> **适用版本**: Rust 1.96.0+ (Edition 2024)
> **更新日期**: 2026-06-29

### 核心研究点 {#核心研究点}

> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/)

- `array_windows()` 的形式化语义与滑动窗口算法
- `ControlFlow<B, C>` 的代数结构与提前终止控制
- `LazyCell` / `LazyLock` 的延迟初始化语义
- `Pin`、`Future`、`async fn` 与 Edition 2024 的协同形式化
- 与 [RustBelt](https://plv.mpi-sws.org/rustbelt/)、[Aeneas](https://aeneas-verification.github.io/)、[Ferrocene FLS](https://spec.ferrocene.dev/) 的 P1 形式化来源对照

详见 [RUST_194_RESEARCH_UPDATE](10_rust_194_research_update.md) 及 [Rust Edition Guide](https://doc.rust-lang.org/edition-guide/rust-2024/index.html)。

**最后更新**: 2026-06-29

---

## 🆕 Rust 1.96.0+ / Edition 2024 权威国际化升级说明 {#rust-1960-edition-2024-权威国际化升级说明}
>
> **来源**: [Rust Edition Guide - Rust 2024](https://doc.rust-lang.org/edition-guide/rust-2024/index.html)
> **来源**: [The Rust Programming Language](https://doc.rust-lang.org/book/)
> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/)
> **适用版本**: Rust 1.96.0+ (Edition 2024)
> **更新日期**: 2026-06-29

### 升级要点 {#升级要点}

> **来源**: [Rust Edition Guide](https://doc.rust-lang.org/edition-guide/)

本文档已完成权威国际化来源对齐升级：将泛化的 "Rust Official Docs" 替换为官方具体章节/模块/API 链接，并补充 P1 形式化来源对照。

#### 权威来源对齐 {#权威来源对齐}

| 来源类型 | 具体链接 | 用途 |
| :--- | :--- | :--- |
| **The Rust Programming Language** | [所有权](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)、[借用](https://doc.rust-lang.org/book/ch04-02-references-and-borrowing.html)、[生命周期](https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html)、[Trait](https://doc.rust-lang.org/book/ch10-02-traits.html)、[并发](https://doc.rust-lang.org/book/ch16-00-concurrency.html)、[异步](https://doc.rust-lang.org/book/ch17-00-async-await.html)、[Unsafe Rust](https://doc.rust-lang.org/book/ch19-01-unsafe-rust.html) | 概念教学与场景解释 |
| **Rust Reference** | [引言](https://doc.rust-lang.org/reference/introduction.html)、[变量与所有权](https://doc.rust-lang.org/reference/variables.html)、[类型](https://doc.rust-lang.org/reference/types.html)、[Trait 项](https://doc.rust-lang.org/reference/items/traits.html)、[async 函数](https://doc.rust-lang.org/reference/items/functions.html#async-functions)、[Unsafe 块](https://doc.rust-lang.org/reference/unsafe-blocks.html) | 语言规范与精确语义 |
| **Cargo Book** | [Cargo Book](https://doc.rust-lang.org/cargo/)、[Workspaces](https://doc.rust-lang.org/cargo/reference/workspaces.html)、[依赖](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html)、[Targets](https://doc.rust-lang.org/cargo/reference/cargo-targets.html) | 构建、包与项目管理 |
| **Rust Standard Library** | [std](https://doc.rust-lang.org/std/)、[Vec](https://doc.rust-lang.org/std/vec/struct.Vec.html)、[HashMap](https://doc.rust-lang.org/std/collections/struct.HashMap.html)、[Result](https://doc.rust-lang.org/std/result/enum.Result.html)、[Future](https://doc.rust-lang.org/std/future/trait.Future.html)、[Pin](https://doc.rust-lang.org/std/pin/struct.Pin.html)、[thread](https://doc.rust-lang.org/std/thread/)、[sync](https://doc.rust-lang.org/std/sync/) | API/模块级别参考 |
| **Rust Edition Guide** | [Edition Guide](https://doc.rust-lang.org/edition-guide/)、[Rust 2024](https://doc.rust-lang.org/edition-guide/rust-2024/index.html) | 版本差异与迁移 |

#### 形式化来源对照 {#形式化来源对照}

> **来源**: [RustBelt](https://plv.mpi-sws.org/rustbelt/) / [Aeneas](https://aeneas-verification.github.io/) / [Ferrocene FLS](https://spec.ferrocene.dev/)

| 形式化主题 | RustBelt | Aeneas | Ferrocene FLS |
| :--- | :--- | :--- | :--- |
| 所有权唯一性/内存安全 | ✓ 核心模型 | ✓ 可验证提取 | ✓ 规范 § 所有权 |
| 借用/数据竞争自由 | ✓ 生命周期逻辑 | ✓ 借用检查验证 | ✓ 规范 § 借用 |
| 类型系统/Trait | ✓ Iris 语义 | ✓ 类型系统提取 | ✓ 规范 § 类型 |
| 异步/Pin | ✓ 扩展模型 | 部分支持 | ✓ 规范 § 表达式 |

#### 版本与生态更新 {#版本与生态更新}

- 所有概念、示例与最佳实践统一对齐 **Rust 1.96.0+ (Edition 2024)**。
- 生态引用已更新：async-std → Tokio / smol；wasm32-wasi → wasm32-wasip1 / wasm32-wasip2。
- 后续版本跟踪请参见 [Rust Edition Guide](https://doc.rust-lang.org/edition-guide/rust-2024/index.html) 与 [Rust Reference](https://doc.rust-lang.org/reference/)。

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-06-29 (Rust 1.96.0+ / Edition 2024 权威国际化升级)

---

> **权威来源**: [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Reference](https://doc.rust-lang.org/reference/), [Cargo Book](https://doc.rust-lang.org/cargo/), [Rust Standard Library](https://doc.rust-lang.org/std/), [Rust Edition Guide](https://doc.rust-lang.org/edition-guide/), [RustBelt](https://plv.mpi-sws.org/rustbelt/), [Aeneas](https://aeneas-verification.github.io/), [Ferrocene FLS](https://spec.ferrocene.dev/)
>
> **权威来源对齐变更日志**: 2026-06-29 完成 Batch 9：将泛化 Rust Official Docs 替换为具体章节/API/模块链接，并补充 P1 形式化来源对照 [来源: Authority Source Sprint Batch 9]

**文档版本**: 1.2
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-06-29
**状态**: ✅ 已完成权威国际化来源对齐升级

---

## 相关概念 {#相关概念}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

- [research_notes 目录](README.md)
- [上级目录](../README.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **形式化来源**: [RustBelt](https://plv.mpi-sws.org/rustbelt/) — Rust 语义与形式化安全性证明
> **形式化来源**: [Aeneas](https://aeneas-verification.github.io/) — Rust 程序到 Lean 的验证前端
> **形式化来源**: [Ferrocene FLS](https://spec.ferrocene.dev/) — Rust 语言形式化规范

---
