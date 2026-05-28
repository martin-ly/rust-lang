# 并发模型选择决策树

> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **根据应用场景选择最佳并发模型**

---

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [并发模型选择决策树](#并发模型选择决策树)
  - [📑 目录](#-目录)
  - [1. 顶层决策树](#1-顶层决策树)
  - [2. 详细决策流程](#2-详细决策流程)
    - [2.1 Actor模型选择](#21-actor模型选择)
    - [2.2 Async运行时选择](#22-async运行时选择)
    - [2.3 共享状态选择](#23-共享状态选择)
    - [2.4 同步原语选择](#24-同步原语选择)
  - [3. 场景匹配表](#3-场景匹配表)
  - [4. 性能对比决策](#4-性能对比决策)
  - [5. 安全性优先决策](#5-安全性优先决策)
  - [6. 快速决策检查表](#6-快速决策检查表)
    - [6.1 检查清单](#61-检查清单)
    - [6.2 常见错误避免](#62-常见错误避免)
  - [**适用版本**: Rust 1.75+](#适用版本-rust-175)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

## 1. 顶层决策树
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

```text
开始选择并发模型
        │
        ▼
┌─────────────────────┐
│ 需要跨进程/网络通信? │
└──────────┬──────────┘
           │
    ┌──────┴──────┐
    ▼             ▼
   是             否
    │             │
    ▼             ▼
┌─────────────┐ ┌─────────────────────┐
│ Actor模型   │ │ 需要在多线程间共享? │
│ (分布式)    │ └──────────┬──────────┘
└─────────────┘            │
                  ┌────────┴────────┐
                  ▼                 ▼
                 是                 否
                  │                 │
                  ▼                 ▼
        ┌─────────────────┐ ┌─────────────────┐
        │ 共享状态类型?    │ │ 单线程内并发?   │
        └────────┬────────┘ └────────┬────────┘
                 │                   │
        ┌────────┼────────┐          ▼
        ▼        ▼        ▼   ┌──────────────┐
      可变    不可变     混合  │ Async/await  │
        │       │        │    │ (协作式)     │
        ▼       ▼        ▼    └──────────────┘
   ┌────────┐ ┌──────┐ ┌──────────┐
   │ Mutex  │ │ Arc  │ │ Actor    │
   │ RwLock │ │ 只读 │ │ (本地)   │
   │ 原子   │ └──────┘ └──────────┘
   └────────┘
```

---

## 2. 详细决策流程
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

### 2.1 Actor模型选择
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

```text
选择Actor模型
      │
      ├──▶ 需要容错/监督? ──▶ 是 ──▶ Bastion
      │                          ├── 监督树
      │                          ├── 故障隔离
      │                          └── 分布式支持
      │
      ├──▶ 需要最高性能? ──▶ 是 ──▶ Actix
      │                          ├── 零拷贝消息
      │                          ├── 工作窃取
      │                          └── 本地优先
      │
      ├──▶ 需要简单API? ──▶ 是 ──▶ Xtra
      │                          └── 轻量级
      │
      └──▶ 需要分布式集群? ──▶ 是 ──▶ coerce
                                   ├── 远程Actor
                                   ├── 集群发现
                                   └── 位置透明
```

### 2.2 Async运行时选择
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```text
选择Async运行时
      │
      ├──▶ 目标平台? ──▶ 嵌入式 ──▶ Embassy/RTIC
      │                          ├── 无堆分配
      │                          ├── 中断集成
      │                          └── 实时性
      │
      ├──▶ 性能要求? ──▶ 极致 ──▶ io_uring (monoio/glommio)
      │                          ├── Linux 5.6+
      │                          ├── 零拷贝
      │                          └── 提交队列轮询
      │
      ├──▶ 需要完整生态? ──▶ 是 ──▶ Tokio
      │                          ├── 网络/文件/时间
      │                          ├── 丰富的中间件
      │                          └── 生产验证
      │
      └──▶ 需要轻量级? ──▶ 是 ──▶ smol/async-std
                                   ├── 较小体积
                                   └── 标准库风格
```

### 2.3 共享状态选择
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```text
共享状态并发
      │
      ├──▶ 需要可变共享? ──▶ 否 ──▶ Arc<T>
      │                          ├── 不可变数据
      │                          └── 引用计数
      │
      └──▶ 是 ──▶ 访问模式?
                   │
                   ├──▶ 多读少写 ──▶ RwLock<T>
                   │                   ├── 并行读
                   │                   └── 独占写
                   │
                   ├──▶ 写多读少 ──▶ Mutex<T>
                   │                   ├── 简单
                   │                   └── 通用
                   │
                   ├──▶ 高频计数 ──▶ Atomic*
                   │                   ├── 无锁
                   │                   ├── CAS操作
                   │                   └── 内存序选择
                   │
                   └──▶ 复杂结构 ──▶ 考虑无锁结构
                                       ├── crossbeam
                                       ├── lock-free
                                       └── 专家级
```

### 2.4 同步原语选择
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```text
同步需求
      │
      ├──▶ 需要线程屏障? ──▶ 是 ──▶ Barrier
      │                          └── 等待所有线程到达
      │
      ├──▶ 需要信号量? ──▶ 是 ──▶ Semaphore
      │                          └── 限制并发数
      │
      ├──▶ 需要条件变量? ──▶ 是 ──▶ Condvar
      │                          └── 复杂等待条件
      │
      ├──▶ 需要一次性初始化? ──▶ 是 ──▶ Once/OnceLock
      │                              └── 延迟初始化
      │
      └──▶ 需要等待多个事件? ──▶ 是 ──▶ select!/join!
                                         ├── 等待任一
                                         └── 等待全部
```

---

## 3. 场景匹配表
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

| 场景 | 推荐模型 | 具体实现 | 理由 |
|:---|:---|:---|:---|
| Web服务器 | Async + ThreadPool | Tokio + hyper | 高并发IO |
| 实时控制 | Actor + RTIC | Actix/Embassy | 确定性响应 |
| 数据处理 | Data Parallel | Rayon | 自动并行化 |
| 游戏服务器 | Actor | Actix/coerce | 状态隔离 |
| 微服务 | Async + gRPC | Tokio + tonic | 异步RPC |
| 嵌入式传感器 | Async + Interrupt | Embassy | 低功耗 |
| 区块链节点 | Actor + Consensus | 自定义 | 容错需求 |
| 机器学习 | Data Parallel | Rayon/tch-rs | 张量并行 |

---

## 4. 性能对比决策
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```text
性能优先?
      │
      ├──▶ 吞吐量优先 ──▶ 选择
      │      ├── 网络IO: io_uring (1M+ conn/s)
      │      ├── 文件IO: io_uring + DirectIO
      │      └── 计算: Rayon并行迭代器
      │
      ├──▶ 延迟优先 ──▶ 选择
      │      ├── 极低延迟: 无锁队列 + busy-wait
      │      ├── 低延迟: Tokio + 工作窃取
      │      └── 可预测: RTIC确定性调度
      │
      └──▶ 内存优先 ──▶ 选择
             ├── 极小内存: Embassy (100B/任务)
             ├── 小内存: smol
             └── 标准: Tokio
```

---

## 5. 安全性优先决策
>
> **[来源: [crates.io](https://crates.io/)]**

```text
安全性要求?
      │
      ├──▶ 绝对无数据竞争 ──▶ 选择
      │      ├── Actor模型 (消息传递)
      │      └── 纯函数式 (不可变状态)
      │
      ├──▶ 避免死锁 ──▶ 策略
      │      ├── 锁顺序一致化
      │      ├── 使用try_lock超时
      │      └── 考虑lock-free结构
      │
      └──▶ 避免内存泄漏 ──▶ 策略
             ├── RAII资源管理
             ├── 使用弱引用打破循环
             └── 定期监控内存使用
```

---

## 6. 快速决策检查表
>
> **[来源: [docs.rs](https://docs.rs/)]**

### 6.1 检查清单
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```markdown
□ 需要跨网络? → Actor模型
□ 需要容错? → Actor + 监督
□ 单线程内并发? → Async/await
□ 需要共享状态? → Arc<Mutex/RwLock>
□ 只读共享? → Arc<T>或&'static T
□ 高频计数? → Atomic类型
□ 实时性要求? → RTIC或无锁
□ 资源受限? → Embassy/smool
```

### 6.2 常见错误避免
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```markdown
❌ 在async中使用阻塞IO
   ✅ 使用tokio::fs代替std::fs

❌ 在lock中持有await
   ✅ 缩短锁的作用域

❌ 使用std::sync::Mutex在async中
   ✅ 使用tokio::sync::Mutex

❌ 创建过多线程
   ✅ 使用线程池

❌ 忽略Send/Sync约束
   ✅ 正确实现或标记
```

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [Parent README](../README.md)

---

## 相关概念
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

- [上级目录](../README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Memory Safety]**

> **[来源: TRPL Ch. 4 - Ownership]**

> **[来源: Rustonomicon - Ownership]**

> **[来源: POPL 2018 - RustBelt]**

> **[来源: Wikipedia - Concurrency]**

> **[来源: TRPL Ch. 16 - Fearless Concurrency]**

> **[来源: crossbeam Documentation]**

> **[来源: ACM - Concurrent Programming]**

---

## 权威来源索引

> **[来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/)]**
>
> **[来源: [Tree Borrows](https://plv.mpi-sws.org/rustbelt/tree-borrows/)]**
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**
>
> **[来源: [Rayon Documentation](https://docs.rs/rayon/latest/rayon/)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
