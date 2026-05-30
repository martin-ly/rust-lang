# 综合概念对比矩阵

> **分级**: [C]
> **Bloom 层级**: L5-L6 (分析/评价/创造)

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [综合概念对比矩阵](#综合概念对比矩阵)
  - [📑 目录](#目录)
  - [1. 并发模型对比矩阵](#1-并发模型对比矩阵)
  - [2. 同步原语对比矩阵](#2-同步原语对比矩阵)
  - [3. 智能指针对比矩阵](#3-智能指针对比矩阵)
  - [4. 运行时选择矩阵](#4-运行时选择矩阵)
  - [5. Web框架对比矩阵](#5-web框架对比矩阵)
  - [6. 形式化验证工具对比矩阵](#6-形式化验证工具对比矩阵)
  - [7. 内存管理策略对比矩阵](#7-内存管理策略对比矩阵)
  - [8. 设计模式适用性矩阵](#8-设计模式适用性矩阵)
  - [9. 错误处理策略对比矩阵](#9-错误处理策略对比矩阵)
  - [10. 代码组织模式对比矩阵](#10-代码组织模式对比矩阵)
  - [使用指南](#使用指南)
    - [如何选择正确的工具/模式？](#如何选择正确的工具模式)
    - [常见决策路径](#常见决策路径)
  - **更新日期**: 2026-03-05
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

## 1. 并发模型对比矩阵
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

| 特性 | OS线程 | async/await | Actor | 数据并行 |
|:---|:---:|:---:|:---:|:---:|
| **内存开销** | 高 (1-8MB) | 低 (几KB) | 中 | 低 |
| **上下文切换** | 内核级 | 用户级 | 消息传递 | 隐式 |
| **数据共享** | 共享内存 | 共享内存 | 消息传递 | 分块处理 |
| **数据竞争风险** | 高 | 中 | 低 | 低 |
| **死锁风险** | 高 | 中 | 低 | 无 |
| **扩展性** | 低 | 高 | 高 | 中 |
| **适用场景** | CPU密集型 | IO密集型 | 分布式系统 | 数值计算 |
| **Rust支持** | std::thread | tokio/async-std | actix/bastion | rayon |
| **学习曲线** | 低 | 中 | 高 | 低 |
| **调试难度** | 高 | 中 | 中 | 低 |

## 2. 同步原语对比矩阵
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

| 原语 | 所有权 | Send | Sync | 阻塞 | 适用场景 |
|:---|:---:|:---:|:---:|:---:|:---|
| `Mutex<T>` | 有 | 是* | 是* | 是 | 线程间可变共享 |
| `RwLock<T>` | 有 | 是* | 是* | 是 | 多读一写 |
| `Atomic*` | 无 | 是 | 是 | 否 | 简单计数器 |
| `Channel` | 转移 | 是 | 否 | 可选 | 任务间通信 |
| `RefCell<T>` | 有 | 否 | 否 | 是(panic) | 单线程内部可变 |
| `Cell<T>` | 有 | 否 | 否 | 否 | 单线程简单可变 |

> *注: 要求T: Send/Sync

## 3. 智能指针对比矩阵
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

| 指针 | 所有权 | 引用计数 | 线程安全 | 可变性 | 开销 |
|:---|:---:|:---:|:---:|:---:|:---:|
| `Box<T>` | 独占 | 否 | 是 | 可变 | 0 |
| `Rc<T>` | 共享 | 是(单线程) | 否 | 不可变 | +1usize |
| `Arc<T>` | 共享 | 是(多线程) | 是 | 不可变 | +2 AtomicUsize |
| `Weak<T>` | 弱引用 | 是 | 是 | 不可变 | 同Rc/Arc |
| `Cow<'a, T>` | 借用/拥有 | 否 | 是 | 可变 | 枚举开销 |

## 4. 运行时选择矩阵
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

| 运行时 | 平台 | IO模型 | 最小化 | 特性 | 适用场景 |
|:---|:---|:---|:---:|:---|:---|
| Tokio | Linux/Mac/Win | epoll/kqueue/IOCP | 否 | 完整生态 | 通用async |
| async-std | Linux/Mac/Win | epoll/kqueue/IOCP | 否 | 标准库风格 | 通用async |
| smol | Linux/Mac/Win | epoll/kqueue/IOCP | 是 | 轻量 | 资源受限 |
| monoio | Linux 5.6+ | io_uring | 是 | 极致性能 | 高性能网关 |
| glommio | Linux 5.6+ | io_uring + DMA | 是 | 存储优化 | 存储密集型 |
| Embassy | 嵌入式 | 中断驱动 | 是 | no_std | 嵌入式 |

## 5. Web框架对比矩阵
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| 框架 | 性能 | 人体工学 | 生态 | 学习曲线 | 特色 |
|:---:|:---:|:---:|:---:|:---:|:---|
| Axum | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | 中 | Tower生态集成 |
| Actix-web | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | 中 | Actor模型 |
| Rocket | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | 低 | 声明式宏 |
| poem | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | 中 | 模块化设计 |
| salvo | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ | 中 | 简化版Axum |
| tide | ⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐ | 低 | 异步初学者 |

## 6. 形式化验证工具对比矩阵
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 工具 | 验证类型 | 自动化 | 学习曲线 | 覆盖范围 | 成熟度 |
|:---:|:---:|:---:|:---:|:---:|:---:|
| Miri | 未定义行为 | 全自动 | 低 | 运行时 | ⭐⭐⭐⭐⭐ |
| Kani | 模型检测 | 全自动 | 中 | 状态空间 | ⭐⭐⭐⭐ |
| Creusot | 定理证明 | 半自动 | 高 | 功能正确 | ⭐⭐⭐ |
| Prusti | 合约验证 | 半自动 | 中 | 前后条件 | ⭐⭐⭐ |
| Crux | 符号执行 | 全自动 | 中 | 路径覆盖 | ⭐⭐⭐ |

## 7. 内存管理策略对比矩阵
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

| 策略 | 分配 | 释放 | 性能 | 安全 | 适用场景 |
|:---|:---:|:---:|:---:|:---:|:---|
| Stack | 自动 | 自动 | 最高 | ⭐⭐⭐⭐⭐ | 固定大小数据 |
| Box | 动态 | 自动 | 高 | ⭐⭐⭐⭐⭐ | 堆数据、递归类型 |
| Rc/Arc | 动态 | 引用计数 | 中 | ⭐⭐⭐⭐ | 共享所有权 |
| Arena | 批量 | 批量 | 高 | ⭐⭐⭐⭐ | 同生命周期对象 |
| Pool | 预分配 | 重用 | 高 | ⭐⭐⭐⭐ | 固定大小频繁分配 |
| Custom | 手动 | 手动 | 可变 | ⭐⭐ | 特殊场景 |

## 8. 设计模式适用性矩阵

| 模式 | 内存安全 | 线程安全 | 零成本 | 复杂度 | 适用频率 |
|:---:|:---:|:---:|:---:|:---:|:---:|
| Builder | ⭐⭐⭐⭐⭐ | N/A | ⭐⭐⭐⭐⭐ | 低 | 高 |
| Into/From | ⭐⭐⭐⭐⭐ | N/A | ⭐⭐⭐⭐⭐ | 低 | 极高 |
| Newtype | ⭐⭐⭐⭐⭐ | N/A | ⭐⭐⭐⭐⭐ | 低 | 高 |
| RAII | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | 低 | 极高 |
| TypeState | ⭐⭐⭐⭐⭐ | N/A | ⭐⭐⭐⭐⭐ | 中 | 中 |
| `Arc<Mutex>` | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ | 低 | 高 |
| Channel | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | 低 | 高 |
| Pin | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | 高 | 中 |

## 9. 错误处理策略对比矩阵

| 策略 | 性能 | 类型安全 | 调试友好 | 代码简洁 | 适用场景 |
|:---:|:---:|:---:|:---:|:---:|:---|
| panic! | 高 | N/A | 好 | 简洁 | 不可恢复错误 |
| Result | 高 | ⭐⭐⭐⭐⭐ | 好 | 中 | 可恢复错误 |
| Option | 高 | ⭐⭐⭐⭐⭐ | 中 | 中 | 可选值 |
| ? operator | 高 | ⭐⭐⭐⭐⭐ | 好 | ⭐⭐⭐⭐⭐ | 错误传播 |
| unwrap/expect | 高 | N/A | 差 | ⭐⭐⭐⭐⭐ | 快速原型 |
| anyhow | 中 | ⭐⭐⭐ | 好 | ⭐⭐⭐⭐⭐ | 应用错误处理 |
| thiserror | 中 | ⭐⭐⭐⭐⭐ | 好 | ⭐⭐⭐⭐ | 库错误处理 |

## 10. 代码组织模式对比矩阵

| 模式 | 耦合度 | 内聚性 | 可测试性 | 可扩展性 | 适用规模 |
|:---:|:---:|:---:|:---:|:---:|:---:|
| 模块化 | 低 | 高 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | 任何 |
| 分层架构 | 低 | 高 | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | 中型+ |
| 微服务 | 极低 | 高 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | 大型 |
| Actor | 低 | 高 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | 分布式 |
| ECS | 低 | 高 | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | 游戏/仿真 |

---

## 使用指南

### 如何选择正确的工具/模式？

1. **确定约束条件**: 性能要求、线程安全、平台限制
2. **对比候选方案**: 使用上述矩阵横向对比
3. **评估权衡**: 在安全性、性能、复杂度之间找到平衡
4. **验证选择**: 通过原型代码验证选择是否正确

### 常见决策路径

```text
需要并发?
├── 是 → 需要共享状态?
│          ├── 是 → 需要跨线程?
│          │          ├── 是 → Arc<Mutex<T>>
│          │          └── 否 → RefCell<T>
│          └── 否 → Channel / Actor
└── 否 → 单线程操作
```

---

**维护者**: Rust Analysis Team
**更新日期**: 2026-03-05
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

- [上级目录](../README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Memory Safety]**

> **[来源: TRPL Ch. 4 - Ownership]**

> **[来源: Rustonomicon - Ownership]**

> **[来源: POPL 2018 - RustBelt]**

---

## 权威来源索引

> **[来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/)]**
>
> **[来源: [Tree Borrows](https://plv.mpi-sws.org/rustbelt/tree-borrows/)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
