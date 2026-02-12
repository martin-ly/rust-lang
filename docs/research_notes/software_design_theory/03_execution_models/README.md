# 执行模型形式化框架

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: 100% 完成

---

## 宗旨

对同步、异步、并发、并行、分布式五类执行模型进行形式化分析，并与 Rust 形式化基础（async_state_machine、pin、Send/Sync、ownership、borrow）衔接。

---

## 执行模型分类

| 模型 | 定义 | 形式化文档 |
| :--- | :--- | :--- |
| 同步 | 顺序执行，单线程 | [01_synchronous](01_synchronous.md) |
| 异步 | Future、async/await、单线程协作式多任务 | [02_async](02_async.md) |
| 并发 | 多线程、Send/Sync、消息传递/共享状态 | [03_concurrent](03_concurrent.md) |
| 并行 | 数据并行、任务并行 | [04_parallel](04_parallel.md) |
| 分布式 | 跨进程/跨节点、Actor、RPC | [05_distributed](05_distributed.md) |

---

## 依赖引用

| 依赖 | 文档 |
| :--- | :--- |
| 异步状态机 | [async_state_machine](../../formal_methods/async_state_machine.md) |
| Pin | [pin_self_referential](../../formal_methods/pin_self_referential.md) |
| 借用 | [borrow_checker_proof](../../formal_methods/borrow_checker_proof.md) |
| 所有权 | [ownership_model](../../formal_methods/ownership_model.md) |
| Rust Book Ch16 | 线程、消息传递、Send/Sync |
| Async Book | Future、async/await、Pin |

---

## 边界分析

[06_boundary_analysis](06_boundary_analysis.md)：各模型的安全/支持/表达边界。

---

## 模型选型决策（实质内容）

| 需求组合 | 推荐模型 | 典型场景 |
| :--- | :--- | :--- |
| 单线程、无 I/O 等待 | 同步 | 批处理、脚本、算法核心 |
| 多 I/O、高并发连接 | 异步 | Web 服务、数据库、网络 |
| 多线程、消息传递 | 并发 | 生产者-消费者、多工作者 |
| CPU 密集、批量计算 | 并行 | 图像处理、数据分析、rayon |
| 跨节点通信 | 分布式 | tonic、actix、RPC |

**与设计模式映射**：同步—全部 23；异步—Observer、Command、State；并发—Singleton、Observer、Mediator；并行—Strategy、Iterator；分布式—Proxy、Gateway、DTO。详见 [06_boundary_analysis](06_boundary_analysis.md)。

---

## 模型选择速查

| 需求 | 推荐模型 | crate |
| :--- | :--- | :--- |
| 顺序执行 | 同步 | std |
| I/O 密集、高并发连接 | 异步 | tokio、async-std |
| 多线程、消息传递 | 并发 | std::thread、mpsc |
| CPU 密集、批量计算 | 并行 | rayon |
| 跨节点通信 | 分布式 | tonic、actix |
