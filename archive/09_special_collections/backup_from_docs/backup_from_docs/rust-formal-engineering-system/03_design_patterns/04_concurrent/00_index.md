# 并发模式（Concurrent Patterns）索引

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: 🔄 进行中

---

## 📊 目录

- [并发模式（Concurrent Patterns）索引](#并发模式concurrent-patterns索引)
  - [📊 目录](#-目录)
  - [目的](#目的)
  - [核心模式](#核心模式)
  - [Rust 化要点](#rust-化要点)
  - [术语（Terminology）](#术语terminology)
  - [实践与样例（Practice）](#实践与样例practice)
    - [文件级清单（精选）](#文件级清单精选)
  - [📚 内容文档](#-内容文档)
  - [相关索引](#相关索引)
  - [导航](#导航)

---

## 目的

- 介绍并发设计模式在 Rust 中的实现与应用。
- 提供并发编程的最佳实践与 Rust 化改造方案。

---

## 核心模式

- **生产者-消费者模式（Producer-Consumer）**: 通过队列解耦生产和消费
- **读写锁模式（Read-Write Lock）**: 允许多个读或单个写
- **屏障模式（Barrier）**: 同步多个线程到达某个点
- **信号量模式（Semaphore）**: 控制并发访问数量
- **工作窃取模式（Work Stealing）**: 动态负载均衡
- **Actor 模式**: 通过消息传递实现并发
- **CSP 模式（Communicating Sequential Processes）**: 通过通道通信

---

## Rust 化要点

- **Channel 通信**: 使用 `mpsc`、`oneshot` 等通道
- **同步原语**: 使用 `Mutex`、`RwLock`、`Barrier` 等
- **Arc 共享**: 使用 `Arc` 共享不可变数据
- **消息传递**: 优先使用消息传递而非共享状态

---

## 术语（Terminology）

- 并发模式（Concurrent Patterns）
- 生产者-消费者（Producer-Consumer）
- 读写锁（Read-Write Lock）、屏障（Barrier）
- 信号量（Semaphore）、工作窃取（Work Stealing）

---

## 实践与样例（Practice）

### 文件级清单（精选）

- 参见 [`crates/c05_threads/`](../../../../crates/c05_threads/) 目录
- 参见 [`crates/c06_async/`](../../../../crates/c06_async/) 目录

---

## 📚 内容文档

- **[并发模式基础](./01_concurrent_patterns_basics.md)** - 并发模式实践和示例 ✅

## 相关索引

- [并发编程范式](../../02_programming_paradigms/05_concurrent/00_index.md)
- [设计模式总索引](../00_index.md)

---

## 导航

- 返回总索引：[`../00_index.md`](../00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
- 并发编程：[`../../02_programming_paradigms/05_concurrent/00_index.md`](../../02_programming_paradigms/05_concurrent/00_index.md)
