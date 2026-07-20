# 并行模式（Parallel Patterns）索引

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: 🔄 进行中

---

## 📊 目录

- [并行模式（Parallel Patterns）索引](#并行模式parallel-patterns索引)
  - [📊 目录](#-目录)
  - [目的](#目的)
  - [核心模式](#核心模式)
  - [Rust 化要点](#rust-化要点)
  - [术语（Terminology）](#术语terminology)
  - [实践与样例（Practice）](#实践与样例practice)
    - [文件级清单（精选）](#文件级清单精选)
  - [相关索引](#相关索引)
  - [导航](#导航)

---

## 目的

- 介绍并行设计模式在 Rust 中的实现与应用。
- 提供并行编程的最佳实践与 Rust 化改造方案。

---

## 核心模式

- **Map-Reduce 模式**: 并行映射和归约操作
- **分治模式（Divide and Conquer）**: 将问题分解为子问题并行解决
- **流水线模式（Pipeline）**: 将任务分解为阶段并行执行
- **扇出-扇入模式（Fan-out/Fan-in）**: 分发任务并收集结果
- **并行扫描模式（Parallel Scan）**: 并行前缀和计算
- **并行排序模式**: 并行排序算法

---

## Rust 化要点

- **Rayon 并行**: 使用 Rayon 实现数据并行
- **并行迭代器**: 使用并行迭代器简化并行代码
- **工作窃取**: 利用工作窃取实现负载均衡
- **SIMD 优化**: 利用 SIMD 指令加速计算

---

## 术语（Terminology）

- 并行模式（Parallel Patterns）
- Map-Reduce、分治（Divide and Conquer）
- 流水线（Pipeline）、扇出-扇入（Fan-out/Fan-in）
- 并行扫描（Parallel Scan）

---

## 实践与样例（Practice）

### 文件级清单（精选）

- 参见 [`crates/c08_algorithms/`](../../../../crates/c08_algorithms/) 目录
- 参见 [`crates/c08_algorithms/benches/`](../../../../crates/c08_algorithms/benches/) 目录

---

## 相关索引

- [并行编程范式](../../02_programming_paradigms/06_parallel/00_index.md)
- [设计模式总索引](../00_index.md)

---

## 导航

- 返回总索引：[`../00_index.md`](../00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
- 并行编程：[`../../02_programming_paradigms/06_parallel/00_index.md`](../../02_programming_paradigms/06_parallel/00_index.md)
