# 调试（Debugging）索引

## 📊 目录

- [调试（Debugging）索引](#调试debugging索引)
  - [📊 目录](#-目录)
  - [目的](#目的)
  - [核心概念](#核心概念)
  - [与 Rust 的关联](#与-rust-的关联)
  - [术语（Terminology）](#术语terminology)
  - [实践与样例](#实践与样例)
    - [文件级清单（精选）](#文件级清单精选)
  - [相关索引](#相关索引)
  - [导航](#导航)

## 目的

- 介绍调试工具在 Rust 项目中的应用与实践。
- 提供调试策略、调试工具、调试技巧的技术指导。

## 核心概念

- 调试策略：断点调试、日志调试、交互调试
- 调试工具：调试器、分析器、监控器
- 调试技巧：问题定位、错误分析、性能调试
- 远程调试：远程连接、远程执行、远程监控
- 内存调试：内存泄漏、内存错误、内存分析
- 并发调试：线程调试、死锁检测、竞态条件
- 网络调试：网络分析、协议分析、流量分析
- 性能调试：性能瓶颈、性能分析、性能优化

## 与 Rust 的关联

- 内存安全：减少调试需求
- 性能优势：快速的调试工具
- 并发安全：安全的并发调试
- 跨平台：支持多种调试环境

## 术语（Terminology）

- 调试（Debugging）、调试策略（Debugging Strategy）
- 调试工具（Debugging Tools）、调试技巧（Debugging Techniques）
- 远程调试（Remote Debugging）、内存调试（Memory Debugging）
- 并发调试（Concurrency Debugging）、网络调试（Network Debugging）

## 实践与样例

- 调试工具：参见 [crates/c61_debugging](../../../crates/c61_debugging/)
- 工具链生态：[`../../06_toolchain_ecosystem/00_index.md`](../../06_toolchain_ecosystem/00_index.md)
- 质量保障：[`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)

### 文件级清单（精选）

- `crates/c61_debugging/src/`：
  - `debugging_strategy.rs`：调试策略
  - `debugging_tools.rs`：调试工具
  - `debugging_techniques.rs`：调试技巧
  - `remote_debugging.rs`：远程调试
  - `memory_debugging.rs`：内存调试

## 相关索引

- 理论基础（并发模型）：[`../../01_theoretical_foundations/04_concurrency_models/00_index.md`](../../01_theoretical_foundations/04_concurrency_models/00_index.md)
- 编程范式（异步）：[`../../02_programming_paradigms/02_async/00_index.md`](../../02_programming_paradigms/02_async/00_index.md)
- 工具链生态：[`../../06_toolchain_ecosystem/00_index.md`](../../06_toolchain_ecosystem/00_index.md)

## 导航

- 返回工具链生态：[`../00_index.md`](../00_index.md)
- IDE 集成：[`../08_ide_integration/00_index.md`](../08_ide_integration/00_index.md)
- 监控：[`../10_monitoring/00_index.md`](../10_monitoring/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
