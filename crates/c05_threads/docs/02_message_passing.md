# 第 2 章：使用消息传递在线程间通信

> **EN**: Threading / Concurrency Guide (crate example index)
> **Summary**: A stub page pointing to the canonical concept authority. General Rust explanations have been migrated to `concept/`; runnable examples remain in the crate.

> **权威来源**: 通用 Rust 概念解释已迁移至 canonical authority page:
> [`concept/03_advanced/00_concurrency/10_concurrency_patterns.md`](../../../concept/03_advanced/00_concurrency/10_concurrency_patterns.md).

本文件原为对应 crate 的通用概念教程。根据 AGENTS.md §6.4 治理规则，
通用 Rust 概念解释已迁移至 `concept/`，此处仅保留索引与 canonical 链接。
具体可运行示例请参见本 crate 的 `examples/` 与 `src/bin/` 目录。

## 主题速览

- 🎯 消息传递核心知识图谱
  - 消息传递概念关系图
  - 通道数据流图
- 📊 通道类型多维对比
  - 标准库 vs 第三方库对比
  - 通道性能特征对比
  - 接收方法对比
- 1. 核心思想：通道与所有权
  - 1.1. 通道 (Channels) 的理论基础
  - 1.2. Rust 的实现：`mpsc` 模块
- 2. MPSC 通道详解
  - 2.1. 创建通道与发送数据
  - 2.2. 接收数据：`recv` 与 `try_recv`
- 3. 所有权与消息传递的交互
  - 3.1. 所有权转移是关键
  - 3.2. 多发送者 (Multiple Producers)
- 4. 哲学批判性分析
  - 4.1. "不要通过共享内存来通信"
  - 4.2. 局限性与替代方案
- 🚀 Rust 1.92.0 增强特性（自 Rust 1.90 引入）
  - Rust 1.92.0 通道性能提升（自 Rust 1.90 引入）
  - 🚀 示例 1: Rust 1.92.0 改进的 MPSC 通道（自 Rust 1.90 引入）
  - 🚀 示例 2: 有界通道与背压处理
  - 🚀 示例 3: 多生产者模式
  - 📊 性能基准对比
- 💡 思维导图：通道选择策略
- 📋 快速参考
  - 常用通道API
  - 错误类型速查
- 5. 总结
  - 核心优势 ✅
  - Rust 1.90 改进 🚀
  - 最佳实践建议
  - 学习路径
