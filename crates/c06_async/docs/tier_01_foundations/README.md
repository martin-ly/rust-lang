> **生态状态提示**：
>
> 本文档提及 `async-std` 与/或 `wasm32-wasi`。
> 请注意：
>
> - `async-std` 项目已进入维护模式，2024 年后不再活跃开发；新项目建议优先评估 **Tokio** 或 **smol**。
> - `wasm32-wasi` 旧目标名已重命名为 **`wasm32-wasip1`**；WASI Preview 2 对应目标为 **`wasm32-wasip2`**。

---

# Tier 1: 基础层 - 异步编程基础

**难度**: ⭐
**预计学习时间**: 2-4 小时
**适合人群**: Rust 初学者、需要快速了解异步编程的开发者

---

## 📚 本层内容

Tier 1 提供异步编程的快速入门和核心概念概览，帮助您在最短时间内理解 Rust 异步编程的基础知识。

### 核心文档

1. **[项目概览](01_project_overview.md)** ⭐ 推荐起点
   - 模块目标与定位
   - 异步编程核心特性
   - 学习路径指引
2. **[主索引导航](02_navigation.md)**
   - 文档分类索引
   - 学习路径规划
   - 快速查找指南
3. **[术语表](03_glossary.md)**
   - 异步编程核心术语
   - Future、async/await、runtime 术语
   - 并发模型术语
4. **[常见问题](04_faq.md)**
   - 新手常见疑问
   - 异步编程最佳实践
   - 故障排除指南

---

## 🎯 学习目标

完成 Tier 1 后，您将能够：

- ✅ 理解 Rust 异步编程的基本概念（Future、async/await）
- ✅ 了解异步运行时（Tokio、async-std [已归档]）的作用
- ✅ 理解异步与同步、并行的区别
- ✅ 能够查阅文档并规划学习路径

---

## ⏭️ 下一步

完成 Tier 1 后，建议：

1. **继续深入**: 进入 [Tier 2: 实践层](../tier_02_guides/README.md) 学习异步编程技巧
2. **查阅参考**: 使用 [Tier 3: 参考层](../tier_03_references/README.md) 查找具体 API
3. **理论深入**: 准备好后探索 [Tier 4: 高级层](../tier_04_advanced/README.md) 的高级主题

---

## 📖 推荐学习顺序

```text
01_project_overview.md (15分钟)
    ↓
02_navigation.md (10分钟)
    ↓
03_glossary.md (30分钟)
    ↓
04_faq.md (40分钟)
    ↓
进入 Tier 2 实践指南
```
---

## 🌟 Rust 1.93.0 异步特性

- ✅ 异步闭包（`async |x| ...`）
- ✅ Trait 中的异步函数（AFIT）
- ✅ 返回位置 impl Trait in Traits (RPITIT)
- ✅ 异步性能优化
- ✅ 改进的异步运行时性能
- ✅ 增强的异步特性支持
- ✅ 编译器优化

---

**最后更新**: 2025-10-24
**维护状态**: 🟢 活跃维护中
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.1+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
