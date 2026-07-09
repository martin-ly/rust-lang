> **EN**: Rust Async Runtime Deep Comparison 2025: Glommio vs Tokio vs Smol
> **Summary**: Comparative analysis of Rust async runtimes in 2025: Glommio (thread-per-core, io_uring), Tokio (work-stealing), Smol (lightweight), and async-std (archived). Covers architecture, performance benchmarks, I/O behavior, ecosystem, use-case decision tree, and migration guidance.
>
> **权威来源**: [concept/06_ecosystem/04_web_and_networking/42_glommio_and_thread_per_core.md](../../../../concept/06_ecosystem/04_web_and_networking/42_glommio_and_thread_per_core.md)

# Rust 异步运行时深度对比 2025: Glommio vs Tokio vs Smol

> 本文档已由 `crates/*/docs/` 合规整改迁移。原始详细内容现已纳入 `concept/` 权威页；本页仅保留主题索引与入口链接。

---

## 主题索引

- 运行时特性对比
- 选择决策树
- 架构对比
  - Glommio: Thread-per-core
  - Tokio: Work-stealing
  - Smol: 轻量级多模式
  - async-std（已归档）
- 性能基准测试
  - 延迟、吞吐量、内存、CPU 效率
- I/O 性能对比
  - 文件 I/O、网络 I/O
- 并发模型对比
- 生态系统对比
- 使用场景分析
- 代码对比（基础示例 / 并发任务 / 网络服务器）
- 学习曲线对比
- 生产环境考量
- 迁移指南
- 混合使用策略
- 未来趋势

---

> ⚠️ **生态状态提示**：`async-std` 已于 2025 年 3 月停止维护，新项目建议优先评估 Tokio 或 smol。
>
> **权威来源**: [concept/06_ecosystem/04_web_and_networking/42_glommio_and_thread_per_core.md](../../../../concept/06_ecosystem/04_web_and_networking/42_glommio_and_thread_per_core.md)
