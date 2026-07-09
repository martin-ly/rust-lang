# Glommio 最佳实践指南 2025

> **EN**: Glommio Best Practices 2025
> **Summary**: Glommio high-performance async runtime based on io_uring and thread-per-core architecture: CPU pinning, NUMA awareness, zero-copy I/O, and deployment guidelines. Migrated to the ecosystem authority.
>
> **适用 Rust 版本**: 1.96.1+
> **文档类型**: 重定向 stub

---

> **权威来源**: [concept/06_ecosystem/04_web_and_networking/42_glommio_and_thread_per_core.md](../../../../concept/06_ecosystem/04_web_and_networking/42_glommio_and_thread_per_core.md)

---

## 主题列表

- Glommio 与 io_uring 定位
- Thread-per-core 架构原理
- CPU pinning 与 NUMA 优化
- 任务调度与优先级队列
- DMA 文件 I/O 与零拷贝技术
- Channel Mesh 与跨执行器通信
- 性能优化、监控与生产部署
- 与 Tokio / smol 的选型对比
