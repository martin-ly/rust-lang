> **EN**: Process Performance Engineering
> **Summary**: Advanced guide to performance analysis, profiling, zero-copy IPC, and production optimization for Rust process management. The canonical concept explanation has been migrated to the concept authority page.

# Tier 4: 性能工程实践

> **权威来源**: [concept/03_advanced/02_process_ipc/08_process_performance_engineering.md](../../../../concept/03_advanced/02_process_ipc/08_process_performance_engineering.md)

本文件为 `crates/c07_process` 的专题实践材料。通用 Rust 进程性能工程概念请参见上方权威页；完整代码示例、练习与案例仍保留在本书。

## 主题列表

- 性能分析方法论与指标体系
- 性能剖析工具（perf、Flamegraph、Valgrind/Massif、strace/ltrace、pprof）
- 热点分析（CPU、内存、I/O 瓶颈）
- 性能调优策略（系统级、应用级、编译器优化）
- 零拷贝技术（splice、sendfile、内存映射）
- 生产环境优化与持续优化流程
- 高性能进程池优化实战案例
