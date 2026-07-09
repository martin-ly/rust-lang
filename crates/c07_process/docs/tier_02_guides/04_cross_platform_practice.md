> **EN**: Cross-Platform Process Practice
> **Summary**: Practical guide for writing portable process-management code across Windows, Linux, and macOS. The canonical concept explanation has been migrated to the concept authority page.

# Tier 2: 跨平台实践

> **权威来源**: [concept/03_advanced/02_process_ipc/04_cross_platform_process_management.md](../../../../concept/03_advanced/02_process_ipc/04_cross_platform_process_management.md)

本文件为 `crates/c07_process` 的专题实践材料。通用 Rust 跨平台进程管理概念请参见上方权威页；完整代码示例、练习与案例仍保留在本书。

## 主题列表

- 平台差异（进程创建、信号、进程组、路径、环境变量）
- 跨平台命令抽象与通用命令映射
- Unix / Windows / macOS 特定功能
- 统一抽象层设计
- 跨平台测试策略
- 跨平台进程监控与自动更新实战案例
