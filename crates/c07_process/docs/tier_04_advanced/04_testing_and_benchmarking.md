> **EN**: Process Testing and Benchmarking
> **Summary**: Advanced guide to testing strategies, process-specific test techniques, benchmarking, stress testing, and CI integration for Rust process management. The canonical concept explanation has been migrated to the concept authority page.

# Tier 4: 测试与基准

> **权威来源**: [concept/03_advanced/02_process_ipc/09_process_testing_and_benchmarking.md](../../../../concept/03_advanced/02_process_ipc/09_process_testing_and_benchmarking.md)

本文件为 `crates/c07_process` 的专题实践材料。通用 Rust 进程测试与基准概念请参见上方权威页；完整代码示例、练习与案例仍保留在本书。

## 主题列表

- 测试策略（单元测试、集成测试、端到端测试）
- 进程测试技巧（超时、错误注入、僵尸进程处理、信号处理）
- 基准测试（Criterion、IPC 基准、进程池基准）
- 压力测试（负载生成、稳定性、内存泄漏、资源耗尽）
- CI/CD 集成与性能回归检测
- 高级测试模式（属性测试、模糊测试、覆盖率）
- 完整测试套件实战案例
