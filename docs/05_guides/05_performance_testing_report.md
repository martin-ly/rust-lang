# 性能测试报告 {#性能测试报告}

> **EN**: Performance Testing Report
> **Summary**: 性能测试报告 Performance Testing Report.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **最后更新**: 2026-06-09
>
> **受众**: [初学者] / [进阶]
> **内容分级**: [综述级]
> **权威来源**: 性能测试与基准测试概念见 [concept/06_ecosystem/09_testing_and_quality/04_benchmarking.md](../../concept/06_ecosystem/09_testing_and_quality/04_benchmarking.md) 与 [concept/06_ecosystem/10_performance/01_performance_optimization.md](../../concept/06_ecosystem/10_performance/01_performance_optimization.md)。
> **说明**: 本文件为项目性能测试报告，记录工具、方法与数据，不属于 Rust 概念知识本身，不建立 concept/ 权威页。

本文件记录 Rust 代码性能测试的方法、工具和基准数据。

## 测试方法 {#测试方法}

| 方法 | 工具 | 适用场景 |
|:---|:---|:---|
| 微基准测试 | `criterion` | 函数级性能对比 |
| 集成性能测试 | `cargo bench` | 模块（Module）级性能评估 |
| 内存分析 | `heaptrack`, `valgrind` | 堆分配分析 |
| CPU 分析 | `perf`, `flamegraph` | 热点识别 |

## 关键指标 {#关键指标}

- **吞吐量**: 每秒处理请求/数据量
- **延迟**: P50/P99 响应时间
- **内存占用**: 峰值 RSS / 堆分配总量
- **编译时间**: `cargo build` 耗时

## 相关指南 {#相关指南}

- [性能调优完整指南](05_performance_tuning_guide.md)
- [测试与覆盖率指南](05_testing_coverage_guide.md)
