# 性能测试报告 {#性能测试报告}

> **EN**: Performance Testing Report
> **Summary**: 性能测试报告 Performance Testing Report.
> **Rust 版本**: 1.96.1+ (Edition 2024)
> **最后更新**: 2026-06-09
>
> **受众**: [初学者] / [进阶]
> **内容分级**: [综述级]

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
