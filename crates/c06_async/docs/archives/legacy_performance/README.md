# 性能优化 (Performance)

本目录包含Rust异步编程的性能优化指南、基准测试分析和优化技巧。

## 📚 文档列表

- **[01_optimization_guide.md](./01_optimization_guide.md)** - 性能优化指南  
  全面的性能优化技巧和策略

- **[02_benchmark_analysis.md](./02_benchmark_analysis.md)** - 基准测试分析  
  如何进行异步性能测试和分析

- **[03_benchmark_results.md](./03_benchmark_results.md)** - 基准测试结果  
  实际测试数据和对比分析

## 🎯 性能优化要点

### 1. 减少分配

- 使用对象池
- 重用缓冲区
- 避免不必要的Clone

### 2. 批量处理

- 批量发送请求
- 减少系统调用
- 使用buffered channel

### 3. 并发控制

- 合理配置worker数
- 使用Semaphore限流
- 避免过度spawn

### 4. 零拷贝

- 使用引用而非所有权
- Bytes crate
- 内存映射文件

## 📊 性能指标

关注的关键指标：

- **吞吐量** (Throughput)
- **延迟** (Latency) - P50, P99
- **CPU使用率**
- **内存使用**
- **任务调度开销**

## 🔗 相关资源

- [../guides/04_best_practices.md](../guides/04_best_practices.md)
- [../../benches/](../../benches/) - 性能测试代码

**最后更新**: 2025-10-19
