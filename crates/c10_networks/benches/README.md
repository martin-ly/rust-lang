# C10 Networks 基准测试

本目录包含了 C10 Networks 库的全面性能基准测试套件。

## 基准测试文件

### 1. 并发性能测试 (`concurrency_performance.rs`)

测试多线程环境下的错误处理和并发操作性能：

- 错误创建性能
- 错误恢复机制性能
- 错误统计性能
- 错误传播性能
- 错误处理链性能
- 错误日志记录性能
- 错误序列化性能
- 错误处理性能
- 并发错误处理性能

### 2. 错误处理性能测试 (`error_handling_performance.rs`)

专注于错误处理机制的性能测试：

- 错误类型创建性能
- 错误恢复策略性能
- 错误统计收集性能
- 错误传播开销
- 错误处理链性能
- 错误格式化性能
- 完整错误处理流程性能
- 并发错误处理性能

### 3. 内存性能测试 (`memory_performance.rs`)

测试内存管理相关性能：

- 内存分配性能
- 内存池性能
- 缓存性能
- 数据包内存性能
- 大数据块处理性能
- 内存碎片化性能
- 并发内存分配性能
- 内存使用模式性能
- 内存泄漏检测性能

### 4. 协议性能测试 (`protocol_performance.rs`)

测试各种网络协议的性能：

- HTTP 协议性能
- WebSocket 协议性能
- TCP 协议性能
- 套接字配置性能
- 协议解析性能
- 协议序列化性能
- 协议兼容性性能
- 协议错误处理性能

## 运行基准测试

### 运行所有基准测试

```bash
cargo bench
```

### 运行特定基准测试

```bash
# 并发性能测试
cargo bench --bench concurrency_performance

# 错误处理性能测试
cargo bench --bench error_handling_performance

# 内存性能测试
cargo bench --bench memory_performance

# 协议性能测试
cargo bench --bench protocol_performance
```

### 运行特定测试组

```bash
# 只运行错误创建测试
cargo bench --bench concurrency_performance error_creation

# 只运行内存池测试
cargo bench --bench memory_performance memory_pool
```

## 基准测试结果

基准测试结果会保存在 `target/criterion/` 目录下，包含：

- 详细的性能报告
- 可视化图表
- 历史性能对比

## 性能指标

### 主要性能指标

- **延迟 (Latency)**: 操作完成时间
- **吞吐量 (Throughput)**: 每秒操作数
- **内存使用**: 内存分配和释放性能
- **CPU 使用**: CPU 利用率
- **并发性能**: 多线程环境下的性能表现

### 性能基准

- 错误创建: < 1ns
- 错误恢复: < 10ns
- 内存分配: < 100ns
- 协议解析: < 1μs
- 缓存操作: < 1μs

## 基准测试最佳实践

### 1. 测试环境

- 使用稳定的硬件环境
- 关闭不必要的后台程序
- 确保系统处于空闲状态

### 2. 测试数据

- 使用真实的数据大小和模式
- 测试不同负载下的性能
- 包含边界条件测试

### 3. 结果分析

- 关注性能趋势变化
- 识别性能瓶颈
- 优化关键路径

## 持续集成

基准测试已集成到 CI/CD 流程中：

- 每次提交都会运行基准测试
- 性能回归检测
- 自动生成性能报告

## 贡献指南

### 添加新的基准测试

1. 在相应的基准测试文件中添加新的测试函数
2. 使用 `criterion_group!` 宏注册测试
3. 确保测试覆盖不同的场景和边界条件
4. 添加适当的文档和注释

### 基准测试命名规范

- 使用描述性的函数名
- 包含测试的具体场景
- 遵循 `bench_` 前缀

### 性能优化建议

- 使用 `black_box` 防止编译器优化
- 避免在基准测试中使用 `println!`
- 确保测试的可重复性
- 使用适当的样本大小

## 故障排除

### 常见问题

1. **编译错误**: 检查依赖项和导入
2. **性能异常**: 检查测试环境
3. **内存泄漏**: 使用内存分析工具
4. **结果不稳定**: 增加测试样本数量

### 调试技巧

- 使用 `cargo bench -- --nocapture` 查看输出
- 使用 `cargo bench -- --help` 查看选项
- 检查 `target/criterion/` 目录下的详细报告

## 相关文档

- [Criterion 基准测试框架文档](https://docs.rs/criterion/)
- [Rust 性能优化指南](https://doc.rust-lang.org/book/ch13-00-functional-features.html)
- [C10 Networks 性能优化指南](../docs/PERFORMANCE_OPTIMIZATION_GUIDE.md)
