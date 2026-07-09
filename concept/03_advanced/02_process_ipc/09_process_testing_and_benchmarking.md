> **EN**: Process Testing and Benchmarking in Rust
> **Summary**: Testing strategies, process-specific test techniques, benchmarking, stress testing, and CI integration for Rust process management.

# Rust 进程测试与基准

> **权威页地位**：本页为 Rust 进程测试与基准概念的 canonical 解释来源。
>
> 通用 Rust 测试策略请参见 [Rust 测试策略](../../06_ecosystem/09_testing_and_quality/12_testing_strategies.md)。

## 1. 概念定义

**进程测试与基准 (Process Testing and Benchmarking)** 覆盖验证子进程行为、性能与稳定性的方法：从单元测试单个命令执行，到集成测试管道，再到压力测试与 CI 集成。

## 2. 测试分层

| 层级 | 范围 | 典型方法 |
| :--- | :--- | :--- |
| 单元测试 | 单个 `Command` 调用 | `#[test]` 验证退出码/输出 |
| 集成测试 | 进程通信、管道 | `tokio::test` 异步管道 |
| 端到端测试 | 完整工作流 | 启动真实进程并验证结果 |

## 3. 进程测试技巧

### 3.1 超时保护

所有可能阻塞的进程测试都应使用 `tokio::time::timeout` 或自定义超时包装器。

### 3.2 错误注入

通过 mock 进程或随机失败包装器验证系统对启动失败、非零退出码、stderr 的处理。

### 3.3 僵尸进程防护

使用 `ProcessGuard` 在测试失败或 panic 时自动 `kill` + `wait` 子进程。

### 3.4 信号处理测试

Unix 上向子进程发送 SIGTERM/SIGKILL，验证优雅关闭与强制终止行为。

## 4. 基准测试

使用 Criterion 建立可重复的基准：

- **进程创建基准**：比较 `std::process` 与 `tokio::process`。
- **IPC 基准**：测量管道、Unix socket、共享内存的吞吐与延迟。
- **进程池基准**：不同池大小与任务长度下的吞吐量。

## 5. 压力测试

- **并发 spawn 测试**：同时启动大量进程，验证资源限制。
- **稳定性测试**：长时间运行并监控失败率。
- **内存泄漏测试**：通过 `sysinfo` 监控自身内存增长。
- **资源耗尽测试**：逼近文件描述符上限，验证优雅降级。

## 6. CI 集成

- 在 `ubuntu-latest`、`macos-latest`、`windows-latest` 上运行测试矩阵。
- 将压力测试标记为 `#[ignore]`，通过 `cargo test -- --ignored` 单独触发。
- 使用 `cargo bench` 与 Criterion 基线对比检测性能回归。

## 7. 相关概念

- [进程模型与生命周期](01_process_model_and_lifecycle.md)
- [高级进程管理](02_advanced_process_management.md)
- [异步进程管理](03_async_process_management.md)
- [Rust 测试策略](../../06_ecosystem/09_testing_and_quality/12_testing_strategies.md)
- [基准测试](../../06_ecosystem/09_testing_and_quality/17_benchmarking.md)

---

> **权威来源**: [The Rust Programming Language — Testing](https://doc.rust-lang.org/book/ch11-00-testing.html) · [Criterion.rs](https://bheisler.github.io/criterion.rs/book/) · [Rust By Example — Process](https://doc.rust-lang.org/rust-by-example/std_misc/process.html)
