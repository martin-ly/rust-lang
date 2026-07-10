# 线程基础与生命周期

> **EN**: Thread Basics and Lifetimes
> **Summary**: Creating OS threads in Rust, move closures, JoinHandle, scoped threads, thread configuration, panic handling, and best practices. Migrated to the concurrency authority.
>
> **适用 Rust 版本**: 1.97.0+
> **文档类型**: 重定向 stub

---

> **权威来源**: [concept/03_advanced/00_concurrency/01_concurrency.md](../../../../concept/03_advanced/00_concurrency/01_concurrency.md)

---

## 主题列表

- `std::thread::spawn` 与 1:1 线程模型
- `move` 闭包与所有权转移
- `JoinHandle` 与 `join` 语义
- 作用域线程（scoped threads）
- 线程 Builder 配置（栈大小、名称）
- 线程 panic 处理与 `catch_unwind`
- 线程池与 `available_parallelism`
- 缓存行填充与伪共享
