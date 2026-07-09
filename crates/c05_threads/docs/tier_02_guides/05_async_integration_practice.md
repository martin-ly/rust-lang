# 异步集成实践

> **EN**: Async Integration Practice
> **Summary**: Combining threads and async runtimes: spawn_blocking bridges, mixed CPU/IO architectures, Tokio thread pool configuration, and channel interoperability. Migrated to the async patterns authority.
>
> **适用 Rust 版本**: 1.96.1+
> **文档类型**: 重定向 stub

---

> **权威来源**: [concept/03_advanced/01_async/26_async_patterns.md](../../../../concept/03_advanced/01_async/26_async_patterns.md)

---

## 主题列表

- 线程 vs 异步：性能、内存、适用场景
- `tokio::task::spawn_blocking` 桥接阻塞任务
- Tokio 运行时配置与工作线程池
- `Handle` 跨线程提交异步任务
- oneshot / mpsc / watch 通道互操作
- 混合架构设计（Web 服务器 + CPU 密集型任务）
- 取消任务与错误处理
