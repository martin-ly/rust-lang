# 跨平台并发

> **EN**: Cross-Platform Concurrency
> **Summary**: Platform-specific threading models, synchronization primitives, and conditional-compilation strategies for portable concurrent Rust across Windows, Linux, macOS, and mobile targets.
>
> **适用 Rust 版本**: 1.97.0+
> **文档类型**: 重定向 stub

---

> **权威来源**: [concept/03_advanced/00_concurrency/05_cross_platform_concurrency.md](../../../../concept/03_advanced/00_concurrency/05_cross_platform_concurrency.md)

---

## 主题列表

- Windows / Linux / macOS 线程模型差异
- 平台同步原语实现（SRWLock、pthread_mutex、futex）
- Windows IOCP、Linux epoll/io_uring、macOS GCD
- `#[cfg(target_os = "...")]` 条件编译策略
- 平台抽象层与统一接口设计
- Android / iOS 后台执行限制
- 跨平台线程池最佳实践
