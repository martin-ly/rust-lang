# 同步原语实践

> **EN**: Synchronization Primitives Practice
> **Summary**: Practical usage of Mutex, RwLock, Condvar, Barrier, Once, and OnceLock for coordinating shared state in concurrent Rust. Migrated to the concurrency authority.
>
> **适用 Rust 版本**: 1.96.1+
> **文档类型**: 重定向 stub

---

> **权威来源**: [concept/03_advanced/00_concurrency/01_concurrency.md](../../../../concept/03_advanced/00_concurrency/01_concurrency.md)

---

## 主题列表

- `Mutex<T>` 基础用法与锁中毒（poisoning）
- `RwLock<T>` 读写分离与读多写少优化
- `Condvar` 条件变量与生产者-消费者模式
- `Barrier` 屏障同步点
- `Once` / `OnceLock<T>` 一次性初始化
- `try_lock` / `try_read` / `try_write` 非阻塞尝试
- 死锁避免与最小化锁持有时间
- `parking_lot` 等替代实现简介
