# Rust 同步原语深度解析

> **权威来源**: 本主题深度解释见 [concept/03_advanced/01_concurrency.md](../../../concept/03_advanced/01_concurrency.md)。
> **历史版本存档**: [archive/knowledge/03_advanced/concurrency/02_synchronization.md](../../../archive/knowledge/03_advanced/concurrency/02_synchronization.md)
>
> **定位**: 本文件为精简知识卡片，保留核心规则/概念与常见陷阱。详细解释、形式化语义与代码示例请查看权威来源。

---

## 核心概念

1. `Mutex` 提供互斥访问，`RwLock` 区分读写
2. `Condvar` 条件变量用于等待/通知
3. `Barrier` 让一组线程同步到同一点
4. 消息传递（mpsc）可避免共享状态

## 关键区分

| 原语 | 并发模型 | 适用场景 |
|---|---|---|
| `Mutex` | 共享状态 + 互斥 | 频繁写 |
| `RwLock` | 共享状态 + 读写分离 | 多读少写 |
| `mpsc` | 消息传递 | 任务流水线 |

## 常见陷阱

- 在 async 代码中持有阻塞锁跨越 await
- 死锁：嵌套锁加锁顺序不一致
- 忽略 `MutexGuard` 的 poisoning

---

**详细内容已迁移**：请点击上方 [concept/03_advanced/01_concurrency.md](../../../concept/03_advanced/01_concurrency.md) 查看最新权威解释。
