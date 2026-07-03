# Rust 原子操作 (Atomic Operations)

> **EN**: Atomic Operations
> **Summary**: Rust 原子操作 Atomic Operations. (stub/archive redirect)
> **权威来源**: 本主题深度解释见 [concept/03_advanced/11_atomics_and_memory_ordering.md](../../../concept/03_advanced/11_atomics_and_memory_ordering.md)。
> **历史版本存档**: [archive/knowledge/03_advanced/concurrency/01_atomics.md](../../../archive/knowledge/03_advanced/concurrency/01_atomics.md)
>
> **定位**: 本文件为精简知识卡片，保留核心规则/概念与常见陷阱。详细解释、形式化语义与代码示例请查看权威来源。

---

## 核心概念

1. `Atomic*` 类型提供无锁原子读写
2. 内存顺序 Relaxed/Acquire/Release/AcqRel/SeqCst 控制可见性
3. CAS 循环是实现无锁算法的基础
4. 原子类型实现 `Send + Sync`，但不一定 `Copy`

## 关键区分

| 内存序 | 同步强度 | 典型用法 |
|---|---|---|
| Relaxed | 无顺序 | 计数器 |
| Acquire | 保证看到释放前写入 | 读标志 |
| Release | 保证之前写入对获取可见 | 写标志 |
| SeqCst | 全局顺序 | 多变量同步 |

## 常见陷阱

- 使用 Relaxed 实现需要 happens-before 的同步
- CAS 循环未处理 ABA 问题
- 原子与互斥锁混用导致逻辑错误

---

**详细内容已迁移**：请点击上方 [concept/03_advanced/11_atomics_and_memory_ordering.md](../../../concept/03_advanced/11_atomics_and_memory_ordering.md) 查看最新权威解释。
