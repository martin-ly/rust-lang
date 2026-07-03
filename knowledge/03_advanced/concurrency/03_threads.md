# Rust 线程与并发安全模型

> **EN**: Threads
> **Summary**: Rust 线程与并发安全模型 Threads. (stub/archive redirect)
> **权威来源**: 本主题深度解释见 [concept/03_advanced/01_concurrency.md](../../../concept/03_advanced/01_concurrency.md)。
> **历史版本存档**: [archive/knowledge/03_advanced/concurrency/03_threads.md](../../../archive/knowledge/03_advanced/concurrency/03_threads.md)
>
> **定位**: 本文件为精简知识卡片，保留核心规则/概念与常见陷阱。详细解释、形式化语义与代码示例请查看权威来源。

---

## 核心概念

1. `std::thread::spawn` 创建 OS 线程
2. `Send` 允许跨线程转移所有权，`Sync` 允许跨线程共享引用
3. 借用检查器在线程间同样生效，阻止数据竞争
4. `join` 等待线程完成并返回结果

## 关键区分

| trait | 含义 | 示例 |
|---|---|---|
| `Send` | 可安全移到另一线程 | 大多数拥有类型 |
| `Sync` | 可安全被多线程共享引用 | `&T: Send` 当 `T: Sync` |
| `!Send/!Sync` | 标记非线程安全 | `Rc`, `*const T` |

## 常见陷阱

- 在闭包中捕获 `Rc` 发送到线程
- 主线程不 join 导致子线程 panic 未处理
- 误解 `Sync` 与 `Send` 的关系

---

**详细内容已迁移**：请点击上方 [concept/03_advanced/01_concurrency.md](../../../concept/03_advanced/01_concurrency.md) 查看最新权威解释。
