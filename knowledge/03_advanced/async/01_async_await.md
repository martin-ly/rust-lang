# async/await 异步编程

> **EN**: Async Await
> **Summary**: async/await 异步编程 Async Await. (stub/archive redirect)
> **权威来源**: 本主题深度解释见 [concept/03_advanced/02_async.md](../../../concept/03_advanced/02_async.md)。
> **历史版本存档**: [archive/knowledge/03_advanced/async/01_async_await.md](../../../archive/knowledge/03_advanced/async/01_async_await.md)
>
> **定位**: 本文件为精简知识卡片，保留核心规则/概念与常见陷阱。详细解释、形式化语义与代码示例请查看权威来源。

---

## 核心概念

1. `async fn` 返回实现 `Future` 的状态机
2. `.await` 将控制权交还运行时，非阻塞当前线程
3. 异步任务需要运行时（Tokio/async-std/smol）调度
4. `Pin` 保证自引用类型的内存稳定

## 关键区分

| 模型 | 阻塞 | 资源占用 | 适用 |
|---|---|---|---|
| async/await | 任务级非阻塞 | 少量栈 | 高并发 IO |
| OS 线程 | 线程阻塞 | 较大栈 | CPU 密集型 |

## 常见陷阱

- 在 async 中使用阻塞 IO 拖慢整个运行时
- 跨越 `.await` 持有非 `Send` 数据导致编译错误
- 忽略取消安全导致任务取消时状态异常

---

**详细内容已迁移**：请点击上方 [concept/03_advanced/02_async.md](../../../concept/03_advanced/02_async.md) 查看最新权威解释。
