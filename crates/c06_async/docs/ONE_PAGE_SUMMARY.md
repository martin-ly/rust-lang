# C06 异步编程 - 一页纸总结

> **用途**: 快速回顾核心概念、常见坑、学习路径
> **完整文档**: [00_MASTER_INDEX](./00_MASTER_INDEX.md)

---

## 核心概念（4 条）

| 概念 | 说明 |
| :--- | :--- || **async/await** | `async fn` 返回 `Future`；`.await` 挂起与恢复 |
| **Future** | 惰性执行；需 executor 轮询；`Pin` 自引用 |
| **运行时** | Tokio、async-std；`#[tokio::main]`；任务调度 |
| **并发模型** | 多任务单线程（协作式）；与 OS 线程互补 |

---

## 常见坑与解决

| 坑 | 解决 |
| :--- | :--- || 持锁跨 `await` | 缩短锁作用域；用 `tokio::sync::Mutex` |
| 空 Future 不执行 | 必须 `.await` 或 `spawn` 才会执行 |
| `!Send` 跨 await 点 | 确保 `Future: Send`；避免 `Rc`/`RefCell` 跨 await |
| 阻塞运行时 | 用 `spawn_blocking` 或 `tokio::task::block_in_place` |

---

## 异步速选

| 场景 | 选型 |
| :--- | :--- || 异步运行时 | Tokio（主流）或 async-std |
| 异步锁 | `tokio::sync::Mutex` |
| 异步通道 | `tokio::sync::mpsc` |
| 超时/取消 | `tokio::time::timeout`；`CancellationToken` |

---

## 学习路径

1. **入门** (1–2 周): async/await 语法 → Future 基础 → Tokio 入门
2. **进阶** (2–4 周): 运行时原理 → Pin/Unpin → 自引用
3. **高级** (持续): 自定义运行时、与 C05 对比选型

---

## 速查与练习

- **速查卡**: [async_patterns](../../../docs/02_reference/quick_reference/async_patterns.md)
- **RBE 练习**: [Async](https://doc.rust-lang.org/rust-by-example/async.html)
- **Rustlings**: 无异步专题；参考 RBE 与 C06 模块
