# C05 线程与并发 - 一页纸总结

> **用途**: 快速回顾核心概念、常见坑、学习路径
> **完整文档**: [00_MASTER_INDEX](./00_MASTER_INDEX.md)

---

## 核心概念（4 条）

| 概念 | 说明 |
| :--- | :--- || **线程创建** | `thread::spawn`；`JoinHandle`；`move` 闭包转移所有权 |
| **Send 与 Sync** | `Send` 可跨线程转移；`Sync` 可多线程共享引用 |
| **同步原语** | `Mutex`、`RwLock`、`Condvar`；`Arc` 共享所有权 |
| **原子操作** | `AtomicUsize`、`Ordering`；无锁并发 |

---

## 常见坑与解决

| 坑 | 解决 |
| :--- | :--- || 数据竞争 | 用 `Mutex`/`RwLock` 保护；确保 `Sync` |
| 死锁 | 避免嵌套加锁；统一加锁顺序；缩短持锁时间 |
| 假共享（False Sharing） | 缓存行对齐；`#[repr(align(64))]`；参考 [ALIGNMENT_GUIDE](../../../docs/02_reference/ALIGNMENT_GUIDE.md) |
| `Rc` 跨线程 | 改用 `Arc`；`Rc` 非 `Send` |

---

## 并发速选

| 场景 | 选型 |
| :--- | :--- || 共享可变状态 | `Arc<Mutex<T>>` 或 `Arc<RwLock<T>>` |
| 消息传递 | `mpsc::channel`；`crossbeam` |
| 无锁计数/标志 | `AtomicUsize`、`AtomicBool` |
| 多生产者 | `crossbeam` 或 `flume` |

---

## 学习路径

1. **入门** (1–2 周): 线程创建 → `Send`/`Sync` → `Mutex`/`Arc`
2. **进阶** (2–3 周): 原子操作 → 通道 → 无锁结构
3. **高级** (持续): 性能调优、假共享、与 C06 异步对比

---

## 速查与练习

- **速查卡**: [threads_concurrency_cheatsheet](../../../docs/02_reference/quick_reference/threads_concurrency_cheatsheet.md)
- **RBE 练习**: [Threads](https://doc.rust-lang.org/rust-by-example/std_misc/threads.html)
- **Rustlings**: [20_threads](https://github.com/rust-lang/rustlings/tree/main/exercises/20_threads)
