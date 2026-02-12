# 并发执行模型形式化

> **创建日期**: 2026-02-12
> **分类**: 执行模型
> **安全边界**: 纯 Safe

---

## 形式化定义

**Def 1.1（并发执行）**

并发执行满足：

- 多线程、多任务可交错
- 执行序列非确定：$e_1 \parallel e_2$ 表示 $e_1$ 与 $e_2$ 可交错执行
- 无数据竞争：由类型系统保证（Send/Sync）

**Def 1.2（Send）**

$T : \mathrm{Send}$ 当且仅当 $T$ 可安全跨线程边界转移所有权。形式化：若 $v : T$ 在线程 $t_1$ 中，转移至 $t_2$ 后 $t_1$ 不再访问，且 $t_2$ 可安全使用。

**Def 1.3（Sync）**

$T : \mathrm{Sync}$ 当且仅当 $\&T$ 可安全跨线程共享。形式化：多线程同时持有 $\&T$ 时无数据竞争。

**Axiom CO1**：非 Send 类型不可跨线程传递；违反则编译错误。

**Axiom CO2**：非 Sync 类型不可多线程共享；违反则编译错误。

**定理 CO-T1**：由 [borrow_checker_proof](../../formal_methods/borrow_checker_proof.md) 数据竞争自由；Send/Sync 为结构性质，组合保持。

**定理 CO-T2**：由 [async_state_machine](../../formal_methods/async_state_machine.md) 定理 6.2，Send + Sync 保证并发安全。

---

## Rust 并发原语

| 原语 | 用途 | 所有权/借用 |
|------|------|-------------|
| `std::thread::spawn` | 创建线程 | 闭包需 `Send`，捕获值转移 |
| `mpsc::channel` | 消息传递 | `Sender`/`Receiver` 分离，无共享 |
| `Mutex<T>` | 互斥共享 | 持有所有权，`lock()` 返回 `MutexGuard` |
| `RwLock<T>` | 读写锁 | 多读或单写 |
| `Arc<T>` | 跨线程共享 | 引用计数，$T$ 需 `Send` |

---

## 代码示例

### 消息传递

```rust
use std::thread;
use std::sync::mpsc;

let (tx, rx) = mpsc::channel();
thread::spawn(move || {
    tx.send(42).unwrap();
});

assert_eq!(rx.recv().unwrap(), 42);
```

### 共享状态

```rust
use std::sync::{Arc, Mutex};
use std::thread;

let data = Arc::new(Mutex::new(0));
let mut handles = vec![];

for _ in 0..10 {
    let data = Arc::clone(&data);
    let h = thread::spawn(move || {
        let mut g = data.lock().unwrap();
        *g += 1;
    });
    handles.push(h);
}

for h in handles {
    h.join().unwrap();
}
assert_eq!(*data.lock().unwrap(), 10);
```

**形式化对应**：`Arc<Mutex<T>>` 中 `T` 需 `Send`；`MutexGuard` 为 RAII，释放锁时 drop。符合所有权与借用规则。

---

## 典型场景

| 场景 | 说明 |
|------|------|
| 生产者-消费者 | `mpsc` 通道、任务队列 |
| 共享缓存 | `Arc<RwLock<HashMap>>` |
| 后台任务 | `spawn` 执行耗时操作 |
| 多路 I/O | `select!`、`join!` |

---

## 原子操作与内存顺序

**Def 1.4（原子类型）**

`AtomicUsize`、`AtomicBool` 等提供无锁并发。内存顺序（Ordering）控制可见性：

| Ordering | 说明 |
|----------|------|
| `SeqCst` | 顺序一致，最强保证 |
| `Acquire` | 读屏障，后续操作不可重排到之前 |
| `Release` | 写屏障，之前操作不可重排到之后 |
| `Relaxed` | 无同步保证 |

**定理 CO-T3**：`Acquire`-`Release` 配对建立 happens-before 关系；保证无数据竞争。

---

## 死锁与避免

**反例**：锁顺序不一致导致死锁。

```rust
// 错误：线程1 获取 A 再 B，线程2 获取 B 再 A
// 解决：全局锁顺序（如按地址排序）
```

**实践**：缩小锁范围、使用 `try_lock`、`Condvar` 等待条件、或优先 channel 传递所有权。

---

## 通道与共享状态选型

| 需求 | 选型 | 说明 |
|------|------|------|
| 多生产者单消费者 | `mpsc::channel` | 无共享 |
| 多生产者多消费者 | `sync_channel` 或 `broadcast` | 有界/无界 |
| 共享可变 | `Mutex` / `RwLock` | 锁保护 |
| 简单计数 | `AtomicUsize` | 无锁 |
| 跨 async 边界 | `tokio::sync::mpsc` | 异步 channel |

---

## 典型反例

| 反例 | 后果 |
|------|------|
| `Rc` 跨线程 | 编译错误（非 Send） |
| `RefCell` 跨线程共享 | 编译错误（非 Sync） |
| 锁内持锁 | 死锁 |
| 忘记 join | 主线程退出时子线程被强制终止 |

---

## 边界

| 维度 | 分类 |
|------|------|
| 安全 | 纯 Safe |
| 支持 | 原生 |
| 表达 | 等价 |
