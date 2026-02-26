# 并发速查卡

> **一页纸速查** - 并发原语、Send/Sync、异步

---

## Send与Sync

```text
Send: 可跨线程转移所有权
Sync: 可安全跨线程共享(&T: Send)

T: Send + Sync      T: Send + !Sync    !Send + !Sync
├── i32             ├── Cell<T>        ├── Rc<T>
├── String          ├── RefCell<T>     └── *const T
├── Vec<T>          └── mpsc::Sender
└── Arc<T>(T:Sync)
```

---

## 同步原语

| 原语 | 用途 | 场景 |
| :--- | :--- | :--- |
| `Mutex<T>` | 互斥访问 | 通用 |
| `RwLock<T>` | 多读单写 | 读多写少 |
| `AtomicUsize` | 原子计数 | 高性能计数 |
| `mpsc::channel` | 消息传递 | 线程通信 |
| `Barrier` | 等待所有线程 | 并行计算 |

---

## 线程操作

```rust
// 创建
let handle = thread::spawn(|| { ... });

// 等待
handle.join().unwrap();

// 线程池
use rayon::prelude::*;
vec.par_iter().map(|x| x * 2).collect();
```

---

## 异步基础

```rust
// async函数
async fn foo() -> i32 { 42 }

// .await
let result = foo().await;

// spawn
tokio::spawn(async { ... });

// select
select! {
    _ = task1 => println!("1"),
    _ = task2 => println!("2"),
}
```

---

## 常见错误

```rust
// ❌ Rc跨线程
let rc = Rc::new(5);
// thread::spawn(move || *rc); // 错误！

// ✅ Arc跨线程
let arc = Arc::new(5);
thread::spawn(move || *arc); // OK
```

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-24
**状态**: ✅ 已完成 - 并发速查卡 (3/5)
