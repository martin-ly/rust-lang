# 并发安全验证(Concurrency Safety Verification)


## 📊 目录

- [1. 目标](#1-目标)
- [2. 模型](#2-模型)
- [3. Rust模式](#3-rust模式)
- [4. 定理](#4-定理)
- [5. 基本证明思路](#5-基本证明思路)
- [6. 工具化](#6-工具化)
- [最小可验证示例(MVE)](#最小可验证示例mve)
  - [MVE-2: 原子计数器与内存序](#mve-2-原子计数器与内存序)
  - [MVE-3: 通道同步建立 hb 边](#mve-3-通道同步建立-hb-边)
  - [MVE-4: Loom 检验锁顺序与互斥（示意）](#mve-4-loom-检验锁顺序与互斥示意)
  - [设计约束与反例提示](#设计约束与反例提示)
- [证明义务(Proof Obligations)](#证明义务proof-obligations)


- 文档版本: 1.0  
- 创建日期: 2025-01-27  
- 状态: 已完成

## 1. 目标

- 无数据竞争、无死锁、顺序一致性或更强内存模型下的正确性。

## 2. 模型

```math
(\mathcal{T},\ \mathcal{S},\ \rightarrow_{hb}) \quad \text{happens-before 边与原子操作序}
```

细化：

- 线程集 \(\mathcal{T}\) 与共享状态 \(\mathcal{S}\)，以事件集 E 与顺序关系定义：
  - 程序内顺序 po，原子读写同步关系 sw（如 `store(Release)` → `load(Acquire)`），
  - 锁/解锁边 ls（`lock` → 临界区 → `unlock`），
  - 形成 hb = (po ∪ sw ∪ ls)^+（传递闭包）。
- 安全性：不存在数据竞争，即对同一位置的两个冲突访问（至少一个写）不在 hb 上有确定顺序时，必须经同步原语建立 hb 或互斥保护。
- 活性（条件）：在公平调度与有限临界区的假设下不存在永久阻塞（无死锁）。

## 3. Rust模式

- `Send/Sync` 自动定理检查(编译期)
- 原子与锁: `Atomic*`, `Mutex`, `RwLock`, `Barrier`
- 通道与任务: `std::sync::mpsc`, `crossbeam`, `tokio::sync`（单向通信构造 hb 边）
- 内存序：`Relaxed`, `Acquire`, `Release`, `AcqRel`, `SeqCst`（选择成本/保证的权衡）

## 4. 定理

- Race Freedom: `!Sync` 非共享; 共享经 `Sync` 保证安全访问。
- Deadlock Freedom(条件): 拓扑排序的锁顺序策略。
- Atomic Order Soundness: 对给定内存序，推导的 hb 边保证可见性与单调性；`SeqCst` 提供全序栅栏语义。

## 5. 基本证明思路

- 基于hb图的循环消除与临界区互斥证明。
- 将通道发送/接收建模为 sw 同步对（send → recv）。
- 以锁顺序图 L 的无环性证明无环等待（死锁避免）。

## 6. 工具化

- Loom模型检验、小规模并发单元测试搜索
- Miri 检查未定义行为；`cargo tarpaulin` 度量并发路径覆盖；`tokio::test` 驱动异步场景。
- 竞争检测（平台相关）：TSan/Valgrind（配合 FFI 与原子回退检查）。

## 最小可验证示例(MVE)

```rust
use std::sync::{Arc, Mutex};
use std::thread;

#[test]
fn arc_mutex_increments() {
    let v = Arc::new(Mutex::new(0));
    let mut handles = Vec::new();
    for _ in 0..4 {
        let v = v.clone();
        handles.push(thread::spawn(move || {
            let mut g = v.lock().unwrap();
            *g += 1;
        }));
    }
    for h in handles { h.join().unwrap(); }
    assert_eq!(*v.lock().unwrap(), 4);
}
```

### MVE-2: 原子计数器与内存序

```rust
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread;

#[test]
fn atomic_counter_seqcst() {
    let n = 8;
    let iters = 10_000;
    let c = Arc::new(AtomicUsize::new(0));
    let mut hs = Vec::new();
    for _ in 0..n {
        let c2 = c.clone();
        hs.push(thread::spawn(move || {
            for _ in 0..iters { c2.fetch_add(1, Ordering::SeqCst); }
        }));
    }
    for h in hs { h.join().unwrap(); }
    assert_eq!(c.load(Ordering::SeqCst), n * iters);
}
```

说明：`SeqCst` 提供全序，避免不同线程观察到非单调增长；若用 `Relaxed`，总和仍正确（因使用 fetch_add 原子 RMW），但跨线程的可见顺序不具全序保证。

### MVE-3: 通道同步建立 hb 边

```rust
use std::sync::mpsc;
use std::thread;

#[test]
fn channel_happens_before() {
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        // 工作前置
        tx.send(42).unwrap();
    });
    // recv 对 send 建立同步（Acquire←Release）
    let v = rx.recv().unwrap();
    assert_eq!(v, 42);
}
```

### MVE-4: Loom 检验锁顺序与互斥（示意）

```rust
// 需要在 dev-dependencies 引入 loom = "*"
#[cfg(all(test, feature = "loom"))]
mod loom_tests {
    use loom::sync::{Arc, Mutex};
    use loom::thread;

    #[test]
    fn loom_mutex_exclusion() {
        loom::model(|| {
            let v = Arc::new(Mutex::new(0));
            let v1 = v.clone();
            let v2 = v.clone();
            let t1 = thread::spawn(move || { *v1.lock().unwrap() += 1; });
            let t2 = thread::spawn(move || { *v2.lock().unwrap() += 1; });
            t1.join().unwrap();
            t2.join().unwrap();
            assert!(*v.lock().unwrap() == 2);
        });
    }
}
```

### 设计约束与反例提示

- 锁顺序不变式：对多把锁 L1, L2,… 规定全序 `L1 < L2 < ...`，任何临界区的加锁序必须单调不降，避免循环等待。
- `RwLock` 升级反模式：避免在持有读锁时尝试获取写锁；使用单写路径或“读→释放→写”的转换。
- 原子对齐与共享可变：严禁将 `&mut T` 分裂到多线程；跨线程共享需 `Arc<...>` + 同步原语。

## 证明义务(Proof Obligations)

- C1: 互斥锁在任意时刻仅允许一个持有者(互斥)
- C2: `Arc<T>` 保证共享所有权但不破坏 `Send/Sync` 边界
- C3: 无环等待(通过固定加锁顺序或单锁模型)
- C4: 原子操作的内存序为指定的可见性提供足够的 hb 边（例如 `Release→Acquire` 传递）
- C5: 通道 send/recv 在模型中形成同步对，接收后读取到发送前建立的先行效果
- C6: 异步执行器下任务取消与 Join 的资源释放有界且无悬垂引用
- C7: `RwLock` 下读读并行与写独占不变式保持
- C8: Loom 完整探索的状态空间中不存在断言失败与死锁
