> **内容分级**: [专家级]

# 并发 模式：从消息 传递到锁自由的数据结构
>
> **EN**: Concurrency
> **Summary**: Concurrency. Core Rust concept covering mental model building, mechanism analysis, in-depth analysis.
> **受众**: [专家]
>
> **Bloom 层级**: 分析 → 评价
> **A/S/P 标记**: **S+P** — Structure + Procedure
> **双维定位**: C×Ana — 分析并发模式的设计意图
> **定位**: 深入分析 Rust **并发编程的高级模式**——从 Actor 模型、通道模式到无锁数据结构和内存序，揭示 Rust 所有权系统如何为并发安全提供编译期保证。
> **前置概念**: [Concurrency](./01_concurrency.md) · [Async](./02_async.md) · [Type System](../01_foundation/04_type_system.md)
> **后置概念**: [Distributed Systems](../06_ecosystem/18_distributed_systems.md) · [Lockfree](../03_advanced/01_concurrency.md)

---

> **来源**: [The Rust Programming Language — Concurrency](https://doc.rust-lang.org/book/ch16-00-concurrency.html) ·
> [Rust Atomics and Locks](https://marabos.nl/atomics/) ·
> [crossbeam crate](https://docs.rs/crossbeam/latest/crossbeam/) ·
> [tokio::sync](https://docs.rs/tokio/latest/tokio/sync/index.html) ·
> [Wikipedia — Non-blocking Algorithm](https://en.wikipedia.org/wiki/Non-blocking_algorithm)

> **对应 Crate**: [`c05_threads`](../../crates/c05_threads/)
> **对应练习**: [`exercises/src/concurrency/`](../../exercises/src/concurrency/)

## 📑 目录

- [并发 模式：从消息 传递到锁自由的数据结构](#并发-模式从消息-传递到锁自由的数据结构)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
    - [1.1 所有权与并发的统一](#11-所有权与并发的统一)
    - [1.2 Send 与 Sync：编译期并发安全](#12-send-与-sync编译期并发安全)
    - [1.3 共享状态 vs 消息传递](#13-共享状态-vs-消息传递)
  - [二、技术细节](#二技术细节)
    - [2.1 通道模式](#21-通道模式)
    - [2.2 无锁数据结构](#22-无锁数据结构)
    - [2.3 内存顺序](#23-内存顺序)
  - [三、并发模式矩阵](#三并发模式矩阵)
  - [四、反命题与边界分析](#四反命题与边界分析)
    - [4.1 反命题树](#41-反命题树)
    - [4.2 边界极限](#42-边界极限)
  - [五、常见陷阱](#五常见陷阱)
    - [编译错误示例](#编译错误示例)
    - [4.4 边界测试：`ScopedThread` 中引用逃逸（编译错误）](#44-边界测试scopedthread-中引用逃逸编译错误)
    - [4.5 边界测试：`Condvar` 虚假唤醒未处理（逻辑错误）](#45-边界测试condvar-虚假唤醒未处理逻辑错误)
  - [六、来源与延伸阅读](#六来源与延伸阅读)
  - [相关概念文件](#相关概念文件)
  - [逆向推理链（Backward Reasoning）](#逆向推理链backward-reasoning)
  - [权威来源索引](#权威来源索引)
    - [10.3 边界测试：`crossbeam::channel` 的关闭检测与迭代终止（逻辑错误）](#103-边界测试crossbeamchannel-的关闭检测与迭代终止逻辑错误)
    - [10.4 边界测试：Send/Sync 的 auto trait 边界与线程安全（编译错误）](#104-边界测试sendsync-的-auto-trait-边界与线程安全编译错误)
  - [参考来源](#参考来源)
  - [认知路径](#认知路径)
    - [核心推理链](#核心推理链)
    - [反命题与边界](#反命题与边界)
  - [实践](#实践)
    - [对应代码示例](#对应代码示例)
    - [建议练习](#建议练习)
  - [导航：下一步去哪？](#导航下一步去哪)
  - [嵌入式测验](#嵌入式测验)
    - [测验 1：并发模式识别（记忆层）](#测验-1并发模式识别记忆层)
    - [测验 2：Arc 引用计数（理解层）](#测验-2arc-引用计数理解层)
    - [测验 3：工作窃取模式（应用层）](#测验-3工作窃取模式应用层)
    - [测验 4：死锁预防（分析层）](#测验-4死锁预防分析层)

---

## 一、核心概念
>
>

### 1.1 所有权与并发的统一
>

```text
Rust 并发的核心洞察:

  所有权 → 并发安全:
  ├── 一个值只有一个所有者
  ├── 所有者移动到新线程 [来源: [std::thread](https://doc.rust-lang.org/std/thread/index.html)] → 值跟随移动
  ├── 无数据竞争（编译期保证）
  └── 无需 GC 或运行时检查

  借用 → 共享读取:
  ├── 多个不可变引用同时存在
  ├── 不可变引用可以跨线程共享
  ├── 读-读不冲突
  └── 编译期验证无写冲突

  可变借用 → 独占写入:
  ├── 一个可变引用独占访问
  ├── Mutex [来源: [std::sync::Mutex](https://doc.rust-lang.org/std/sync/struct.Mutex.html)] 包装可变引用
  ├── 运行时在锁保护下提供独占性
  └── 编译期验证正确传递

  统一模型:
  ┌─────────────────────────────────────────┐
  │  所有权规则（单线程）                    │
  │  ├─ 一个所有者                           │
  │  ├─ 多个不可变借用                       │
  │  └─ 一个可变借用（独占）                 │
  ├─────────────────────────────────────────┤
  │  并发扩展                                │
  │  ├─ 所有者跨线程移动（Send）            │
  │  ├─ 不可变借用跨线程共享（Sync）        │
  │  └─ 可变借用通过 Mutex/Arc [来源: [std::sync::Arc](https://doc.rust-lang.org/std/sync/struct.Arc.html)]Mutex 保护    │
  └─────────────────────────────────────────┘
```

> **认知功能**: Rust 的**并发安全不是独立的系统**——它是**所有权规则的自然延伸**。
> [来源: [TRPL — Concurrency](https://doc.rust-lang.org/book/ch16-00-concurrency.html)]

---

### 1.2 Send 与 Sync：编译期并发安全
>

```rust,ignore
// Send: 可以跨线程转移所有权
pub unsafe auto trait Send { }

// Sync: 可以跨线程共享引用 (&T is Send)
pub unsafe auto trait Sync { }

// 自动推导规则:
// ├── 原始类型: Send + Sync
// ├── 包含 Send 的类型: Send
// ├── 包含 Sync 的类型: Sync
// ├── 原始指针 (*const T, *mut T): !Send + !Sync
// ├── Rc<T>: !Send + !Sync（非原子引用计数）
// ├── Cell<T>: Send + !Sync（内部可变）
// └── RefCell<T>: !Send（运行时借用检查非线程安全）

// 手动实现（需要 unsafe）:
struct MyType(*mut c_void);

unsafe impl Send for MyType {}  // 我保证可以安全跨线程移动
unsafe impl Sync for MyType {}  // 我保证可以安全跨线程共享

// 使用场景:
// ├── Send: 将数据 move 到新线程
// ├── Sync: 多个线程同时读取共享数据
// └── 两者: Arc<Mutex<T>> 同时满足

// 编译期检查:
fn spawn_thread<T: Send + 'static>(data: T) {
    std::thread::spawn(move || {
        // data 在这里安全可用
    });
}
```

> **Send/Sync 洞察**: `Send` 和 `Sync` 是 Rust **并发安全的类型系统根基**——它们将线程安全从文档约定提升为**编译期可验证的属性**。
> [来源: [std::marker::Send](https://doc.rust-lang.org/std/marker/trait.Send.html)]

---

### 1.3 共享状态 vs 消息传递
>

```text
两种并发模型:

  消息传递（Go 风格）:
  ├── 通道（Channel）传输数据
  ├── 所有权随消息转移
  ├── 无共享状态
  ├── 更容易推理
  └── 适合: 任务并行、流水线

  共享状态（传统风格）:
  ├── Mutex/RwLock [来源: [std::sync::RwLock](https://doc.rust-lang.org/std/sync/struct.RwLock.html)] 保护数据
  ├── Arc 共享所有权
  ├── 状态集中管理
  ├── 更细粒度控制
  └── 适合: 高性能缓存、计数器

  Rust 的融合:
  ├── 消息传递: std::sync::mpsc / crossbeam::channel [来源: [std::sync::mpsc](https://doc.rust-lang.org/std/sync/mpsc/index.html)]
  ├── 共享状态: Mutex + Arc
  ├── 混合使用: 通道传递 Arc
  └── 选择取决于场景

  代码对比:

  消息传递:
    let (tx, rx) = mpsc::channel();
    tx.send(data).unwrap();
    let received = rx.recv().unwrap();

  共享状态:
    let counter = Arc::new(Mutex::new(0));
    let counter2 = Arc::clone(&counter);
    thread::spawn(move || {
        *counter2.lock().unwrap() += 1;
    });
```

> **模型洞察**: Rust 的**所有权系统**使两种模型都可以**安全地实现**——消息传递自动转移所有权，共享状态通过类型系统保证互斥。
> [来源: [Rust By Example — Concurrency](https://doc.rust-lang.org/rust-by-example/std_misc/threads.html)]

---

## 二、技术细节

### 2.1 通道模式
>

```rust,ignore
// 通道的类型与选择

use std::sync::mpsc;

// 1. 多生产者单消费者 (MPSC)
let (tx, rx) = mpsc::channel();
let tx2 = tx.clone();  // 多个发送者

// 2. 同步通道（有界容量）
let (tx, rx) = mpsc::sync_channel(100);  // 缓冲 100 个消息

// crossbeam 的无界/有界通道（更优）
use crossbeam::channel;
let (tx, rx) = channel::unbounded();  // 无界
let (tx, rx) = channel::bounded(100);  // 有界

// 通道模式:
// ├── 请求-响应: 两个通道（req, resp）
// ├── 广播: crossbeam::channel 不支持，用 bus crate
// ├── 工作窃取: crossbeam::deque
// └── select: 多路复用接收

// Select（crossbeam）:
use crossbeam::channel::select;

select! {
    recv(rx1) -> msg => println!("从 rx1: {:?}", msg),
    recv(rx2) -> msg => println!("从 rx2: {:?}", msg),
    default => println!("无消息"),
}

// async 通道（tokio）:
use tokio::sync::mpsc;
let (tx, mut rx) = mpsc::channel(100);
// 异步发送/接收
```

> **通道洞察**: **crossbeam 通道**是 Rust **同步并发**的标准选择——它比 std::sync::mpsc 更快且支持 select。
> [来源: [crossbeam::channel](https://docs.rs/crossbeam/latest/crossbeam/channel/index.html)]

---

### 2.2 无锁数据结构
>

```text
无锁并发 primitives:

  Atomic 类型:
  ├── AtomicUsize / AtomicIsize
  ├── AtomicBool
  ├── AtomicPtr<T>
  └── 操作: load, store, swap, compare_exchange, fetch_add

  内存顺序:
  ├── Relaxed: 最弱，仅原子性
  ├── Acquire/Release: 同步点
  ├── AcqRel: 同时获取和释放
  └── SeqCst: 最强，顺序一致

  Lock-free 数据结构:
  ├── crossbeam::epoch: 基于epoch的内存回收
  ├── crossbeam::queue: MSQ 无锁队列
  └── 自定义: Atomic + unsafe

  示例（原子计数器）:
  use std::sync::atomic::{AtomicUsize, Ordering};

  let counter = AtomicUsize::new(0);
  counter.fetch_add(1, Ordering::Relaxed);
  let val = counter.load(Ordering::Acquire);

  何时使用无锁:
  ├── 极高并发（锁竞争严重）
  ├── 低延迟要求（无上下文切换）
  ├── 实时系统（避免锁的不可预测性）
  └── 但: 实现复杂，容易出错
```

> **无锁洞察**: Rust 的 **Atomic + unsafe** 使**无锁数据结构**可以安全地实现——但 `unsafe` 代码必须经过严格审查。
> [来源: [Rust Atomics and Locks](https://marabos.nl/atomics/)]

---

### 2.3 内存顺序
>

```rust,ignore
// 内存顺序详解

use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

// 1. Relaxed: 仅保证原子性，无顺序约束
let x = AtomicUsize::new(0);
x.fetch_add(1, Ordering::Relaxed);

// 2. Acquire/Release: 成对同步
// 线程 A:
let data = vec![1, 2, 3];
let ptr = data.as_ptr();
DATA_PTR.store(ptr as usize, Ordering::Release);  // Release: 之前的写可见

// 线程 B:
let ptr = DATA_PTR.load(Ordering::Acquire) as *const i32;  // Acquire: 之后的读可见
if !ptr.is_null() {
    // 可以安全读取 *ptr（A 中 Release 之前的写已可见）
}

// 3. AcqRel: 同时获取和释放
// 用于 read-modify-write 操作
x.fetch_add(1, Ordering::AcqRel);

// 4. SeqCst: 顺序一致性
// 所有线程看到相同的操作顺序
// 最慢但最容易推理
x.store(1, Ordering::SeqCst);

// 选择指南:
// ├── 独立计数器: Relaxed
// ├── 标志位 + 数据传递: Acquire/Release
// ├── 复杂同步: SeqCst
// └── 不确定时用 SeqCst，确认瓶颈后再优化
```

> **内存序洞察**: **内存顺序是并发编程中最复杂的主题**——Rust 暴露这些细节使开发者可以**精确控制性能**，但也要求深入理解硬件内存模型。
> [source: [std::sync::atomic::Ordering](https://doc.rust-lang.org/std/sync/atomic/enum.Ordering.html)]

---

## 三、并发模式矩阵

```text
场景 → 方案 → 工具

任务并行:
  → rayon::join / par_iter
  → 数据并行，自动工作窃取
  → v.par_iter().map(|x| x * 2).sum()

生产者-消费者:
  → crossbeam::channel
  → 有界/无界通道
  → 背压控制

读者-写者:
  → RwLock
  → 多读单写
  → 注意写者饥饿

状态机并发:
  → Actor 模型 (actix)
  → 消息驱动，状态隔离
  → 每个 Actor 单线程

无锁队列:
  → crossbeam::queue::SegQueue
  → 多生产者多消费者
  → 无锁，无阻塞

定时任务:
  → tokio::time::interval
  → 异步超时和间隔
  → 与 async/await 集成
```

> **模式矩阵**: Rust 的**并发生态**覆盖了从**高层数据并行**（rayon）到**底层无锁**（crossbeam）的全谱系。
> [source: [rayon crate](https://docs.rs/rayon/latest/rayon/)]

---

## 四、反命题与边界分析

### 4.1 反命题树
>

```mermaid
graph TD
    ROOT["命题: 所有并发都应使用无锁结构"]
    ROOT --> Q1{"是否有极端性能要求?"}
    Q1 -->|是| Q2{"团队是否理解内存模型?"}
    Q1 -->|否| LOCK["✅ Mutex/RwLock 足够"]
    Q2 -->|是| LOCKFREE["✅ 无锁可行"]
    Q2 -->|否| LEARN["⚠️ 先学习，再应用"]

    style LOCK fill:#c8e6c9
    style LOCKFREE fill:#c8e6c9
    style LEARN fill:#fff3e0
```

> **认知功能**: **无锁不是默认选择**——只有在**性能测量**证明锁是瓶颈，且团队有能力正确实现时，才使用无锁。
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
> [source: [Rust Atomics and Locks — When to Use](https://marabos.nl/atomics/when-to-use.html)]

---

### 4.2 边界极限
>

```text
边界 1: 死锁
├── Rust 不能编译期防止死锁
├── 运行时仍可能死锁
├── 需要设计层面的避免策略
└── 缓解: 锁顺序、超时、try_lock

边界 2: 优先级反转
├── 低优先级线程持有锁
├── 高优先级线程等待
├── 实时系统问题
└── 缓解: 优先级继承、无锁结构

边界 3: 伪共享（False Sharing）
├── 不同 CPU 核心访问同一缓存行的不同变量
├── 性能骤降
├── Rust 无自动防护
└── 缓解: cache-padding（crossbeam::util::CachePadded）

边界 4: ABA 问题
├── 无锁算法中的经典问题
├── 指针被释放后重新分配
├── 比较操作误判
└── 缓解: epoch-based GC, tagged pointers

边界 5: 调试困难
├── 并发 bug 难以复现
├── race condition 取决于时序
├── 传统调试器帮助有限
└── 缓解: loom model checker, TSan
```

> **边界要点**: 并发编程的边界主要与**死锁**、**优先级反转**、**伪共享**、**ABA** 和**调试**相关。
> [source: [crossbeam::epoch](https://docs.rs/crossbeam/latest/crossbeam/epoch/index.html)]

---

## 五、常见陷阱

```text
陷阱 1: 在持有锁时调用用户代码
  ❌ let data = mutex.lock().unwrap();
     callback(&data);  // 回调可能 panic 或死锁！

  ✅ let data = mutex.lock().unwrap().clone();
     drop(data);  // 先释放锁
     callback(&data);

陷阱 2: 忘记 Arc
  ❌ let data = Mutex::new(vec![]);
     thread::spawn(move || { data.lock(); });
     // Mutex 被 move，主线程无法使用

  ✅ let data = Arc::new(Mutex::new(vec![]));
     let data2 = Arc::clone(&data);
     thread::spawn(move || { data2.lock(); });

陷阱 3: 锁粒度不当
  ❌ 一个大 Mutex 保护所有数据
     // 串行化所有操作

  ✅ 细粒度锁，或按功能分区
     // 或使用 lock-free 结构

陷阱 4: 阻塞在 async 中
  ❌ async fn bad() {
         let data = mutex.lock().unwrap();  // 阻塞线程！
     }

  ✅ async fn good() {
         let data = async_mutex.lock().await;  // tokio::sync::Mutex
     }

陷阱 5: 忽略内存序
  ❌ flag.store(true, Ordering::Relaxed);
     // 其他线程可能看不到更新

  ✅ flag.store(true, Ordering::Release);
     // 配对的 Acquire 保证可见性
```

> **陷阱总结**: 并发陷阱主要与**锁内回调**、**Arc 遗漏**、**锁粒度**、**async 阻塞**和**内存序**相关。
> [source: [Common Rust Concurrency Mistakes](https://rust-unofficial.github.io/too-many-lists/)]

### 编译错误示例

```rust,compile_fail
use std::sync::Mutex;
use std::thread;

fn mutex_guard_lifetime() {
    let data = Mutex::new(0);
    let guard = data.lock().unwrap();
    // ❌ 编译错误: `MutexGuard` 不能跨线程发送
    // 某些平台/实现中 `MutexGuard` 不实现 `Send`
    thread::spawn(move || {
        println!("{}", *guard);
    });
}
```

> **修正**: 避免将 `MutexGuard` 移动到闭包中。若需跨线程共享数据，使用 `Arc<Mutex<T>>` 并在每个线程中独立 `lock()`。

```rust,compile_fail
use std::sync::Arc;
use std::cell::RefCell;

fn arc_refcell_thread() {
    let data = Arc::new(RefCell::new(0));
    let data2 = Arc::clone(&data);
    // ❌ 编译错误: `RefCell<i32>` 未实现 `Sync`
    // Arc<T> 要求 T: Sync 才能安全跨线程共享
    std::thread::spawn(move || {
        *data2.borrow_mut() += 1;
    });
}
```

> **修正**: `RefCell` 提供单线程内部可变性。跨线程场景必须使用 `Mutex<T>`、`RwLock<T>` 或原子类型。

```rust,compile_fail
use std::thread;

fn thread_spawn_lifetime() {
    let data = vec![1, 2, 3];
    // ❌ 编译错误: `data` 的生命周期不够长
    // thread::spawn 要求闭包是 'static
    let handle = thread::spawn(|| {
        println!("{:?}", data);
    });
    drop(data); // data 可能在此 drop
    handle.join().unwrap();
}
```

> **修正**: `thread::spawn` 要求闭包满足 `'static` 生命周期。引用栈数据必须通过 `move` 闭包转移所有权，或使用 `crossbeam::scope` 进行有界线程。

### 4.4 边界测试：`ScopedThread` 中引用逃逸（编译错误）

```rust,compile_fail
use std::thread;

fn scoped_borrow() {
    let mut data = vec![1, 2, 3];
    // ❌ 编译错误: `data` 的生命周期不够长
    // thread::scope 要求闭包在 scope 结束前完成
    let handle = thread::spawn(|| {
        data.push(4); // 闭包捕获 &mut data
    });
    // handle 可能在 scope 外被 join
    // 标准库 thread::spawn 要求 'static
}

// 正确: 使用 crossbeam::scope 或 std::thread::scope (Rust 1.63+)
fn scoped_fixed() {
    let mut data = vec![1, 2, 3];
    std::thread::scope(|s| {
        s.spawn(|| {
            data.push(4); // ✅ scope 保证线程在作用域结束前 join
        });
    }); // 所有子线程在此 join
    println!("{:?}", data);
}
```

> **修正**: `std::thread::scope`（Rust 1.63+）允许创建非 `'static` 线程，保证所有子线程在 scope 结束时 join。这通过编译期生命周期检查实现——闭包借用栈数据的生命周期与 scope 绑定。[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]

### 4.5 边界测试：`Condvar` 虚假唤醒未处理（逻辑错误）

```rust,ignore
use std::sync::{Arc, Mutex, Condvar};
use std::thread;

fn main() {
    let pair = Arc::new((Mutex::new(false), Condvar::new()));
    let pair2 = Arc::clone(&pair);

    thread::spawn(move || {
        let (lock, cvar) = &*pair2;
        let mut started = lock.lock().unwrap();
        *started = true;
        cvar.notify_one();
    });

    let (lock, cvar) = &*pair;
    let mut started = lock.lock().unwrap();
    // ⚠️ 逻辑错误: 直接用 if 检查条件
    if !*started {
        let _ = cvar.wait(started).unwrap(); // 虚假唤醒后不会重新检查
    }
    // 可能因虚假唤醒而提前退出
}

// 正确: 始终使用 while 循环
fn fixed() {
    let pair = Arc::new((Mutex::new(false), Condvar::new()));
    let pair2 = Arc::clone(&pair);

    thread::spawn(move || {
        let (lock, cvar) = &*pair2;
        let mut started = lock.lock().unwrap();
        *started = true;
        cvar.notify_one();
    });

    let (lock, cvar) = &*pair;
    let mut started = lock.lock().unwrap();
    while !*started { // ✅ 虚假唤醒后重新检查条件
        started = cvar.wait(started).unwrap();
    }
}
```

> **修正**: `Condvar::wait` 可能因"虚假唤醒"（spurious wakeup）而在未被 `notify` 时返回。必须始终使用 `while` 循环而非 `if` 检查条件，确保在虚假唤醒后重新验证条件。[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]

---

## 六、来源与延伸阅读
>

| 来源 | 可信度 | 说明 |
| [Rust Standard Library](https://doc.rust-lang.org/std/) | ✅ 一级 | 标准库参考 |
| [Rust By Example](https://doc.rust-lang.org/rust-by-example/) | ✅ 一级 | 交互式教程 |
| [This Week in Rust](https://this-week-in-rust.org/) | ✅ 二级 | 社区动态 |

| [Rust Reference](https://doc.rust-lang.org/reference/) | ✅ 一级 | 语言参考 |
|:---|:---:|:---|
| [Rust Atomics and Locks](https://marabos.nl/atomics/) | ✅ 一级 | 并发权威 |
| [TRPL — Concurrency](https://doc.rust-lang.org/book/ch16-00-concurrency.html) | ✅ 一级 | 基础教程 |
| [crossbeam](https://docs.rs/crossbeam/latest/crossbeam/) | ✅ 一级 | 无锁并发 |
| [rayon](https://docs.rs/rayon/latest/rayon/) | ✅ 一级 | 数据并行 |
| [tokio::sync](https://docs.rs/tokio/latest/tokio/sync/index.html) | ✅ 一级 | 异步同步 |

---

## 相关概念文件

- [Concurrency](./01_concurrency.md) — 并发基础
- [Async](./02_async.md) — 异步编程
- [Distributed Systems](../06_ecosystem/18_distributed_systems.md) — 分布式系统

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/)
>
> **权威来源对齐变更日志**: 2026-05-22 创建 [来源: Authority Source Sprint Batch 10]

**文档版本**: 1.0
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-22
**状态**: ✅ 概念文件创建完成

---

## 逆向推理链（Backward Reasoning）

> **从编译错误反推**：
>
> ```text
> 并发模式安全 ⟸ Send/Sync + 锁协议
> ```
>
## 权威来源索引

>
>
>
>
>
>

---

---

---

### 10.3 边界测试：`crossbeam::channel` 的关闭检测与迭代终止（逻辑错误）

```rust,compile_fail
use crossbeam::channel::bounded;

fn main() {
    let (tx, rx) = bounded::<i32>(10);

    tx.send(1).unwrap();
    tx.send(2).unwrap();
    drop(tx); // 关闭发送端

    // ❌ 逻辑错误: 未检测 channel 关闭，迭代器提前终止不通知
    for msg in rx.iter() {
        println!("{}", msg);
    }
    println!("done"); // 会执行，但无显式关闭通知
}
```

> **修正**: `crossbeam::channel` 的关闭语义：
>
> 1) 所有 `Sender` drop → `Receiver::recv()` 返回 `Err(RecvError)`（Disconnected）；
> 2) `Receiver::iter()` 在 channel 关闭且所有消息消费完后终止；
> 3) 无显式"关闭信号"——需协议层实现（发送特殊 sentinel 值）。
> 与 `std::sync::mpsc` 的区别：`crossbeam` 支持多生产者/多消费者、无界和有界 channel、选择（`select!`）。
> 有界 channel 的 `send` 在满时阻塞（或超时），防止无限内存增长。
> 这与 Go 的 channel（语言原生，自动处理关闭和 range 迭代）或 Tokio 的 `mpsc`（异步，背压控制）不同——Rust 的 channel 库多样，`crossbeam` 是同步场景的性能最优选择。
> [来源: [crossbeam-channel](https://docs.rs/crossbeam-channel/)] · [来源: [Rust Atomics and Locks](https://marabos.nl/atomics/)]

### 10.4 边界测试：Send/Sync 的 auto trait 边界与线程安全（编译错误）

```rust,compile_fail,compute_fail
use std::rc::Rc;
use std::thread;

fn main() {
    let data = Rc::new(42);
    // ❌ 编译错误: Rc<i32> 未实现 Send，不能跨线程传递
    thread::spawn(move || {
        println!("{}", data);
    }).join().unwrap();
}
```

> **修正**:
> **`Send`** 和 **`Sync`** 是 auto trait：
>
> 1) `Send` — 类型可安全转移到其他线程；
> 2) `Sync` — 类型可安全被多线程共享引用（`&T` 是 `Send`）；
> 3) `Rc<T>` 既不是 `Send` 也不是 `Sync`（引用计数非原子）。
>
> 线程安全替代：
>
> 1) `Arc<T>` — 原子引用计数，实现 `Send + Sync`（若 `T: Send + Sync`）；
> 2) `Mutex<T>` / `RwLock<T>` — 互斥访问；
> 3) `mpsc` / `crossbeam` channel — 消息传递。
>
> 自定义类型的线程安全：
>
> 1) 包含 `Send` 字段 → 自动 `Send`；
> 2) 包含 `Rc` / `Cell` / `RefCell` → 自动 `!Send`；
> 3) 可 `unsafe impl Send for MyType {}`（需手动保证）。
> 这与 Go 的 goroutine（所有数据可共享，通过 channel 或 mutex 协调）或 Java 的 `synchronized`（所有对象有 monitor，编译器不检查线程安全）不同
> ——Rust 的 `Send`/`Sync` 是编译期线程安全检查。
> [来源: [The Rust Programming Language](https://doc.rust-lang.org/book/ch16-04-extensible-concurrency-sync-and-send.html)] · [来源: [Rustonomicon — Send and Sync](https://doc.rust-lang.org/nomicon/send-and-sync.html)]

## 参考来源

> [来源: [Tokio Concurrency Primitives](https://tokio.rs/tokio/tutorial/shared-state)]
> [来源: [Rustonomicon — Concurrency](https://doc.rust-lang.org/nomicon/concurrency.html)]
> [来源: [Herlihy & Shavit — Art of Multiprocessor Programming](https://dl.acm.org/doi/book/10.5555/2385452)]
> [来源: [RFC 0458 — Send and Sync](https://rust-lang.github.io/rfcs//0458-send-improvements.html)]
> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/) · [The Rust Programming Language](https://doc.rust-lang.org/book/) · [Rust Standard Library](https://doc.rust-lang.org/std/) · [Rustonomicon](https://doc.rust-lang.org/nomicon/)
> **对应 Rust 版本**: 1.96.0+ (Edition 2024)

## 认知路径

> **认知路径**: 从 L0 基础概念出发，经由本节的 **并发 模式：从消息 传递到锁自由的数据结构** 核心原理，通向 L2 进阶模式与 L3 工程实践。

### 核心推理链

| 定理 | 前提 | 结论 | 置信度 |
|:---|:---|:---|:---|
| 并发 模式：从消息 传递到锁自由的数据结构 基础定义 ⟹ 正确用法 | 理解语法与语义 | 能写出符合惯用法的代码 | 高 |
| 并发 模式：从消息 传递到锁自由的数据结构 正确用法 ⟹ 常见陷阱 | 忽略边界条件 | 编译错误或运行时 bug | 高 |
| 并发 模式：从消息 传递到锁自由的数据结构 常见陷阱 ⟹ 深度掌握 | 系统学习反模式 | 能进行代码审查与优化 | 高 |

> 无数据竞争 ⟸ Send/Sync 正确实现 ⟸ 类型系统验证
> 死锁避免 ⟸ 锁顺序协议 ⟸ 类型状态机
> **过渡**: 掌握 并发 模式：从消息 传递到锁自由的数据结构 的基础语法后，下一步需要理解其在类型系统中的位置与与其他概念的交互关系。

> **过渡**: 在实践中应用 并发 模式：从消息 传递到锁自由的数据结构 时，务必关注边界条件与异常处理，这是从"能编译"到"能生产"的关键跃迁。

> **过渡**: 并发 模式：从消息 传递到锁自由的数据结构 的设计理念体现了 Rust 零成本抽象与安全保证的核心权衡，理解这一权衡有助于迁移到更高级的并发与形式化验证领域。

### 反命题与边界

> **反命题**: "并发 模式：从消息 传递到锁自由的数据结构 在所有场景下都是最佳选择" —— 错误。需要根据具体上下文权衡性能、可读性与安全性，某些场景下显式替代方案可能更优。

---

---

## 实践

> 将本节概念转化为可编译代码。

### 对应代码示例

- **[crates/c05_threads](../../../crates/c05_threads/)** — 与本节概念对应的可编译 crate 示例

### 建议练习

1. 阅读 `crates/c05_threads/` 中与"并发设计模式"相关的源码和示例
2. 运行 `cargo test -p c05_threads` 验证理解

---

## 导航：下一步去哪？

> **自检**：你当前掌握的核心概念是否已能独立应用？

| 选择 | 条件 | 目标 |
|:---|:---|:---|
| 🔙 巩固基础 | 仍有模糊概念 | 回到 [L2 对应主题](../02_intermediate/) 或 [MVP 学习路径](../00_meta/LEARNING_MVP_PATH.md) |
| 🔜 深入 L3 其他主题 | 想扩展高级技能 | [L3 README](./README.md) 选择其他主题 |
| 🎓 进入 L4 形式化 | 想理解"为什么"的数学证明 | [L4 形式化](../04_formal/README.md) |
| 🏗️ 进入 L6 生态 | 想掌握生产工具链 | [L6 生态](../06_ecosystem/README.md) |

---

## 嵌入式测验

### 测验 1：并发模式识别（记忆层）

**题目**: 以下场景最适合哪种并发模式？

| 场景 | 最佳模式 |
|:---|:---|
| 多个线程读取共享配置，偶尔更新 | A. `Mutex<T>` |
| 多个线程同时读取和写入共享缓存 | B. `RwLock<T>` |
| 一个线程生产任务，多个线程消费 | C. `mpsc::channel` |
| 多个线程竞争执行一次性初始化 | D. `std::sync::OnceLock` |

- A. 1-A, 2-B, 3-C, 4-D
- B. 1-B, 2-A, 3-C, 4-D
- C. 1-B, 2-B, 3-C, 4-D
- D. 1-D, 2-A, 3-B, 4-C

<details>
<summary>✅ 答案与解析</summary>

**正确答案是 B**。

| 场景 | 最佳模式 | 原因 |
|:---|:---|:---|
| 多线程读取、偶尔更新 | **`RwLock<T>`** | 读操作可并发，写操作独占 |
| 同时读写共享缓存 | **`Mutex<T>`** | 读写都频繁时，`RwLock` 的升级/降级开销反而更差 |
| 生产者-消费者 | **`mpsc::channel`** | 天然的消息传递，无锁竞争 |
| 一次性初始化 | **`OnceLock`** | 线程安全的惰性初始化，初始化后零开销 |

**RwLock vs Mutex 的选择指南**：

```rust,ignore
use std::sync::{Mutex, RwLock};

// 场景1: 读多写少 → RwLock
let config: RwLock<Config> = RwLock::new(Config::default());
{
    let _guard = config.read().unwrap();  // 多个读锁可并发
}
{
    let mut _guard = config.write().unwrap();  // 写锁独占
}

// 场景2: 读写都频繁 → Mutex（更简单，无死锁风险）
let cache: Mutex<Cache> = Mutex::new(Cache::default());
```

> **陷阱**: `RwLock` 在写操作频繁时会**饿死读者**或**饿死写者**（取决于实现）。Tokio 的 `RwLock` 是公平锁，但 std 的 `RwLock` 平台依赖。
</details>

---

### 测验 2：Arc 引用计数（理解层）

**题目**: 以下代码能否编译？如果不能，为什么？

```rust,compile_fail
use std::sync::Arc;
use std::thread;

fn main() {
    let data = Arc::new(vec![1, 2, 3]);

    let handle = thread::spawn(move || {
        println!("{:?}", data);
    });

    println!("{:?}", data);  // 还能用吗？
    handle.join().unwrap();
}
```

- A. 可以编译，`Arc` 自动实现了 `Copy`
- B. 不能编译，`move` 将 `data` 移入闭包，主线程无法再使用
- C. 可以编译，`Arc` 的 `clone()` 在 `move` 闭包中自动调用
- D. 不能编译，需要先 `let data2 = Arc::clone(&data)` 再 `move`

<details>
<summary>✅ 答案与解析</summary>

**正确答案是 B**。

**问题**：`move ||` 闭包会将捕获的变量**所有权移入**闭包。`Arc` 没有实现 `Copy`，所以 `data` 被移动后，主线程无法再使用。

**修复方案**：

```rust
use std::sync::Arc;
use std::thread;

fn main() {
    let data = Arc::new(vec![1, 2, 3]);

    // 关键：先 clone Arc，增加引用计数
    let data_clone = Arc::clone(&data);

    let handle = thread::spawn(move || {
        println!("线程: {:?}", data_clone);
    });

    // 主线程仍可使用原始 data
    println!("主线程: {:?}", data);
    handle.join().unwrap();

    // 两个 Arc 都 drop 后，内部数据才被释放
}
```

**`Arc::clone(&data)` 的本质**：

```rust,ignore
// 不是深拷贝！只是增加引用计数
impl<T> Clone for Arc<T> {
    fn clone(&self) -> Self {
        // 原子操作: ref_count += 1
        self.inner().ref_count.fetch_add(1, Relaxed);
        Arc { ptr: self.ptr }
    }
}
```

**常见模式**：

```rust,ignore
// N 个线程共享同一数据
let data = Arc::new(Mutex::new(0));
let mut handles = vec![];

for _ in 0..10 {
    let d = Arc::clone(&data);
    handles.push(thread::spawn(move || {
        let mut num = d.lock().unwrap();
        *num += 1;
    }));
}

for h in handles { h.join().unwrap(); }
assert_eq!(*data.lock().unwrap(), 10);
```

> **关键洞察**: `Arc` 解决"数据该由谁释放"的问题，`Mutex`/`RwLock` 解决"数据如何安全访问"的问题。两者常配合使用，但职责不同。
</details>

---

### 测验 3：工作窃取模式（应用层）

**题目**: 以下代码使用 Rayon 的 `join` 实现了并行快速排序。`rayon::join` 的核心优势是什么？

```rust
use rayon::prelude::*;

fn quicksort(arr: &mut [i32]) {
    if arr.len() <= 1 { return; }

    let pivot = partition(arr);
    let (left, right) = arr.split_at_mut(pivot);

    rayon::join(
        || quicksort(left),
        || quicksort(right),
    );
}
```

- A. `join` 自动选择更快的分支先执行
- B. `join` 将两个闭包分发到不同线程，利用工作窃取调度器平衡负载
- C. `join` 保证左分支总是先于右分支完成
- D. `join` 只是语法糖，等价于顺序执行两个闭包

<details>
<summary>✅ 答案与解析</summary>

**正确答案是 B**。

**Rayon 的工作窃取调度器**：

```
线程1: [taskA] [taskB] [taskC] ← 本地队列
线程2: [taskD] ← 队列为空时，从线程1"窃取"任务
```

| 特性 | 说明 |
|:---|:---|
| **工作窃取** | 空闲线程从忙碌线程的队列尾部"偷"任务，避免负载不均 |
| **fork-join** | `rayon::join` 创建子任务，完成后自动汇合 |
| **线程池复用** | Rayon 全局线程池（默认 = CPU 核心数），避免频繁创建线程 |
| **无锁队列** | 每个线程的双端队列：本地 push/pop（无锁），窃取端（CAS）|

**为什么不用 `thread::spawn`**：

```rust,ignore
// 错误示范：每次递归都创建新线程，开销巨大
thread::spawn(|| quicksort(left));
thread::spawn(|| quicksort(right));
// 1000 个元素的快速排序可能创建 1000+ 个线程！

// Rayon 的优化：
// - 小任务内联执行（不创建线程）
// - 大任务才分发给线程池
// - 任务粒度由调度器自动决定
```

**Rayon 的阈值优化**：

```rust
fn quicksort(arr: &mut [i32]) {
    if arr.len() <= 10_000 {
        // 小数组：顺序排序更快（避免线程切换开销）
        arr.sort_unstable();
        return;
    }
    // 大数组：并行分治
    let pivot = partition(arr);
    let (left, right) = arr.split_at_mut(pivot);
    rayon::join(|| quicksort(left), || quicksort(right));
}
```

> **核心洞察**: 并行不是越多越好。Rayon 的调度器自动处理任务粒度、负载平衡和线程管理，开发者只需关注"哪些任务可以并行"。
</details>

---

### 测验 4：死锁预防（分析层）

**题目**: 以下代码存在死锁风险。问题在哪里？如何修复？

```rust
use std::sync::Mutex;

struct Account {
    balance: Mutex<i32>,
}

fn transfer(from: &Account, to: &Account, amount: i32) {
    let mut from_balance = from.balance.lock().unwrap();
    let mut to_balance = to.balance.lock().unwrap();

    *from_balance -= amount;
    *to_balance += amount;
}

fn main() {
    let a = Account { balance: Mutex::new(100) };
    let b = Account { balance: Mutex::new(100) };

    std::thread::scope(|s| {
        s.spawn(|| transfer(&a, &b, 10));
        s.spawn(|| transfer(&b, &a, 20));  // 潜在死锁！
    });
}
```

- A. 没有死锁风险，`Mutex` 会自动处理
- B. 线程1先锁a再锁b，线程2先锁b再锁a，形成循环等待 → 死锁
- C. 应该用 `RwLock` 替代 `Mutex` 避免死锁
- D. 应该用 `std::sync::atomic::AtomicI32` 替代 `Mutex`

<details>
<summary>✅ 答案与解析</summary>

**正确答案是 B**。

**死锁四条件（Coffman 条件）**：

| 条件 | 本例 |
|:---|:---|
| 互斥 | `Mutex` 保证 |
| 占有且等待 | 线程1持有 `a.lock()`，等待 `b.lock()` |
| 不可抢占 | `Mutex` 不支持强制释放 |
| 循环等待 | 线程1: a→b，线程2: b→a |

**修复方案 — 统一加锁顺序**：

```rust,ignore
use std::sync::Mutex;

fn transfer(from: &Account, to: &Account, amount: i32) {
    // 方案1: 按内存地址排序加锁
    let (first, second) = if from as *const _ < to as *const _ {
        (from, to)
    } else {
        (to, from)
    };

    let mut first_balance = first.balance.lock().unwrap();
    let mut second_balance = second.balance.lock().unwrap();

    // 现在锁顺序总是按地址升序，无循环等待
    // ... 执行转账
}
```

**或者使用 `parking_lot::deadlock` 检测**（开发环境）：

```rust
// parking_lot 提供死锁检测功能
parking_lot::deadlock::check();
```

**更优方案 — 无锁转账**：

```rust
use std::sync::atomic::{AtomicI32, Ordering};

struct Account {
    balance: AtomicI32,
}

fn transfer(from: &Account, to: &Account, amount: i32) {
    from.balance.fetch_sub(amount, Ordering::Relaxed);
    to.balance.fetch_add(amount, Ordering::Relaxed);
}
// 无锁 = 无死锁！但无法保证原子性（中间状态可见）
```

> **生产环境法则**: 多锁场景必须定义全局顺序（如资源ID升序）。如果无法定义顺序，考虑：a) 使用无锁结构 b) 使用 `try_lock` 超时重试 c) 使用事务内存（如 `stm` crate）。
</details>

---

> **测验设计来源**: [Bloom Taxonomy 2001] · [TRPL Ch16](https://doc.rust-lang.org/book/ch16-00-concurrency.html) · [Rayon Docs](https://docs.rs/rayon/) · [Brown University Interactive TRPL](https://rust-book.cs.brown.edu/)
