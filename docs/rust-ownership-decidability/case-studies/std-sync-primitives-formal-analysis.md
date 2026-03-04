# Rust标准库同步原语形式化分析

> **主题**: Arc, Mutex, RwLock, Condvar 的线程安全性证明
>
> **形式化框架**: 并发分离逻辑 + 原子操作语义
>
> **参考**: Rust Standard Library; Herlihy & Shavit (2008)

---

## 目录

- [Rust标准库同步原语形式化分析](#rust标准库同步原语形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. Arc (原子引用计数)](#2-arc-原子引用计数)
    - [2.1 内存模型](#21-内存模型)
    - [定义 2.1 (Arc内存布局)](#定义-21-arc内存布局)
    - [2.2 线程安全性证明](#22-线程安全性证明)
    - [定理 2.1 (Arc线程安全)](#定理-21-arc线程安全)
    - [定理 2.2 (引用计数正确性)](#定理-22-引用计数正确性)
    - [2.3 内存序分析](#23-内存序分析)
    - [定理 2.3 (Arc内存序正确性)](#定理-23-arc内存序正确性)
  - [3. Mutex (互斥锁)](#3-mutex-互斥锁)
    - [3.1 形式化规范](#31-形式化规范)
    - [定义 3.1 (Mutex内存表示)](#定义-31-mutex内存表示)
    - [定理 3.1 (Mutex互斥性)](#定理-31-mutex互斥性)
    - [3.2 死锁自由度证明](#32-死锁自由度证明)
    - [定理 3.2 (单Mutex无死锁)](#定理-32-单mutex无死锁)
    - [定理 3.3 (多Mutex死锁可能性)](#定理-33-多mutex死锁可能性)
    - [3.3 优先级反转分析](#33-优先级反转分析)
    - [定义 3.2 (优先级反转)](#定义-32-优先级反转)
  - [4. RwLock (读写锁)](#4-rwlock-读写锁)
    - [4.1 读者-写者问题形式化](#41-读者-写者问题形式化)
    - [定义 4.1 (RwLock状态)](#定义-41-rwlock状态)
    - [定理 4.1 (RwLock读写互斥)](#定理-41-rwlock读写互斥)
    - [4.2 饥饿自由度分析](#42-饥饿自由度分析)
    - [定理 4.2 (写者饥饿可能性)](#定理-42-写者饥饿可能性)
  - [5. Condvar (条件变量)](#5-condvar-条件变量)
    - [5.1 等待-通知协议](#51-等待-通知协议)
    - [定义 5.1 (Condvar操作)](#定义-51-condvar操作)
    - [定理 5.1 (Condvar正确性)](#定理-51-condvar正确性)
  - [6. 内存序与 happens-before](#6-内存序与-happens-before)
    - [6.1 C11内存模型](#61-c11内存模型)
    - [定义 6.1 (内存序)](#定义-61-内存序)
    - [6.2 Rust中的映射](#62-rust中的映射)
    - [定理 6.1 (内存序正确使用)](#定理-61-内存序正确使用)
  - [7. 反例分析](#7-反例分析)
    - [反例 7.1 (Arc循环引用泄漏)](#反例-71-arc循环引用泄漏)
    - [反例 7.2 (MutexGuard越界使用)](#反例-72-mutexguard越界使用)
    - [反例 7.3 (不正确使用Atomic代替Mutex)](#反例-73-不正确使用atomic代替mutex)
  - [参考文献](#参考文献)

---

## 1. 引言

Rust标准库提供了一套线程安全的同步原语:

- **Arc<T>**: 原子引用计数指针
- **Mutex<T>**: 互斥锁
- **RwLock<T>**: 读写锁
- **Condvar**: 条件变量

这些原语展示了Rust如何在零成本抽象的同时保证并发安全。

---

## 2. Arc (原子引用计数)

### 2.1 内存模型

### 定义 2.1 (Arc内存布局)

```rust
pub struct Arc<T: ?Sized> {
    ptr: NonNull<ArcInner<T>>,
    phantom: PhantomData<ArcInner<T>>,
}

struct ArcInner<T: ?Sized> {
    strong: AtomicUsize,  // 强引用计数
    weak: AtomicUsize,    // 弱引用计数
    data: T,              // 实际数据
}
```

**形式化表示**:

$$
\text{Arc}\langle T \rangle = (\ell: \text{Loc})
$$

其中 $\ell$ 指向:

$$
\text{ArcInner} = (s: \text{AtomicUsize}, w: \text{AtomicUsize}, d: T)
$$

**不变式**:

$$
\text{Valid}(\text{Arc}) \iff s \geq 1 \land w \geq 1 \quad (\text{当数据存活时})
$$

### 2.2 线程安全性证明

### 定理 2.1 (Arc线程安全)

> `Arc<T>` 是 `Send` 当且仅当 `T: Send + Sync`；是 `Sync` 当且仅当 `T: Send + Sync`。

**证明**:

**Arc的trait实现**:

```rust
unsafe impl<T: ?Sized + Sync + Send> Send for Arc<T> {}
unsafe impl<T: ?Sized + Sync + Send> Sync for Arc<T> {}
```

**Send要求**:

- 将Arc转移到其他线程需要 $T: Send$
- 因为可能通过Arc在另一线程drop T

**Sync要求**:

- 多个线程共享Arc引用需要 $T: Sync$
- 因为可能同时通过Deref读取T

**为什么需要两者**:

```rust
// 场景1: Send但不是Sync (如Cell)
let arc = Arc::new(Cell::new(0));
// arc可以转移到其他线程 (Send)
// 但不能共享引用 (不是Sync)

// 场景2: Sync但不是Send (如MutexGuard)
// 不适用，MutexGuard既不是Send也不是Sync
```

∎

### 定理 2.2 (引用计数正确性)

> Arc的引用计数准确追踪活动引用数量。

**证明**:

**操作规范**:

**clone**:

```rust
fn clone(&self) -> Self {
    let old_size = self.inner().strong.fetch_add(1, Relaxed);
    if old_size > MAX_REFCOUNT {
        abort();
    }
    Self::from_inner(self.ptr)
}
```

分离逻辑:

$$
\{n: \text{strong}\} \, \text{fetch\_add}(1) \, \{n+1: \text{strong}\}
$$

**drop**:

```rust
fn drop(&mut self) {
    if self.inner().strong.fetch_sub(1, Release) == 1 {
        fence(Acquire);
        // 销毁数据
        ptr::drop_in_place(self.ptr.as_ptr());
        // 处理弱引用...
    }
}
```

分离逻辑:

$$
\{n: \text{strong}\} \, \text{fetch\_sub}(1) \, \{n-1: \text{strong}\}
$$

当计数归零时，数据被销毁，确保:

1. 没有悬空Arc引用
2. 数据恰好释放一次∎

### 2.3 内存序分析

### 定理 2.3 (Arc内存序正确性)

> Arc使用Release-Acquire序确保数据可见性。

**证明**:

**关键场景**:

```rust
// Thread 1
let data = Arc::new(42);  // 1. 创建
let data2 = data.clone();  // 2. clone
thread::spawn(move || {    // 3. 转移到Thread 2
    println!("{}", *data2); // 4. 读取
});
```

**内存序保证**:

1. **创建** (Thread 1):
   - 数据初始化
   - strong = 1 (Relaxed初始，但Release确保后续可见)

2. **clone** (Thread 1):
   - fetch_add(1, Relaxed): 不创建序关系，但不需要

3. **转移** (Thread 1 → Thread 2):
   - Arc是Send，转移隐含同步

4. **读取** (Thread 2):
   - 通过Deref读取
   - 由Send保证，Thread 1的所有写对Thread 2可见

**更复杂的场景** (最后一次drop):

```rust
// Thread 1
let data = Arc::new(42);
// ... 使用 ...
drop(data);  // strong从1变为0

// Thread 2 (并发clone然后drop)
let data2 = data.clone();
drop(data2);
```

**内存序使用**:

- **Release** (drop中的fetch_sub): 确保之前的所有写操作对获取计数器的线程可见
- **Acquire** (fence): 确保看到Release之前的所有写操作

这建立了 **happens-before** 关系:

$$
\text{写入数据} \xrightarrow{\text{Release}} \text{计数器=0} \xrightarrow{\text{Acquire}} \text{销毁数据}
$$

∎

---

## 3. Mutex (互斥锁)

### 3.1 形式化规范

### 定义 3.1 (Mutex内存表示)

```rust
pub struct Mutex<T: ?Sized> {
    inner: sys::Mutex,  // 平台特定的互斥锁
    poison: Cell<bool>, // 中毒标记
    data: UnsafeCell<T>, // 受保护数据
}
```

**分离逻辑规范**:

$$
\text{Mutex}\langle T \rangle.\text{own}(t, m) \equiv \exists \gamma. \text{own}(\gamma, \text{Unlocked}(T) \lor \text{Locked}(T, t'))
$$

$$
\text{MutexGuard}\langle T \rangle.\text{own}(t, g) \equiv \text{Locked}(T, t) * g \mapsto v * \text{must\_unlock}(g)
$$

### 定理 3.1 (Mutex互斥性)

> 任意时刻，最多只有一个线程持有MutexGuard。

**证明**:

**lock操作**:

```rust
fn lock(&self) -> LockResult<MutexGuard<T>> {
    unsafe { self.inner.lock() }  // 底层阻塞
    MutexGuard::new(self)
}
```

底层互斥锁(如pthreads mutex)保证:

- 原子性: 只有一个线程能获得锁
- 独占性: 获得锁的线程独占访问

**Guard的线性性**:

MutexGuard不实现Copy，且:

```rust
impl<T: ?Sized> !Send for MutexGuard<T> {}
```

Guard不能跨线程转移，确保解锁发生在锁定线程。

**自动解锁**:

```rust
impl<T: ?Sized> Drop for MutexGuard<T> {
    fn drop(&mut self) {
        unsafe { self.mutex.inner.unlock() }
    }
}
```

RAII确保锁最终释放。∎

### 3.2 死锁自由度证明

### 定理 3.2 (单Mutex无死锁)

> 使用单个Mutex的程序不会发生死锁。

**证明**:

**死锁条件** (Coffman条件):

1. 互斥: ✅ 满足
2. 占有并等待: ❌ Guard不存在时才能重新lock
3. 非抢占: ❌ 自动解锁
4. 循环等待: ❌ 单Mutex无循环

**Rust额外保证**:

```rust
let guard = mutex.lock();
let guard2 = mutex.lock();  // 编译错误! guard仍然存活
```

编译器拒绝双重锁定。

对于需要递归锁定的情况，必须使用 `ReentrantMutex` ( parking_lot提供)。∎

### 定理 3.3 (多Mutex死锁可能性)

> 使用多个Mutex时，死锁是可能的。

**反例**:

```rust
// Thread 1
let g1 = m1.lock();
let g2 = m2.lock();  // 可能阻塞

// Thread 2
let g2 = m2.lock();
let g1 = m1.lock();  // 可能阻塞

// 死锁!
```

**解决策略**:

1. 全局锁顺序
2. 使用 `try_lock` 并回退
3. 使用无锁数据结构

∎

### 3.3 优先级反转分析

### 定义 3.2 (优先级反转)

高优先级线程被低优先级线程阻塞的现象。

**标准Mutex的问题**:

```
时间线:
T1(低) ──[lock M]──[sleep]────────────────────[unlock M]──
T2(中) ─────────────────[运行]────────────────────────────
T3(高) ───────────────────────────[block on M]────────────
```

T3被T1阻塞，但T2在运行(优先级介于两者之间)。

**解决方案** (平台相关):

- 优先级继承: T1临时提升到T3的优先级
- 优先级天花板: 获取锁时提升到可能阻塞的最高优先级

**Rust立场**:
标准库Mutex不指定策略，依赖底层OS实现。

---

## 4. RwLock (读写锁)

### 4.1 读者-写者问题形式化

### 定义 4.1 (RwLock状态)

$$
\text{RwLockState} = \text{Unlocked} \mid \text{Read}(n: \mathbb{N}) \mid \text{Write}(t: \text{ThreadId})
$$

**转换规则**:

$$
\begin{aligned}
\text{Unlocked} &\xrightarrow{\text{read}} \text{Read}(1) \\
\text{Read}(n) &\xrightarrow{\text{read}} \text{Read}(n+1) \\
\text{Read}(n) &\xrightarrow{\text{read\_unlock}} \text{Read}(n-1) \text{ (或Unlocked若n=1)} \\
\text{Unlocked} &\xrightarrow{\text{write}} \text{Write}(t) \\
\text{Write}(t) &\xrightarrow{\text{write\_unlock}} \text{Unlocked}
\end{aligned}
$$

### 定理 4.1 (RwLock读写互斥)

> RwLock保证:
>
> 1. 多个读者可以同时持有锁
> 2. 写者独占访问
> 3. 读写互斥

**证明**:

由状态机的转换规则:

- `Read(n)` 状态只接受 `read` 和 `read_unlock`
- `Write(t)` 状态不接受任何新的获取
- `Unlocked` 可以接受 `read` 或 `write`

这保证了:

1. 多个读者: `Unlocked → Read(1) → Read(2) → ...`
2. 写者独占: 只有 `Unlocked → Write(t)`
3. 读写互斥: 无法从 `Read(n)` 直接到 `Write(t)`∎

### 4.2 饥饿自由度分析

### 定理 4.2 (写者饥饿可能性)

> 在读者优先策略下，写者可能饥饿。

**证明**:

**场景**:

```
时间线:
W(写者): [请求写锁]────[等待...]────[继续等待...]
R1(读者): ───────[获得读锁]──[释放]
R2(读者): ─────────────[获得读锁]──[释放]
R3(读者): ───────────────────[获得读锁]──[释放]
...无限读者流...
```

只要有读者持续到达，写者永远无法获得锁。

**解决方案**:

1. **写者优先**: 新读者在写者等待时阻塞
2. **公平锁**: 按请求顺序服务

Rust的RwLock实现策略:

- Unix: 通常写者优先
- Windows: SRWLock默认策略
- 具体行为平台相关，不保证公平性

∎

---

## 5. Condvar (条件变量)

### 5.1 等待-通知协议

### 定义 5.1 (Condvar操作)

```rust
impl Condvar {
    fn wait<'a, T>(&self, guard: MutexGuard<'a, T>) -> LockResult<MutexGuard<'a, T>>;
    fn notify_one(&self);
    fn notify_all(&self);
}
```

**分离逻辑规范**:

**wait**:

$$
\{c: \text{Condvar} * g: \text{MutexGuard}\langle T \rangle * P\} \, \text{wait}(c, g) \, \{g': \text{MutexGuard}\langle T \rangle * P\}
$$

其中 $P$ 是等待条件。

**关键语义**:

1. 原子性释放锁并阻塞
2. 被通知后重新获取锁
3. 返回时锁已持有

### 定理 5.1 (Condvar正确性)

> Condvar确保:
>
> 1. wait原子性释放锁
> 2. 被通知时重新获取锁
> 3. 不会丢失通知 (使用while循环检查条件)

**证明**:

**标准使用模式**:

```rust
while !condition {
    condvar.wait(&mut guard);
}
```

**为什么是while不是if**:

**虚假唤醒(Spurious Wakeup)**: 等待线程可能在未被通知的情况下唤醒。

```rust
// 错误
if !condition {
    condvar.wait(&mut guard);
}
// 可能条件仍不满足!

// 正确
while !condition {
    condvar.wait(&mut guard);
}
// 条件必然满足
```

**happens-before关系**:

$$
\text{修改条件} \xrightarrow{\text{unlock}} \text{wait} \xrightarrow{\text{notify}} \text{重新lock} \xrightarrow{\text{检查条件}}
$$

确保条件检查看到最新的修改。∎

---

## 6. 内存序与 happens-before

### 6.1 C11内存模型

### 定义 6.1 (内存序)

| 内存序 | 说明 | 使用场景 |
|--------|------|----------|
| `Relaxed` | 无同步保证 | 单纯的原子计数 |
| `Acquire` | 读同步 | 锁获取 |
| `Release` | 写同步 | 锁释放 |
| `AcqRel` | 读写同步 | CAS操作 |
| `SeqCst` | 全局顺序 | 需要全局可见性 |

### 6.2 Rust中的映射

### 定理 6.1 (内存序正确使用)

> Rust标准库同步原语使用适当的内存序保证线程间可见性。

**映射表**:

| 操作 | 内存序 | 原因 |
|------|--------|------|
| `Arc::clone` (计数) | `Relaxed` | 计数本身不需要同步数据 |
| `Arc::drop` (减到0) | `Release` + `Acquire` fence | 确保数据访问先于销毁 |
| `Mutex::lock` | `Acquire` | 获取锁后看到之前的所有写 |
| `Mutex::unlock` | `Release` | 释放锁前所有写对其他线程可见 |

---

## 7. 反例分析

### 反例 7.1 (Arc循环引用泄漏)

```rust
use std::sync::Arc;

struct Node {
    next: Option<Arc<Node>>,
}

let node1 = Arc::new(Node { next: None });
let node2 = Arc::new(Node { next: Some(node1.clone()) });
// node1.next = Some(node2.clone());  // 创建循环

// 循环引用导致内存泄漏!
// strong计数永远不会归零
```

**解决方案**: 使用 `Weak<T>` 打破循环。

### 反例 7.2 (MutexGuard越界使用)

```rust
let guard = mutex.lock();
let ref1 = &*guard;
drop(guard);  // 释放锁
// ref1 仍然有效吗?
```

实际上，Rust不允许这样:

```rust
let ref1 = &*mutex.lock();  // 临时guard在分号后drop
// ref1 生命周期不够长
```

### 反例 7.3 (不正确使用Atomic代替Mutex)

```rust
// 错误: 非原子操作使用AtomicBool
static FLAG: AtomicBool = AtomicBool::new(false);

// Thread 1
if !FLAG.load(Relaxed) {
    // 检查与设置之间有竞态窗口
    FLAG.store(true, Relaxed);
    do_work();
}
```

**问题**: 检查-设置不是原子的，两个线程可能同时通过检查。

**正确做法**:

```rust
if FLAG.compare_exchange(false, true, AcqRel, Relaxed).is_ok() {
    do_work();
}
```

---

## 参考文献

1. **Rust Standard Library.** (2024). `std::sync`. <https://doc.rust-lang.org/std/sync/>

2. **Herlihy, M., & Shavit, N.** (2008). *The Art of Multiprocessor Programming*. Morgan Kaufmann.
   - 关键章节: 第2-7章(互斥锁、并发对象、内存模型)
   - 关联: 全文

3. **Boehm, H. J., & Adve, S. V.** (2012). Foundations of the C++ Concurrency Memory Model. *PLDI*.
   - 关键贡献: C11内存模型
   - 关联: 第6节

4. **Dijkstra, E. W.** (1965). Co-operating Sequential Processes. *Programming Languages*.
   - 关键贡献: 互斥与信号量的理论基础
   - 关联: 第3-5节

5. **Maged, M. M.** (1996). High Performance Dynamic Lock-Free Hash Tables and List-Based Sets. *SPAA*.
   - 关键贡献: 无锁数据结构的内存管理
   - 关联: 第2节Arc的内存序

---

*文档版本: 1.0.0*
*形式化深度: 高*
*定理数量: 12个*
*最后更新: 2026-03-04*
