# Rust 线程安全模式

> **Rust版本**: 1.94
> **覆盖范围**: Send/Sync trait、内部可变性、锁类型、死锁预防
> **权威参考**: The Rust Programming Language (第16章), Rust Atomics and Locks

---

## 目录

- [Rust 线程安全模式](#rust-线程安全模式)
  - [目录](#目录)
  - [1. 理论基础](#1-理论基础)
    - [1.1 并发安全的形式化定义](#11-并发安全的形式化定义)
    - [1.2 Send 和 Sync trait 理论](#12-send-和-sync-trait-理论)
    - [1.3 数据竞争与竞态条件](#13-数据竞争与竞态条件)
  - [2. Send 和 Sync 深入解析](#2-send-和-sync-深入解析)
    - [2.1 Send trait](#21-send-trait)
    - [2.2 Sync trait](#22-sync-trait)
    - [2.3 自动推导规则](#23-自动推导规则)
    - [2.4 手动实现示例](#24-手动实现示例)
  - [3. 内部可变性模式](#3-内部可变性模式)
    - [3.1 RefCell 与线程安全](#31-refcell-与线程安全)
    - [3.2 Mutex 详解](#32-mutex-详解)
    - [3.3 RwLock 详解](#33-rwlock-详解)
    - [3.4 延迟初始化模式 (Rust 1.94)](#34-延迟初始化模式-rust-194)
    - [线程局部存储中的 LazyCell](#线程局部存储中的-lazycell)
    - [3.5 原子类型](#35-原子类型)
    - [3.5 性能对比与选择](#35-性能对比与选择)
  - [4. 锁的类型与实现](#4-锁的类型与实现)
    - [4.1 操作系统互斥锁](#41-操作系统互斥锁)

---

## 1. 理论基础

### 1.1 并发安全的形式化定义

在并发编程中，安全性通常使用以下形式化概念描述：

**定义 1.1.1 (数据竞争自由)**
程序 P 是数据竞争自由的，当且仅当对于任意两个访问同一内存位置的操作 o₁ 和 o₂，如果至少一个是写操作，则它们之间存在 happens-before 关系。

```text
∀o₁, o₂ ∈ Operations(P):
  loc(o₁) = loc(o₂) ∧ (is_write(o₁) ∨ is_write(o₂))
  ⇒ o₁ →hb o₂ ∨ o₂ →hb o₁
```

**定义 1.1.2 (竞态条件)**
竞态条件发生在程序的行为依赖于事件或线程的相对时序时。与数据竞争不同，竞态条件可能发生在数据竞争自由的程序中。

```rust
// 竞态条件示例：检查-操作（TOCTOU）
use std::sync::Arc;
use std::thread;

fn toctou_race(shared: Arc<Mutex<i32>>) {
    // 线程 1
    let t1 = {
        let s = shared.clone();
        thread::spawn(move || {
            let guard = s.lock().unwrap();
            if *guard > 0 {
                // 检查通过后，值可能已被修改
                std::thread::sleep(std::time::Duration::from_millis(1));
                println!("Value is positive: {}", *guard);
            }
        })
    };

    // 线程 2
    let t2 = {
        let s = shared.clone();
        thread::spawn(move || {
            let mut guard = s.lock().unwrap();
            *guard = -1; // 修改值
        })
    };

    t1.join().unwrap();
    t2.join().unwrap();
}
```

### 1.2 Send 和 Sync trait 理论

**定理 1.2.1 (Send 保证)**
如果类型 T: Send，则可以将 T 的值的所有权安全地转移到另一个线程。

**定理 1.2.2 (Sync 保证)**
如果类型 T: Sync，则可以安全地从多个线程同时引用 T 的值（&T）。

**定理 1.2.3 (组合规则)**

```text
T: Send + Sync     ⇔ &T: Send
T: Send            ⇔ &mut T: Send
T: Sync            ⇔ Arc<T>: Send (当 T: Send + Sync)
T: Send            ⇔ Box<T>: Send
T: Send + Sync     ⇔ Rc<T>: !Send ∧ !Sync (因为引用计数非原子)
```

### 1.3 数据竞争与竞态条件

**数据竞争三要素**:

1. 两个或更多线程访问同一内存位置
2. 至少一个是写操作
3. 没有同步

Rust 通过类型系统在编译时防止数据竞争：

```rust
use std::rc::Rc;
use std::thread;

fn data_race_prevention() {
    // ❌ 编译错误：Rc 不是 Send
    // let data = Rc::new(42);
    // thread::spawn(move || {
    //     println!("{}", *data);
    // });

    // ✅ 正确：Arc 是 Send + Sync
    let data = Arc::new(Mutex::new(42));
    let data2 = data.clone();
    thread::spawn(move || {
        let mut guard = data2.lock().unwrap();
        *guard += 1;
    });
}
```

---

## 2. Send 和 Sync 深入解析

### 2.1 Send trait

```rust
pub unsafe auto trait Send {
    // 空 trait，仅用于标记
}
```

**自动实现规则**:

- 所有原始类型（i32, f64, bool, char 等）都是 Send
- 如果 T: Send，则 Box<T>, Vec<T>, Option<T>, Result<T, E> 都是 Send
- 如果 T: Send + Sync，则 Arc<T> 是 Send
- 包含原始指针 `*const T` 或 `*mut T` 的类型不是自动 Send

**手动实现示例**:

```rust
use std::sync::atomic::{AtomicPtr, Ordering};
use std::marker::PhantomData;

/// 线程安全的原始指针包装器
pub struct SendPtr<T>(*mut T);

/// # Safety
/// 实现者必须确保：
/// 1. 指针指向的内存是线程安全的
/// 2. 指针的创建和访问遵循 Rust 的规则
unsafe impl<T> Send for SendPtr<T> where T: Send {}

impl<T> SendPtr<T> {
    pub fn new(ptr: *mut T) -> Self {
        Self(ptr)
    }

    /// # Safety
    /// 调用者必须确保：
    /// 1. 没有其他线程正在写入该位置
    /// 2. 指针仍然有效
    pub unsafe fn as_ref(&self) -> &T {
        &*self.0
    }
}

/// FFI 场景中的线程安全包装
pub struct ThreadSafeHandle {
    handle: *mut c_void,
    _marker: PhantomData<*const ()>, // 确保 !Send + !Sync 的默认行为
}

// 仅当底层 C 库是线程安全时才实现
unsafe impl Send for ThreadSafeHandle {}
unsafe impl Sync for ThreadSafeHandle {}
```

### 2.2 Sync trait

```rust
pub unsafe auto trait Sync {
    // 空 trait，仅用于标记
}
```

**核心性质**:

```text
T: Sync ⇔ &T: Send
```

这意味着如果 T 是 Sync，可以在多个线程之间安全地共享对 T 的引用。

**典型 Sync 类型**:

- 所有原始类型
- 原子类型：AtomicUsize, AtomicBool 等
- 只读数据结构：&str, &[T], String（因为 &String 是 Send）

**典型 !Sync 类型**:

- Cell<T>（内部可变性，非线程安全）
- RefCell<T>（运行时借用检查，非线程安全）

```rust
use std::cell::Cell;
use std::sync::Arc;
use std::thread;

fn sync_demonstration() {
    // Cell 是 !Sync
    let cell = Arc::new(Cell::new(42));

    // ❌ 编译错误
    // for i in 0..10 {
    //     let c = cell.clone();
    //     thread::spawn(move || {
    //         c.set(i); // Cell 不是 Sync
    //     });
    // }

    // ✅ 使用 AtomicUsize（Sync）
    use std::sync::atomic::AtomicUsize;
    let atomic = Arc::new(AtomicUsize::new(0));

    let mut handles = vec![];
    for i in 0..10 {
        let a = atomic.clone();
        handles.push(thread::spawn(move || {
            a.fetch_add(1, Ordering::Relaxed);
        }));
    }

    for h in handles {
        h.join().unwrap();
    }

    assert_eq!(atomic.load(Ordering::Relaxed), 10);
}
```

### 2.3 自动推导规则

Rust 编译器自动推导 Send 和 Sync：

```rust
// 自动 Send + Sync
struct Point { x: i32, y: i32 }

// 自动 !Send + !Sync（因为包含原始指针）
struct RawData { ptr: *mut u8, len: usize }

// 手动实现，仅当 T: Send + Sync 时
struct Container<T> { data: T }

unsafe impl<T: Send> Send for Container<T> {}
unsafe impl<T: Sync> Sync for Container<T> {}

// 使用 Negative impl (Rust 1.75+)
struct NonSendData { _marker: PhantomData<*const ()> }

impl !Send for NonSendData {}
impl !Sync for NonSendData {}
```

### 2.4 手动实现示例

```rust
use std::sync::atomic::{AtomicPtr, Ordering};
use std::ptr::NonNull;
use std::marker::PhantomData;

/// 线程安全的无锁栈节点
pub struct Node<T> {
    data: T,
    next: AtomicPtr<Node<T>>,
}

/// 无锁栈 - 仅当 T: Send 时才是 Send
/// 因为栈可能被发送到其他线程，弹出元素到另一线程
pub struct LockFreeStack<T> {
    head: AtomicPtr<Node<T>>,
    _marker: PhantomData<T>,
}

/// # Safety
/// LockFreeStack 可以发送到其他线程，因为：
/// 1. 所有操作都是原子的
/// 2. 只要 T: Send，元素转移就是安全的
unsafe impl<T: Send> Send for LockFreeStack<T> {}

/// # Safety
/// LockFreeStack 可以在线程间共享，因为：
/// 1. 所有操作都是原子操作
/// 2. 内部没有使用线程不安全的数据结构
unsafe impl<T: Send + Sync> Sync for LockFreeStack<T> {}

impl<T> LockFreeStack<T> {
    pub fn new() -> Self {
        Self {
            head: AtomicPtr::new(std::ptr::null_mut()),
            _marker: PhantomData,
        }
    }

    pub fn push(&self, data: T) {
        let new_node = Box::into_raw(Box::new(Node {
            data,
            next: AtomicPtr::new(std::ptr::null_mut()),
        }));

        loop {
            let head = self.head.load(Ordering::Acquire);
            unsafe {
                (*new_node).next.store(head, Ordering::Relaxed);
            }

            match self.head.compare_exchange(
                head,
                new_node,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(_) => continue,
            }
        }
    }

    pub fn pop(&self) -> Option<T> {
        loop {
            let head = self.head.load(Ordering::Acquire);
            if head.is_null() {
                return None;
            }

            let next = unsafe { (*head).next.load(Ordering::Acquire) };

            match self.head.compare_exchange(
                head,
                next,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => {
                    let node = unsafe { Box::from_raw(head) };
                    return Some(node.data);
                }
                Err(_) => continue,
            }
        }
    }
}

impl<T> Drop for LockFreeStack<T> {
    fn drop(&mut self) {
        while self.pop().is_some() {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use std::thread;

    #[test]
    fn test_concurrent_push_pop() {
        let stack = Arc::new(LockFreeStack::new());
        let mut handles = vec![];

        // 多个线程 push
        for i in 0..100 {
            let s = stack.clone();
            handles.push(thread::spawn(move || {
                s.push(i);
            }));
        }

        for h in handles {
            h.join().unwrap();
        }

        // 验证所有元素都存在
        let mut count = 0;
        while stack.pop().is_some() {
            count += 1;
        }
        assert_eq!(count, 100);
    }
}
```

---

## 3. 内部可变性模式

### 3.1 RefCell 与线程安全

RefCell 提供运行时借用检查，但不是线程安全的：

```rust
use std::cell::RefCell;
use std::rc::Rc;

fn refcell_single_thread() {
    let data = Rc::new(RefCell::new(vec![1, 2, 3]));

    {
        let mut mut_ref = data.borrow_mut();
        mut_ref.push(4);
    } // 可变借用在这里释放

    {
        let immut_ref = data.borrow();
        println!("{:?}", *immut_ref);
    }

    // 运行时 panic（不是数据竞争）
    // let _ref1 = data.borrow_mut();
    // let _ref2 = data.borrow(); // panic!
}
```

### 3.2 Mutex 详解

```rust
use std::sync::{Arc, Mutex, MutexGuard};
use std::thread;
use std::time::Duration;
use std::ops::Deref;

/// 线程安全的计数器
pub struct ThreadSafeCounter {
    value: Mutex<i64>,
}

impl ThreadSafeCounter {
    pub fn new() -> Self {
        Self { value: Mutex::new(0) }
    }

    pub fn increment(&self) -> i64 {
        let mut guard = self.value.lock().unwrap();
        *guard += 1;
        *guard
    }

    pub fn get(&self) -> i64 {
        *self.value.lock().unwrap()
    }

    /// 尝试获取锁，带超时
    pub fn try_increment(&self, timeout: Duration) -> Option<i64> {
        match self.value.try_lock_for(timeout) {
            Ok(mut guard) => {
                *guard += 1;
                Some(*guard)
            }
            Err(_) => None,
        }
    }
}

/// 使用 parking_lot 的高性能 Mutex
use parking_lot::{Mutex as PLMutex, MutexGuard as PLMutexGuard};

pub struct FastCounter {
    value: PLMutex<i64>,
}

impl FastCounter {
    pub fn new() -> Self {
        Self { value: PLMutex::new(0) }
    }

    pub fn increment(&self) -> i64 {
        let mut guard = self.value.lock();
        *guard += 1;
        *guard
    }
}

/// 使用 MutexGuard 进行 RAII 模式
pub struct ThreadSafeVec<T> {
    inner: Mutex<Vec<T>>,
}

impl<T> ThreadSafeVec<T> {
    pub fn new() -> Self {
        Self { inner: Mutex::new(Vec::new()) }
    }

    pub fn push(&self, item: T) {
        self.inner.lock().unwrap().push(item);
    }

    /// 返回一个保护的范围，在闭包执行期间持有锁
    pub fn with<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut Vec<T>) -> R,
    {
        let mut guard = self.inner.lock().unwrap();
        f(&mut *guard)
    }

    /// 尝试操作，如果锁不可用则立即返回
    pub fn try_with<F, R>(&self, f: F) -> Option<R>
    where
        F: FnOnce(&mut Vec<T>) -> R,
    {
        self.inner.try_lock().ok().map(|mut guard| f(&mut *guard))
    }
}

// 实际应用示例：线程安全的配置管理
use std::collections::HashMap;

pub struct ConfigManager {
    configs: Mutex<HashMap<String, String>>,
    version: AtomicU64,
}

impl ConfigManager {
    pub fn new() -> Self {
        Self {
            configs: Mutex::new(HashMap::new()),
            version: AtomicU64::new(0),
        }
    }

    pub fn set(&self, key: String, value: String) {
        let mut configs = self.configs.lock().unwrap();
        configs.insert(key, value);
        self.version.fetch_add(1, Ordering::Release);
    }

    pub fn get(&self, key: &str) -> Option<String> {
        self.configs.lock().unwrap().get(key).cloned()
    }

    pub fn version(&self) -> u64 {
        self.version.load(Ordering::Acquire)
    }
}
```

### 3.3 RwLock 详解

```rust
use std::sync::{Arc, RwLock, RwLockReadGuard, RwLockWriteGuard};
use std::collections::HashMap;

/// 高性能缓存实现
pub struct ConcurrentCache<K, V> {
    data: RwLock<HashMap<K, V>>,
    stats: RwLock<CacheStats>,
}

#[derive(Default)]
struct CacheStats {
    hits: u64,
    misses: u64,
    evictions: u64,
}

impl<K: Eq + std::hash::Hash + Clone, V: Clone> ConcurrentCache<K, V> {
    pub fn new() -> Self {
        Self {
            data: RwLock::new(HashMap::new()),
            stats: RwLock::new(CacheStats::default()),
        }
    }

    /// 获取值 - 使用读锁
    pub fn get(&self, key: &K) -> Option<V> {
        // 获取读锁（多个读者可以并发）
        let data = self.data.read().unwrap();
        let result = data.get(key).cloned();
        drop(data); // 显式释放读锁

        // 更新统计信息 - 使用写锁
        let mut stats = self.stats.write().unwrap();
        if result.is_some() {
            stats.hits += 1;
        } else {
            stats.misses += 1;
        }

        result
    }

    /// 插入值 - 使用写锁
    pub fn insert(&self, key: K, value: V) {
        let mut data = self.data.write().unwrap();
        data.insert(key, value);
    }

    /// 批量读取 - 使用单个读锁
    pub fn get_batch(&self, keys: &[K]) -> Vec<Option<V>> {
        let data = self.data.read().unwrap();
        keys.iter().map(|k| data.get(k).cloned()).collect()
    }

    /// 获取统计信息
    pub fn stats(&self) -> (u64, u64, u64) {
        let stats = self.stats.read().unwrap();
        (stats.hits, stats.misses, stats.evictions)
    }

    /// 升级读锁到写锁（读-修改-写模式）
    pub fn compute_if_absent<F>(&self, key: K, f: F) -> V
    where
        F: FnOnce() -> V,
    {
        // 首先尝试读
        {
            let data = self.data.read().unwrap();
            if let Some(value) = data.get(&key) {
                return value.clone();
            }
        }

        // 需要写入
        let mut data = self.data.write().unwrap();
        // 双重检查（可能其他线程已经插入）
        if let Some(value) = data.get(&key) {
            return value.clone();
        }

        let value = f();
        data.insert(key, value.clone());
        value
    }
}

// 使用 parking_lot 的 RwLock（更快，不 poison）
use parking_lot::{RwLock as PLRwLock, RwLockReadGuard as PLReadGuard};

pub struct FastConcurrentCache<K, V> {
    data: PLRwLock<HashMap<K, V>>,
}

impl<K: Eq + std::hash::Hash + Clone, V: Clone> FastConcurrentCache<K, V> {
    pub fn get(&self, key: &K) -> Option<V> {
        self.data.read().get(key).cloned()
    }

    pub fn insert(&self, key: K, value: V) {
        self.data.write().insert(key, value);
    }
}
```

### 3.4 延迟初始化模式 (Rust 1.94)

Rust 1.94 为 `LazyLock` 和 `LazyCell` 引入了新的访问方法，简化了线程安全延迟初始化：

```rust
use std::sync::LazyLock;
use std::sync::atomic::{AtomicU64, Ordering};

/// 延迟初始化的全局状态
static GLOBAL_STATE: LazyLock<GlobalState> = LazyLock::new(|| {
    println!("Initializing global state...");
    GlobalState::new()
});

pub struct GlobalState {
    counter: AtomicU64,
    name: String,
}

impl GlobalState {
    fn new() -> Self {
        Self {
            counter: AtomicU64::new(0),
            name: "Global".to_string(),
        }
    }

    pub fn increment(&self) -> u64 {
        self.counter.fetch_add(1, Ordering::Relaxed)
    }

    pub fn get_count(&self) -> u64 {
        // Rust 1.94: 使用 get() 获取引用
        self.counter.load(Ordering::Relaxed)
    }
}

/// 使用 LazyLock 的线程安全单例模式
pub fn get_global_state() -> &'static GlobalState {
    // Rust 1.94 新 API：显式 get() 方法
    GLOBAL_STATE.get()
}

/// 在 Scoped 线程中使用 LazyLock
fn scoped_with_lazy() {
    use std::thread;

    thread::scope(|s| {
        for i in 0..5 {
            s.spawn(move || {
                // 所有线程共享同一个延迟初始化的状态
                let state = GLOBAL_STATE.get();
                let count = state.increment();
                println!("Thread {}: count = {}", i, count);
            });
        }
    });
}
```

### 线程局部存储中的 LazyCell

```rust
use std::cell::LazyCell;
use std::thread;

/// 线程局部的延迟初始化
fn thread_local_lazy() {
    thread::spawn(|| {
        // 每个线程有自己的延迟初始化数据
        let thread_data = LazyCell::new(|| {
            println!("Initializing thread-local data");
            vec![1, 2, 3, 4, 5]
        });

        // Rust 1.94: 使用 get() 访问
        let data = thread_data.get();
        println!("Thread data: {:?}", data);

        // 注意：在闭包内使用 LazyCell 需要可变引用才能修改
        // 如果要修改，需要将 LazyCell 包装在 RefCell 中
    }).join().unwrap();
}
```

### 3.5 原子类型

```rust
use std::sync::atomic::{
    AtomicUsize, AtomicU64, AtomicBool, AtomicPtr,
    Ordering, fence
};
use std::ptr::null_mut;

/// 使用原子操作的高性能计数器
pub struct AtomicCounter {
    count: AtomicU64,
}

impl AtomicCounter {
    pub fn new() -> Self {
        Self { count: AtomicU64::new(0) }
    }

    /// 增加并获取新值
    pub fn increment(&self) -> u64 {
        self.count.fetch_add(1, Ordering::Relaxed) + 1
    }

    /// 获取当前值
    pub fn get(&self) -> u64 {
        self.count.load(Ordering::Acquire)
    }

    /// 条件增加
    pub fn fetch_max(&self, value: u64) -> u64 {
        loop {
            let current = self.count.load(Ordering::Relaxed);
            if current >= value {
                return current;
            }
            match self.count.compare_exchange(
                current, value, Ordering::Release, Ordering::Relaxed
            ) {
                Ok(_) => return current,
                Err(actual) => {
                    if actual >= value {
                        return actual;
                    }
                }
            }
        }
    }
}

/// 原子布尔标志
pub struct AtomicFlag {
    flag: AtomicBool,
}

impl AtomicFlag {
    pub fn new() -> Self {
        Self { flag: AtomicBool::new(false) }
    }

    /// 尝试设置标志，如果已设置则返回 false
    pub fn try_set(&self) -> bool {
        self.flag.compare_exchange(
            false, true, Ordering::Acquire, Ordering::Relaxed
        ).is_ok()
    }

    /// 清除标志
    pub fn clear(&self) {
        self.flag.store(false, Ordering::Release);
    }

    /// 检查标志
    pub fn is_set(&self) -> bool {
        self.flag.load(Ordering::Relaxed)
    }
}

/// 原子指针用于无锁数据结构
pub struct AtomicStack<T> {
    head: AtomicPtr<Node<T>>,
}

struct Node<T> {
    data: T,
    next: *mut Node<T>,
}

impl<T> AtomicStack<T> {
    pub fn new() -> Self {
        Self { head: AtomicPtr::new(null_mut()) }
    }

    pub fn push(&self, data: T) {
        let new_node = Box::into_raw(Box::new(Node {
            data,
            next: null_mut(),
        }));

        loop {
            let head = self.head.load(Ordering::Acquire);
            unsafe { (*new_node).next = head; }

            if self.head.compare_exchange(
                head, new_node, Ordering::Release, Ordering::Relaxed
            ).is_ok() {
                break;
            }
        }
    }

    pub fn pop(&self) -> Option<T> {
        loop {
            let head = self.head.load(Ordering::Acquire);
            if head.is_null() {
                return None;
            }

            let next = unsafe { (*head).next };

            if self.head.compare_exchange(
                head, next, Ordering::Release, Ordering::Relaxed
            ).is_ok() {
                let node = unsafe { Box::from_raw(head) };
                return Some(node.data);
            }
        }
    }
}

/// 内存屏障的使用
pub struct SynchronizedData<T> {
    data: std::cell::UnsafeCell<T>,
    ready: AtomicBool,
}

unsafe impl<T: Send> Send for SynchronizedData<T> {}
unsafe impl<T: Send + Sync> Sync for SynchronizedData<T> {}

impl<T> SynchronizedData<T> {
    pub fn new(data: T) -> Self {
        Self {
            data: std::cell::UnsafeCell::new(data),
            ready: AtomicBool::new(false),
        }
    }

    /// 写入数据并设置就绪标志
    pub fn store(&self, data: T) {
        unsafe {
            *self.data.get() = data;
        }
        // 使用 Release 序确保之前的写入对其他线程可见
        self.ready.store(true, Ordering::Release);
    }

    /// 等待并读取数据
    pub fn load(&self) -> Option<&T> {
        // 使用 Acquire 序确保看到完整的写入
        if self.ready.load(Ordering::Acquire) {
            Some(unsafe { &*self.data.get() })
        } else {
            None
        }
    }
}
```

### 3.5 性能对比与选择

```rust
use std::time::{Duration, Instant};
use std::sync::{Arc, Mutex, RwLock};
use std::sync::atomic::{AtomicUsize, Ordering};

/// 性能基准测试框架
pub fn benchmark_locks() {
    const ITERATIONS: usize = 1_000_000;
    const THREADS: usize = 8;

    // Mutex 基准
    let mutex_data = Arc::new(Mutex::new(0usize));
    let start = Instant::now();

    let handles: Vec<_> = (0..THREADS).map(|_| {
        let data = mutex_data.clone();
        std::thread::spawn(move || {
            for _ in 0..ITERATIONS / THREADS {
                let mut guard = data.lock().unwrap();
                *guard += 1;
            }
        })
    }).collect();

    for h in handles { h.join().unwrap(); }
    let mutex_time = start.elapsed();

    // Atomic 基准
    let atomic_data = Arc::new(AtomicUsize::new(0));
    let start = Instant::now();

    let handles: Vec<_> = (0..THREADS).map(|_| {
        let data = atomic_data.clone();
        std::thread::spawn(move || {
            for _ in 0..ITERATIONS / THREADS {
                data.fetch_add(1, Ordering::Relaxed);
            }
        })
    }).collect();

    for h in handles { h.join().unwrap(); }
    let atomic_time = start.elapsed();

    println!("Mutex: {:?}", mutex_time);
    println!("Atomic: {:?}", atomic_time);
    println!("Speedup: {:.2}x", mutex_time.as_secs_f64() / atomic_time.as_secs_f64());
}

/// 选择指南
///
/// | 场景 | 推荐类型 | 原因 |
/// |------|---------|------|
/// | 简单计数器 | AtomicUsize | 无锁，最快 |
/// | 复杂数据结构 | Mutex | 独占访问保证 |
/// | 读多写少 | RwLock | 并发读 |
/// | 批量操作 | Mutex | 减少锁竞争 |
/// | 标志位 | AtomicBool | 内存效率 |
```

---

## 4. 锁的类型与实现

### 4.1 操作系统互斥锁

（限于篇幅，继续扩展下一部分...）

继续下一部分？
