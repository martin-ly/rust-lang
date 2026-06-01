// [来源: Rust Atomics and Locks / Rust Reference]
//! 原子操作与内存排序深度专题
//! atomic operation and memory ordering
//! ## 内存排序概述
//! ## memory ordering
//! 决定了一个线程的写入何时对其他线程可见。
//! thread to its thread 。
//! ### 五种内存排序
//! ### memory ordering
//! ### 五种memory ordering
//! | 排序 | 强度 | 用途 |
//! | ordering | | purpose |
//! | ordering | 强度 | purpose |
//! ### x86-64 vs ARM64 差异
//! ### x86-64 vs ARM64 difference
//! - **x86-64**: 具有强内存模型（TSO, Total Store Order），大多数原子操作隐式带有 Acquire/Release 语义。
//! - **x86-64**: has memory model （TSO, Total Store Order），atomic operation Acquire/Release 。

use std::sync::atomic::{AtomicBool, AtomicPtr, AtomicUsize, Ordering};
#[cfg(test)]
use std::sync::Arc;
#[cfg(test)]
use std::thread;

/// 返回在不同内存序下的自增结果（用于展示 API，可编译通过）。
/// Returns在不同内存序下的自增结果（用于展示 API，可编译通过）。
/// in memory under result （ API，）。
pub fn relaxed_increment(counter: &AtomicUsize) -> usize {
    counter.fetch_add(1, Ordering::Relaxed)
}

pub fn seqcst_increment(counter: &AtomicUsize) -> usize {
    counter.fetch_add(1, Ordering::SeqCst)
}

// ========== 示例 1: Relaxed 计数器 ==========
/// `Ordering::Relaxed` 仅保证原子性，不保证顺序性。
/// `Ordering::Relaxed` ，order 。
/// 适用场景：简单的计数器（如统计请求次数），
/// scenario ：simple （），
/// 只要最终计数正确，中间状态的可见性不重要。
/// ultimately ，in state important 。
/// 编译as `ldaddal` orcirculation `ldxr`/`stxr`。
pub struct RelaxedCounter {
    value: AtomicUsize,
}

impl Default for RelaxedCounter {
    fn default() -> Self {
        Self::new()
    }
}

impl RelaxedCounter {
    /// 创建新计数器
    /// Creates新计数器
    pub const fn new() -> Self {
        Self {
            value: AtomicUsize::new(0),
        }
    }

    /// 自增并返回旧值
    /// Increments并返回旧值
    /// and
    pub fn increment(&self) -> usize {
        self.value.fetch_add(1, Ordering::Relaxed)
    }

    /// 获取当前值（可能不是绝对最新）
    /// Gets当前值（可能不是绝对最新）
    /// when before （may to ）
    pub fn get(&self) -> usize {
        self.value.load(Ordering::Relaxed)
    }
}

// ========== 示例 2: Acquire-Release 标志位 ==========
/// `Release` + `Acquire` 用于建立 happens-before 关系。
/// 场景：一个线程初始化数据，另一个线程读取数据。
/// scenario ：thread ，thread 。
/// 使用 `store(_, Release)` 发布数据，
/// `store(_, Release)` ，
/// # 原理
/// # principle
/// #
/// 线程 A: 写入数据 -> store(flag, Release)
/// 线程 B: load(flag, Acquire) -> 读取数据
/// x86 强模型under，`Release`/`Acquire` 通常编译as普通 `mov`，
/// `store(_, Release)` 编译as `stlr`（Store-Release），
/// `load(_, Acquire)` 编译as `ldar`（Load-Acquire）。
pub struct AcqRelFlag {
    ready: AtomicBool,
    data: AtomicUsize,
}

impl Default for AcqRelFlag {
    fn default() -> Self {
        Self::new()
    }
}

impl AcqRelFlag {
    /// 创建未就绪的标志
    /// Creates未就绪的标志
    /// mark
    pub const fn new() -> Self {
        Self {
            ready: AtomicBool::new(false),
            data: AtomicUsize::new(0),
        }
    }

    /// 发布数据（线程 A）
    /// （thread A）
    ///
    /// 调用者必须确保 `data` 在 `store` 之前已完成所有初始化写入。
    /// must `data` in `store` 's before all 。
    pub fn publish(&self, value: usize) {
        self.data.store(value, Ordering::Relaxed);
        // Release 保证：此 store 之前的所有写入对 Acquire 读取可见
        self.ready.store(true, Ordering::Release);
    }

    /// 等待并获取数据（线程 B）
    /// Waits for并获取数据（线程 B）
    /// etc. and （thread B）
    pub fn wait_and_get(&self) -> Option<usize> {
        // Acquire 保证：如果看到了 true，则能看到 publish 中 data 的写入
        if self.ready.load(Ordering::Acquire) {
            Some(self.data.load(Ordering::Relaxed))
        } else {
            None
        }
    }
}

// ========== 示例 3: AcqRel 读-改-写（自旋锁） ==========
/// 适用于读-改-写操作（如 `fetch_add`, `compare_exchange`）。
/// `lock cmpxchg` 用于 `compare_exchange`。
/// # ARM64
/// `ldaxr`/`stlxr` 循环实现 compare-and-swap。
pub struct SimpleSpinlock {
    locked: AtomicBool,
}

impl Default for SimpleSpinlock {
    fn default() -> Self {
        Self::new()
    }
}

impl SimpleSpinlock {
    /// 创建未锁定的自旋锁
    /// Creates未锁定的自旋锁
    /// lock spinlock
    pub const fn new() -> Self {
        Self {
            locked: AtomicBool::new(false),
        }
    }

    /// 尝试获取锁（自旋等待）
    /// Attempts to获取锁（自旋等待）
    /// lock （etc. ）
    /// 尝试Getlock（自旋Wait）
    /// Attempts toGetlock（自旋Wait）
    pub fn lock(&self) {
        while self
            .locked
            .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
            .is_err()
        {
            // 自旋等待，可使用 yield 降低 CPU 占用
            while self.locked.load(Ordering::Relaxed) {
                std::hint::spin_loop();
            }
        }
    }

    /// 释放锁
    /// Releases锁
    /// lock
    /// # Safety
    ///
    /// 调用者必须确实持有锁。
    /// must lock 。
    pub unsafe fn unlock(&self) {
        self.locked.store(false, Ordering::Release);
    }
}

// ========== 示例 4: SeqCst 全局顺序 ==========
/// 或使用 `mov` + `mfence`。
/// oruse `mov` + `mfence`。
/// # ARM64
pub struct SeqCstBarrier {
    flag: AtomicBool,
}

impl Default for SeqCstBarrier {
    fn default() -> Self {
        Self::new()
    }
}

impl SeqCstBarrier {
    /// 创建新屏障
    /// Creates新屏障
    /// barrier
    pub const fn new() -> Self {
        Self {
            flag: AtomicBool::new(false),
        }
    }

    pub fn set(&self) {
        self.flag.store(true, Ordering::SeqCst);
    }

    pub fn check(&self) -> bool {
        self.flag.load(Ordering::SeqCst)
    }
}

// ========== 示例 5: AtomicPtr 与无锁数据结构概念（无锁队列节点） ==========
/// # 内存安全警告
/// # memorysafewarning
/// # memory safety warning
/// 生产环境请使用 `crossbeam-queue`。
/// environment `crossbeam-queue`。
pub struct AtomicNode<T> {
    next: AtomicPtr<AtomicNode<T>>,
    value: std::mem::MaybeUninit<T>,
}

impl<T> AtomicNode<T> {
    /// 创建新节点
    /// Creates新节点
    /// node
    pub fn new(value: T) -> Self {
        Self {
            next: AtomicPtr::new(std::ptr::null_mut()),
            value: std::mem::MaybeUninit::new(value),
        }
    }

    /// 获取 next 指针（Acquire，建立 happens-before）
    /// Gets next 指针（Acquire，建立 happens-before）
    /// Get next pointer（Acquire，建立 happens-before）
    pub fn next_acquire(&self) -> *mut AtomicNode<T> {
        self.next.load(Ordering::Acquire)
    }

    /// 设置 next 指针（Release，发布节点）
    /// Sets next 指针（Release，发布节点）
    /// next pointer （Release，node ）
    /// # Safety
    ///
    pub unsafe fn set_next_release(&self, new_next: *mut AtomicNode<T>) {
        self.next.store(new_next, Ordering::Release);
    }

    /// # Safety
    ///
    /// 调用者必须处理 ABA 问题和内存生命周期。
    /// must ABA problem and memory lifetime 。
    pub unsafe fn compare_exchange_next(
        &self,
        current: *mut AtomicNode<T>,
        new: *mut AtomicNode<T>,
    ) -> Result<*mut AtomicNode<T>, *mut AtomicNode<T>> {
        self.next
            .compare_exchange(current, new, Ordering::AcqRel, Ordering::Acquire)
    }
}

/// 概念性无锁队列（单生产者单消费者简化版）
/// concept lock-free queue （single-producer single-consumer ）
/// 此实现仅用于教学，展示 Acquire/Release 如何构建 happens-before 链。
/// this ， Acquire/Release happens-before 。
/// 不支持多生产者/多消费者的并发入队/出队。
/// /concurrency /。
pub struct ConceptualLockFreeQueue<T> {
    head: AtomicPtr<AtomicNode<T>>,
    tail: AtomicPtr<AtomicNode<T>>,
}

impl<T> ConceptualLockFreeQueue<T> {
    /// 创建空队列
    /// Creates空队列
    /// Createsemptyqueue
    pub fn new() -> Self {
        let dummy = Box::into_raw(Box::new(AtomicNode {
            next: AtomicPtr::new(std::ptr::null_mut()),
            value: std::mem::MaybeUninit::uninit(),
        }));
        Self {
            head: AtomicPtr::new(dummy),
            tail: AtomicPtr::new(dummy),
        }
    }

    /// 入队（概念演示，非线程安全的多生产者版本）
    /// （concept demonstration ，thread-safe this ）
    ///
    /// 真实实现需要循环 CAS 和内存回收。
    /// real circulation CAS and memory 。
    pub unsafe fn enqueue(&self, value: T) {
        let new_node = Box::into_raw(Box::new(AtomicNode::new(value)));
        let tail = self.tail.load(Ordering::Relaxed);
        // Release: 保证 value 的写入在 next 设置前完成
        unsafe {
            (*tail).next.store(new_node, Ordering::Release);
        }
        // Release: 保证 next 的写入在 tail 更新前完成
        self.tail.store(new_node, Ordering::Release);
    }

    /// 出队（概念演示）
    /// （concept demonstration ）
    ///
    /// 调用者必须确保队列非空或正确处理并发。
    /// must or concurrency 。
    pub unsafe fn dequeue(&self) -> Option<T> {
        let head = self.head.load(Ordering::Relaxed);
        let next = unsafe { (*head).next.load(Ordering::Acquire) };
        if next.is_null() {
            return None;
        }
        self.head.store(next, Ordering::Relaxed);
        // 转移所有权（概念上）
        let value = unsafe { std::ptr::read((*next).value.as_ptr()) };
        let _ = unsafe { Box::from_raw(head) }; // dummy 或旧 head
        Some(value)
    }
}

impl<T> Drop for ConceptualLockFreeQueue<T> {
    fn drop(&mut self) {
        unsafe {
            let mut current = self.head.load(Ordering::Relaxed);
            let mut is_first = true;
            while !current.is_null() {
                let next = (*current).next.load(Ordering::Relaxed);
                if !is_first {
                    std::ptr::drop_in_place((*current).value.as_mut_ptr());
                }
                let _ = Box::from_raw(current);
                current = next;
                is_first = false;
            }
        }
    }
}

impl<T> Default for ConceptualLockFreeQueue<T> {
    fn default() -> Self {
        Self::new()
    }
}

// ========== 平台差异总结 ==========
/// 打印内存模型平台差异说明
/// Prints内存模型平台差异说明
/// memory model platform explain
pub fn print_arch_memory_model_differences() {
    let arch = if cfg!(target_arch = "x86_64") {
        "x86-64"
    } else if cfg!(target_arch = "aarch64") {
        "ARM64"
    } else {
        "其他架构"
    };
    println!("当前架构: {}", arch);
    println!(
        r#"
内存模型差异总结:
- x86-64 (TSO 强模型):
  * 所有 Store 按程序顺序执行，Store-Load 是唯一可能重排序的地方
  * Acquire/Release 通常不生成额外屏障指令（除编译器屏障）
  * Relaxed 计数器依然编译为 lock 前缀指令（保证原子性）
  * SeqCst 需要 mfence 或 xchg

- ARM64 (弱模型):
  * 所有内存操作都可能重排序（Load-Load, Load-Store, Store-Load, Store-Store）
  * Acquire/Release 必须生成显式屏障: ldar / stlr
  * Relaxed 仅保证原子性，无顺序保证
  * SeqCst 需要 dmb ish 全屏障
"#
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_relaxed_counter() {
        let counter = Arc::new(RelaxedCounter::new());
        let mut handles = vec![];

        for _ in 0..4 {
            let c = Arc::clone(&counter);
            handles.push(thread::spawn(move || {
                for _ in 0..1000 {
                    c.increment();
                }
            }));
        }

        for h in handles {
            h.join().unwrap();
        }

        assert_eq!(counter.get(), 4000);
    }

    #[test]
    fn test_acqrel_flag() {
        let flag = Arc::new(AcqRelFlag::new());
        let flag2 = Arc::clone(&flag);

        let producer = thread::spawn(move || {
            flag2.publish(42);
        });

        // 等待生产者完成
        producer.join().unwrap();

        // 此时一定能看到 42
        assert_eq!(flag.wait_and_get(), Some(42));
    }

    #[test]
    fn test_spinlock() {
        let lock = Arc::new(SimpleSpinlock::new());
        let data = Arc::new(AtomicUsize::new(0));
        let mut handles = vec![];

        for _ in 0..4 {
            let l = Arc::clone(&lock);
            let d = Arc::clone(&data);
            handles.push(thread::spawn(move || {
                l.lock();
                // 临界区
                let old = d.load(Ordering::Relaxed);
                d.store(old + 1, Ordering::Relaxed);
                unsafe { l.unlock() };
            }));
        }

        for h in handles {
            h.join().unwrap();
        }

        assert_eq!(data.load(Ordering::Relaxed), 4);
    }

    #[test]
    fn test_seqcst_global_ordering() {
        let barrier = Arc::new(SeqCstBarrier::new());
        let b2 = Arc::clone(&barrier);

        let t = thread::spawn(move || {
            b2.set();
        });

        t.join().unwrap();
        assert!(barrier.check());
    }

    #[test]
    fn test_atomic_ptr_concept() {
        let node = AtomicNode::new(100);
        let node2 = Box::into_raw(Box::new(AtomicNode::new(200)));

        unsafe {
            node.set_next_release(node2);
            let loaded = node.next_acquire();
            assert!(!loaded.is_null());
            // 清理
            let _ = Box::from_raw(node2);
        }
    }

    #[test]
    fn test_conceptual_queue() {
        let q = ConceptualLockFreeQueue::new();
        unsafe {
            q.enqueue(42);
            q.enqueue(100);
            assert_eq!(q.dequeue(), Some(42));
            assert_eq!(q.dequeue(), Some(100));
            assert_eq!(q.dequeue(), None);
        }
    }

    #[test]
    fn test_arch_info() {
        print_arch_memory_model_differences();
    }
}
