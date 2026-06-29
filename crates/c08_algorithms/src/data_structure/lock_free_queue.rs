// [来源: Michael & Scott 1996 / Rust Atomics and Locks / crossbeam-epoch]
//! 无锁队列实现 (Michael-Scott Queue) —— 基于 `crossbeam-epoch` 的内存安全版本
//!
//! ## 核心算法
//!
//! 1. `enqueue`：将新节点 CAS 到 `tail.next`；成功后（或帮助其他线程后）推进 `tail`。
//! 2. `dequeue`：移动 `head` 到 `head.next`，返回原 `head.next` 的数据；旧哨兵节点延迟释放。
//!
//! ## 内存安全
//!
//! - 使用 `crossbeam-epoch` 的 `Guard` 保护所有对共享节点的读取。
//! - 退役节点（被弹出的哨兵或已出队元素）通过 `defer_unchecked` 延迟释放。
//! - 哨兵节点保证 `head` 与 `tail` 永不为空，简化边界条件。
//!
//! ## 复杂度
//!
//! - `enqueue` / `dequeue`：均摊 **O(1)**，最坏 CAS 重试次数取决于竞争。

use std::sync::atomic::Ordering::{Acquire, Release};

use crossbeam_epoch::{Atomic, Owned};

/// 队列节点。
struct Node<T> {
    data: Option<T>,
    next: Atomic<Node<T>>,
}

impl<T> Node<T> {
    fn new(data: T) -> Self {
        Self {
            data: Some(data),
            next: Atomic::null(),
        }
    }

    fn sentinel() -> Self {
        Self {
            data: None,
            next: Atomic::null(),
        }
    }
}

/// 无锁队列 (Michael-Scott Queue)。
///
/// 线程安全的无锁 FIFO 队列，基于 `crossbeam-epoch` 实现安全内存回收。
///
/// # 示例
///
/// ```
/// use c08_algorithms::data_structure::lock_free_queue::LockFreeQueue;
///
/// let queue = LockFreeQueue::new();
/// queue.enqueue(1);
/// queue.enqueue(2);
/// assert_eq!(queue.dequeue(), Some(1));
/// assert_eq!(queue.dequeue(), Some(2));
/// assert_eq!(queue.dequeue(), None);
/// ```
pub struct LockFreeQueue<T> {
    head: Atomic<Node<T>>,
    tail: Atomic<Node<T>>,
}

unsafe impl<T: Send> Send for LockFreeQueue<T> {}
unsafe impl<T: Send> Sync for LockFreeQueue<T> {}

impl<T> LockFreeQueue<T> {
    /// 创建新的空队列。
    pub fn new() -> Self {
        let sentinel = Owned::new(Node::sentinel());
        let guard = &crossbeam_epoch::pin();
        let shared = sentinel.into_shared(guard);
        Self {
            head: Atomic::from(shared),
            tail: Atomic::from(shared),
        }
    }

    /// 将元素加入队列尾部。
    pub fn enqueue(&self, data: T) {
        let guard = &crossbeam_epoch::pin();
        let new = Owned::new(Node::new(data)).into_shared(guard);

        loop {
            let tail = self.tail.load(Acquire, guard);
            // SAFETY: tail 仅在初始化时或为已发布的节点，故非空且有效。
            let tail_ref = unsafe { tail.deref() };
            let next = tail_ref.next.load(Acquire, guard);

            // 再次确认 tail 未改变。
            if tail != self.tail.load(Acquire, guard) {
                continue;
            }

            if next.is_null() {
                // 尝试将新节点链接到尾节点。
                if tail_ref
                    .next
                    .compare_exchange(next, new, Release, Acquire, guard)
                    .is_ok()
                {
                    // 尝试推进 tail；即使失败，后续操作会帮助推进。
                    let _ = self
                        .tail
                        .compare_exchange(tail, new, Release, Acquire, guard);
                    return;
                }
            } else {
                // 帮助推进落后的 tail。
                let _ = self
                    .tail
                    .compare_exchange(tail, next, Release, Acquire, guard);
            }
        }
    }

    /// 从队列头部移除元素；若队列为空返回 `None`。
    pub fn dequeue(&self) -> Option<T> {
        let guard = &crossbeam_epoch::pin();

        loop {
            let head = self.head.load(Acquire, guard);
            // SAFETY: head 永不为空（哨兵节点）。
            let head_ref = unsafe { head.deref() };
            let tail = self.tail.load(Acquire, guard);
            let next = head_ref.next.load(Acquire, guard);

            if head != self.head.load(Acquire, guard) {
                continue;
            }

            if head == tail {
                if next.is_null() {
                    return None;
                }
                // 帮助推进落后的 tail。
                let _ = self
                    .tail
                    .compare_exchange(tail, next, Release, Acquire, guard);
            } else {
                // next 非空，尝试移动 head。
                if self
                    .head
                    .compare_exchange(head, next, Release, Acquire, guard)
                    .is_ok()
                {
                    unsafe {
                        // next 成为新的哨兵；从中取出数据后它仍保留在队列中。
                        let data = (&mut *(next.as_raw() as *mut Node<T>)).data.take();
                        // 旧 head 哨兵延迟释放。
                        guard.defer_unchecked(move || {
                            let _ = head.into_owned();
                        });
                        return data;
                    }
                }
            }
        }
    }

    /// 检查队列是否为空。
    ///
    /// 注意：该结果是瞬态的，并发 `enqueue` 可能立即改变它。
    pub fn is_empty(&self) -> bool {
        let guard = &crossbeam_epoch::pin();
        let head = self.head.load(Acquire, guard);
        let head_ref = unsafe { head.deref() };
        let tail = self.tail.load(Acquire, guard);

        if head != tail {
            return false;
        }

        head_ref.next.load(Acquire, guard).is_null()
    }
}

impl<T> Default for LockFreeQueue<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Drop for LockFreeQueue<T> {
    fn drop(&mut self) {
        while self.dequeue().is_some() {}
        // 释放最终残留的哨兵节点。
        let guard = &crossbeam_epoch::pin();
        let head = self.head.load(Acquire, guard);
        if !head.is_null() {
            unsafe {
                guard.defer_unchecked(move || {
                    let _ = head.into_owned();
                });
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use std::thread;

    #[test]
    fn test_basic_enqueue_dequeue() {
        let queue = LockFreeQueue::new();
        assert!(queue.is_empty());

        queue.enqueue(1);
        queue.enqueue(2);
        queue.enqueue(3);
        assert!(!queue.is_empty());

        assert_eq!(queue.dequeue(), Some(1));
        assert_eq!(queue.dequeue(), Some(2));
        assert_eq!(queue.dequeue(), Some(3));
        assert_eq!(queue.dequeue(), None);
        assert!(queue.is_empty());
    }

    #[test]
    fn test_fifo_order() {
        let queue = LockFreeQueue::new();
        for i in 0..100 {
            queue.enqueue(i);
        }
        for i in 0..100 {
            assert_eq!(queue.dequeue(), Some(i));
        }
    }

    #[test]
    fn test_drop() {
        let queue = LockFreeQueue::new();
        for i in 0..100 {
            queue.enqueue(i);
        }
        drop(queue);
    }

    #[test]
    fn test_concurrent_enqueue() {
        const THREADS: usize = 4;
        const OPS: usize = 1000;

        let queue = Arc::new(LockFreeQueue::new());
        let mut handles = vec![];

        for t in 0..THREADS {
            let q = Arc::clone(&queue);
            handles.push(thread::spawn(move || {
                for i in 0..OPS {
                    q.enqueue(t * OPS + i);
                }
            }));
        }

        for h in handles {
            h.join().unwrap();
        }

        let mut count = 0;
        while queue.dequeue().is_some() {
            count += 1;
        }
        assert_eq!(count, THREADS * OPS);
    }

    #[test]
    fn test_concurrent_mixed_operations() {
        const THREADS: usize = 4;
        const OPS: usize = 500;

        let queue = Arc::new(LockFreeQueue::new());
        let mut handles = vec![];

        for t in 0..THREADS {
            let q = Arc::clone(&queue);
            handles.push(thread::spawn(move || {
                for i in 0..OPS {
                    q.enqueue(t * OPS + i);
                    if i % 2 == 0 {
                        q.dequeue();
                    }
                }
            }));
        }

        for h in handles {
            h.join().unwrap();
        }

        // 验证无崩溃；剩余数量取决于调度。
        while queue.dequeue().is_some() {}
    }
}
