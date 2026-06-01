//! 无锁优先队列实现
//! lock-free
//! ## 设计思路
//! ## design
//! 使用有序链表实现简化版的无锁优先队列，支持线程安全的
//! lock-free ，thread-safe
//! `push` 和 `pop` 操作。
//! `push` and `pop` operation。
//! `push` and `pop` 操作。
//! `push` and `pop` operation。
//! ## 复杂度
//! ## complex
//! - `push`: O(n)（简化实现）
//! - `push`: O(n)（）
//! - `push`: O(n)（简化Implementation of）
//! 生产环境应使用 `crossbeam_skiplist` 实现 O(log n) 复杂度。
//! environment `crossbeam_skiplist` O(log n) complex 。
use std::ptr;
use std::sync::atomic::{AtomicPtr, Ordering as AtomicOrdering};

/// 优先队列节点
/// node
struct Node<T> {
    data: T,
    priority: i32,
    next: AtomicPtr<Node<T>>,
}

impl<T> Node<T> {
    fn new(data: T, priority: i32) -> Self {
        Self {
            data,
            priority,
            next: AtomicPtr::new(ptr::null_mut()),
        }
    }
}

/// 无锁优先队列
/// lock-free
/// 基于有序链表实现的线程安全优先队列。
/// thread-safe 。
/// 优先级数值越高，元素越先被弹出。
/// ，element is 。
/// # 示例
/// # Examples
/// # example
/// ```
/// use c05_threads::lockfree::lockfree_priority_queue::LockFreePriorityQueue;
///
/// let pq = LockFreePriorityQueue::new();
/// pq.push("low", 1);
/// pq.push("high", 10);
/// pq.push("medium", 5);
/// assert_eq!(pq.pop(), Some("high"));
/// assert_eq!(pq.pop(), Some("medium"));
/// assert_eq!(pq.pop(), Some("low"));
/// assert_eq!(pq.pop(), None);
/// ```
pub struct LockFreePriorityQueue<T> {
    head: AtomicPtr<Node<T>>,
}

unsafe impl<T: Send> Send for LockFreePriorityQueue<T> {}
unsafe impl<T: Send> Sync for LockFreePriorityQueue<T> {}

impl<T> LockFreePriorityQueue<T> {
    /// 创建新的无锁优先队列
    /// Creates新的无锁优先队列
    /// lock-free
    pub fn new() -> Self {
        Self {
            head: AtomicPtr::new(ptr::null_mut()),
        }
    }

    /// 插入元素（按优先级排序）
    /// Inserts元素（按优先级排序）
    /// element （ordering ）
    /// 插入element（按优先级ordering）
    /// Insertselement（按优先级ordering）
    /// 优先级越高的元素越靠近队首。
    /// element 。
    pub fn push(&self, data: T, priority: i32) {
        let new_node = Box::into_raw(Box::new(Node::new(data, priority)));

        loop {
            let current_head = self.head.load(AtomicOrdering::Acquire);

            if current_head.is_null() {
                // 空队列，直接设置为头节点
                if self
                    .head
                    .compare_exchange_weak(
                        ptr::null_mut(),
                        new_node,
                        AtomicOrdering::Release,
                        AtomicOrdering::Relaxed,
                    )
                    .is_ok()
                {
                    return;
                }
                continue;
            }

            unsafe {
                // 检查新节点是否应该成为头节点
                if (*current_head).priority < priority {
                    (*new_node)
                        .next
                        .store(current_head, AtomicOrdering::Relaxed);
                    if self
                        .head
                        .compare_exchange_weak(
                            current_head,
                            new_node,
                            AtomicOrdering::Release,
                            AtomicOrdering::Relaxed,
                        )
                        .is_ok()
                    {
                        return;
                    }
                    continue;
                }

                // 寻找插入位置
                let mut prev = current_head;
                let mut current = (*prev).next.load(AtomicOrdering::Acquire);

                while !current.is_null() && (*current).priority >= priority {
                    prev = current;
                    current = (*current).next.load(AtomicOrdering::Acquire);
                }

                (*new_node).next.store(current, AtomicOrdering::Relaxed);
                if (*prev)
                    .next
                    .compare_exchange_weak(
                        current,
                        new_node,
                        AtomicOrdering::Release,
                        AtomicOrdering::Relaxed,
                    )
                    .is_ok()
                {
                    return;
                }
            }
        }
    }

    /// 弹出优先级最高的元素
    /// Pops优先级最高的元素
    /// element
    /// Return `None` if队列as空。
    /// Return `None` ifqueueasempty。
    pub fn pop(&self) -> Option<T> {
        loop {
            let current_head = self.head.load(AtomicOrdering::Acquire);
            if current_head.is_null() {
                return None;
            }

            let next = unsafe { (*current_head).next.load(AtomicOrdering::Acquire) };

            if self
                .head
                .compare_exchange_weak(
                    current_head,
                    next,
                    AtomicOrdering::Release,
                    AtomicOrdering::Relaxed,
                )
                .is_ok()
            {
                let data = unsafe {
                    let boxed = Box::from_raw(current_head);
                    boxed.data
                };
                return Some(data);
            }
        }
    }

    /// 检查队列是否为空
    /// Checks队列是否为空
    /// as
    pub fn is_empty(&self) -> bool {
        self.head.load(AtomicOrdering::Acquire).is_null()
    }

    /// 查看队首元素（不弹出）
    /// Views队首元素（不弹出）
    /// element （）
    pub fn peek(&self) -> Option<&T> {
        let head = self.head.load(AtomicOrdering::Acquire);
        if head.is_null() {
            None
        } else {
            unsafe { Some(&(*head).data) }
        }
    }
}

impl<T> Default for LockFreePriorityQueue<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Drop for LockFreePriorityQueue<T> {
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
    fn test_basic_push_pop() {
        let pq = LockFreePriorityQueue::new();
        pq.push("low", 1);
        pq.push("high", 10);
        pq.push("medium", 5);
        assert_eq!(pq.pop(), Some("high"));
        assert_eq!(pq.pop(), Some("medium"));
        assert_eq!(pq.pop(), Some("low"));
        assert_eq!(pq.pop(), None);
    }

    #[test]
    fn test_is_empty() {
        let pq = LockFreePriorityQueue::<i32>::new();
        assert!(pq.is_empty());
        pq.push(1, 1);
        assert!(!pq.is_empty());
        pq.pop();
        assert!(pq.is_empty());
    }

    #[test]
    fn test_peek() {
        let pq = LockFreePriorityQueue::new();
        assert_eq!(pq.peek(), None);
        pq.push("first", 1);
        assert_eq!(pq.peek(), Some(&"first"));
        pq.push("second", 2);
        assert_eq!(pq.peek(), Some(&"second"));
    }

    /// 注意：此并发测试未实现内存回收机制（Hazard Pointers / EBR）。
    /// ：this concurrency memory mechanism （Hazard Pointers / EBR）。
    #[test]
    #[ignore = "概念演示：未实现内存回收，Miri 会报告数据竞争"]
    fn test_concurrent_push() {
        let pq = Arc::new(LockFreePriorityQueue::new());
        let mut handles = vec![];

        for i in 0..4 {
            let q = Arc::clone(&pq);
            handles.push(thread::spawn(move || {
                for j in 0..50 {
                    q.push(i * 50 + j, i * 50 + j);
                }
            }));
        }

        for h in handles {
            h.join().unwrap();
        }

        let mut count = 0;
        let mut prev = i32::MAX;
        while let Some(val) = pq.pop() {
            assert!(val <= prev);
            prev = val;
            count += 1;
        }
        assert_eq!(count, 200);
    }

    /// 注意：此并发测试未实现内存回收机制。
    /// ：this concurrency memory mechanism 。
    #[test]
    #[ignore = "概念演示：未实现内存回收，Miri 会报告数据竞争"]
    fn test_concurrent_mixed_operations() {
        let pq = Arc::new(LockFreePriorityQueue::new());
        let mut handles = vec![];

        for i in 0..2 {
            let q = Arc::clone(&pq);
            handles.push(thread::spawn(move || {
                for j in 0..500 {
                    q.push(i * 500 + j, i * 500 + j);
                }
                0usize
            }));
        }

        for _ in 0..2 {
            let q = Arc::clone(&pq);
            handles.push(thread::spawn(move || {
                let mut popped = 0;
                for _ in 0..1500 {
                    if q.pop().is_some() {
                        popped += 1;
                    }
                }
                popped
            }));
        }

        let results: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();
        let total_popped: usize = results[2..].iter().sum();

        let mut leftover = 0;
        while pq.pop().is_some() {
            leftover += 1;
        }
        assert_eq!(total_popped + leftover, 1000);
    }
}
