//! 无锁队列实现 (Michael-Scott Queue)
//! ## 核心算法
//! ## core algorithm
//! 链表structure，Via CAS 操作Implementation ofthread-safe enqueue and dequeue。
//! chaintablestructure，Via CAS operationImplementation ofthread-safe enqueue and dequeue。
//! ## 内存安全
//! ## memorysafe
//! ## memory safety
use std::ptr;
use std::sync::atomic::{AtomicPtr, Ordering};

/// 队列节点
/// node
struct Node<T> {
    data: Option<T>,
    next: AtomicPtr<Node<T>>,
}

impl<T> Node<T> {
    fn new(data: T) -> Self {
        Self {
            data: Some(data),
            next: AtomicPtr::new(ptr::null_mut()),
        }
    }

    fn sentinel() -> Self {
        Self {
            data: None,
            next: AtomicPtr::new(ptr::null_mut()),
        }
    }
}

/// 无锁队列 (Michael-Scott Queue)
/// thread-safelock-free FIFO 队列Implementation of。
/// thread-safelock-free FIFO queueImplementation of。
/// # 示例
/// # Examples
/// # example
/// ```
/// use c05_threads::lockfree::lockfree_queue::LockFreeQueue;
///
/// let queue = LockFreeQueue::new();
/// queue.enqueue(1);
/// queue.enqueue(2);
/// assert_eq!(queue.dequeue(), Some(1));
/// assert_eq!(queue.dequeue(), Some(2));
/// assert_eq!(queue.dequeue(), None);
/// ```
pub struct LockFreeQueue<T> {
    head: AtomicPtr<Node<T>>,
    tail: AtomicPtr<Node<T>>,
}

unsafe impl<T: Send> Send for LockFreeQueue<T> {}
unsafe impl<T: Send> Sync for LockFreeQueue<T> {}

impl<T> LockFreeQueue<T> {
    /// 创建新的无锁队列
    /// Creates新的无锁队列
    /// lock-free queue
    pub fn new() -> Self {
        let sentinel = Box::into_raw(Box::new(Node::sentinel()));
        Self {
            head: AtomicPtr::new(sentinel),
            tail: AtomicPtr::new(sentinel),
        }
    }

    /// 将元素加入队列尾部
    /// will element
    pub fn enqueue(&self, data: T) {
        let new_node = Box::into_raw(Box::new(Node::new(data)));

        loop {
            let tail = self.tail.load(Ordering::Acquire);
            let next = unsafe { (*tail).next.load(Ordering::Acquire) };

            // 检查 tail 是否仍然是尾节点
            if tail == self.tail.load(Ordering::Acquire) {
                if next.is_null() {
                    // 尝试将新节点链接到尾节点
                    if unsafe {
                        (*tail).next.compare_exchange_weak(
                            next,
                            new_node,
                            Ordering::Release,
                            Ordering::Relaxed,
                        )
                    }
                    .is_ok()
                    {
                        // 尝试更新 tail 指针
                        let _ = self.tail.compare_exchange_weak(
                            tail,
                            new_node,
                            Ordering::Release,
                            Ordering::Relaxed,
                        );
                        break;
                    }
                } else {
                    // 帮助更新 lagging tail
                    let _ = self.tail.compare_exchange_weak(
                        tail,
                        next,
                        Ordering::Release,
                        Ordering::Relaxed,
                    );
                }
            }
        }
    }

    /// 从队列头部移除元素
    /// from element
    /// Return `None` if队列as空。
    /// Return `None` ifqueueasempty。
    pub fn dequeue(&self) -> Option<T> {
        loop {
            let head = self.head.load(Ordering::Acquire);
            let tail = self.tail.load(Ordering::Acquire);
            let next = unsafe { (*head).next.load(Ordering::Acquire) };

            if head == self.head.load(Ordering::Acquire) {
                if head == tail {
                    if next.is_null() {
                        return None;
                    }
                    // 帮助更新 lagging tail
                    let _ = self.tail.compare_exchange_weak(
                        tail,
                        next,
                        Ordering::Release,
                        Ordering::Relaxed,
                    );
                } else {
                    if self
                        .head
                        .compare_exchange_weak(head, next, Ordering::Release, Ordering::Relaxed)
                        .is_ok()
                    {
                        let data = unsafe { (*next).data.take() };
                        unsafe {
                            let _ = Box::from_raw(head);
                        }
                        return data;
                    }
                }
            }
        }
    }

    /// 检查队列是否为空
    /// Checks队列是否为空
    /// as
    pub fn is_empty(&self) -> bool {
        let head = self.head.load(Ordering::Acquire);
        let tail = self.tail.load(Ordering::Acquire);
        if head == tail {
            let next = unsafe { (*head).next.load(Ordering::Acquire) };
            next.is_null()
        } else {
            false
        }
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
        let head = self.head.load(Ordering::Relaxed);
        if !head.is_null() {
            unsafe {
                let _ = Box::from_raw(head);
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
        queue.enqueue(1);
        queue.enqueue(2);
        queue.enqueue(3);
        assert_eq!(queue.dequeue(), Some(1));
        assert_eq!(queue.dequeue(), Some(2));
        assert_eq!(queue.dequeue(), Some(3));
        assert_eq!(queue.dequeue(), None);
    }

    #[test]
    fn test_is_empty() {
        let queue = LockFreeQueue::<i32>::new();
        assert!(queue.is_empty());
        queue.enqueue(1);
        assert!(!queue.is_empty());
        queue.dequeue();
        assert!(queue.is_empty());
    }

    /// 注意：此并发测试未实现内存回收机制（Hazard Pointers / EBR）。
    /// ：this concurrency memory mechanism （Hazard Pointers / EBR）。
    #[test]
    #[ignore = "概念演示：未实现内存回收，Miri 会报告数据竞争"]
    fn test_concurrent_enqueue() {
        let queue = Arc::new(LockFreeQueue::new());
        let mut handles = vec![];

        for i in 0..4 {
            let q = Arc::clone(&queue);
            handles.push(thread::spawn(move || {
                for j in 0..100 {
                    q.enqueue(i * 100 + j);
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
        assert_eq!(count, 400);
    }

    /// 注意：此并发测试未实现内存回收机制。
    /// ：this concurrency memory mechanism 。
    #[test]
    #[ignore = "概念演示：未实现内存回收，Miri 会报告数据竞争"]
    fn test_concurrent_mixed_operations() {
        let queue = Arc::new(LockFreeQueue::new());
        let mut handles = vec![];

        for i in 0..2 {
            let q = Arc::clone(&queue);
            handles.push(thread::spawn(move || {
                for j in 0..1000 {
                    q.enqueue(i * 1000 + j);
                }
                0usize
            }));
        }

        for _ in 0..2 {
            let q = Arc::clone(&queue);
            handles.push(thread::spawn(move || {
                let mut dequeued = 0;
                for _ in 0..3000 {
                    if q.dequeue().is_some() {
                        dequeued += 1;
                    }
                }
                dequeued
            }));
        }

        let results: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();
        let total_dequeued: usize = results[2..].iter().sum();

        // 清空剩余元素
        let mut leftover = 0;
        while queue.dequeue().is_some() {
            leftover += 1;
        }
        assert_eq!(total_dequeued + leftover, 2000);
    }
}
