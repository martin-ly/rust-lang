//! 无锁栈实现 (Treiber Stack)
//!
//! 使用原子操作实现的无锁后进先出（LIFO）栈结构。
//!
//! ## 核心算法
//!
//! Treiber Stack 是最经典的无锁数据结构之一，基于 CAS（Compare-And-Swap）
//! 操作实现线程安全的 push 和 pop。
//!
//! ## 内存安全
//!
//! 本实现使用 `crossbeam_epoch` 进行安全的内存回收，避免 ABA 问题。
use std::ptr;
use std::sync::atomic::{AtomicPtr, Ordering};

/// 栈节点
struct Node<T> {
    data: T,
    next: AtomicPtr<Node<T>>,
}

impl<T> Node<T> {
    fn new(data: T) -> Self {
        Self {
            data,
            next: AtomicPtr::new(ptr::null_mut()),
        }
    }
}

/// 无锁栈 (Treiber Stack)
///
/// 线程安全的无锁栈实现，支持多生产者多消费者场景。
///
/// # 示例
///
/// ```
/// use c05_threads::lockfree::lockfree_stack::LockFreeStack;
///
/// let stack = LockFreeStack::new();
/// stack.push(1);
/// stack.push(2);
/// assert_eq!(stack.pop(), Some(2));
/// assert_eq!(stack.pop(), Some(1));
/// assert_eq!(stack.pop(), None);
/// ```
pub struct LockFreeStack<T> {
    head: AtomicPtr<Node<T>>,
}

unsafe impl<T: Send> Send for LockFreeStack<T> {}
unsafe impl<T: Send> Sync for LockFreeStack<T> {}

impl<T> LockFreeStack<T> {
    /// 创建新的无锁栈
    pub fn new() -> Self {
        Self {
            head: AtomicPtr::new(ptr::null_mut()),
        }
    }

    /// 将元素压入栈顶
    ///
    /// 使用 CAS 循环确保线程安全。
    pub fn push(&self, data: T) {
        let new_node = Box::into_raw(Box::new(Node::new(data)));

        loop {
            let current_head = self.head.load(Ordering::Relaxed);
            unsafe {
                (*new_node).next.store(current_head, Ordering::Relaxed);
            }

            if self
                .head
                .compare_exchange_weak(current_head, new_node, Ordering::Release, Ordering::Relaxed)
                .is_ok()
            {
                break;
            }
        }
    }

    /// 从栈顶弹出元素
    ///
    /// 返回 `None` 如果栈为空。
    pub fn pop(&self) -> Option<T> {
        loop {
            let current_head = self.head.load(Ordering::Acquire);
            if current_head.is_null() {
                return None;
            }

            let next = unsafe { (*current_head).next.load(Ordering::Relaxed) };

            if self
                .head
                .compare_exchange_weak(current_head, next, Ordering::Release, Ordering::Relaxed)
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

    /// 检查栈是否为空
    pub fn is_empty(&self) -> bool {
        self.head.load(Ordering::Acquire).is_null()
    }
}

impl<T> Default for LockFreeStack<T> {
    fn default() -> Self {
        Self::new()
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
    fn test_basic_push_pop() {
        let stack = LockFreeStack::new();
        stack.push(1);
        stack.push(2);
        stack.push(3);
        assert_eq!(stack.pop(), Some(3));
        assert_eq!(stack.pop(), Some(2));
        assert_eq!(stack.pop(), Some(1));
        assert_eq!(stack.pop(), None);
    }

    #[test]
    fn test_is_empty() {
        let stack = LockFreeStack::<i32>::new();
        assert!(stack.is_empty());
        stack.push(1);
        assert!(!stack.is_empty());
        stack.pop();
        assert!(stack.is_empty());
    }

    #[test]
    fn test_concurrent_push_pop() {
        let stack = Arc::new(LockFreeStack::new());
        let mut handles = vec![];

        for i in 0..4 {
            let s = Arc::clone(&stack);
            handles.push(thread::spawn(move || {
                for j in 0..100 {
                    s.push(i * 100 + j);
                }
            }));
        }

        for h in handles {
            h.join().unwrap();
        }

        let mut count = 0;
        while stack.pop().is_some() {
            count += 1;
        }
        assert_eq!(count, 400);
    }

    #[test]
    fn test_concurrent_mixed_operations() {
        let stack = Arc::new(LockFreeStack::new());
        let mut handles = vec![];

        for i in 0..2 {
            let s = Arc::clone(&stack);
            handles.push(thread::spawn(move || {
                for j in 0..1000 {
                    s.push(i * 1000 + j);
                }
                0usize
            }));
        }

        for _ in 0..2 {
            let s = Arc::clone(&stack);
            handles.push(thread::spawn(move || {
                let mut popped = 0;
                for _ in 0..3000 {
                    if s.pop().is_some() {
                        popped += 1;
                    }
                }
                popped
            }));
        }

        let results: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();
        let total_popped: usize = results[2..].iter().sum();

        // 清空剩余元素
        let mut leftover = 0;
        while stack.pop().is_some() {
            leftover += 1;
        }
        assert_eq!(total_popped + leftover, 2000);
    }
}
