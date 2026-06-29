// [来源: Treiber 1986 / Rust Atomics and Locks]
//! Treiber Stack 无锁数据结构 —— 基于 `std::sync::atomic::AtomicPtr` 的教学实现
//!
//! ## 核心算法
//!
//! 1. `push(x)`：分配新节点 `n`，令 `n.next = head`，然后 CAS `head = n`。
//! 2. `pop()`：读取 `head`，若为空返回 `None`；否则读取 `head.next`，CAS `head = next`，
//!    返回 `head.data`。
//!
//! ## 教学限制
//!
//! 本实现仅使用标准库 `std::sync::atomic::AtomicPtr`，因此：
//!
//! - 被弹出的节点**不立即释放**，而是直接泄漏其节点内存，避免 ABA 问题导致的
//!   use-after-free。栈被丢弃时仅释放当时仍挂在栈上的节点。
//! - 生产环境请使用基于 `crossbeam-epoch` 的
//!   [`crate::data_structure::lock_free_stack::LockFreeStack`]，它提供安全的 epoch
//!   延迟释放与 ABA 防护。
//!
//! ## 复杂度
//!
//! - `push` / `pop`：均摊 **O(1)**，最坏 CAS 重试次数取决于并发竞争。

use std::sync::atomic::{AtomicPtr, Ordering};

/// 栈节点。
struct Node<T> {
    data: Option<T>,
    next: *mut Node<T>,
}

impl<T> Node<T> {
    fn new(data: T) -> Self {
        Self {
            data: Some(data),
            next: std::ptr::null_mut(),
        }
    }
}

/// Treiber Stack 无锁 LIFO 栈（`std::sync::atomic::AtomicPtr` 教学实现）。
///
/// 线程安全的无锁栈。本实现为了展示核心 CAS 算法，故意不对弹出节点做立即回收；
/// 详细限制见模块文档。
///
/// # 示例
///
/// ```
/// use c08_algorithms::data_structure::treiber_stack::TreiberStack;
///
/// let stack = TreiberStack::new();
/// stack.push(1);
/// stack.push(2);
/// assert_eq!(stack.pop(), Some(2));
/// assert_eq!(stack.pop(), Some(1));
/// assert_eq!(stack.pop(), None);
/// ```
pub struct TreiberStack<T> {
    head: AtomicPtr<Node<T>>,
}

// SAFETY: `TreiberStack<T>` 可被发送到其他线程，只要 `T: Send`。
// 所有共享状态都通过 `AtomicPtr` 访问，没有线程本地数据。
unsafe impl<T: Send> Send for TreiberStack<T> {}

// SAFETY: `TreiberStack<T>` 可被多线程共享，只要 `T: Send`。
// `push` 将 `T` 移动到节点中；`pop` 将 `T` 从节点中移出。没有其他线程能在无同步的情况下
// 访问已被弹出的 `T`。节点本身通过 `AtomicPtr` 进行同步。
unsafe impl<T: Send> Sync for TreiberStack<T> {}

impl<T> TreiberStack<T> {
    /// 创建新的空栈。
    pub const fn new() -> Self {
        Self {
            head: AtomicPtr::new(std::ptr::null_mut()),
        }
    }

    /// 将元素压入栈顶。
    pub fn push(&self, data: T) {
        // 分配新节点。若后续 CAS 失败，同一节点会被复用，不会泄漏。
        let new = Box::into_raw(Box::new(Node::new(data)));

        loop {
            let head = self.head.load(Ordering::Acquire);
            // SAFETY: `new` 是本线程刚刚分配的，没有其他线程能访问它。
            unsafe {
                (*new).next = head;
            }

            match self
                .head
                .compare_exchange(head, new, Ordering::Release, Ordering::Relaxed)
            {
                Ok(_) => return,
                Err(_) => continue,
            }
        }
    }

    /// 从栈顶弹出元素；若栈空返回 `None`。
    pub fn pop(&self) -> Option<T> {
        loop {
            let head = self.head.load(Ordering::Acquire);
            if head.is_null() {
                return None;
            }

            // SAFETY: `head` 非空，且通过 `Acquire` load 观察到其他线程 `Release` 发布的节点。
            // 本实现不释放弹出节点，因此 `head` 始终有效。
            let next = unsafe { (*head).next };

            match self
                .head
                .compare_exchange(head, next, Ordering::Release, Ordering::Relaxed)
            {
                Ok(_) => {
                    // SAFETY: 我们已通过 CAS 将 `head` 从栈上移除，获得该节点的独占所有权。
                    // 取出数据后，节点被泄漏（教学实现不回收），避免其他线程的悬垂读。
                    let data = unsafe { (*head).data.take() };
                    return data;
                }
                Err(_) => continue,
            }
        }
    }

    /// 检查栈是否为空。
    ///
    /// 注意：该结果是瞬态的，并发 `push` 可能立即改变它。
    pub fn is_empty(&self) -> bool {
        self.head.load(Ordering::Acquire).is_null()
    }
}

impl<T> Default for TreiberStack<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Drop for TreiberStack<T> {
    fn drop(&mut self) {
        let mut current = self.head.load(Ordering::Relaxed);
        while !current.is_null() {
            // SAFETY: `Drop` 时栈不再被其他线程访问（`&mut self` 保证独占）。
            let node = unsafe { Box::from_raw(current) };
            current = node.next;
            // `node` 在这里被释放；`data` 为 `None`（已被弹出）或仍包含数据（从未弹出）。
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use std::thread;

    #[test]
    fn test_basic_push_pop() {
        let stack = TreiberStack::new();
        assert!(stack.is_empty());

        stack.push(1);
        stack.push(2);
        stack.push(3);
        assert!(!stack.is_empty());

        assert_eq!(stack.pop(), Some(3));
        assert_eq!(stack.pop(), Some(2));
        assert_eq!(stack.pop(), Some(1));
        assert_eq!(stack.pop(), None);
        assert!(stack.is_empty());
    }

    #[test]
    fn test_drop() {
        let stack = TreiberStack::new();
        for i in 0..100 {
            stack.push(i);
        }
        for _ in 0..50 {
            stack.pop();
        }
        drop(stack); // 应无 panic
    }

    #[test]
    fn test_concurrent_push() {
        const THREADS: usize = 4;
        const OPS: usize = 1000;

        let stack = Arc::new(TreiberStack::new());
        let mut handles = vec![];

        for t in 0..THREADS {
            let s = Arc::clone(&stack);
            handles.push(thread::spawn(move || {
                for i in 0..OPS {
                    s.push(t * OPS + i);
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
        assert_eq!(count, THREADS * OPS);
    }

    #[test]
    fn test_concurrent_mixed_operations() {
        const THREADS: usize = 4;
        const OPS: usize = 500;

        let stack = Arc::new(TreiberStack::new());
        let mut handles = vec![];

        for t in 0..THREADS {
            let s = Arc::clone(&stack);
            handles.push(thread::spawn(move || {
                for i in 0..OPS {
                    s.push(t * OPS + i);
                    if i % 2 == 0 {
                        s.pop();
                    }
                }
            }));
        }

        for h in handles {
            h.join().unwrap();
        }

        // 仅验证无崩溃与内存错误；剩余元素数量取决于调度。
        while stack.pop().is_some() {}
    }
}
