// [来源: Treiber 1986 / Rust Atomics and Locks / crossbeam-epoch]
//! 无锁栈实现 (Treiber Stack) —— 基于 `crossbeam-epoch` 的内存安全版本
//!
//! ## 核心算法
//!
//! 1. `push`：创建新节点，令 `next` 指向当前 `head`，随后 CAS `head`。
//! 2. `pop`：读取当前 `head`，CAS 将 `head` 替换为 `head.next`，并通过 epoch 延迟释放旧头节点。
//!
//! ## 内存安全
//!
//! - 所有共享节点访问均在 `epoch::pin()` 返回的 `Guard` 保护下进行。
//! - 被弹出的节点通过 `guard.defer_unchecked` 延迟到所有线程离开当前 epoch 后再释放，
//!   从而避免 ABA 问题与悬垂指针。
//!
//! ## 复杂度
//!
//! - `push` / `pop`：均摊 **O(1)**，最坏情况下 CAS 重试次数取决于并发竞争。

use std::sync::atomic::Ordering::{Acquire, Relaxed, Release};

use crossbeam_epoch::{Atomic, Owned};

/// 栈节点。
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
}

/// 无锁栈 (Treiber Stack)。
///
/// 线程安全的无锁 LIFO 栈，基于 `crossbeam-epoch` 实现安全内存回收。
///
/// # 示例
///
/// ```
/// use c08_algorithms::data_structure::lock_free_stack::LockFreeStack;
///
/// let stack = LockFreeStack::new();
/// stack.push(1);
/// stack.push(2);
/// assert_eq!(stack.pop(), Some(2));
/// assert_eq!(stack.pop(), Some(1));
/// assert_eq!(stack.pop(), None);
/// ```
pub struct LockFreeStack<T> {
    head: Atomic<Node<T>>,
}

unsafe impl<T: Send> Send for LockFreeStack<T> {}
unsafe impl<T: Send> Sync for LockFreeStack<T> {}

impl<T> LockFreeStack<T> {
    /// 创建新的空栈。
    pub const fn new() -> Self {
        Self {
            head: Atomic::null(),
        }
    }

    /// 将元素压入栈顶。
    pub fn push(&self, data: T) {
        let guard = &crossbeam_epoch::pin();
        let new = Owned::new(Node::new(data)).into_shared(guard);

        loop {
            let head = self.head.load(Acquire, guard);
            unsafe {
                (*new.as_raw()).next.store(head, Relaxed);
            }

            match self
                .head
                .compare_exchange(head, new, Release, Acquire, guard)
            {
                Ok(_) => return,
                Err(_) => continue,
            }
        }
    }

    /// 从栈顶弹出元素；若栈空返回 `None`。
    pub fn pop(&self) -> Option<T> {
        let guard = &crossbeam_epoch::pin();

        loop {
            let head = self.head.load(Acquire, guard);
            let head_ref = unsafe { head.as_ref() }?;

            let next = head_ref.next.load(Acquire, guard);

            if self
                .head
                .compare_exchange(head, next, Release, Acquire, guard)
                .is_ok()
            {
                unsafe {
                    // 我们已通过 CAS 将 head 从数据结构中移除，获得独占所有权。
                    // 先取出数据，再通过 epoch 延迟释放节点，避免悬垂指针与 ABA。
                    let data = (&mut *(head.as_raw() as *mut Node<T>)).data.take();
                    guard.defer_unchecked(move || {
                        let _ = head.into_owned();
                    });
                    return data;
                }
            }
        }
    }

    /// 检查栈是否为空。
    ///
    /// 注意：该结果是瞬态的，并发 `push` 可能立即改变它。
    pub fn is_empty(&self) -> bool {
        let guard = &crossbeam_epoch::pin();
        self.head.load(Acquire, guard).is_null()
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
        let stack = LockFreeStack::new();
        for i in 0..100 {
            stack.push(i);
        }
        drop(stack); // 应无泄漏/重复释放
    }

    #[test]
    fn test_concurrent_push_pop() {
        const THREADS: usize = 4;
        const OPS: usize = 1000;

        let stack = Arc::new(LockFreeStack::new());
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

        let stack = Arc::new(LockFreeStack::new());
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
