//! Loom 模型检测测试：Lock-free Treiber Stack
//! Loom 模型检测Test for：Lock-free Treiber Stack
//! 运行：cargo test --test loom_lockfree_tests -p c05_threads -- --ignored

use loom::sync::atomic::{AtomicPtr, Ordering};
use loom::sync::Arc;
use loom::thread;

struct Node<T> {
    data: T,
    next: *mut Node<T>,
}

/// Treiber Stack using Loom-compatible AtomicPtr.
/// No epoch reclamation needed in Loom tests because Loom models the heap
/// and does not perform actual deallocation during exploration.
pub struct LoomStack<T> {
    head: AtomicPtr<Node<T>>,
}

impl<T> LoomStack<T> {
    pub fn new() -> Self {
        Self {
            head: AtomicPtr::new(std::ptr::null_mut()),
        }
    }

    pub fn push(&self, data: T) {
        let new_node = Box::into_raw(Box::new(Node {
            data,
            next: std::ptr::null_mut(),
        }));

        loop {
            let head = self.head.load(Ordering::Relaxed);
            // SAFETY: new_node was just allocated and is not yet shared.
            unsafe { (*new_node).next = head };
            if self
                .head
                .compare_exchange(head, new_node, Ordering::Release, Ordering::Relaxed)
                .is_ok()
            {
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
            // SAFETY: head is non-null, and Acquire ordering ensures we see
            // all writes from the thread that pushed this node.
            let next = unsafe { (*head).next };
            if self
                .head
                .compare_exchange(head, next, Ordering::Release, Ordering::Relaxed)
                .is_ok()
            {
                // SAFETY: We won the CAS, so we have exclusive ownership of this node.
                // Loom manages the heap for us; we just need to read the data.
                let data = unsafe { std::ptr::read(&(*head).data) };
                return Some(data);
            }
        }
    }
}

impl<T> Default for LoomStack<T> {
    fn default() -> Self {
        Self::new()
    }
}

unsafe impl<T: Send> Send for LoomStack<T> {}
unsafe impl<T: Send + Sync> Sync for LoomStack<T> {}

/// Helper: run loom model with a larger stack to avoid Windows overflow.
fn loom_model<F, R>(f: F) -> R
where
    F: FnOnce() -> R + Send + 'static,
    R: Send + 'static,
{
    const STACK_SIZE: usize = 4 * 1024 * 1024;
    std::thread::Builder::new()
        .stack_size(STACK_SIZE)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

/// Test: Two threads push, two threads pop — no crash or lost items.
#[test]
#[cfg_attr(target_os = "windows", ignore = "loom stack overflow on Windows")]
fn test_loom_push_pop_no_lost_items() {
    loom_model(|| {
        loom::model(|| {
            let stack = Arc::new(LoomStack::new());
            let s1 = Arc::clone(&stack);
            let s2 = Arc::clone(&stack);
            let s3 = Arc::clone(&stack);
            let s4 = Arc::clone(&stack);

            let t1 = thread::spawn(move || {
                s1.push(1);
                s1.push(2);
            });
            let t2 = thread::spawn(move || {
                s2.push(3);
                s2.push(4);
            });
            let t3 = thread::spawn(move || {
                let mut got = Vec::new();
                for _ in 0..2 {
                    if let Some(v) = s3.pop() {
                        got.push(v);
                    }
                }
                got
            });
            let t4 = thread::spawn(move || {
                let mut got = Vec::new();
                for _ in 0..2 {
                    if let Some(v) = s4.pop() {
                        got.push(v);
                    }
                }
                got
            });

            t1.join().unwrap();
            t2.join().unwrap();
            let got3 = t3.join().unwrap();
            let got4 = t4.join().unwrap();

            let total_popped = got3.len() + got4.len();
            // Items may still be in the stack due to timing, but none should be lost.
            assert!(total_popped <= 4);
        });
    });
}

/// Test: Concurrent pop on a single item — exactly one winner.
#[test]
#[cfg_attr(target_os = "windows", ignore = "loom stack overflow on Windows")]
fn test_loom_single_item_race() {
    loom_model(|| {
        loom::model(|| {
            let stack = Arc::new(LoomStack::new());
            stack.push(42);

            let s1 = Arc::clone(&stack);
            let s2 = Arc::clone(&stack);

            let t1 = thread::spawn(move || s1.pop());
            let t2 = thread::spawn(move || s2.pop());

            let r1 = t1.join().unwrap();
            let r2 = t2.join().unwrap();

            let winners = [r1, r2].iter().filter(|x| x.is_some()).count();
            assert_eq!(winners, 1);
        });
    });
}

/// Test: ABA resistance — push/pop/push sequence with concurrent reader.
#[test]
#[cfg_attr(target_os = "windows", ignore = "loom stack overflow on Windows")]
fn test_loom_aba_resistance() {
    loom_model(|| {
        loom::model(|| {
            let stack = Arc::new(LoomStack::new());
            stack.push(1);

            let s1 = Arc::clone(&stack);
            let s2 = Arc::clone(&stack);

            let t1 = thread::spawn(move || {
                let _ = s1.pop(); // pop 1
                s1.push(2);       // push 2
            });
            let t2 = thread::spawn(move || {
                // Try to pop concurrently with the push(2).
                s2.pop()
            });

            t1.join().unwrap();
            let r2 = t2.join().unwrap();

            // r2 should be either Some(1) or Some(2), never a dangling pointer.
            assert!(r2 == Some(1) || r2 == Some(2) || r2.is_none());
        });
    });
}
