//! Lock-free Stack with Epoch-Based Reclamation (EBR) Demo
//!
//! Demonstrates safe memory reclamation using `crossbeam_epoch`:
//! - `Atomic` pointer with epoch tracking
//! - `Owned` for new allocations
//! - `Shared` for shared references within a pin scope
//! - `Guard` for read-side critical sections
//!
//! Run: cargo run --example lockfree_epoch_stack_demo -p c05_threads

use crossbeam_epoch::{self as epoch, Atomic, Owned};
use std::sync::atomic::Ordering::{Acquire, Relaxed, Release};
use std::sync::Arc;
use std::thread;

/// A lock-free Treiber stack with epoch-based memory reclamation.
///
/// # Safety Invariants
/// - All node allocations go through `crossbeam_epoch::Owned`.
/// - All reads happen inside a `pin()` critical section via `Shared`.
/// - Retired nodes are deferred to the global epoch collector.
pub struct EpochStack<T> {
    head: Atomic<Node<T>>,
}

struct Node<T> {
    data: T,
    next: Atomic<Node<T>>,
}

impl<T> EpochStack<T> {
    pub fn new() -> Self {
        Self {
            head: Atomic::null(),
        }
    }

    /// Push a value onto the stack (lock-free, wait-free on the happy path).
    pub fn push(&self, data: T) {
        let new_node = Owned::new(Node {
            data,
            next: Atomic::null(),
        });
        let guard = &epoch::pin();
        let new_ptr = new_node.into_shared(guard);

        loop {
            let head = self.head.load(Relaxed, guard);
            unsafe { new_ptr.deref().next.store(head, Relaxed) };
            if self
                .head
                .compare_exchange(head, new_ptr, Release, Relaxed, guard)
                .is_ok()
            {
                break;
            }
        }
    }

    /// Pop a value from the stack (lock-free).
    pub fn pop(&self) -> Option<T> {
        let guard = &epoch::pin();

        loop {
            let head = self.head.load(Acquire, guard);
            let head_ref = unsafe { head.as_ref()? };
            let next = head_ref.next.load(Relaxed, guard);

            if self
                .head
                .compare_exchange(head, next, Release, Relaxed, guard)
                .is_ok()
            {
                // SAFETY: We won the CAS, so no other thread can access this node.
                // We must defer deallocation until all readers in older epochs retire.
                unsafe {
                    let data = std::ptr::read(&head_ref.data);
                    guard.defer_unchecked(move || {
                        let _ = head.into_owned();
                    });
                    return Some(data);
                }
            }
        }
    }

    /// Check if the stack is empty.
    pub fn is_empty(&self) -> bool {
        let guard = &epoch::pin();
        self.head.load(Acquire, guard).is_null()
    }
}

impl<T> Drop for EpochStack<T> {
    fn drop(&mut self) {
        let guard = unsafe { epoch::unprotected() };
        let mut curr = self.head.load(Relaxed, guard);
        while let Some(node) = unsafe { curr.as_ref() } {
            let next = node.next.load(Relaxed, guard);
            // SAFETY: We have exclusive access during Drop.
            unsafe { curr.into_owned(); }
            curr = next;
        }
    }
}

impl<T> Default for EpochStack<T> {
    fn default() -> Self {
        Self::new()
    }
}

// SAFETY: EpochStack uses epoch-based reclamation, so data races on nodes
// are prevented by the epoch protocol.
unsafe impl<T: Send> Send for EpochStack<T> {}
unsafe impl<T: Send + Sync> Sync for EpochStack<T> {}

fn demo_single_threaded() {
    println!("=== Single-threaded push/pop ===");
    let stack = EpochStack::new();
    stack.push(1);
    stack.push(2);
    stack.push(3);
    assert_eq!(stack.pop(), Some(3));
    assert_eq!(stack.pop(), Some(2));
    assert_eq!(stack.pop(), Some(1));
    assert_eq!(stack.pop(), None);
    println!("✅ Single-threaded: LIFO order preserved");
}

fn demo_multi_threaded() {
    println!("\n=== Multi-threaded contention ===");
    let stack = Arc::new(EpochStack::new());
    let mut handles = Vec::new();

    for t in 0..4 {
        let s = Arc::clone(&stack);
        handles.push(thread::spawn(move || {
            for i in 0..100 {
                s.push(t * 100 + i);
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
    println!("✅ Multi-threaded: {} items pushed/popped without data races", count);
}

fn demo_epoch_reclamation() {
    println!("\n=== Epoch reclamation under churn ===");
    let stack = Arc::new(EpochStack::new());
    let mut handles = Vec::new();

    // Writers
    for _ in 0..2 {
        let s = Arc::clone(&stack);
        handles.push(thread::spawn(move || {
            for i in 0..1000 {
                s.push(i);
            }
        }));
    }

    // Readers + poppers
    let mut popper_handles = Vec::new();
    for _ in 0..2 {
        let s = Arc::clone(&stack);
        popper_handles.push(thread::spawn(move || {
            let mut local = Vec::new();
            for _ in 0..1000 {
                if let Some(v) = s.pop() {
                    local.push(v);
                }
            }
            local
        }));
    }

    for h in handles {
        h.join().unwrap();
    }
    for h in popper_handles {
        h.join().unwrap();
    }

    // Drain any remaining items
    let mut remaining = 0;
    while stack.pop().is_some() {
        remaining += 1;
    }
    println!("✅ Epoch reclamation: churn completed, {} items remaining", remaining);
}

fn main() {
    demo_single_threaded();
    demo_multi_threaded();
    demo_epoch_reclamation();
    println!("\n🎉 Lock-free epoch stack demo completed!");
}
