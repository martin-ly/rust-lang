//! 自旋锁（教学示例，生产环境请优先用 `Mutex`）
//! - 基于 `AtomicBool` 的简化自旋锁
//! - 支持 `try_lock`

use std::cell::UnsafeCell;
use std::ops::{Deref, DerefMut};
use std::sync::atomic::{AtomicBool, Ordering};
use std::hint;
use std::sync::Arc;
use std::thread;

pub struct SpinLock<T> {
    locked: AtomicBool,
    value: UnsafeCell<T>,
}

unsafe impl<T: Send> Send for SpinLock<T> {}
unsafe impl<T: Send> Sync for SpinLock<T> {}

impl<T> SpinLock<T> {
    pub fn new(v: T) -> Self {
        Self { locked: AtomicBool::new(false), value: UnsafeCell::new(v) }
    }

    pub fn lock(&self) -> SpinGuard<'_, T> {
        while self
            .locked
            .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
            .is_err()
        {
            hint::spin_loop();
        }
        SpinGuard { lock: self }
    }

    pub fn try_lock(&self) -> Option<SpinGuard<'_, T>> {
        if self
            .locked
            .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
            .is_ok()
        {
            Some(SpinGuard { lock: self })
        } else {
            None
        }
    }

    fn unlock(&self) { self.locked.store(false, Ordering::Release); }
}

pub struct SpinGuard<'a, T> {
    lock: &'a SpinLock<T>,
}

impl<'a, T> Deref for SpinGuard<'a, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target { unsafe { &*self.lock.value.get() } }
}

impl<'a, T> DerefMut for SpinGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target { unsafe { &mut *self.lock.value.get() } }
}

impl<'a, T> Drop for SpinGuard<'a, T> {
    fn drop(&mut self) { self.lock.unlock(); }
}

/// 演示：多个线程在短临界区自旋更新
pub fn spinlock_demo(workers: usize, iters: usize) -> usize {
    let lock = Arc::new(SpinLock::new(0usize));
    let mut handles = Vec::new();
    for _ in 0..workers {
        let l = Arc::clone(&lock);
        handles.push(thread::spawn(move || {
            for _ in 0..iters {
                let mut g = l.lock();
                *g += 1;
            }
        }));
    }
    for h in handles { h.join().unwrap(); }
    *lock.lock()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_spinlock_demo() {
        let total = spinlock_demo(4, 10_000);
        assert_eq!(total, 4 * 10_000);
    }
}