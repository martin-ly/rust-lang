//! Work-Stealing Queue（Chase-Lev 双端队列）
//!
//! 工作窃取队列允许一个"拥有者"线程在尾部 push/pop，多个"窃取者"线程从头部 steal。
//! 本实现基于 Chase-Lev 算法，使用原子变量维护 top/bottom 指针与可扩容的环形缓冲，
//! 是 Rayon、Tokio 等调度器的核心数据结构之一。
//!
//! # 时间复杂度
//! - `push`（owner）: O(1) 均摊
//! - `pop`（owner）: O(1) 均摊
//! - `steal`（非 owner）: O(1) 均摊
//!
//! # 安全说明
//! 本实现为教学版，使用 `std::sync::atomic` 与 `unsafe` 进行指针操作。生产环境请优先
//! 使用 `crossbeam-deque` 或 `rayon` 的实现。
//!
//! # 来源
//! - [Chase & Lev — Dynamic Circular Work-Stealing Deque](https://dl.acm.org/doi/10.1145/1073970.1073974)
//! - [Rust Atomics and Locks](https://marabos.nl/atomics/)

use std::sync::atomic::{AtomicIsize, AtomicUsize, Ordering};
use std::sync::Arc;

const INITIAL_CAPACITY: usize = 16;

struct CircularBuffer<T> {
    buffer: *mut Option<T>,
    capacity: usize,
}

impl<T> CircularBuffer<T> {
    fn new(capacity: usize) -> Self {
        let layout = std::alloc::Layout::array::<Option<T>>(capacity).unwrap();
        let buffer = unsafe { std::alloc::alloc(layout) as *mut Option<T> };
        assert!(!buffer.is_null(), "allocation failed");
        for i in 0..capacity {
            unsafe { std::ptr::write(buffer.add(i), None) };
        }
        Self { buffer, capacity }
    }

    fn capacity(&self) -> usize {
        self.capacity
    }

    fn set(&self, idx: usize, value: Option<T>) {
        unsafe { std::ptr::write(self.buffer.add(idx % self.capacity), value) };
    }

    /// 取出指定位置的值，原地留下 `None`。
    fn take(&self, idx: usize) -> Option<T> {
        unsafe {
            let ptr = self.buffer.add(idx % self.capacity);
            let value = std::ptr::read(ptr);
            std::ptr::write(ptr, None);
            value
        }
    }

    fn copy_to(&self, new_buf: &CircularBuffer<T>, bottom: isize, top: isize) {
        let mut i = top;
        while i < bottom {
            let value = self.take(i as usize);
            new_buf.set(i as usize, value);
            i += 1;
        }
    }
}

impl<T> Drop for CircularBuffer<T> {
    fn drop(&mut self) {
        unsafe {
            let layout = std::alloc::Layout::array::<Option<T>>(self.capacity).unwrap();
            std::alloc::dealloc(self.buffer as *mut u8, layout);
        }
    }
}

/// Chase-Lev 工作窃取队列。
pub struct WorkStealingQueue<T> {
    top: AtomicIsize,
    bottom: AtomicIsize,
    buffer: AtomicUsize, // 实际存储 *mut CircularBuffer<T> 的地址，用 usize 做原子交换
    _marker: std::marker::PhantomData<T>,
}

impl<T> WorkStealingQueue<T> {
    /// 创建空队列。
    pub fn new() -> Self {
        let buf = Arc::into_raw(Arc::new(CircularBuffer::<T>::new(INITIAL_CAPACITY))) as usize;
        Self {
            top: AtomicIsize::new(0),
            bottom: AtomicIsize::new(0),
            buffer: AtomicUsize::new(buf),
            _marker: std::marker::PhantomData,
        }
    }

    fn load_buffer(&self) -> Arc<CircularBuffer<T>> {
        let ptr = self.buffer.load(Ordering::Acquire);
        unsafe { Arc::increment_strong_count(ptr as *const CircularBuffer<T>) };
        unsafe { Arc::from_raw(ptr as *const CircularBuffer<T>) }
    }

    /// 拥有者在尾部添加任务。
    pub fn push(&self, value: T) {
        let b = self.bottom.load(Ordering::Relaxed);
        let t = self.top.load(Ordering::Acquire);
        let buf = self.load_buffer();

        // 扩容
        if (b - t) as usize >= buf.capacity() - 1 {
            let new_capacity = buf.capacity() * 2;
            let new_buf = CircularBuffer::<T>::new(new_capacity);
            buf.copy_to(&new_buf, b, t);
            let new_ptr = Arc::into_raw(Arc::new(new_buf)) as usize;
            let old_ptr = self.buffer.load(Ordering::Relaxed);

            // 只有一个 owner 会修改 buffer，因此直接存储即可
            self.buffer.store(new_ptr, Ordering::Release);
            unsafe { Arc::decrement_strong_count(old_ptr as *const CircularBuffer<T>) };

            // 继续用新 buffer 完成 push
            let buf = self.load_buffer();
            buf.set(b as usize, Some(value));
            self.bottom.store(b + 1, Ordering::Release);
            return;
        }

        buf.set(b as usize, Some(value));
        self.bottom.store(b + 1, Ordering::Release);
    }

    /// 拥有者从尾部弹出任务。
    pub fn pop(&self) -> Option<T> {
        let b = self.bottom.load(Ordering::Relaxed);
        b.checked_sub(1)?;
        let b = b - 1;
        self.bottom.store(b, Ordering::Relaxed);

        let t = self.top.load(Ordering::Relaxed);
        let buf = self.load_buffer();

        let size = b - t + 1;
        if size <= 0 {
            self.bottom.store(t, Ordering::Relaxed);
            return None;
        }

        let value = buf.take(b as usize);

        if b == t {
            // 最后一个元素，需要与 steal 竞争
            if self
                .top
                .compare_exchange(t, t + 1, Ordering::SeqCst, Ordering::Relaxed)
                .is_err()
            {
                // 竞争失败，说明被 steal 了
                self.bottom.store(t + 1, Ordering::Relaxed);
                return None;
            }
            self.bottom.store(t + 1, Ordering::Relaxed);
        }

        value
    }

    /// 非拥有者从头部窃取任务。
    pub fn steal(&self) -> Option<T> {
        let t = self.top.load(Ordering::Acquire);
        let b = self.bottom.load(Ordering::Acquire);

        if t >= b {
            return None;
        }

        let buf = self.load_buffer();
        let value = buf.take(t as usize);

        if self
            .top
            .compare_exchange(t, t + 1, Ordering::SeqCst, Ordering::Relaxed)
            .is_ok()
        {
            value
        } else {
            None
        }
    }

    /// 当前任务数（近似值，并发下可能不一致）。
    pub fn len(&self) -> isize {
        let b = self.bottom.load(Ordering::Acquire);
        let t = self.top.load(Ordering::Acquire);
        (b - t).max(0)
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<T> Default for WorkStealingQueue<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Drop for WorkStealingQueue<T> {
    fn drop(&mut self) {
        let ptr = self.buffer.load(Ordering::Relaxed);
        unsafe { Arc::decrement_strong_count(ptr as *const CircularBuffer<T>) };
    }
}

unsafe impl<T: Send> Send for WorkStealingQueue<T> {}
unsafe impl<T: Send> Sync for WorkStealingQueue<T> {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ws_single_threaded() {
        let q = WorkStealingQueue::new();
        q.push(1);
        q.push(2);
        q.push(3);

        assert_eq!(q.pop(), Some(3));
        assert_eq!(q.steal(), Some(1));
        assert_eq!(q.pop(), Some(2));
        assert_eq!(q.pop(), None);
    }

    #[test]
    fn test_ws_grow() {
        let q = WorkStealingQueue::new();
        for i in 0..100 {
            q.push(i);
        }
        for i in (0..100).rev() {
            assert_eq!(q.pop(), Some(i));
        }
    }
}
