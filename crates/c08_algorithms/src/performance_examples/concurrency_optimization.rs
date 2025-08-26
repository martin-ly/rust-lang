//! 并发性能优化实践示例

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;

/// 原子计数器
pub struct AtomicCounter {
    value: AtomicUsize,
}

impl AtomicCounter {
    pub fn new() -> Self {
        Self {
            value: AtomicUsize::new(0),
        }
    }

    pub fn increment(&self) -> usize {
        self.value.fetch_add(1, Ordering::Relaxed)
    }

    pub fn get(&self) -> usize {
        self.value.load(Ordering::Relaxed)
    }
}

/// 简单线程池
pub struct SimpleThreadPool {
    workers: Vec<thread::JoinHandle<()>>,
    sender: Option<std::sync::mpsc::Sender<Box<dyn FnOnce() + Send + 'static>>>,
}

impl SimpleThreadPool {
    pub fn new(size: usize) -> Self {
        let (sender, receiver) = std::sync::mpsc::channel::<Box<dyn FnOnce() + Send + 'static>>();
        let receiver = Arc::new(Mutex::new(receiver));

        let mut workers = Vec::with_capacity(size);

        for _ in 0..size {
            let receiver = Arc::clone(&receiver);
            workers.push(thread::spawn(move || {
                while let Ok(job) = receiver.lock().unwrap().recv() {
                    job();
                }
            }));
        }

        SimpleThreadPool { workers, sender: Some(sender) }
    }

    pub fn execute<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'static,
    {
        self.sender.send(Box::new(f)).unwrap();
    }
}

impl Drop for SimpleThreadPool {
    fn drop(&mut self) {
        // 通过丢弃sender关闭通道，工作线程将退出循环
        self.sender.take();
        for handle in self.workers.drain(..) {
            let _ = handle.join();
        }
    }
}

/// 无锁栈（简化版）
pub struct LockFreeStack<T> {
    head: Arc<AtomicUsize>,
    data: Arc<Mutex<Vec<Option<T>>>>,
}

impl<T> LockFreeStack<T> {
    pub fn new() -> Self {
        Self {
            head: Arc::new(AtomicUsize::new(0)),
            data: Arc::new(Mutex::new(Vec::new())),
        }
    }

    pub fn push(&self, value: T) {
        let mut data = self.data.lock().unwrap();
        data.push(Some(value));
        self.head.fetch_add(1, Ordering::Relaxed);
    }

    pub fn pop(&self) -> Option<T> {
        let current = self.head.load(Ordering::Relaxed);
        if current == 0 {
            return None;
        }
        
        self.head.fetch_sub(1, Ordering::Relaxed);
        let mut data = self.data.lock().unwrap();
        data.pop().flatten()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_atomic_counter() {
        let counter = AtomicCounter::new();
        
        assert_eq!(counter.increment(), 0);
        assert_eq!(counter.increment(), 1);
        assert_eq!(counter.get(), 2);
    }

    #[test]
    fn test_simple_thread_pool() {
        let pool = SimpleThreadPool::new(2);
        let counter = Arc::new(AtomicCounter::new());
        
        for _ in 0..10 {
            let counter = Arc::clone(&counter);
            pool.execute(move || {
                counter.increment();
            });
        }
        
        thread::sleep(std::time::Duration::from_millis(100));
        assert_eq!(counter.get(), 10);
    }

    #[test]
    fn test_lock_free_stack() {
        let stack = LockFreeStack::new();
        
        stack.push(1);
        stack.push(2);
        
        assert_eq!(stack.pop(), Some(2));
        assert_eq!(stack.pop(), Some(1));
        assert_eq!(stack.pop(), None);
    }
}
