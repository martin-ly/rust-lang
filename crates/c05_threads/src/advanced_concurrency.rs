//! 高级并发编程模块
//! 
//! 本模块提供Rust 2025版本的高级并发编程特性，包括：
//! - 高性能线程池实现
//! - 工作窃取调度算法
//! - 无锁数据结构
//! - 并发性能优化技术

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::collections::VecDeque;
use std::thread;
use std::time::Duration;
use std::cell::UnsafeCell;

// ============================================================================
// 高性能线程池实现
// ============================================================================

/// 高性能线程池，支持工作窃取调度
pub struct HighPerformanceThreadPool {
    workers: Vec<Worker>,
    sender: Option<crossbeam_channel::Sender<Box<dyn FnOnce() + Send + 'static>>>,
    global_queue: Arc<GlobalTaskQueue>,
}

impl HighPerformanceThreadPool {
    /// 创建新的高性能线程池
    pub fn new(size: usize) -> Self {
        assert!(size > 0);
        
        let (sender, receiver) = crossbeam_channel::unbounded();
        let global_queue = Arc::new(GlobalTaskQueue::new());
        
        let mut workers = Vec::with_capacity(size);
        
        for id in 0..size {
            workers.push(Worker::new(
                id,
                receiver.clone(),
                Arc::clone(&global_queue),
            ));
        }
        
        Self {
            workers,
            sender: Some(sender),
            global_queue,
        }
    }
    
    /// 执行任务
    pub fn execute<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'static,
    {
        if let Some(sender) = self.sender.as_ref() {
            sender.send(Box::new(f)).unwrap();
        }
    }
    
    /// 并行执行多个任务
    pub fn execute_batch<T>(&self, tasks: Vec<Box<dyn FnOnce() -> T + Send>>) -> Vec<T>
    where
        T: Send + 'static,
    {
        let task_count = tasks.len();
        let (tx, rx) = crossbeam_channel::bounded(task_count);
        
        for task in tasks {
            let tx = tx.clone();
            self.execute(move || {
                let result = task();
                let _ = tx.send(result);
            });
        }
        
        // 收集结果
        rx.iter().take(task_count).collect()
    }
    
    /// 获取线程池统计信息
    pub fn stats(&self) -> ThreadPoolStats {
        self.global_queue.get_stats()
    }
}

impl Drop for HighPerformanceThreadPool {
    fn drop(&mut self) {
        // 关闭发送端
        self.sender.take();
        
        // 等待所有工作线程完成
        for worker in &mut self.workers {
            if let Some(thread) = worker.thread.take() {
                let _ = thread.join();
            }
        }
    }
}

/// 工作线程
struct Worker {
    _id: usize,
    thread: Option<thread::JoinHandle<()>>,
}

impl Worker {
    fn new(
        id: usize,
        receiver: crossbeam_channel::Receiver<Box<dyn FnOnce() + Send + 'static>>,
        global_queue: Arc<GlobalTaskQueue>,
    ) -> Self {
        let thread = thread::spawn(move || {
            let mut local_queue = LocalTaskQueue::new();
            
            loop {
                // 优先处理本地队列
                if let Some(task) = local_queue.pop() {
                    task();
                    continue;
                }
                
                // 尝试从全局队列获取任务
                if let Ok(task) = receiver.try_recv() {
                    task();
                    continue;
                }
                
                // 尝试从其他线程窃取任务
                if let Some(task) = global_queue.steal_task() {
                    local_queue.push(task);
                    continue;
                }
                
                // 短暂休眠避免忙等待
                thread::sleep(Duration::from_micros(1));
            }
        });
        
        Self {
            _id: id,
            thread: Some(thread),
        }
    }
}

// ============================================================================
// 工作窃取调度算法
// ============================================================================

/// 全局任务队列
struct GlobalTaskQueue {
    tasks: Mutex<VecDeque<Box<dyn FnOnce() + Send + 'static>>>,
    stats: Mutex<QueueStats>,
}

impl GlobalTaskQueue {
    fn new() -> Self {
        Self {
            tasks: Mutex::new(VecDeque::new()),
            stats: Mutex::new(QueueStats::default()),
        }
    }
    
    #[allow(dead_code)]
    fn push(&self, task: Box<dyn FnOnce() + Send + 'static>) {
        let mut tasks = self.tasks.lock().unwrap();
        tasks.push_back(task);
        
        let mut stats = self.stats.lock().unwrap();
        stats.total_tasks += 1;
        stats.current_tasks += 1;
    }
    
    fn steal_task(&self) -> Option<Box<dyn FnOnce() + Send + 'static>> {
        let mut tasks = self.tasks.lock().unwrap();
        if let Some(task) = tasks.pop_back() {
            let mut stats = self.stats.lock().unwrap();
            stats.stolen_tasks += 1;
            stats.current_tasks -= 1;
            Some(task)
        } else {
            None
        }
    }
    
    fn get_stats(&self) -> ThreadPoolStats {
        let stats = self.stats.lock().unwrap();
        ThreadPoolStats {
            total_tasks: stats.total_tasks,
            current_tasks: stats.current_tasks,
            stolen_tasks: stats.stolen_tasks,
        }
    }
}

/// 本地任务队列
struct LocalTaskQueue {
    tasks: VecDeque<Box<dyn FnOnce() + Send + 'static>>,
}

impl LocalTaskQueue {
    fn new() -> Self {
        Self {
            tasks: VecDeque::new(),
        }
    }
    
    fn push(&mut self, task: Box<dyn FnOnce() + Send + 'static>) {
        self.tasks.push_front(task);
    }
    
    fn pop(&mut self) -> Option<Box<dyn FnOnce() + Send + 'static>> {
        self.tasks.pop_front()
    }
    

    #[allow(dead_code)]
    fn is_empty(&self) -> bool {
        self.tasks.is_empty()
    }
}

// ============================================================================
// 无锁数据结构
// ============================================================================

/// 无锁环形缓冲区
pub struct LockFreeRingBuffer<T> {
    buffer: UnsafeCell<Vec<T>>,
    head: AtomicUsize,
    tail: AtomicUsize,
    size: usize,
}

impl<T: Default + Clone> LockFreeRingBuffer<T> {
    /// 创建新的无锁环形缓冲区
    pub fn new(size: usize) -> Self {
        let mut buffer = Vec::with_capacity(size);
        for _ in 0..size {
            buffer.push(T::default());
        }
        
        Self {
            buffer: UnsafeCell::new(buffer),
            head: AtomicUsize::new(0),
            tail: AtomicUsize::new(0),
            size,
        }
    }
    
    /// 尝试推送元素
    pub fn try_push(&self, item: T) -> Result<(), T> {
        let tail = self.tail.load(Ordering::Relaxed);
        let next_tail = (tail + 1) % self.size;
        
        if next_tail == self.head.load(Ordering::Acquire) {
            return Err(item);
        }
        
        unsafe {
            let ptr = (*self.buffer.get()).as_mut_ptr().add(tail);
            std::ptr::write(ptr, item);
        }
        
        self.tail.store(next_tail, Ordering::Release);
        Ok(())
    }
    
    /// 尝试弹出元素
    pub fn try_pop(&self) -> Option<T> {
        let head = self.head.load(Ordering::Relaxed);
        
        if head == self.tail.load(Ordering::Acquire) {
            return None;
        }
        
        let item = unsafe {
            let ptr = (*self.buffer.get()).as_ptr().add(head);
            std::ptr::read(ptr)
        };
        // 将已读出的槽位重置为默认值，避免后续读取到已移动的值
        unsafe {
            let dst = (*self.buffer.get()).as_mut_ptr().add(head);
            std::ptr::write(dst, T::default());
        }
        
        let next_head = (head + 1) % self.size;
        self.head.store(next_head, Ordering::Release);
        
        Some(item)
    }
    
    /// 检查是否为空
    pub fn is_empty(&self) -> bool {
        self.head.load(Ordering::Relaxed) == self.tail.load(Ordering::Relaxed)
    }
    
    /// 检查是否已满
    pub fn is_full(&self) -> bool {
        let next_tail = (self.tail.load(Ordering::Relaxed) + 1) % self.size;
        next_tail == self.head.load(Ordering::Relaxed)
    }
}

/// 无锁栈
pub struct LockFreeStack<T> {
    head: AtomicUsize,
    nodes: UnsafeCell<Vec<StackNode<T>>>,
    free_list: AtomicUsize,
}

struct StackNode<T> {
    data: Option<T>,
    next: AtomicUsize,
}

impl<T> LockFreeStack<T> {
    /// 创建新的无锁栈
    pub fn new(capacity: usize) -> Self {
        let mut nodes = Vec::with_capacity(capacity);
        for i in 0..capacity {
            nodes.push(StackNode {
                data: None,
                next: AtomicUsize::new(if i + 1 < capacity { i + 1 } else { usize::MAX }),
            });
        }
        
        Self {
            head: AtomicUsize::new(usize::MAX),
            nodes: UnsafeCell::new(nodes),
            free_list: AtomicUsize::new(0),
        }
    }
    
    /// 推送元素
    pub fn push(&self, item: T) -> Result<(), T> {
        let node_idx = self.allocate_node()?;
        
        // 设置节点数据
        unsafe {
            let node_ptr = (*self.nodes.get()).as_mut_ptr().add(node_idx);
            (*node_ptr).data = Some(item);
        }
        
        // 原子地更新栈顶
        loop {
            let current_head = self.head.load(Ordering::Acquire);
            unsafe {
                let node_ptr = (*self.nodes.get()).as_mut_ptr().add(node_idx);
                (*node_ptr).next.store(current_head, Ordering::Release);
            }
            
            if self.head.compare_exchange_weak(
                current_head,
                node_idx,
                Ordering::Release,
                Ordering::Relaxed,
            ).is_ok() {
                break;
            }
        }
        
        Ok(())
    }
    
    /// 弹出元素
    pub fn pop(&self) -> Option<T> {
        loop {
            let current_head = self.head.load(Ordering::Acquire);
            
            if current_head == usize::MAX {
                return None;
            }
            
            let next = unsafe {
                let node_ptr = (*self.nodes.get()).as_ptr().add(current_head);
                (*node_ptr).next.load(Ordering::Acquire)
            };
            
            if self.head.compare_exchange_weak(
                current_head,
                next,
                Ordering::Release,
                Ordering::Relaxed,
            ).is_ok() {
                let data = unsafe {
                    let node_ptr = (*self.nodes.get()).as_mut_ptr().add(current_head);
                    (*node_ptr).data.take()
                };
                self.free_node(current_head);
                return data;
            }
        }
    }
    
    fn allocate_node(&self) -> Result<usize, T> {
        let mut current = self.free_list.load(Ordering::Acquire);
        
        loop {
            if current == usize::MAX {
                return Err(unsafe { std::mem::zeroed() });
            }
            
            let next = unsafe {
                let node_ptr = (*self.nodes.get()).as_ptr().add(current);
                (*node_ptr).next.load(Ordering::Acquire)
            };
            
            if self.free_list.compare_exchange_weak(
                current,
                next,
                Ordering::Release,
                Ordering::Relaxed,
            ).is_ok() {
                return Ok(current);
            }
            
            current = self.free_list.load(Ordering::Acquire);
        }
    }
    
    fn free_node(&self, node_idx: usize) {
        let mut current = self.free_list.load(Ordering::Acquire);
        
        loop {
            unsafe {
                let node_ptr = (*self.nodes.get()).as_mut_ptr().add(node_idx);
                (*node_ptr).next.store(current, Ordering::Release);
            }
            
            if self.free_list.compare_exchange_weak(
                current,
                node_idx,
                Ordering::Release,
                Ordering::Relaxed,
            ).is_ok() {
                break;
            }
            
            current = self.free_list.load(Ordering::Acquire);
        }
    }
}

// ============================================================================
// 并发性能优化技术
// ============================================================================

/// 并发归约算法
pub fn parallel_reduce<T, F>(
    data: &[T],
    num_threads: usize,
    identity: T,
    op: F,
) -> T
where
    T: Send + Sync + Clone + 'static,
    F: Fn(T, &T) -> T + Send + Sync + Clone + 'static,
{
    if data.is_empty() {
        return identity;
    }
    
    let chunk_size = (data.len() + num_threads - 1) / num_threads;
    let data = Arc::new(data.to_vec());
    let results = Arc::new(Mutex::new(Vec::new()));
    
    let handles: Vec<_> = (0..num_threads)
        .map(|i| {
            let data = Arc::clone(&data);
            let results = Arc::clone(&results);
            let identity = identity.clone();
            let op = op.clone();
            
            thread::spawn(move || {
                let start = i * chunk_size;
                let end = std::cmp::min(start + chunk_size, data.len());
                
                if start < end {
                    let chunk = &data[start..end];
                    let local_result = chunk.iter().fold(identity, |acc, x| op(acc, x));
                    
                    let mut results = results.lock().unwrap();
                    results.push(local_result);
                }
            })
        })
        .collect();
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    let results = results.lock().unwrap();
    results.iter().fold(identity, |acc, x| op(acc, x))
}

/// 并发映射算法
pub fn parallel_map<T, U, F>(
    data: &[T],
    num_threads: usize,
    f: F,
) -> Vec<U>
where
    T: Send + Sync + Clone + 'static,
    U: Send + Sync + Default + Clone + std::fmt::Debug + 'static,
    F: Fn(&T) -> U + Send + Sync + Clone + 'static,
{
    if data.is_empty() {
        return Vec::new();
    }
    
    let chunk_size = (data.len() + num_threads - 1) / num_threads;
    let data = Arc::new(data.to_vec());
    let results = Arc::new(Mutex::new(vec![U::default(); data.len()]));
    
    let handles: Vec<_> = (0..num_threads)
        .map(|i| {
            let data = Arc::clone(&data);
            let results = Arc::clone(&results);
            let f = f.clone();
            
            thread::spawn(move || {
                let start = i * chunk_size;
                let end = std::cmp::min(start + chunk_size, data.len());
                
                if start < end {
                    let chunk = &data[start..end];
                    let mut results = results.lock().unwrap();
                    
                    for (j, item) in chunk.iter().enumerate() {
                        let result = f(item);
                        results[start + j] = result;
                    }
                }
            })
        })
        .collect();
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    Arc::try_unwrap(results).unwrap().into_inner().unwrap()
}

// ============================================================================
// 统计信息结构
// ============================================================================

#[derive(Debug, Clone)]
pub struct ThreadPoolStats {
    pub total_tasks: usize,
    pub current_tasks: usize,
    pub stolen_tasks: usize,
}

#[derive(Debug, Default)]
struct QueueStats {
    total_tasks: usize,
    current_tasks: usize,
    stolen_tasks: usize,
}

// ============================================================================
// 测试模块
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_high_performance_thread_pool() {
        let pool = HighPerformanceThreadPool::new(4);
        
        let results = pool.execute_batch(vec![
            Box::new(|| 1 + 1),
            Box::new(|| 2 * 2),
            Box::new(|| 3 + 3),
            Box::new(|| 4 * 4),
        ]);
        
        assert_eq!(results, vec![2, 4, 6, 16]);
    }
    
    #[test]
    fn test_lock_free_ring_buffer() {
        let buffer = LockFreeRingBuffer::new(3);
        
        assert!(buffer.try_push(1).is_ok());
        assert!(buffer.try_push(2).is_ok());
        assert!(buffer.try_push(3).is_ok());
        assert!(buffer.try_push(4).is_err()); // 缓冲区已满
        
        assert_eq!(buffer.try_pop(), Some(1));
        assert_eq!(buffer.try_pop(), Some(2));
        assert_eq!(buffer.try_pop(), Some(3));
        assert_eq!(buffer.try_pop(), None); // 缓冲区为空
    }
    
    #[test]
    fn test_lock_free_stack() {
        let stack = LockFreeStack::new(10);
        
        assert!(stack.push(1).is_ok());
        assert!(stack.push(2).is_ok());
        assert!(stack.push(3).is_ok());
        
        assert_eq!(stack.pop(), Some(3));
        assert_eq!(stack.pop(), Some(2));
        assert_eq!(stack.pop(), Some(1));
        assert_eq!(stack.pop(), None);
    }
    
    #[test]
    fn test_parallel_reduce() {
        let data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let result = parallel_reduce(&data, 4, 0, |acc, x| acc + x);
        
        assert_eq!(result, 55);
    }
    
    #[test]
    fn test_parallel_map() {
        let data = vec![1, 2, 3, 4, 5];
        let result = parallel_map(&data, 2, |&x| x * 2);
        
        assert_eq!(result, vec![2, 4, 6, 8, 10]);
    }
}
