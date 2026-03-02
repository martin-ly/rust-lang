//! Rust并发模式与所有权
//! 
//! 本文件展示Rust在并发环境下的所有权管理：
//! - Send/Sync trait的语义
//! - 线程间数据共享
//! - 锁模式
//! - 无锁数据结构

use std::sync::{Arc, Mutex, RwLock, mpsc};
use std::thread;
use std::time::Duration;

// ============================================
// 1. Send与Sync基础
// ============================================

/// Send: 值可以在线程间转移所有权
/// Sync: 值可以在多个线程间共享引用（&T是Send）
///
/// 自动推导规则：
/// - 原始类型都是Send+Sync
/// - 包含Send的类型是Send
/// - 包含Sync的类型是Sync（除非包含Cell等内部可变性）

/// 模式1: 验证Send/Sync实现
struct MyData {
    value: i32,
    name: String,
}

// MyData自动实现Send+Sync，因为所有字段都是Send+Sync

/// 模式2: 非Send类型
use std::rc::Rc;

// Rc<T>不是Send，因为引用计数不是线程安全的
// fn broken_send() {
//     let data = Rc::new(42);
//     thread::spawn(move || {
//         println!("{}", data); // ❌ 编译错误
//     });
// }

/// 模式3: 使用Arc替代Rc
fn arc_is_send() {
    let data = Arc::new(42);
    let data2 = Arc::clone(&data);
    
    thread::spawn(move || {
        println!("{}", data2); // ✅ OK
    });
    
    println!("{}", data);
}

// ============================================
// 2. 线程间数据共享模式
// ============================================

/// 模式4: 使用Arc<Mutex<T>>共享可变状态
struct SharedState {
    counter: i32,
    data: Vec<String>,
}

fn shared_mutable_state() {
    let state = Arc::new(Mutex::new(SharedState {
        counter: 0,
        data: vec![],
    }));
    
    let mut handles = vec![];
    
    for i in 0..5 {
        let state = Arc::clone(&state);
        let handle = thread::spawn(move || {
            let mut guard = state.lock().unwrap();
            guard.counter += 1;
            guard.data.push(format!("Thread {}", i));
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    let final_state = state.lock().unwrap();
    println!("Counter: {}", final_state.counter);
    println!("Data: {:?}", final_state.data);
}

/// 模式5: 读写锁模式 - 读多写少场景
fn rwlock_pattern() {
    let data = Arc::new(RwLock::new(vec![1, 2, 3, 4, 5]));
    
    // 多个读线程
    let mut readers = vec![];
    for _ in 0..3 {
        let data = Arc::clone(&data);
        readers.push(thread::spawn(move || {
            let read_guard = data.read().unwrap();
            println!("Read: {:?}", *read_guard);
        }));
    }
    
    // 一个写线程
    let data_writer = Arc::clone(&data);
    let writer = thread::spawn(move || {
        let mut write_guard = data_writer.write().unwrap();
        write_guard.push(6);
        println!("Written");
    });
    
    for r in readers {
        r.join().unwrap();
    }
    writer.join().unwrap();
}

/// 模式6: 使用channel进行消息传递
fn message_passing() {
    let (tx, rx) = mpsc::channel();
    
    // 发送线程
    thread::spawn(move || {
        for i in 0..5 {
            tx.send(format!("Message {}", i)).unwrap();
            thread::sleep(Duration::from_millis(100));
        }
    });
    
    // 接收主线程
    for received in rx {
        println!("Received: {}", received);
    }
}

/// 模式7: 多生产者单消费者
fn mpmc_pattern() {
    let (tx, rx) = mpsc::channel();
    
    // 多个发送线程
    for i in 0..3 {
        let tx = tx.clone();
        thread::spawn(move || {
            for j in 0..3 {
                tx.send((i, j)).unwrap();
            }
        });
    }
    
    // 必须drop原始sender，否则rx不会结束
    drop(tx);
    
    // 收集所有消息
    let mut messages: Vec<_> = rx.iter().collect();
    messages.sort();
    println!("All messages: {:?}", messages);
}

// ============================================
// 3. 作用域线程（Scoped Threads）
// ============================================

/// 模式8: 使用scope允许借用本地数据
fn scoped_threads() {
    let mut data = vec![1, 2, 3, 4, 5];
    
    // 使用rayon或std::thread::scope (Rust 1.63+)
    std::thread::scope(|s| {
        s.spawn(|| {
            println!("Thread 1: {:?}", data);
        });
        
        s.spawn(|| {
            // 可以同时存在多个只读引用
            println!("Thread 2: {:?}", data);
        });
    });
    
    // scope结束后，data的所有权回归
    data.push(6);
    println!("Main: {:?}", data);
}

/// 模式9: 并行处理切片
fn parallel_slice_processing(data: &mut [i32]) {
    use std::thread;
    
    let mid = data.len() / 2;
    let (left, right) = data.split_at_mut(mid);
    
    thread::scope(|s| {
        s.spawn(|| {
            for x in left.iter_mut() {
                *x *= 2;
            }
        });
        
        s.spawn(|| {
            for x in right.iter_mut() {
                *x *= 2;
            }
        });
    });
}

// ============================================
// 4. 锁粒度优化模式
// ============================================

use std::collections::HashMap;

/// 模式10: 细粒度锁 - 分段锁
struct ShardedLock<T, const N: usize> {
    shards: [Mutex<T>; N],
}

impl<T: Default, const N: usize> ShardedLock<T, N> {
    fn new() -> Self {
        let shards = std::array::from_fn(|_| Mutex::new(T::default()));
        Self { shards }
    }
    
    fn get_shard(&self, key: usize) -> &Mutex<T> {
        &self.shards[key % N]
    }
}

/// 模式11: 读写锁优化 - 读优先vs写优先
struct PriorityRwLock<T> {
    data: RwLock<T>,
    // 可以添加优先级控制逻辑
}

/// 模式12: 锁消除 - 使用原子操作
use std::sync::atomic::{AtomicUsize, Ordering};

struct LockFreeCounter {
    count: AtomicUsize,
}

impl LockFreeCounter {
    fn new() -> Self {
        Self { count: AtomicUsize::new(0) }
    }
    
    fn increment(&self) {
        self.count.fetch_add(1, Ordering::Relaxed);
    }
    
    fn get(&self) -> usize {
        self.count.load(Ordering::Relaxed)
    }
}

// ============================================
// 5. 内部可变性与线程安全
// ============================================

use std::cell::RefCell;

/// 模式13: RefCell不是Sync，不能在线程间共享
// fn refcell_not_sync() {
//     let data = Arc::new(RefCell::new(0));
//     let data2 = Arc::clone(&data);
//     
//     thread::spawn(move || {
//         *data2.borrow_mut() += 1; // ❌ 编译错误
//     });
// }

/// 模式14: Mutex替代RefCell实现线程安全的内部可变性
fn mutex_interior_mutability() {
    let data = Arc::new(Mutex::new(RefCell::new(vec![1, 2, 3])));
    let data2 = Arc::clone(&data);
    
    thread::spawn(move || {
        let guard = data2.lock().unwrap();
        guard.borrow_mut().push(4);
    });
}

/// 模式15: RwLock<RefCell<T>>模式
fn rwlock_refcell() {
    use std::sync::RwLock;
    
    let data = Arc::new(RwLock::new(RefCell::new(HashMap::new())));
    
    // 读线程
    let reader = Arc::clone(&data);
    let r = thread::spawn(move || {
        let read_guard = reader.read().unwrap();
        let map = read_guard.borrow();
        println!("Read: {:?}", map.get("key"));
    });
    
    // 写线程
    let writer = Arc::clone(&data);
    let w = thread::spawn(move || {
        let write_guard = writer.write().unwrap();
        write_guard.borrow_mut().insert("key", "value");
    });
    
    r.join().unwrap();
    w.join().unwrap();
}

// ============================================
// 6. 线程池模式
// ============================================

use std::sync::mpsc::{Sender, Receiver};

type Job = Box<dyn FnOnce() + Send + 'static>;

/// 模式16: 简单线程池实现
struct ThreadPool {
    workers: Vec<Worker>,
    sender: Option<Sender<Job>>,
}

struct Worker {
    id: usize,
    thread: Option<thread::JoinHandle<()>>,
}

impl ThreadPool {
    fn new(size: usize) -> Self {
        let (sender, receiver) = mpsc::channel();
        let receiver = Arc::new(Mutex::new(receiver));
        
        let mut workers = Vec::with_capacity(size);
        
        for id in 0..size {
            workers.push(Worker::new(id, Arc::clone(&receiver)));
        }
        
        Self {
            workers,
            sender: Some(sender),
        }
    }
    
    fn execute<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'static,
    {
        let job = Box::new(f);
        self.sender.as_ref().unwrap().send(job).unwrap();
    }
}

impl Worker {
    fn new(id: usize, receiver: Arc<Mutex<Receiver<Job>>>) -> Self {
        let thread = thread::spawn(move || loop {
            let job = receiver.lock().unwrap().recv();
            
            match job {
                Ok(job) => {
                    println!("Worker {} got a job; executing.", id);
                    job();
                }
                Err(_) => {
                    println!("Worker {} shutting down.", id);
                    break;
                }
            }
        });
        
        Self {
            id,
            thread: Some(thread),
        }
    }
}

impl Drop for ThreadPool {
    fn drop(&mut self) {
        drop(self.sender.take());
        
        for worker in &mut self.workers {
            if let Some(thread) = worker.thread.take() {
                thread.join().unwrap();
            }
        }
    }
}

// ============================================
// 7. 死锁避免模式
// ============================================

/// 模式17: 固定加锁顺序避免死锁
struct Account {
    id: u32,
    balance: Mutex<i64>,
}

fn transfer(from: &Account, to: &Account, amount: i64) {
    // 始终按ID顺序加锁
    let (first, second) = if from.id < to.id {
        (from, to)
    } else {
        (to, from)
    };
    
    let mut first_guard = first.balance.lock().unwrap();
    let mut second_guard = second.balance.lock().unwrap();
    
    // 实际转账逻辑
    if from.id < to.id {
        *first_guard -= amount;
        *second_guard += amount;
    } else {
        *second_guard -= amount;
        *first_guard += amount;
    }
}

/// 模式18: 使用try_lock避免死锁
fn try_lock_pattern() {
    let data1 = Arc::new(Mutex::new(0));
    let data2 = Arc::new(Mutex::new(0));
    
    let d1 = Arc::clone(&data1);
    let d2 = Arc::clone(&data2);
    
    thread::spawn(move || {
        loop {
            if let Ok(guard1) = d1.try_lock() {
                if let Ok(guard2) = d2.try_lock() {
                    println!("Got both locks: {}, {}", *guard1, *guard2);
                    break;
                }
            }
            // 短暂等待后重试
            thread::sleep(Duration::from_millis(10));
        }
    });
}

// ============================================
// 8. 屏障与同步模式
// ============================================

use std::sync::Barrier;

/// 模式19: 使用Barrier同步多个线程
fn barrier_sync() {
    let barrier = Arc::new(Barrier::new(3));
    
    for i in 0..3 {
        let b = Arc::clone(&barrier);
        thread::spawn(move || {
            println!("Thread {} before barrier", i);
            b.wait();
            println!("Thread {} after barrier", i);
        });
    }
}

/// 模式20: 条件变量模式
use std::sync::Condvar;

struct BlockingQueue<T> {
    queue: Mutex<Vec<T>>,
    cond: Condvar,
}

impl<T> BlockingQueue<T> {
    fn new() -> Self {
        Self {
            queue: Mutex::new(vec![]),
            cond: Condvar::new(),
        }
    }
    
    fn push(&self, item: T) {
        let mut queue = self.queue.lock().unwrap();
        queue.push(item);
        self.cond.notify_one();
    }
    
    fn pop(&self) -> T {
        let mut queue = self.queue.lock().unwrap();
        loop {
            if let Some(item) = queue.pop() {
                return item;
            }
            queue = self.cond.wait(queue).unwrap();
        }
    }
}

// ============================================
// 测试
// ============================================

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_parallel_processing() {
        let mut data = vec![1, 2, 3, 4, 5, 6];
        parallel_slice_processing(&mut data);
        assert_eq!(data, vec![2, 4, 6, 8, 10, 12]);
    }
    
    #[test]
    fn test_lock_free_counter() {
        let counter = Arc::new(LockFreeCounter::new());
        let mut handles = vec![];
        
        for _ in 0..10 {
            let c = Arc::clone(&counter);
            handles.push(thread::spawn(move || {
                for _ in 0..100 {
                    c.increment();
                }
            }));
        }
        
        for h in handles {
            h.join().unwrap();
        }
        
        assert_eq!(counter.get(), 1000);
    }
    
    #[test]
    fn test_thread_pool() {
        let pool = ThreadPool::new(4);
        let counter = Arc::new(Mutex::new(0));
        
        for _ in 0..8 {
            let c = Arc::clone(&counter);
            pool.execute(move || {
                let mut guard = c.lock().unwrap();
                *guard += 1;
            });
        }
        
        // 等待所有任务完成
        drop(pool);
        
        assert_eq!(*counter.lock().unwrap(), 8);
    }
}

fn main() {
    println!("并发模式示例");
    
    shared_mutable_state();
    message_passing();
    scoped_threads();
    
    let mut data = vec![1, 2, 3, 4, 5, 6];
    parallel_slice_processing(&mut data);
    println!("Processed: {:?}", data);
}
