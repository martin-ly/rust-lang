//! 并发数据结构示例
//! 
//! 整合 C04(泛型), C05(并发), C08(算法), C09(设计模式)

use std::collections::VecDeque;
use std::sync::{Arc, Condvar, Mutex};
use std::thread;
use std::time::Duration;

/// 泛型有界阻塞队列（生产者-消费者模式）
pub struct BoundedQueue<T> {
    queue: Mutex<VecDeque<T>>,
    condvar: Condvar,
    capacity: usize,
}

impl<T> BoundedQueue<T> {
    pub fn new(capacity: usize) -> Self {
        Self {
            queue: Mutex::new(VecDeque::new()),
            condvar: Condvar::new(),
            capacity,
        }
    }
    
    /// 入队（阻塞）
    pub fn enqueue(&self, item: T) {
        let mut queue = self.queue.lock().unwrap();
        
        while queue.len() >= self.capacity {
            queue = self.condvar.wait(queue).unwrap();
        }
        
        queue.push_back(item);
        self.condvar.notify_one();
    }
    
    /// 出队（阻塞）
    pub fn dequeue(&self) -> T {
        let mut queue = self.queue.lock().unwrap();
        
        while queue.is_empty() {
            queue = self.condvar.wait(queue).unwrap();
        }
        
        let item = queue.pop_front().unwrap();
        self.condvar.notify_one();
        item
    }
    
    /// 尝试入队（非阻塞）
    pub fn try_enqueue(&self, item: T) -> bool {
        let mut queue = self.queue.lock().unwrap();
        
        if queue.len() < self.capacity {
            queue.push_back(item);
            self.condvar.notify_one();
            true
        } else {
            false
        }
    }
    
    /// 尝试出队（非阻塞）
    pub fn try_dequeue(&self) -> Option<T> {
        let mut queue = self.queue.lock().unwrap();
        
        let item = queue.pop_front();
        if item.is_some() {
            self.condvar.notify_one();
        }
        item
    }
    
    /// 当前大小
    pub fn len(&self) -> usize {
        self.queue.lock().unwrap().len()
    }
    
    /// 是否为空
    pub fn is_empty(&self) -> bool {
        self.queue.lock().unwrap().is_empty()
    }
}

/// 泛型线程安全栈
pub struct ConcurrentStack<T> {
    stack: Mutex<Vec<T>>,
    condvar: Condvar,
}

impl<T> ConcurrentStack<T> {
    pub fn new() -> Self {
        Self {
            stack: Mutex::new(Vec::new()),
            condvar: Condvar::new(),
        }
    }
    
    pub fn push(&self, item: T) {
        let mut stack = self.stack.lock().unwrap();
        stack.push(item);
        self.condvar.notify_one();
    }
    
    pub fn pop(&self) -> Option<T> {
        let mut stack = self.stack.lock().unwrap();
        stack.pop()
    }
    
    pub fn blocking_pop(&self) -> T {
        let mut stack = self.stack.lock().unwrap();
        
        loop {
            if let Some(item) = stack.pop() {
                return item;
            }
            stack = self.condvar.wait(stack).unwrap();
        }
    }
    
    pub fn len(&self) -> usize {
        self.stack.lock().unwrap().len()
    }
    
    pub fn is_empty(&self) -> bool {
        self.stack.lock().unwrap().is_empty()
    }
}

/// 工作窃取队列（简化版）
pub struct WorkStealingQueue<T> {
    local: Mutex<VecDeque<T>>,
    shared: Mutex<VecDeque<T>>,
}

impl<T> WorkStealingQueue<T> {
    pub fn new() -> Self {
        Self {
            local: Mutex::new(VecDeque::new()),
            shared: Mutex::new(VecDeque::new()),
        }
    }
    
    /// 本地线程推送（LIFO）
    pub fn push_local(&self, item: T) {
        self.local.lock().unwrap().push_back(item);
    }
    
    /// 本地线程弹出（LIFO）
    pub fn pop_local(&self) -> Option<T> {
        self.local.lock().unwrap().pop_back()
    }
    
    /// 偷取任务（FIFO，从其他线程调用）
    pub fn steal(&self) -> Option<T> {
        // 先尝试偷取共享队列
        if let Some(item) = self.shared.lock().unwrap().pop_front() {
            return Some(item);
        }
        
        // 再尝试偷取本地队列
        self.local.lock().unwrap().pop_front()
    }
    
    /// 分发到共享队列
    pub fn push_shared(&self, item: T) {
        self.shared.lock().unwrap().push_back(item);
    }
}

/// 演示：生产者-消费者模式
fn demo_producer_consumer() {
    println!("\n📦 演示: 生产者-消费者模式");
    
    let queue = Arc::new(BoundedQueue::new(10));
    let queue_consumer = Arc::clone(&queue);
    
    // 生产者线程
    let producer = thread::spawn(move || {
        for i in 0..20 {
            queue.enqueue(i);
            println!("  生产: {}", i);
            thread::sleep(Duration::from_millis(10));
        }
    });
    
    // 消费者线程
    let consumer = thread::spawn(move || {
        for _ in 0..20 {
            let item = queue_consumer.dequeue();
            println!("  消费: {}", item);
            thread::sleep(Duration::from_millis(20));
        }
    });
    
    producer.join().unwrap();
    consumer.join().unwrap();
    
    println!("  ✅ 完成!");
}

/// 演示：工作窃取
fn demo_work_stealing() {
    println!("\n🔄 演示: 工作窃取队列");
    
    let queue = Arc::new(WorkStealingQueue::new());
    
    // 主线程添加任务
    for i in 0..10 {
        queue.push_local(i);
    }
    
    // 工作线程偷取任务
    let queue_stealer = Arc::clone(&queue);
    let worker = thread::spawn(move || {
        let mut stolen = 0;
        while let Some(item) = queue_stealer.steal() {
            println!("  偷取任务: {}", item);
            stolen += 1;
            thread::sleep(Duration::from_millis(5));
        }
        stolen
    });
    
    // 主线程处理本地任务
    let mut local = 0;
    while let Some(item) = queue.pop_local() {
        println!("  本地任务: {}", item);
        local += 1;
        thread::sleep(Duration::from_millis(5));
    }
    
    let stolen = worker.join().unwrap();
    
    println!("  本地处理: {}, 偷取: {}", local, stolen);
    println!("  ✅ 完成!");
}

/// 演示：并发栈
fn demo_concurrent_stack() {
    println!("\n📚 演示: 并发栈");
    
    let stack = Arc::new(ConcurrentStack::new());
    let mut handles = vec![];
    
    // 多个线程同时压栈
    for i in 0..5 {
        let stack_clone = Arc::clone(&stack);
        let handle = thread::spawn(move || {
            for j in 0..5 {
                stack_clone.push(i * 10 + j);
            }
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("  栈大小: {}", stack.len());
    
    // 弹出所有元素
    while let Some(item) = stack.pop() {
        print!("{} ", item);
    }
    println!("\n  ✅ 完成!");
}

fn main() {
    println!("🦀 Rust 并发数据结构示例");
    println!("整合: 泛型 + 并发 + 算法 + 设计模式\n");
    
    demo_producer_consumer();
    demo_work_stealing();
    demo_concurrent_stack();
    
    println!("\n✨ 所有演示完成!");
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_bounded_queue() {
        let queue = BoundedQueue::new(3);
        
        assert!(queue.try_enqueue(1));
        assert!(queue.try_enqueue(2));
        assert!(queue.try_enqueue(3));
        assert!(!queue.try_enqueue(4)); // 已满
        
        assert_eq!(queue.try_dequeue(), Some(1));
        assert_eq!(queue.try_dequeue(), Some(2));
        assert_eq!(queue.try_dequeue(), Some(3));
        assert_eq!(queue.try_dequeue(), None);
    }
    
    #[test]
    fn test_concurrent_stack() {
        let stack = ConcurrentStack::new();
        
        stack.push(1);
        stack.push(2);
        stack.push(3);
        
        assert_eq!(stack.len(), 3);
        assert_eq!(stack.pop(), Some(3));
        assert_eq!(stack.pop(), Some(2));
    }
}
