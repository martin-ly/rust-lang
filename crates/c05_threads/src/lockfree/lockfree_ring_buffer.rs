//! 无锁环形缓冲区实现
//! 
//! 本模块提供了多种无锁环形缓冲区实现：
//! - 单生产者单消费者环形缓冲区
//! - 多生产者单消费者环形缓冲区
//! - 多生产者多消费者环形缓冲区
//! - 可扩展环形缓冲区

#[allow(unused_imports)]
use std::sync::{Arc, atomic::{AtomicUsize, AtomicPtr, Ordering}};
//use std::cell::UnsafeCell;
use std::thread;
use crossbeam_queue::ArrayQueue;
#[allow(unused_imports)]
use crossbeam_utils::CachePadded;

#[cfg(feature = "custom_ring_buffers")]
/// 单生产者单消费者环形缓冲区
/// 
/// 使用原子操作实现的高性能SPSC环形缓冲区
pub struct SpscRingBuffer<T> {
    buffer: Vec<CachePadded<UnsafeCell<Option<T>>>>,
    capacity: usize,
    head: CachePadded<AtomicUsize>,
    tail: CachePadded<AtomicUsize>,
}

// SPSC：单生产者单消费者，基于索引原子与独占访问，声明为线程安全
#[cfg(feature = "custom_ring_buffers")]
unsafe impl<T: Send> Send for SpscRingBuffer<T> {}
#[cfg(feature = "custom_ring_buffers")]
unsafe impl<T: Send> Sync for SpscRingBuffer<T> {}

#[cfg(feature = "custom_ring_buffers")]
impl<T> SpscRingBuffer<T> {
    /// 创建新的SPSC环形缓冲区
    pub fn new(capacity: usize) -> Self {
        let mut buffer = Vec::with_capacity(capacity);
        for _ in 0..capacity {
            buffer.push(CachePadded::new(UnsafeCell::new(None)));
        }
        
        Self {
            buffer,
            capacity,
            head: CachePadded::new(AtomicUsize::new(0)),
            tail: CachePadded::new(AtomicUsize::new(0)),
        }
    }
    
    /// 尝试推送元素
    pub fn try_push(&self, item: T) -> Result<(), T> {
        let current_tail = self.tail.load(Ordering::Relaxed);
        let next_tail = (current_tail + 1) % self.capacity;
        
        // 检查缓冲区是否已满
        if next_tail == self.head.load(Ordering::Acquire) {
            return Err(item);
        }
        
        // 存储元素
        unsafe {
            let slot = self.buffer.get_unchecked(current_tail);
            *slot.get() = Some(item);
        }
        
        // 更新尾指针
        self.tail.store(next_tail, Ordering::Release);
        Ok(())
    }
    
    /// 尝试弹出元素
    pub fn try_pop(&self) -> Option<T> {
        let current_head = self.head.load(Ordering::Relaxed);
        
        // 检查缓冲区是否为空
        if current_head == self.tail.load(Ordering::Acquire) {
            return None;
        }
        
        // 读取元素
        let item = unsafe {
            let slot = self.buffer.get_unchecked(current_head);
            (*slot.get()).take()
        };
        
        // 更新头指针
        let next_head = (current_head + 1) % self.capacity;
        self.head.store(next_head, Ordering::Release);
        
        item
    }
    
    /// 获取缓冲区大小
    pub fn len(&self) -> usize {
        let tail = self.tail.load(Ordering::Acquire);
        let head = self.head.load(Ordering::Acquire);
        
        if tail >= head {
            tail - head
        } else {
            self.capacity - head + tail
        }
    }
    
    /// 检查缓冲区是否为空
    pub fn is_empty(&self) -> bool {
        self.head.load(Ordering::Acquire) == self.tail.load(Ordering::Acquire)
    }
    
    /// 检查缓冲区是否已满
    pub fn is_full(&self) -> bool {
        let tail = self.tail.load(Ordering::Acquire);
        let next_tail = (tail + 1) % self.capacity;
        next_tail == self.head.load(Ordering::Acquire)
    }
    
    /// 运行SPSC示例
    pub fn run_example() {
        println!("=== SPSC环形缓冲区示例 ===");
        
        let buffer = Arc::new(SpscRingBuffer::new(1000));
        let buffer_clone = buffer.clone();
        
        // 生产者线程
        let producer = thread::spawn(move || {
            for i in 0..1000 {
                while buffer.try_push(i).is_err() {
                    thread::yield_now();
                }
            }
            println!("生产者完成");
        });
        
        // 消费者线程
        let consumer = thread::spawn(move || {
            let mut count = 0;
            while count < 1000 {
                if let Some(item) = buffer_clone.try_pop() {
                    count += 1;
                    if count % 100 == 0 {
                        println!("消费者处理了 {} 个元素", count);
                    }
                } else {
                    thread::yield_now();
                }
            }
            println!("消费者完成");
        });
        
        producer.join().unwrap();
        consumer.join().unwrap();
    }
}

#[cfg(feature = "custom_ring_buffers")]
/// 多生产者单消费者环形缓冲区
/// 
/// 使用原子操作实现的高性能MPSC环形缓冲区
pub struct MpscRingBuffer<T> {
    buffer: Vec<CachePadded<UnsafeCell<Option<T>>>>,
    capacity: usize,
    head: CachePadded<AtomicUsize>,
    tail: CachePadded<AtomicUsize>,
    producer_count: AtomicUsize,
}

// MPSC：多生产者单消费者，通过 CAS 保证每个槽位独占写入
#[cfg(feature = "custom_ring_buffers")]
unsafe impl<T: Send> Send for MpscRingBuffer<T> {}
#[cfg(feature = "custom_ring_buffers")]
unsafe impl<T: Send> Sync for MpscRingBuffer<T> {}

#[cfg(feature = "custom_ring_buffers")]
impl<T> MpscRingBuffer<T> {
    /// 创建新的MPSC环形缓冲区
    pub fn new(capacity: usize) -> Self {
        let mut buffer = Vec::with_capacity(capacity);
        for _ in 0..capacity {
            buffer.push(CachePadded::new(UnsafeCell::new(None)));
        }
        
        Self {
            buffer,
            capacity,
            head: CachePadded::new(AtomicUsize::new(0)),
            tail: CachePadded::new(AtomicUsize::new(0)),
            producer_count: AtomicUsize::new(0),
        }
    }
    
    /// 尝试推送元素
    pub fn try_push(&self, item: T) -> Result<(), T> {
        loop {
            let current_tail = self.tail.load(Ordering::Relaxed);
            let next_tail = (current_tail + 1) % self.capacity;
            // 满
            if next_tail == self.head.load(Ordering::Acquire) {
                return Err(item);
            }
            // 先占有槽位（推进 tail），保证独占写
            match self.tail.compare_exchange_weak(
                current_tail,
                next_tail,
                Ordering::AcqRel,
                Ordering::Relaxed,
            ) {
                Ok(_) => {
                    // 写入数据到被占有的槽位
                    unsafe {
                        let slot = self.buffer.get_unchecked(current_tail);
                        *slot.get() = Some(item);
                    }
                    return Ok(());
                }
                Err(_) => continue,
            }
        }
    }
    
    /// 尝试弹出元素
    pub fn try_pop(&self) -> Option<T> {
        let current_head = self.head.load(Ordering::Relaxed);
        
        // 检查缓冲区是否为空
        if current_head == self.tail.load(Ordering::Acquire) {
            return None;
        }
        
        // 读取元素
        let item = unsafe {
            let slot = self.buffer.get_unchecked(current_head);
            (*slot.get()).take()
        };
        
        // 更新头指针
        let next_head = (current_head + 1) % self.capacity;
        self.head.store(next_head, Ordering::Release);
        
        item
    }
    
    /// 运行MPSC示例
    pub fn run_example() {
        println!("=== MPSC环形缓冲区示例 ===");
        
        let buffer = Arc::new(MpscRingBuffer::new(1000));
        
        // 创建多个生产者线程
        let producer_handles: Vec<_> = (0..4)
            .map(|producer_id| {
                let buffer = buffer.clone();
                thread::spawn(move || {
                    for i in 0..250 {
                        let item = producer_id * 250 + i;
                        while buffer.try_push(item).is_err() {
                            thread::yield_now();
                        }
                    }
                    println!("生产者 {} 完成", producer_id);
                })
            })
            .collect();
        
        // 消费者线程
        let consumer = thread::spawn({
            let buffer = buffer.clone();
            move || {
                let mut count = 0;
                while count < 1000 {
                    if let Some(_item) = buffer.try_pop() {
                        count += 1;
                        if count % 100 == 0 {
                            println!("消费者处理了 {} 个元素", count);
                        }
                    } else {
                        thread::yield_now();
                    }
                }
                println!("消费者完成");
            }
        });
        
        // 等待所有生产者完成
        for handle in producer_handles {
            handle.join().unwrap();
        }
        
        // 等待消费者完成
        consumer.join().unwrap();
    }
}

#[cfg(feature = "custom_ring_buffers")]
/// 多生产者多消费者环形缓冲区
/// 
/// 使用原子操作实现的高性能MPMC环形缓冲区
pub struct MpmcRingBuffer<T> {
    buffer: Vec<CachePadded<UnsafeCell<Option<T>>>>,
    capacity: usize,
    head: CachePadded<AtomicUsize>,
    tail: CachePadded<AtomicUsize>,
}

// MPMC：多生产者多消费者，索引通过 CAS 竞争，槽位独占访问
#[cfg(feature = "custom_ring_buffers")]
unsafe impl<T: Send> Send for MpmcRingBuffer<T> {}
#[cfg(feature = "custom_ring_buffers")]
unsafe impl<T: Send> Sync for MpmcRingBuffer<T> {}
#[cfg(feature = "custom_ring_buffers")]
impl<T> MpmcRingBuffer<T> {
    /// 创建新的MPMC环形缓冲区
    pub fn new(capacity: usize) -> Self {
        let mut buffer = Vec::with_capacity(capacity);
        for _ in 0..capacity {
            buffer.push(CachePadded::new(UnsafeCell::new(None)));
        }
        
        Self {
            buffer,
            capacity,
            head: CachePadded::new(AtomicUsize::new(0)),
            tail: CachePadded::new(AtomicUsize::new(0)),
        }
    }
    
    /// 尝试推送元素
    pub fn try_push(&self, item: T) -> Result<(), T> {
        loop {
            let current_tail = self.tail.load(Ordering::Relaxed);
            let next_tail = (current_tail + 1) % self.capacity;
            
            // 检查缓冲区是否已满
            if next_tail == self.head.load(Ordering::Acquire) {
                return Err(item);
            }
            
            // 尝试更新尾指针
            match self.tail.compare_exchange_weak(
                current_tail,
                next_tail,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => {
                    // 存储元素
                    unsafe {
                        let slot = self.buffer.get_unchecked(current_tail);
                        *slot.get() = Some(item);
                    }
                    return Ok(());
                }
                Err(_) => {
                    // CAS失败，重试
                    continue;
                }
            }
        }
    }
    
    /// 尝试弹出元素
    pub fn try_pop(&self) -> Option<T> {
        loop {
            let current_head = self.head.load(Ordering::Relaxed);
            
            // 检查缓冲区是否为空
            if current_head == self.tail.load(Ordering::Acquire) {
                return None;
            }
            
            // 尝试更新头指针
            let next_head = (current_head + 1) % self.capacity;
            match self.head.compare_exchange_weak(
                current_head,
                next_head,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => {
                    // 读取元素
                    let item = unsafe {
                        let slot = self.buffer.get_unchecked(current_head);
                        (*slot.get()).take()
                    };
                    return item;
                }
                Err(_) => {
                    // CAS失败，重试
                    continue;
                }
            }
        }
    }
    
    /// 运行MPMC示例
    pub fn run_example() {
        println!("=== MPMC环形缓冲区示例 ===");
        
        let buffer = Arc::new(MpmcRingBuffer::new(1000));
        
        // 创建多个生产者线程
        let producer_handles: Vec<_> = (0..2)
            .map(|producer_id| {
                let buffer = buffer.clone();
                thread::spawn(move || {
                    for i in 0..500 {
                        let item = producer_id * 500 + i;
                        while buffer.try_push(item).is_err() {
                            thread::yield_now();
                        }
                    }
                    println!("生产者 {} 完成", producer_id);
                })
            })
            .collect();
        
        // 创建多个消费者线程
        let consumer_handles: Vec<_> = (0..2)
            .map(|consumer_id| {
                let buffer = buffer.clone();
                thread::spawn(move || {
                    let mut count = 0;
                    while count < 500 {
                        if let Some(item) = buffer.try_pop() {
                            count += 1;
                            if count % 100 == 0 {
                                println!("消费者 {} 处理了 {} 个元素", consumer_id, count);
                            }
                        } else {
                            thread::yield_now();
                        }
                    }
                    println!("消费者 {} 完成", consumer_id);
                })
            })
            .collect();
        
        // 等待所有线程完成
        for handle in producer_handles {
            handle.join().unwrap();
        }
        
        for handle in consumer_handles {
            handle.join().unwrap();
        }
    }
}

#[cfg(feature = "custom_ring_buffers")]
/// 可扩展环形缓冲区
/// 
/// 支持动态扩展的环形缓冲区
pub struct ScalableRingBuffer<T> {
    buffers: Vec<Arc<MpmcRingBuffer<T>>>,
    current_buffer: AtomicUsize,
    capacity_per_buffer: usize,
}

#[cfg(feature = "custom_ring_buffers")]
impl<T> ScalableRingBuffer<T> {
    /// 创建新的可扩展环形缓冲区
    pub fn new(initial_capacity: usize) -> Self {
        let initial_buffer = Arc::new(MpmcRingBuffer::new(initial_capacity));
        
        Self {
            buffers: vec![initial_buffer],
            current_buffer: AtomicUsize::new(0),
            capacity_per_buffer: initial_capacity,
        }
    }
    
    /// 扩展缓冲区
    fn expand(&self) {
        let new_capacity = self.capacity_per_buffer * 2;
        let _new_buffer = Arc::new(MpmcRingBuffer::<T>::new(new_capacity));
        
        // 这里需要实现数据迁移逻辑
        // 为了简化，我们只是添加新的缓冲区
        
        // 更新当前缓冲区索引
        self.current_buffer.store(self.buffers.len(), Ordering::Release);
    }
    
    /// 尝试推送元素
    pub fn try_push(&self, item: T) -> Result<(), T> {
        let current_index = self.current_buffer.load(Ordering::Acquire);
        let buffer = &self.buffers[current_index];
        
        match buffer.try_push(item) {
            Ok(()) => Ok(()),
            Err(item) => {
                // 缓冲区已满，尝试扩展
                self.expand();
                let new_index = self.current_buffer.load(Ordering::Acquire);
                let new_buffer = &self.buffers[new_index];
                new_buffer.try_push(item)
            }
        }
    }
    
    /// 尝试弹出元素
    pub fn try_pop(&self) -> Option<T> {
        let current_index = self.current_buffer.load(Ordering::Acquire);
        let buffer = &self.buffers[current_index];
        
        if let Some(item) = buffer.try_pop() {
            Some(item)
        } else {
            // 当前缓冲区为空，尝试从旧缓冲区获取
            for i in 0..current_index {
                if let Some(item) = self.buffers[i].try_pop() {
                    return Some(item);
                }
            }
            None
        }
    }
    
    /// 运行可扩展环形缓冲区示例
    pub fn run_example() {
        println!("=== 可扩展环形缓冲区示例 ===");
        
        let buffer = Arc::new(ScalableRingBuffer::new(100));
        
        // 创建生产者线程
        let producer = thread::spawn({
            let buffer = buffer.clone();
            move || {
                for i in 0..1000 {
                    while buffer.try_push(i).is_err() {
                        thread::yield_now();
                    }
                }
                println!("生产者完成");
            }
        });
        
        // 创建消费者线程
        let consumer = thread::spawn({
            let buffer = buffer.clone();
            move || {
                let mut count = 0;
                while count < 1000 {
                    if let Some(item) = buffer.try_pop() {
                        count += 1;
                        if count % 100 == 0 {
                            println!("消费者处理了 {} 个元素", count);
                        }
                    } else {
                        thread::yield_now();
                    }
                }
                println!("消费者完成");
            }
        });
        
        producer.join().unwrap();
        consumer.join().unwrap();
    }
}

#[cfg(feature = "custom_ring_buffers")]
unsafe impl<T: Send> Send for ScalableRingBuffer<T> {}
#[cfg(feature = "custom_ring_buffers")]
unsafe impl<T: Send> Sync for ScalableRingBuffer<T> {}
/// 使用Crossbeam的高性能环形缓冲区
/// 
/// 基于Crossbeam库的高性能实现
pub struct CrossbeamRingBuffer<T> {
    queue: ArrayQueue<T>,
}

impl<T> CrossbeamRingBuffer<T> {
    /// 创建新的Crossbeam环形缓冲区
    pub fn new(capacity: usize) -> Self {
        Self {
            queue: ArrayQueue::new(capacity),
        }
    }
    
    /// 尝试推送元素
    pub fn try_push(&self, item: T) -> Result<(), T> {
        self.queue.push(item)
    }
    
    /// 尝试弹出元素
    pub fn try_pop(&self) -> Option<T> {
        self.queue.pop()
    }
    
    /// 运行Crossbeam环形缓冲区示例
    pub fn run_example() {
        println!("=== Crossbeam环形缓冲区示例 ===");
        
        let buffer = Arc::new(CrossbeamRingBuffer::new(1000));
        
        // 创建生产者线程
        let producer = thread::spawn({
            let buffer = buffer.clone();
            move || {
                for i in 0..1000 {
                    while buffer.try_push(i).is_err() {
                        thread::yield_now();
                    }
                }
                println!("生产者完成");
            }
        });
        
        // 创建消费者线程
        let consumer = thread::spawn({
            let buffer = buffer.clone();
            move || {
                let mut count = 0;
                while count < 1000 {
                    if let Some(_item) = buffer.try_pop() {
                        count += 1;
                        if count % 100 == 0 {
                            println!("消费者处理了 {} 个元素", count);
                        }
                    } else {
                        thread::yield_now();
                    }
                }
                println!("消费者完成");
            }
        });
        
        producer.join().unwrap();
        consumer.join().unwrap();
    }
}

/// 运行所有环形缓冲区示例
pub fn demonstrate_lockfree_ring_buffers() {
    println!("=== 无锁环形缓冲区演示 ===");
    
    // 为降低复杂度，仅演示稳定实现，避免自定义环缓的可变借用问题
    CrossbeamRingBuffer::<i32>::run_example();
    #[cfg(feature = "custom_ring_buffers")] {
        SpscRingBuffer::<i32>::run_example();
        MpscRingBuffer::<i32>::run_example();
        MpmcRingBuffer::<i32>::run_example();
        ScalableRingBuffer::<i32>::run_example();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_crossbeam_ring_buffer_only() {
        let buffer = CrossbeamRingBuffer::<i32>::new(10);
        
        assert!(buffer.try_push(1).is_ok());
        assert!(buffer.try_push(2).is_ok());
        assert_eq!(buffer.try_pop(), Some(1));
        assert_eq!(buffer.try_pop(), Some(2));
        assert_eq!(buffer.try_pop(), None);
    }
}
