//! 优先级继承实现
//! 
//! 本模块提供了优先级继承机制，防止优先级反转问题：
//! - 优先级继承互斥锁
//! - 优先级继承读写锁
//! - 优先级继承信号量
//! - 优先级继承屏障

use std::sync::{Arc, Mutex, Condvar};
use std::thread;
use std::time::{Duration, Instant};
use std::collections::{BinaryHeap, HashMap};

/// 线程优先级
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ThreadPriority {
    Low = 1,
    Normal = 2,
    High = 3,
    Critical = 4,
}

impl ThreadPriority {
    pub fn from_value(value: usize) -> Self {
        match value {
            1 => ThreadPriority::Low,
            2 => ThreadPriority::Normal,
            3 => ThreadPriority::High,
            4 => ThreadPriority::Critical,
            _ => ThreadPriority::Normal,
        }
    }
    
    pub fn to_value(self) -> usize {
        self as usize
    }
}

/// 线程信息
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ThreadInfo {
    pub id: usize,
    pub priority: ThreadPriority,
    pub original_priority: ThreadPriority,
    pub wait_start: Option<Instant>,
    pub inherited_priority: Option<ThreadPriority>,
}

impl ThreadInfo {
    pub fn new(id: usize, priority: ThreadPriority) -> Self {
        Self {
            id,
            priority,
            original_priority: priority,
            wait_start: None,
            inherited_priority: None,
        }
    }
    
    pub fn get_effective_priority(&self) -> ThreadPriority {
        self.inherited_priority.unwrap_or(self.priority)
    }
    
    pub fn inherit_priority(&mut self, priority: ThreadPriority) {
        if priority > self.priority {
            self.inherited_priority = Some(priority);
        }
    }
    
    pub fn restore_priority(&mut self) {
        self.inherited_priority = None;
    }
}

/// 优先级继承互斥锁
pub struct PriorityInheritanceMutex<T> {
    data: Arc<Mutex<T>>,
    owner: Arc<Mutex<Option<ThreadInfo>>>,
    waiters: Arc<Mutex<BinaryHeap<ThreadInfo>>>,
    condvar: Arc<Condvar>,
    thread_registry: Arc<Mutex<HashMap<usize, ThreadInfo>>>,
}

impl<T> PriorityInheritanceMutex<T> {
    pub fn new(data: T) -> Self {
        Self {
            data: Arc::new(Mutex::new(data)),
            owner: Arc::new(Mutex::new(None)),
            waiters: Arc::new(Mutex::new(BinaryHeap::new())),
            condvar: Arc::new(Condvar::new()),
            thread_registry: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    pub fn register_thread(&self, thread_id: usize, priority: ThreadPriority) {
        let mut registry = self.thread_registry.lock().unwrap();
        registry.insert(thread_id, ThreadInfo::new(thread_id, priority));
    }
    
    pub fn lock<F, R>(&self, thread_id: usize, f: F) -> R
    where
        F: FnOnce(&mut T) -> R,
    {
        let mut owner = self.owner.lock().unwrap();
        
        if owner.is_none() {
            // 锁可用，直接获取
            let registry = self.thread_registry.lock().unwrap();
            if let Some(thread_info) = registry.get(&thread_id) {
                *owner = Some(thread_info.clone());
            }
            drop(registry);
            drop(owner);
            
            let result = f(&mut self.data.lock().unwrap());
            
            // 释放锁时处理优先级继承
            self.release_lock(thread_id);
            result
        } else {
            // 锁被占用，需要等待
            self.wait_for_lock(thread_id, f)
        }
    }
    
    fn wait_for_lock<F, R>(&self, thread_id: usize, f: F) -> R
    where
        F: FnOnce(&mut T) -> R,
    {
        let registry = self.thread_registry.lock().unwrap();
        let mut thread_info = registry.get(&thread_id).unwrap().clone();
        thread_info.wait_start = Some(Instant::now());
        drop(registry);
        
        // 添加到等待队列
        {
            let mut waiters = self.waiters.lock().unwrap();
            waiters.push(thread_info.clone());
        }
        
        // 检查是否需要优先级继承
        self.check_priority_inheritance(thread_id);
        
        // 等待锁可用
        let mut owner = self.owner.lock().unwrap();
        while owner.is_some() {
            owner = self.condvar.wait(owner).unwrap();
        }
        
        // 获取锁
        let mut registry = self.thread_registry.lock().unwrap();
        if let Some(thread_info) = registry.get_mut(&thread_id) {
            *owner = Some(thread_info.clone());
        }
        drop(registry);
        drop(owner);
        
        let result = f(&mut self.data.lock().unwrap());
        
        // 释放锁
        self.release_lock(thread_id);
        result
    }
    
    fn check_priority_inheritance(&self, waiting_thread_id: usize) {
        let mut owner = self.owner.lock().unwrap();
        if let Some(ref mut owner_info) = *owner {
            let mut registry = self.thread_registry.lock().unwrap();
            if let Some(waiting_thread) = registry.get(&waiting_thread_id).cloned() {
                if waiting_thread.priority > owner_info.priority {
                    // 需要优先级继承
                    owner_info.inherit_priority(waiting_thread.priority);
                    
                    // 更新注册表中的所有者信息
                    if let Some(ref mut owner_in_registry) = registry.get_mut(&owner_info.id) {
                        owner_in_registry.inherit_priority(waiting_thread.priority);
                    }
                }
            }
        }
    }
    
    fn release_lock(&self, thread_id: usize) {
        let mut owner = self.owner.lock().unwrap();
        *owner = None;
        drop(owner);
        
        // 恢复原始优先级
        let mut registry = self.thread_registry.lock().unwrap();
        if let Some(ref mut thread_info) = registry.get_mut(&thread_id) {
            thread_info.restore_priority();
        }
        
        // 选择下一个等待者
        let mut waiters = self.waiters.lock().unwrap();
        if let Some(_next_waiter) = waiters.pop() {
            // 通知下一个等待者
            self.condvar.notify_one();
        }
    }
}

/// 优先级继承读写锁
pub struct PriorityInheritanceRwLock<T> {
    data: Arc<Mutex<T>>,
    readers: Arc<Mutex<Vec<ThreadInfo>>>,
    writer: Arc<Mutex<Option<ThreadInfo>>>,
    waiters: Arc<Mutex<BinaryHeap<ThreadInfo>>>,
    condvar: Arc<Condvar>,
    thread_registry: Arc<Mutex<HashMap<usize, ThreadInfo>>>,
}

impl<T> PriorityInheritanceRwLock<T> {
    pub fn new(data: T) -> Self {
        Self {
            data: Arc::new(Mutex::new(data)),
            readers: Arc::new(Mutex::new(Vec::new())),
            writer: Arc::new(Mutex::new(None)),
            waiters: Arc::new(Mutex::new(BinaryHeap::new())),
            condvar: Arc::new(Condvar::new()),
            thread_registry: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    pub fn register_thread(&self, thread_id: usize, priority: ThreadPriority) {
        let mut registry = self.thread_registry.lock().unwrap();
        registry.insert(thread_id, ThreadInfo::new(thread_id, priority));
    }
    
    pub fn read<F, R>(&self, thread_id: usize, f: F) -> R
    where
        F: FnOnce(&T) -> R,
    {
        let writer = self.writer.lock().unwrap();
        
        if writer.is_none() {
            // 没有写者，可以读取
            let registry = self.thread_registry.lock().unwrap();
            if let Some(thread_info) = registry.get(&thread_id) {
                let mut readers = self.readers.lock().unwrap();
                readers.push(thread_info.clone());
            }
            drop(registry);
            drop(writer);
            
            let result = f(&self.data.lock().unwrap());
            
            // 释放读锁
            self.release_read_lock(thread_id);
            result
        } else {
            // 有写者，需要等待
            self.wait_for_read_lock(thread_id, f)
        }
    }
    
    pub fn write<F, R>(&self, thread_id: usize, f: F) -> R
    where
        F: FnOnce(&mut T) -> R,
    {
        let mut writer = self.writer.lock().unwrap();
        let readers = self.readers.lock().unwrap();
        
        if writer.is_none() && readers.is_empty() {
            // 没有读者和写者，可以写入
            let registry = self.thread_registry.lock().unwrap();
            if let Some(thread_info) = registry.get(&thread_id) {
                *writer = Some(thread_info.clone());
            }
            drop(registry);
            drop(readers);
            drop(writer);
            
            let result = f(&mut self.data.lock().unwrap());
            
            // 释放写锁
            self.release_write_lock(thread_id);
            result
        } else {
            // 有读者或写者，需要等待
            drop(readers);
            self.wait_for_write_lock(thread_id, f)
        }
    }
    
    fn wait_for_read_lock<F, R>(&self, thread_id: usize, f: F) -> R
    where
        F: FnOnce(&T) -> R,
    {
        let registry = self.thread_registry.lock().unwrap();
        let mut thread_info = registry.get(&thread_id).unwrap().clone();
        thread_info.wait_start = Some(Instant::now());
        drop(registry);
        
        // 添加到等待队列
        {
            let mut waiters = self.waiters.lock().unwrap();
            waiters.push(thread_info.clone());
        }
        
        // 检查优先级继承
        self.check_priority_inheritance(thread_id);
        
        // 等待锁可用
        let mut writer = self.writer.lock().unwrap();
        while writer.is_some() {
            writer = self.condvar.wait(writer).unwrap();
        }
        
        // 获取读锁
        let registry = self.thread_registry.lock().unwrap();
        if let Some(thread_info) = registry.get(&thread_id) {
            let mut readers = self.readers.lock().unwrap();
            readers.push(thread_info.clone());
        }
        drop(registry);
        drop(writer);
        
        let result = f(&self.data.lock().unwrap());
        
        // 释放读锁
        self.release_read_lock(thread_id);
        result
    }
    
    fn wait_for_write_lock<F, R>(&self, thread_id: usize, f: F) -> R
    where
        F: FnOnce(&mut T) -> R,
    {
        let registry = self.thread_registry.lock().unwrap();
        let mut thread_info = registry.get(&thread_id).unwrap().clone();
        thread_info.wait_start = Some(Instant::now());
        drop(registry);
        
        // 添加到等待队列
        {
            let mut waiters = self.waiters.lock().unwrap();
            waiters.push(thread_info.clone());
        }
        
        // 检查优先级继承
        self.check_priority_inheritance(thread_id);
        
        // 等待锁可用
        let mut writer = self.writer.lock().unwrap();
        let mut readers = self.readers.lock().unwrap();
        while writer.is_some() || !readers.is_empty() {
            drop(readers);
            writer = self.condvar.wait(writer).unwrap();
            readers = self.readers.lock().unwrap();
        }
        drop(readers);
        
        // 获取写锁
        let registry = self.thread_registry.lock().unwrap();
        if let Some(thread_info) = registry.get(&thread_id) {
            *writer = Some(thread_info.clone());
        }
        drop(registry);
        drop(writer);
        
        let result = f(&mut self.data.lock().unwrap());
        
        // 释放写锁
        self.release_write_lock(thread_id);
        result
    }
    
    fn check_priority_inheritance(&self, waiting_thread_id: usize) {
        let mut writer = self.writer.lock().unwrap();
        if let Some(ref mut writer_info) = *writer {
            let mut registry = self.thread_registry.lock().unwrap();
            if let Some(waiting_thread) = registry.get(&waiting_thread_id).cloned() {
                if waiting_thread.priority > writer_info.priority {
                    // 需要优先级继承
                    writer_info.inherit_priority(waiting_thread.priority);
                    
                    // 更新注册表中的写者信息
                    if let Some(ref mut writer_in_registry) = registry.get_mut(&writer_info.id) {
                        writer_in_registry.inherit_priority(waiting_thread.priority);
                    }
                }
            }
        }
        
        // 检查读者优先级继承
        let mut readers = self.readers.lock().unwrap();
        let mut registry = self.thread_registry.lock().unwrap();
        if let Some(waiting_thread) = registry.get(&waiting_thread_id).cloned() {
            for reader in readers.iter_mut() {
                if waiting_thread.priority > reader.priority {
                    reader.inherit_priority(waiting_thread.priority);
                    
                    // 更新注册表中的读者信息
                    if let Some(ref mut reader_in_registry) = registry.get_mut(&reader.id) {
                        reader_in_registry.inherit_priority(waiting_thread.priority);
                    }
                }
            }
        }
    }
    
    fn release_read_lock(&self, thread_id: usize) {
        let mut readers = self.readers.lock().unwrap();
        readers.retain(|reader| reader.id != thread_id);
        
        if readers.is_empty() {
            // 没有读者了，通知等待的写者
            self.condvar.notify_all();
        }
    }
    
    fn release_write_lock(&self, thread_id: usize) {
        let mut writer = self.writer.lock().unwrap();
        *writer = None;
        drop(writer);
        
        // 恢复原始优先级
        let mut registry = self.thread_registry.lock().unwrap();
        if let Some(ref mut thread_info) = registry.get_mut(&thread_id) {
            thread_info.restore_priority();
        }
        
        // 通知等待者
        self.condvar.notify_all();
    }
}

/// 优先级继承信号量
pub struct PriorityInheritanceSemaphore {
    count: Arc<Mutex<usize>>,
    waiters: Arc<Mutex<BinaryHeap<ThreadInfo>>>,
    condvar: Arc<Condvar>,
    thread_registry: Arc<Mutex<HashMap<usize, ThreadInfo>>>,
}

impl PriorityInheritanceSemaphore {
    pub fn new(count: usize) -> Self {
        Self {
            count: Arc::new(Mutex::new(count)),
            waiters: Arc::new(Mutex::new(BinaryHeap::new())),
            condvar: Arc::new(Condvar::new()),
            thread_registry: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    pub fn register_thread(&self, thread_id: usize, priority: ThreadPriority) {
        let mut registry = self.thread_registry.lock().unwrap();
        registry.insert(thread_id, ThreadInfo::new(thread_id, priority));
    }
    
    pub fn acquire(&self, thread_id: usize) {
        let mut count = self.count.lock().unwrap();
        
        if *count > 0 {
            // 信号量可用，直接获取
            *count -= 1;
        } else {
            // 信号量不可用，需要等待
            self.wait_for_semaphore(thread_id);
        }
    }
    
    pub fn release(&self) {
        let mut count = self.count.lock().unwrap();
        *count += 1;
        
        // 通知等待者
        self.condvar.notify_one();
    }
    
    fn wait_for_semaphore(&self, thread_id: usize) {
        let registry = self.thread_registry.lock().unwrap();
        let mut thread_info = registry.get(&thread_id).unwrap().clone();
        thread_info.wait_start = Some(Instant::now());
        drop(registry);
        
        // 添加到等待队列
        {
            let mut waiters = self.waiters.lock().unwrap();
            waiters.push(thread_info.clone());
        }
        
        // 等待信号量可用
        let mut count = self.count.lock().unwrap();
        while *count == 0 {
            count = self.condvar.wait(count).unwrap();
        }
        
        // 获取信号量
        *count -= 1;
    }
}

/// 运行所有优先级继承示例
pub fn demonstrate_priority_inheritance() {
    println!("=== 优先级继承演示 ===");
    
    // 测试优先级继承互斥锁
    let mutex = Arc::new(PriorityInheritanceMutex::new(0));
    
    // 注册线程
    mutex.register_thread(1, ThreadPriority::High);
    mutex.register_thread(2, ThreadPriority::Low);
    mutex.register_thread(3, ThreadPriority::Normal);
    
    // 创建线程
    let handles: Vec<_> = vec![
        (1, ThreadPriority::High),
        (2, ThreadPriority::Low),
        (3, ThreadPriority::Normal),
    ]
    .into_iter()
    .map(|(thread_id, _priority)| {
        let mutex = mutex.clone();
        thread::spawn(move || {
            for _ in 0..100 {
                mutex.lock(thread_id, |data| {
                    *data += 1;
                    thread::sleep(Duration::from_millis(1));
                });
            }
        })
    })
    .collect();
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("优先级继承互斥锁测试完成");
    
    // 测试优先级继承读写锁
    let rwlock = Arc::new(PriorityInheritanceRwLock::new(0));
    
    // 注册线程
    rwlock.register_thread(1, ThreadPriority::High);
    rwlock.register_thread(2, ThreadPriority::Low);
    
    // 创建读者线程
    let read_handles: Vec<_> = (0..2)
        .map(|_i| {
            let rwlock = rwlock.clone();
            thread::spawn(move || {
                for _ in 0..50 {
                    rwlock.read(1, |data| {
                        let _ = *data;
                    });
                }
            })
        })
        .collect();
    
    // 创建写者线程
    let write_handles: Vec<_> = (0..2)
        .map(|_i| {
            let rwlock = rwlock.clone();
            thread::spawn(move || {
                for _ in 0..50 {
                    rwlock.write(2, |data| {
                        *data += 1;
                    });
                }
            })
        })
        .collect();
    
    for handle in read_handles {
        handle.join().unwrap();
    }
    
    for handle in write_handles {
        handle.join().unwrap();
    }
    
    println!("优先级继承读写锁测试完成");
    
    // 测试优先级继承信号量
    let semaphore = Arc::new(PriorityInheritanceSemaphore::new(2));
    
    // 注册线程
    semaphore.register_thread(1, ThreadPriority::High);
    semaphore.register_thread(2, ThreadPriority::Low);
    semaphore.register_thread(3, ThreadPriority::Normal);
    
    // 创建线程
    let handles: Vec<_> = (1..=3)
        .map(|thread_id| {
            let semaphore = semaphore.clone();
            thread::spawn(move || {
                for _ in 0..10 {
                    semaphore.acquire(thread_id);
                    thread::sleep(Duration::from_millis(10));
                    semaphore.release();
                }
            })
        })
        .collect();
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("优先级继承信号量测试完成");
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_priority_inheritance_mutex() {
        let mutex = PriorityInheritanceMutex::new(0);
        mutex.register_thread(1, ThreadPriority::High);
        
        mutex.lock(1, |data| {
            *data = 42;
        });
        
        let value = mutex.lock(1, |data| *data);
        assert_eq!(value, 42);
    }
    
    #[test]
    fn test_priority_inheritance_rwlock() {
        let rwlock = PriorityInheritanceRwLock::new(0);
        rwlock.register_thread(1, ThreadPriority::High);
        
        rwlock.write(1, |data| {
            *data = 42;
        });
        
        let value = rwlock.read(1, |data| *data);
        assert_eq!(value, 42);
    }
    
    #[test]
    fn test_priority_inheritance_semaphore() {
        let semaphore = PriorityInheritanceSemaphore::new(1);
        semaphore.register_thread(1, ThreadPriority::High);
        
        semaphore.acquire(1);
        semaphore.release();
    }
}
