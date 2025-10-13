//! 线程管理
//!
//! 本模块提供了高级线程管理功能：
//! - 线程生命周期管理
//! - 线程池管理
//! - 线程状态监控
//! - 线程通信

use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::mpsc;
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

/// 线程状态
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ThreadState {
    Created,
    Running,
    Blocked,
    Waiting,
    Terminated,
}

/// 线程信息
#[derive(Debug, Clone)]
pub struct ThreadInfo {
    pub id: usize,
    pub name: String,
    pub state: ThreadState,
    pub priority: usize,
    pub cpu_time: Duration,
    pub memory_usage: usize,
    pub created_at: Instant,
    pub last_activity: Instant,
}

impl ThreadInfo {
    pub fn new(id: usize, name: String, priority: usize) -> Self {
        Self {
            id,
            name,
            state: ThreadState::Created,
            priority,
            cpu_time: Duration::ZERO,
            memory_usage: 0,
            created_at: Instant::now(),
            last_activity: Instant::now(),
        }
    }

    pub fn update_state(&mut self, state: ThreadState) {
        self.state = state;
        self.last_activity = Instant::now();
    }

    pub fn update_cpu_time(&mut self, cpu_time: Duration) {
        self.cpu_time += cpu_time;
    }

    pub fn update_memory_usage(&mut self, memory_usage: usize) {
        self.memory_usage = memory_usage;
    }
}

/// 线程管理器
pub struct ThreadManager {
    threads: Arc<Mutex<HashMap<usize, ThreadInfo>>>,
    next_thread_id: Arc<AtomicUsize>,
    thread_count: Arc<AtomicUsize>,
    max_threads: Arc<AtomicUsize>,
    shutdown_requested: Arc<AtomicBool>,
}

impl ThreadManager {
    pub fn new(max_threads: usize) -> Self {
        Self {
            threads: Arc::new(Mutex::new(HashMap::new())),
            next_thread_id: Arc::new(AtomicUsize::new(1)),
            thread_count: Arc::new(AtomicUsize::new(0)),
            max_threads: Arc::new(AtomicUsize::new(max_threads)),
            shutdown_requested: Arc::new(AtomicBool::new(false)),
        }
    }

    pub fn create_thread<F>(&self, name: String, priority: usize, f: F) -> Result<usize, String>
    where
        F: FnOnce() + Send + 'static,
    {
        if self.thread_count.load(Ordering::Relaxed) >= self.max_threads.load(Ordering::Relaxed) {
            return Err("达到最大线程数限制".to_string());
        }

        let thread_id = self.next_thread_id.fetch_add(1, Ordering::Relaxed);
        let thread_info = ThreadInfo::new(thread_id, name.clone(), priority);

        // 注册线程
        {
            let mut threads = self.threads.lock().unwrap();
            threads.insert(thread_id, thread_info);
        }

        // 创建线程
        let threads = self.threads.clone();
        let thread_count = self.thread_count.clone();
        let _shutdown_requested = self.shutdown_requested.clone();

        thread::spawn(move || {
            // 更新线程状态为运行中
            {
                let mut threads = threads.lock().unwrap();
                if let Some(info) = threads.get_mut(&thread_id) {
                    info.update_state(ThreadState::Running);
                }
            }

            // 执行线程函数
            f();

            // 更新线程状态为已终止
            {
                let mut threads = threads.lock().unwrap();
                if let Some(info) = threads.get_mut(&thread_id) {
                    info.update_state(ThreadState::Terminated);
                }
            }

            // 减少线程计数
            thread_count.fetch_sub(1, Ordering::Relaxed);
        });

        self.thread_count.fetch_add(1, Ordering::Relaxed);
        Ok(thread_id)
    }

    pub fn terminate_thread(&self, thread_id: usize) -> Result<(), String> {
        let mut threads = self.threads.lock().unwrap();
        if let Some(info) = threads.get_mut(&thread_id) {
            info.update_state(ThreadState::Terminated);
            Ok(())
        } else {
            Err(format!("线程 {} 不存在", thread_id))
        }
    }

    pub fn get_thread_info(&self, thread_id: usize) -> Option<ThreadInfo> {
        let threads = self.threads.lock().unwrap();
        threads.get(&thread_id).cloned()
    }

    pub fn get_all_threads(&self) -> Vec<ThreadInfo> {
        let threads = self.threads.lock().unwrap();
        threads.values().cloned().collect()
    }

    pub fn get_thread_count(&self) -> usize {
        self.thread_count.load(Ordering::Relaxed)
    }

    pub fn get_max_threads(&self) -> usize {
        self.max_threads.load(Ordering::Relaxed)
    }

    pub fn set_max_threads(&self, max_threads: usize) {
        self.max_threads.store(max_threads, Ordering::Relaxed);
    }

    pub fn shutdown(&self) {
        self.shutdown_requested.store(true, Ordering::Relaxed);
    }

    pub fn is_shutdown_requested(&self) -> bool {
        self.shutdown_requested.load(Ordering::Relaxed)
    }

    pub fn wait_for_all_threads(&self, timeout: Duration) -> bool {
        let start_time = Instant::now();

        while self.thread_count.load(Ordering::Relaxed) > 0 {
            if start_time.elapsed() > timeout {
                return false;
            }
            thread::sleep(Duration::from_millis(10));
        }

        true
    }
}

/// 高级线程池
#[allow(dead_code)]
pub struct AdvancedThreadPool {
    manager: Arc<ThreadManager>,
    task_queue: Arc<Mutex<Vec<Box<dyn FnOnce() + Send + 'static>>>>,
    worker_threads: Arc<Mutex<Vec<usize>>>,
    task_sender: mpsc::Sender<Box<dyn FnOnce() + Send + 'static>>,
    task_receiver: Arc<Mutex<mpsc::Receiver<Box<dyn FnOnce() + Send + 'static>>>>,
    pool_size: AtomicUsize,
    active_tasks: Arc<AtomicUsize>,
    completed_tasks: Arc<AtomicUsize>,
}

impl AdvancedThreadPool {
    pub fn new(pool_size: usize) -> Self {
        let (sender, receiver) = mpsc::channel();

        Self {
            manager: Arc::new(ThreadManager::new(pool_size)),
            task_queue: Arc::new(Mutex::new(Vec::new())),
            worker_threads: Arc::new(Mutex::new(Vec::new())),
            task_sender: sender,
            task_receiver: Arc::new(Mutex::new(receiver)),
            pool_size: AtomicUsize::new(pool_size),
            active_tasks: Arc::new(AtomicUsize::new(0)),
            completed_tasks: Arc::new(AtomicUsize::new(0)),
        }
    }

    pub fn start(&self) -> Result<(), String> {
        let pool_size = self.pool_size.load(Ordering::Relaxed);

        for i in 0..pool_size {
            let thread_id = self.manager.create_thread(
                format!("Worker-{}", i),
                2, // 普通优先级
                {
                    let manager = self.manager.clone();
                    let task_receiver = self.task_receiver.clone();
                    let active_tasks = Arc::clone(&self.active_tasks);
                    let completed_tasks = Arc::clone(&self.completed_tasks);

                    move || {
                        loop {
                            if manager.is_shutdown_requested() {
                                break;
                            }

                            // 接收任务
                            let task = {
                                let receiver = task_receiver.lock().unwrap();
                                receiver.recv_timeout(Duration::from_millis(100))
                            };

                            match task {
                                Ok(task) => {
                                    active_tasks.fetch_add(1, Ordering::Relaxed);
                                    // 执行任务
                                    task();
                                    completed_tasks.fetch_add(1, Ordering::Relaxed);
                                    active_tasks.fetch_sub(1, Ordering::Relaxed);
                                }
                                Err(_) => {
                                    // 超时，继续循环
                                    continue;
                                }
                            }
                        }
                    }
                },
            )?;

            let mut worker_threads = self.worker_threads.lock().unwrap();
            worker_threads.push(thread_id);
        }

        Ok(())
    }

    pub fn submit<F>(&self, task: F) -> Result<(), String>
    where
        F: FnOnce() + Send + 'static,
    {
        if self.manager.is_shutdown_requested() {
            return Err("线程池已关闭".to_string());
        }

        self.task_sender
            .send(Box::new(task))
            .map_err(|_| "发送任务失败".to_string())?;

        Ok(())
    }

    pub fn get_pool_size(&self) -> usize {
        self.pool_size.load(Ordering::Relaxed)
    }

    pub fn get_active_tasks(&self) -> usize {
        self.active_tasks.load(Ordering::Relaxed)
    }

    pub fn get_completed_tasks(&self) -> usize {
        self.completed_tasks.load(Ordering::Relaxed)
    }

    pub fn shutdown(&self) {
        self.manager.shutdown();
    }

    pub fn wait_for_completion(&self, timeout: Duration) -> bool {
        let start_time = Instant::now();

        while self.active_tasks.load(Ordering::Relaxed) > 0 {
            if start_time.elapsed() > timeout {
                return false;
            }
            thread::sleep(Duration::from_millis(10));
        }

        true
    }
}

/// 线程通信管理器
pub struct ThreadCommunicationManager {
    channels: Arc<Mutex<HashMap<String, mpsc::Sender<Message>>>>,
    message_handlers: Arc<Mutex<HashMap<String, Box<dyn Fn(Message) + Send + Sync>>>>,
}

#[derive(Debug, Clone)]
pub struct Message {
    pub id: usize,
    pub sender: String,
    pub receiver: String,
    pub content: String,
    pub timestamp: Instant,
}

impl Default for ThreadCommunicationManager {
    fn default() -> Self {
        Self::new()
    }
}

impl ThreadCommunicationManager {
    pub fn new() -> Self {
        Self {
            channels: Arc::new(Mutex::new(HashMap::new())),
            message_handlers: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    pub fn create_channel(&self, name: String) -> Result<mpsc::Receiver<Message>, String> {
        let (sender, receiver) = mpsc::channel();

        let mut channels = self.channels.lock().unwrap();
        channels.insert(name, sender);

        Ok(receiver)
    }

    pub fn send_message(&self, channel_name: String, message: Message) -> Result<(), String> {
        let channels = self.channels.lock().unwrap();
        if let Some(sender) = channels.get(&channel_name) {
            sender
                .send(message)
                .map_err(|_| "发送消息失败".to_string())?;
            Ok(())
        } else {
            Err(format!("通道 {} 不存在", channel_name))
        }
    }

    pub fn register_message_handler<F>(&self, message_type: String, handler: F)
    where
        F: Fn(Message) + Send + Sync + 'static,
    {
        let mut handlers = self.message_handlers.lock().unwrap();
        handlers.insert(message_type, Box::new(handler));
    }

    pub fn handle_message(&self, message: Message) {
        let handlers = self.message_handlers.lock().unwrap();
        if let Some(handler) = handlers.get(&message.content) {
            handler(message);
        }
    }
}

/// 运行所有线程管理示例
pub fn demonstrate_thread_management() {
    println!("=== 线程管理演示 ===");

    // 测试线程管理器
    let manager = Arc::new(ThreadManager::new(10));

    // 创建线程
    let handles: Vec<_> = (0..3)
        .map(|i| {
            let manager = manager.clone();
            thread::spawn(move || {
                

                manager
                    .create_thread(format!("TestThread-{}", i), 2, move || {
                        for j in 0..100 {
                            thread::sleep(Duration::from_millis(1));
                            if j % 20 == 0 {
                                println!("线程 {} 执行了 {} 次迭代", i, j);
                            }
                        }
                    })
                    .unwrap()
            })
        })
        .collect();

    // 等待线程创建完成
    for handle in handles {
        let _thread_id = handle.join().unwrap();
    }

    // 显示线程信息
    let threads = manager.get_all_threads();
    println!("当前线程数: {}", manager.get_thread_count());
    for thread_info in threads {
        println!(
            "线程 {}: 状态={:?}, 优先级={}, CPU时间={:?}",
            thread_info.id, thread_info.state, thread_info.priority, thread_info.cpu_time
        );
    }

    // 测试高级线程池
    let pool = Arc::new(AdvancedThreadPool::new(4));
    pool.start().unwrap();

    // 提交任务
    for i in 0..10 {
        let pool = pool.clone();
        thread::spawn(move || {
            pool.submit(move || {
                thread::sleep(Duration::from_millis(10));
                println!("任务 {} 完成", i);
            })
            .unwrap();
        });
    }

    // 等待任务完成
    if pool.wait_for_completion(Duration::from_secs(5)) {
        println!("所有任务完成");
    } else {
        println!("任务执行超时");
    }

    println!("线程池统计:");
    println!("  池大小: {}", pool.get_pool_size());
    println!("  活跃任务: {}", pool.get_active_tasks());
    println!("  完成任务: {}", pool.get_completed_tasks());

    // 关闭线程池
    pool.shutdown();

    // 测试线程通信
    let comm_manager = Arc::new(ThreadCommunicationManager::new());

    // 创建通道
    let receiver = comm_manager
        .create_channel("test_channel".to_string())
        .unwrap();

    // 注册消息处理器
    comm_manager.register_message_handler("test".to_string(), |message| {
        println!(
            "收到消息: {} 从 {} 到 {}",
            message.content, message.sender, message.receiver
        );
    });

    // 发送消息
    let message = Message {
        id: 1,
        sender: "sender".to_string(),
        receiver: "receiver".to_string(),
        content: "test".to_string(),
        timestamp: Instant::now(),
    };

    comm_manager
        .send_message("test_channel".to_string(), message)
        .unwrap();

    // 处理消息
    if let Ok(received_message) = receiver.recv_timeout(Duration::from_millis(100)) {
        comm_manager.handle_message(received_message);
    }

    // 等待所有线程完成
    if manager.wait_for_all_threads(Duration::from_secs(5)) {
        println!("所有线程已完成");
    } else {
        println!("等待线程完成超时");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_thread_manager() {
        let manager = ThreadManager::new(5);

        let thread_id = manager
            .create_thread("test".to_string(), 2, || {
                thread::sleep(Duration::from_millis(10));
            })
            .unwrap();

        assert_eq!(manager.get_thread_count(), 1);
        assert!(manager.get_thread_info(thread_id).is_some());

        manager.terminate_thread(thread_id).unwrap();
    }

    #[test]
    fn test_advanced_thread_pool() {
        let pool = AdvancedThreadPool::new(2);
        pool.start().unwrap();

        pool.submit(|| {
            thread::sleep(Duration::from_millis(10));
        })
        .unwrap();

        assert!(pool.wait_for_completion(Duration::from_secs(1)));
        // Add a small delay to ensure the task has fully completed
        thread::sleep(Duration::from_millis(20));
        assert_eq!(pool.get_completed_tasks(), 1);

        pool.shutdown();
    }

    #[test]
    fn test_thread_communication() {
        let comm_manager = ThreadCommunicationManager::new();
        let receiver = comm_manager.create_channel("test".to_string()).unwrap();

        let message = Message {
            id: 1,
            sender: "sender".to_string(),
            receiver: "receiver".to_string(),
            content: "test".to_string(),
            timestamp: Instant::now(),
        };

        comm_manager
            .send_message("test".to_string(), message)
            .unwrap();

        let received = receiver.recv_timeout(Duration::from_millis(100)).unwrap();
        assert_eq!(received.content, "test");
    }
}
