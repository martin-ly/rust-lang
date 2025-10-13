//! 真实世界线程编程示例
//!
//! 本示例展示了在实际项目中常见的线程编程场景：
//! - 多线程文件处理
//! - 并发网络请求
//! - 实时数据处理
//! - 任务调度系统
//! - 资源池管理

use std::sync::{Arc, Mutex, atomic::{AtomicUsize, Ordering}};
use std::thread;
use std::time::{Duration, Instant};
use std::collections::VecDeque;
use std::sync::mpsc;
use rayon::prelude::*;

/// 文件处理任务
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct FileTask {
    id: usize,
    filename: String,
    size: usize,
    priority: u8,
}

impl FileTask {
    fn new(id: usize, filename: String, size: usize, priority: u8) -> Self {
        Self { id, filename, size, priority }
    }
}

/// 多线程文件处理器
#[allow(dead_code)]
pub struct MultiThreadFileProcessor {
    workers: Vec<thread::JoinHandle<()>>,
    task_sender: mpsc::Sender<FileTask>,
    result_receiver: mpsc::Receiver<(usize, Duration)>,
    completed_count: Arc<AtomicUsize>,
}

impl MultiThreadFileProcessor {
    pub fn new(num_workers: usize) -> Self {
        let (task_sender, task_receiver) = mpsc::channel::<FileTask>();
        let (result_sender, result_receiver) = mpsc::channel::<(usize, Duration)>();
        let task_receiver = Arc::new(Mutex::new(task_receiver));
        let completed_count = Arc::new(AtomicUsize::new(0));

        let workers = (0..num_workers)
            .map(|worker_id| {
                let task_receiver = Arc::clone(&task_receiver);
                let result_sender = result_sender.clone();
                let completed_count = Arc::clone(&completed_count);

                thread::spawn(move || {
                    println!("文件处理工作线程 {} 启动", worker_id);
                    
                    loop {
                        let task = {
                            let receiver = task_receiver.lock().unwrap();
                            receiver.recv()
                        };

                        match task {
                            Ok(task) => {
                                let start = Instant::now();
                                
                                // 模拟文件处理（根据文件大小计算处理时间）
                                let processing_time = Duration::from_millis(task.size as u64 / 100);
                                thread::sleep(processing_time);
                                
                                let duration = start.elapsed();
                                println!("工作线程 {} 处理文件 {} 完成，耗时 {:?}", 
                                    worker_id, task.filename, duration);
                                
                                result_sender.send((task.id, duration)).unwrap();
                                completed_count.fetch_add(1, Ordering::Relaxed);
                            }
                            Err(_) => {
                                println!("文件处理工作线程 {} 退出", worker_id);
                                break;
                            }
                        }
                    }
                })
            })
            .collect();

        Self {
            workers,
            task_sender,
            result_receiver,
            completed_count,
        }
    }

    pub fn submit_task(&self, task: FileTask) -> Result<(), mpsc::SendError<FileTask>> {
        self.task_sender.send(task)
    }

    pub fn get_completed_count(&self) -> usize {
        self.completed_count.load(Ordering::Relaxed)
    }

    pub fn shutdown(self) {
        drop(self.task_sender);
        for worker in self.workers {
            worker.join().unwrap();
        }
    }
}

/// 并发网络请求处理器
#[allow(dead_code)]
pub struct ConcurrentHttpClient {
    max_concurrent: usize,
    semaphore: Arc<Mutex<usize>>,
}

impl ConcurrentHttpClient {
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            max_concurrent,
            semaphore: Arc::new(Mutex::new(max_concurrent)),
        }
    }

    pub async fn fetch_url(&self, url: String) -> Result<String, String> {
        // 获取信号量
        {
            let mut sem = self.semaphore.lock().unwrap();
            while *sem == 0 {
                drop(sem);
                thread::sleep(Duration::from_millis(10));
                sem = self.semaphore.lock().unwrap();
            }
            *sem -= 1;
        }

        // 模拟网络请求
        let delay = Duration::from_millis(100 + (url.len() % 200) as u64);
        thread::sleep(delay);

        // 释放信号量
        {
            let mut sem = self.semaphore.lock().unwrap();
            *sem += 1;
        }

        Ok(format!("Response from {}", url))
    }
}

/// 实时数据处理器
#[allow(dead_code)]
pub struct RealTimeDataProcessor {
    buffer: Arc<Mutex<VecDeque<f64>>>,
    processors: Vec<thread::JoinHandle<()>>,
    data_sender: mpsc::Sender<f64>,
}

impl RealTimeDataProcessor {
    pub fn new(num_processors: usize) -> Self {
        let (data_sender, data_receiver) = mpsc::channel();
        let buffer = Arc::new(Mutex::new(VecDeque::new()));
        let data_receiver = Arc::new(Mutex::new(data_receiver));

        let processors = (0..num_processors)
            .map(|processor_id| {
                let buffer = Arc::clone(&buffer);
                let data_receiver = Arc::clone(&data_receiver);

                thread::spawn(move || {
                    println!("数据处理器 {} 启动", processor_id);
                    
                    loop {
                        let data = {
                            let receiver = data_receiver.lock().unwrap();
                            receiver.recv()
                        };

                        match data {
                            Ok(value) => {
                                // 处理数据（例如：计算移动平均）
                                let processed_value = value * 1.1;
                                
                                let mut buf = buffer.lock().unwrap();
                                buf.push_back(processed_value);
                                
                                // 保持缓冲区大小
                                if buf.len() > 1000 {
                                    buf.pop_front();
                                }
                                
                                if processor_id == 0 {
                                    println!("处理器 {} 处理数据: {:.2} -> {:.2}", 
                                        processor_id, value, processed_value);
                                }
                            }
                            Err(_) => {
                                println!("数据处理器 {} 退出", processor_id);
                                break;
                            }
                        }
                    }
                })
            })
            .collect();

        Self {
            buffer,
            processors,
            data_sender,
        }
    }

    pub fn send_data(&self, value: f64) -> Result<(), mpsc::SendError<f64>> {
        self.data_sender.send(value)
    }

    pub fn get_buffer_size(&self) -> usize {
        self.buffer.lock().unwrap().len()
    }

    pub fn shutdown(self) {
        drop(self.data_sender);
        for processor in self.processors {
            processor.join().unwrap();
        }
    }
}

/// 任务调度器
#[allow(dead_code)]
pub struct TaskScheduler {
    tasks: Arc<Mutex<VecDeque<(Instant, Box<dyn FnOnce() + Send + 'static>)>>>,
    scheduler_thread: thread::JoinHandle<()>,
    stop_sender: mpsc::Sender<()>,
}

#[allow(dead_code)]
#[allow(unused_variables)]
impl TaskScheduler {
    pub fn new() -> Self {
        let (stop_sender, stop_receiver) = mpsc::channel();
        let tasks = Arc::new(Mutex::new(VecDeque::new()));

        let scheduler_thread = {
            let tasks = Arc::clone(&tasks);
            thread::spawn(move || {
                println!("任务调度器启动");
                
                loop {
                    // 检查停止信号
                    if stop_receiver.try_recv().is_ok() {
                        println!("任务调度器停止");
                        break;
                    }

                    // 检查待执行任务
                    let now = Instant::now();
                    let mut tasks_guard = tasks.lock().unwrap();
                    
                    while let Some((scheduled_time, task)) = tasks_guard.front() {
                        if *scheduled_time <= now {
                            let (_scheduled_time, task): (Instant, Box<dyn FnOnce() + Send + 'static>) = tasks_guard.pop_front().unwrap();
                            drop(tasks_guard);
                            task();
                            tasks_guard = tasks.lock().unwrap();
                        } else {
                            break;
                        }
                    }
                    
                    drop(tasks_guard);
                    thread::sleep(Duration::from_millis(10));
                }
            })
        };

        Self {
            tasks,
            scheduler_thread,
            stop_sender,
        }
    }

    pub fn schedule_task<F>(&self, delay: Duration, task: F)
    where
        F: FnOnce() + Send + 'static,
    {
        let scheduled_time = Instant::now() + delay;
        self.tasks.lock().unwrap().push_back((scheduled_time, Box::new(task)));
    }

    pub fn shutdown(self) {
        drop(self.stop_sender);
        self.scheduler_thread.join().unwrap();
    }
}

/// 资源池管理器
#[allow(dead_code)]
pub struct ResourcePool<T> {
    resources: Arc<Mutex<Vec<T>>>,
    available: Arc<Mutex<Vec<usize>>>,
    in_use: Arc<Mutex<Vec<usize>>>,
}

impl<T> ResourcePool<T> {
    pub fn new(resources: Vec<T>) -> Self {
        let available_indices: Vec<usize> = (0..resources.len()).collect();
        
        Self {
            resources: Arc::new(Mutex::new(resources)),
            available: Arc::new(Mutex::new(available_indices)),
            in_use: Arc::new(Mutex::new(Vec::new())),
        }
    }

    pub fn acquire(&self) -> Option<usize> {
        let mut available = self.available.lock().unwrap();
        let mut in_use = self.in_use.lock().unwrap();
        
        if let Some(index) = available.pop() {
            in_use.push(index);
            Some(index)
        } else {
            None
        }
    }

    pub fn release(&self, index: usize) {
        let mut available = self.available.lock().unwrap();
        let mut in_use = self.in_use.lock().unwrap();
        
        if let Some(pos) = in_use.iter().position(|&i| i == index) {
            in_use.remove(pos);
            available.push(index);
        }
    }

    pub fn get_resource(&self, _index: usize) -> Option<&T> {
        // 这里简化了实现，实际应该返回引用
        // 注意：这个实现有生命周期问题，仅用于演示
        None
    }

    pub fn get_stats(&self) -> (usize, usize) {
        let available = self.available.lock().unwrap().len();
        let in_use = self.in_use.lock().unwrap().len();
        (available, in_use)
    }
}

/// 演示多线程文件处理
#[allow(dead_code)]
fn demo_file_processing() {
    println!("=== 多线程文件处理演示 ===");
    
    let processor = MultiThreadFileProcessor::new(3);
    
    // 提交文件处理任务
    let files = vec![
        FileTask::new(1, "document1.pdf".to_string(), 5000, 1),
        FileTask::new(2, "image1.jpg".to_string(), 2000, 2),
        FileTask::new(3, "video1.mp4".to_string(), 10000, 1),
        FileTask::new(4, "archive.zip".to_string(), 8000, 3),
        FileTask::new(5, "code.rs".to_string(), 1000, 2),
    ];
    
    for file in files {
        processor.submit_task(file).unwrap();
    }
    
    // 等待处理完成
    thread::sleep(Duration::from_millis(2000));
    println!("处理完成，共处理 {} 个文件", processor.get_completed_count());
    
    processor.shutdown();
    println!();
}

/// 演示并发网络请求
#[allow(dead_code)]
fn demo_concurrent_requests() {
    println!("=== 并发网络请求演示 ===");
    
    let client = ConcurrentHttpClient::new(3);
    let urls = vec![
        "https://api.example.com/users".to_string(),
        "https://api.example.com/products".to_string(),
        "https://api.example.com/orders".to_string(),
        "https://api.example.com/categories".to_string(),
        "https://api.example.com/reviews".to_string(),
    ];
    
    let start = Instant::now();
    
    // 使用 rayon 并行处理请求
    let results: Vec<_> = urls.into_par_iter()
        .map(|url| {
            // 模拟异步调用
            let _client = &client;
            std::thread::spawn(move || {
                // 这里简化了异步调用
                thread::sleep(Duration::from_millis(100));
                format!("Response from {}", url)
            }).join().unwrap()
        })
        .collect();
    
    let duration = start.elapsed();
    println!("并发请求完成，耗时: {:?}", duration);
    println!("收到 {} 个响应", results.len());
    println!();
}

/// 演示实时数据处理
#[allow(dead_code)]
fn demo_real_time_processing() {
    println!("=== 实时数据处理演示 ===");
    
    let processor = RealTimeDataProcessor::new(2);
    
    // 模拟数据流
    for i in 0..50 {
        let value = (i as f64) * 0.1 + (i % 10) as f64;
        processor.send_data(value).unwrap();
        thread::sleep(Duration::from_millis(50));
    }
    
    thread::sleep(Duration::from_millis(1000));
    println!("缓冲区大小: {}", processor.get_buffer_size());
    
    processor.shutdown();
    println!();
}

/// 演示任务调度
#[allow(dead_code)]
fn demo_task_scheduling() {
    println!("=== 任务调度演示 ===");
    
    let scheduler = TaskScheduler::new();
    
    // 调度多个任务
    scheduler.schedule_task(Duration::from_millis(100), || {
        println!("任务 1 执行");
    });
    
    scheduler.schedule_task(Duration::from_millis(200), || {
        println!("任务 2 执行");
    });
    
    scheduler.schedule_task(Duration::from_millis(300), || {
        println!("任务 3 执行");
    });
    
    // 等待任务执行
    thread::sleep(Duration::from_millis(500));
    
    scheduler.shutdown();
    println!();
}

/// 演示资源池管理
#[allow(dead_code)]
fn demo_resource_pool() {
    println!("=== 资源池管理演示 ===");
    
    let resources: Vec<String> = (1..=5).map(|i| format!("Resource-{}", i)).collect();
    let pool = Arc::new(ResourcePool::new(resources));
    
    let mut handles = vec![];
    
    // 模拟多个线程使用资源
    for i in 0..10 {
        let pool = Arc::clone(&pool);
        let handle = thread::spawn(move || {
            if let Some(index) = pool.acquire() {
                println!("线程 {} 获得资源 {}", i, index);
                thread::sleep(Duration::from_millis(100));
                pool.release(index);
                println!("线程 {} 释放资源 {}", i, index);
            } else {
                println!("线程 {} 无法获得资源", i);
            }
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    let (available, in_use) = pool.get_stats();
    println!("资源池状态: 可用 {}, 使用中 {}", available, in_use);
    println!();
}

fn main() {
    println!("=== 真实世界线程编程示例 ===\n");
    
    // 运行各种演示
    demo_file_processing();
    demo_concurrent_requests();
    demo_real_time_processing();
    demo_task_scheduling();
    demo_resource_pool();
    
    println!("=== 所有演示完成 ===");
}
