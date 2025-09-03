//! 线程池模块
//! 
//! 本模块提供线程池的基本实现，包括：
//! - 简单线程池
//! - 可配置线程池
//! - 线程池性能测试

use std::sync::{Arc, Mutex};
use std::sync::mpsc::{channel, Sender, Receiver};
use std::thread;
use std::time::Duration;

/// 简单线程池实现
pub struct SimpleThreadPool {
    workers: Vec<Worker>,
    sender: Option<Sender<Box<dyn FnOnce() + Send + 'static>>>,
}

impl SimpleThreadPool {
    /// 创建新的线程池
    pub fn new(size: usize) -> Self {
        assert!(size > 0);
        
        let (sender, receiver) = channel();
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
    
    /// 执行任务
    pub fn execute<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'static,
    {
        if let Some(sender) = self.sender.as_ref() {
            sender.send(Box::new(f)).unwrap();
        }
    }
}

impl Drop for SimpleThreadPool {
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
    #[allow(dead_code)]
    id: usize,
    thread: Option<thread::JoinHandle<()>>,
}

impl Worker {
    fn new(id: usize, receiver: Arc<Mutex<Receiver<Box<dyn FnOnce() + Send + 'static>>>>) -> Self {
        let thread = thread::spawn(move || {
            loop {
                let message = receiver.lock().unwrap().recv();
                
                match message {
                    Ok(job) => {
                        println!("  工作线程 {} 执行任务", id);
                        job();
                    }
                    Err(_) => {
                        println!("  工作线程 {} 关闭", id);
                        break;
                    }
                }
            }
        });
        
        Self {
            id,
            thread: Some(thread),
        }
    }
}

/// 可配置线程池
pub struct ConfigurableThreadPool {
    workers: Vec<ConfigurableWorker>,
    sender: Option<Sender<Box<dyn FnOnce() + Send + 'static>>>,
    config: ThreadPoolConfig,
}

/// 线程池配置
#[derive(Debug, Clone)]
pub struct ThreadPoolConfig {
    pub min_threads: usize,
    pub max_threads: usize,
    pub keep_alive_time: Duration,
    pub queue_size: usize,
}

impl Default for ThreadPoolConfig {
    fn default() -> Self {
        Self {
            min_threads: 2,
            max_threads: 16,
            keep_alive_time: Duration::from_secs(60),
            queue_size: 1000,
        }
    }
}

impl ConfigurableThreadPool {
    /// 创建新的可配置线程池
    pub fn new(config: ThreadPoolConfig) -> Self {
        assert!(config.min_threads > 0);
        assert!(config.max_threads >= config.min_threads);
        
        let (sender, receiver) = channel();
        let receiver = Arc::new(Mutex::new(receiver));
        
        let mut workers = Vec::with_capacity(config.max_threads);
        
        // 创建最小数量的工作线程
        for id in 0..config.min_threads {
            workers.push(ConfigurableWorker::new(id, Arc::clone(&receiver), config.keep_alive_time));
        }
        
        Self {
            workers,
            sender: Some(sender),
            config,
        }
    }
    
    /// 执行任务
    pub fn execute<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'static,
    {
        if let Some(sender) = self.sender.as_ref() {
            // 如果队列满了，可以考虑动态增加线程
            if let Err(_) = sender.send(Box::new(f)) {
                eprintln!("任务队列已满，无法执行新任务");
            }
        }
    }
    
    /// 获取当前线程数
    pub fn thread_count(&self) -> usize {
        self.workers.len()
    }
    
    /// 获取配置信息
    pub fn config(&self) -> &ThreadPoolConfig {
        &self.config
    }
}

impl Drop for ConfigurableThreadPool {
    fn drop(&mut self) {
        self.sender.take();
        
        for worker in &mut self.workers {
            if let Some(thread) = worker.thread.take() {
                let _ = thread.join();
            }
        }
    }
}

/// 可配置工作线程
struct ConfigurableWorker {
    #[allow(dead_code)]
    id: usize,
    thread: Option<thread::JoinHandle<()>>,
}

impl ConfigurableWorker {
    fn new(
        id: usize, 
        receiver: Arc<Mutex<Receiver<Box<dyn FnOnce() + Send + 'static>>>>,
        keep_alive_time: Duration,
    ) -> Self {
        let thread = thread::spawn(move || {
            loop {
                let message = receiver.lock().unwrap().recv_timeout(keep_alive_time);
                
                match message {
                    Ok(job) => {
                        println!("  可配置工作线程 {} 执行任务", id);
                        job();
                    }
                    Err(_) => {
                        println!("  可配置工作线程 {} 超时关闭", id);
                        break;
                    }
                }
            }
        });
        
        Self {
            id,
            thread: Some(thread),
        }
    }
}

/// 线程池性能测试
pub fn benchmark_thread_pools() {
    println!("🔧 线程池性能测试");
    
    let data_size: usize = 100_000;
    let data: Vec<i32> = (0..data_size as i32).collect();
    
    // 测试简单线程池
    println!("  测试简单线程池...");
    let start = std::time::Instant::now();
    let pool = SimpleThreadPool::new(4);
    
    for chunk in data.chunks(data_size / 4) {
        let chunk = chunk.to_vec();
        pool.execute(move || {
            let _sum: i32 = chunk.iter().sum();
        });
    }
    
    drop(pool); // 等待所有任务完成
    let duration = start.elapsed();
    println!("    简单线程池耗时: {:?}", duration);
    
    // 测试可配置线程池
    println!("  测试可配置线程池...");
    let start = std::time::Instant::now();
    let config = ThreadPoolConfig {
        min_threads: 2,
        max_threads: 8,
        keep_alive_time: Duration::from_secs(30),
        queue_size: 100,
    };
    
    let pool = ConfigurableThreadPool::new(config);
    
    for chunk in data.chunks(data_size / 4) {
        let chunk = chunk.to_vec();
        pool.execute(move || {
            let _sum: i32 = chunk.iter().sum();
        });
    }
    
    drop(pool);
    let duration = start.elapsed();
    println!("    可配置线程池耗时: {:?}", duration);
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_simple_thread_pool() {
        let pool = SimpleThreadPool::new(2);
        
        let (tx, rx) = channel();
        
        pool.execute(move || {
            tx.send(42).unwrap();
        });
        
        let result = rx.recv().unwrap();
        assert_eq!(result, 42);
    }
    
    #[test]
    fn test_configurable_thread_pool() {
        let config = ThreadPoolConfig::default();
        let pool = ConfigurableThreadPool::new(config);
        
        assert_eq!(pool.thread_count(), 2);
        assert_eq!(pool.config().min_threads, 2);
        assert_eq!(pool.config().max_threads, 16);
    }
    
    #[test]
    fn test_thread_pool_benchmark() {
        benchmark_thread_pools();
    }
}
