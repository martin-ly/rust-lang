//! 线程池模块
//!
//! 本模块提供线程池的基本实现，包括：
//! 1) 简单线程池
//! 2) 可配置线程池
//! 3) 线程池性能测试
//! 4) 任务结果返回（补充）
use std::sync::mpsc::{Receiver, Sender, channel};
use std::sync::{Arc, Mutex};
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

    /// 执行带返回值的任务（4）：返回一个接收端用于获取结果
    pub fn execute_with_result<F, R>(&self, f: F) -> Receiver<R>
    where
        F: FnOnce() -> R + Send + 'static,
        R: Send + 'static,
    {
        let (tx, rx) = channel();
        self.execute(move || {
            let _ = tx.send(f());
        });
        rx
    }

    /// 尝试执行任务（发送失败时返回 false）
    pub fn try_execute<F>(&self, f: F) -> bool
    where
        F: FnOnce() + Send + 'static,
    {
        match self.sender.as_ref() {
            Some(sender) => sender.send(Box::new(f)).is_ok(),
            None => false,
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
    receiver: Arc<Mutex<Receiver<Box<dyn FnOnce() + Send + 'static>>>>,
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
            workers.push(ConfigurableWorker::new(
                id,
                Arc::clone(&receiver),
                config.keep_alive_time,
            ));
        }

        Self {
            workers,
            sender: Some(sender),
            receiver,
            config,
        }
    }

    /// 执行任务
    pub fn execute<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'static,
    {
        if let Some(sender) = self.sender.as_ref() {
            // 若未来改为有界队列，可在此触发动态扩容
            let _ = sender.send(Box::new(f));
        }
    }

    /// 尝试执行任务（队列关闭或满时返回 false）
    pub fn try_execute<F>(&self, f: F) -> bool
    where
        F: FnOnce() + Send + 'static,
    {
        match self.sender.as_ref() {
            Some(sender) => sender.send(Box::new(f)).is_ok(),
            None => false,
        }
    }

    /// 主动关闭线程池，停止接收新任务并让工作线程优雅退出
    pub fn shutdown(&mut self) {
        self.sender.take();
    }

    /// 动态扩容一次（在不超过 max_threads 时新增一个临时工作线程）
    pub fn scale_up_once(&mut self) -> bool {
        if self.workers.len() >= self.config.max_threads {
            return false;
        }
        let id = self.workers.len();
        let worker =
            ConfigurableWorker::new(id, Arc::clone(&self.receiver), self.config.keep_alive_time);
        self.workers.push(worker);
        true
    }

    /// 执行带返回值的任务，带超时；超时返回 None
    pub fn execute_with_timeout<F, R>(&self, f: F, timeout: Duration) -> Option<R>
    where
        F: FnOnce() -> R + Send + 'static,
        R: Send + 'static,
    {
        let rx = self.execute_with_result(f);
        rx.recv_timeout(timeout).ok()
    }

    /// 执行带返回值的任务（4）：返回一个接收端用于获取结果
    pub fn execute_with_result<F, R>(&self, f: F) -> Receiver<R>
    where
        F: FnOnce() -> R + Send + 'static,
        R: Send + 'static,
    {
        let (tx, rx) = channel();
        self.execute(move || {
            let _ = tx.send(f());
        });
        rx
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

    #[test]
    fn test_configurable_try_execute_and_shutdown() {
        let mut pool = ConfigurableThreadPool::new(ThreadPoolConfig::default());
        assert!(pool.try_execute(|| {}));
        pool.shutdown();
        assert!(!pool.try_execute(|| {}));
    }

    #[test]
    fn test_simple_pool_execute_with_result() {
        let pool = SimpleThreadPool::new(2);
        let rx = pool.execute_with_result(|| 7 * 6);
        assert_eq!(rx.recv().unwrap(), 42);
    }

    #[test]
    fn test_configurable_pool_execute_with_result() {
        let pool = ConfigurableThreadPool::new(ThreadPoolConfig::default());
        let rx = pool.execute_with_result(|| "ok".to_string());
        assert_eq!(rx.recv().unwrap(), "ok");
    }
}
