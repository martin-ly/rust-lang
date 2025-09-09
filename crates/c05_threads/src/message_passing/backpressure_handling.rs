//! 背压处理机制
//! 
//! 本模块提供了多种背压处理策略：
//! - 阻塞背压
//! - 丢弃背压
//! - 自适应背压
//! - 流量控制背压

use std::sync::{
    Arc, 
    Mutex, 
    //Condvar, 
    atomic::{
        AtomicUsize,
        //AtomicBool,
        Ordering}
    };
use std::thread;
use std::time::{Duration, Instant};
//use std::collections::VecDeque;
use crossbeam_channel::{
    bounded, 
    //unbounded,
    Receiver,
    Sender,
    TrySendError
};
use std::sync::atomic::{AtomicBool, Ordering as AtomicOrdering};
use std::thread::sleep;

//use parking_lot::{
//    Mutex as ParkingMutex,
//    RwLock as ParkingRwLock,
//};

/// 统一发送端抽象
pub trait BackpressureTx<T: Send>: Send + Sync {
    fn send(&self, message: T) -> Result<(), T>;
}

/// 统一接收端抽象
pub trait BackpressureRx<T: Send>: Send + Sync {
    fn recv(&self) -> Option<T>;
}

/// 将任意实现 BackpressureRx 的通道桥接到 crossbeam 的 Sender
pub fn bridge_to_mpsc<T: Send, R>(rx: Arc<R>, tx: Sender<T>, max_forward: Option<usize>, stop: Option<Arc<AtomicBool>>)
where
    R: BackpressureRx<T> + ?Sized,
{
    let mut forwarded = 0usize;
    loop {
        if let Some(flag) = &stop {
            if flag.load(AtomicOrdering::Relaxed) { break; }
        }
        if let Some(v) = rx.recv() {
            if tx.send(v).is_err() { break; }
            forwarded += 1;
            if let Some(limit) = max_forward { if forwarded >= limit { break; } }
        } else {
            break;
        }
    }
}

/// 限速桥接：控制每个元素发送之间的最小时间间隔
pub fn bridge_to_mpsc_rate_limited<T: Send, R>(rx: Arc<R>, tx: Sender<T>, min_interval: Duration, max_forward: Option<usize>, stop: Option<Arc<AtomicBool>>)
where
    R: BackpressureRx<T> + ?Sized,
{
    let mut forwarded = 0usize;
    let mut last = Instant::now();
    loop {
        if let Some(flag) = &stop {
            if flag.load(AtomicOrdering::Relaxed) { break; }
        }
        if let Some(v) = rx.recv() {
            let elapsed = last.elapsed();
            if elapsed < min_interval { sleep(min_interval - elapsed); }
            if tx.send(v).is_err() { break; }
            last = Instant::now();
            forwarded += 1;
            if let Some(limit) = max_forward { if forwarded >= limit { break; } }
        } else {
            break;
        }
    }
}

/// 背压策略枚举
#[derive(Debug, Clone, PartialEq)]
pub enum BackpressureStrategy {
    /// 阻塞策略：当缓冲区满时阻塞发送者
    Blocking,
    /// 丢弃策略：当缓冲区满时丢弃新消息
    Dropping,
    /// 自适应策略：根据系统负载动态调整
    Adaptive,
    /// 流量控制策略：使用滑动窗口控制流量
    FlowControl,
}

/// 背压配置
#[derive(Debug, Clone)]
pub struct BackpressureConfig {
    pub strategy: BackpressureStrategy,
    pub buffer_size: usize,
    pub high_watermark: f64, // 高水位线比例 (0.0 - 1.0)
    pub low_watermark: f64,  // 低水位线比例 (0.0 - 1.0)
    pub drop_threshold: f64, // 丢弃阈值比例 (0.0 - 1.0)
    pub adaptation_interval: Duration,
}

impl Default for BackpressureConfig {
    fn default() -> Self {
        Self {
            strategy: BackpressureStrategy::Blocking,
            buffer_size: 1000,
            high_watermark: 0.8,
            low_watermark: 0.2,
            drop_threshold: 0.9,
            adaptation_interval: Duration::from_millis(100),
        }
    }
}

/// 阻塞背压通道
/// 
/// 当缓冲区满时阻塞发送者，直到有空间可用
pub struct BlockingBackpressureChannel<T> {
    sender: Sender<T>,
    receiver: Receiver<T>,
    buffer_size: usize,
    current_size: AtomicUsize,
}

impl<T> BlockingBackpressureChannel<T> {
    /// 创建新的阻塞背压通道
    pub fn new(buffer_size: usize) -> Self {
        let (sender, receiver) = bounded(buffer_size);
        
        Self {
            sender,
            receiver,
            buffer_size,
            current_size: AtomicUsize::new(0),
        }
    }
    
    /// 发送消息（阻塞）
    pub fn send(&self, message: T) -> Result<(), T> {
        match self.sender.try_send(message) {
            Ok(()) => {
                self.current_size.fetch_add(1, Ordering::Relaxed);
                Ok(())
            }
            Err(TrySendError::Full(message)) => {
                // 阻塞等待
                self.sender.send(message).map_err(|e| e.into_inner())
            }
            Err(TrySendError::Disconnected(message)) => Err(message),
        }
    }
    
    /// 接收消息
    pub fn recv(&self) -> Option<T> {
        let result = self.receiver.recv();
        if result.is_ok() {
            self.current_size.fetch_sub(1, Ordering::Relaxed);
        }
        result.ok()
    }
    
    /// 尝试发送消息（非阻塞）
    pub fn try_send(&self, message: T) -> Result<(), T> {
        match self.sender.try_send(message) {
            Ok(()) => {
                self.current_size.fetch_add(1, Ordering::Relaxed);
                Ok(())
            }
            Err(TrySendError::Full(message)) => Err(message),
            Err(TrySendError::Disconnected(message)) => Err(message),
        }
    }
    
    /// 获取当前缓冲区使用率
    pub fn usage_ratio(&self) -> f64 {
        let current = self.current_size.load(Ordering::Relaxed);
        current as f64 / self.buffer_size as f64
    }
    
    /// 运行阻塞背压示例
    pub fn run_example() {
        println!("=== 阻塞背压通道示例 ===");
        
        let channel = Arc::new(BlockingBackpressureChannel::new(5));
        
        // 创建快速生产者
        let producer = {
            let channel = channel.clone();
            thread::spawn(move || {
                for i in 0..10 {
                    println!("尝试发送消息 {}", i);
                    channel.send(i).unwrap();
                    println!("成功发送消息 {}", i);
                    thread::sleep(Duration::from_millis(100));
                }
                println!("生产者完成");
            })
        };
        
        // 创建慢速消费者
        let consumer = {
            let channel = channel.clone();
            thread::spawn(move || {
                for _i in 0..10 {
                    if let Some(message) = channel.recv() {
                        println!("接收到消息: {}", message);
                        thread::sleep(Duration::from_millis(300));
                    }
                }
                println!("消费者完成");
            })
        };
        
        producer.join().unwrap();
        consumer.join().unwrap();
    }
}

impl<T: Send> BackpressureTx<T> for BlockingBackpressureChannel<T> {
    fn send(&self, message: T) -> Result<(), T> { Self::send(self, message) }
}

impl<T: Send> BackpressureRx<T> for BlockingBackpressureChannel<T> {
    fn recv(&self) -> Option<T> { Self::recv(self) }
}

/// 丢弃背压通道
/// 
/// 当缓冲区满时丢弃新消息
pub struct DroppingBackpressureChannel<T> {
    sender: Sender<T>,
    receiver: Receiver<T>,
    buffer_size: usize,
    current_size: AtomicUsize,
    dropped_count: AtomicUsize,
    drop_threshold: f64,
}

impl<T> DroppingBackpressureChannel<T> {
    /// 创建新的丢弃背压通道
    pub fn new(buffer_size: usize, drop_threshold: f64) -> Self {
        let (sender, receiver) = bounded(buffer_size);
        
        Self {
            sender,
            receiver,
            buffer_size,
            current_size: AtomicUsize::new(0),
            dropped_count: AtomicUsize::new(0),
            drop_threshold,
        }
    }
    
    /// 发送消息（可能丢弃）
    pub fn send(&self, message: T) -> Result<(), T> {
        let usage_ratio = self.usage_ratio();
        
        if usage_ratio > self.drop_threshold {
            // 丢弃消息
            self.dropped_count.fetch_add(1, Ordering::Relaxed);
            return Err(message);
        }
        
        match self.sender.try_send(message) {
            Ok(()) => {
                self.current_size.fetch_add(1, Ordering::Relaxed);
                Ok(())
            }
            Err(TrySendError::Full(message)) => {
                // 缓冲区满，丢弃消息
                self.dropped_count.fetch_add(1, Ordering::Relaxed);
                Err(message)
            }
            Err(TrySendError::Disconnected(message)) => Err(message),
        }
    }
    
    /// 接收消息
    pub fn recv(&self) -> Option<T> {
        let result = self.receiver.recv();
        if result.is_ok() {
            self.current_size.fetch_sub(1, Ordering::Relaxed);
        }
        result.ok()
    }
    
    /// 获取当前缓冲区使用率
    pub fn usage_ratio(&self) -> f64 {
        let current = self.current_size.load(Ordering::Relaxed);
        current as f64 / self.buffer_size as f64
    }
    
    /// 获取丢弃的消息数量
    pub fn dropped_count(&self) -> usize {
        self.dropped_count.load(Ordering::Relaxed)
    }
    
    /// 运行丢弃背压示例
    pub fn run_example() {
        println!("=== 丢弃背压通道示例 ===");
        
        let channel = Arc::new(DroppingBackpressureChannel::new(5, 0.8));
        
        // 创建快速生产者
        let producer = {
            let channel = channel.clone();
            thread::spawn(move || {
                for i in 0..20 {
                    match channel.send(i) {
                        Ok(()) => println!("成功发送消息 {}", i),
                        Err(_) => println!("丢弃消息 {}", i),
                    }
                    thread::sleep(Duration::from_millis(50));
                }
                println!("生产者完成，丢弃了 {} 条消息", channel.dropped_count());
            })
        };
        
        // 创建慢速消费者
        let consumer = {
            let channel = channel.clone();
            thread::spawn(move || {
                for _ in 0..20 {
                    if let Some(message) = channel.recv() {
                        println!("接收到消息: {}", message);
                        thread::sleep(Duration::from_millis(200));
                    }
                }
                println!("消费者完成");
            })
        };
        
        producer.join().unwrap();
        consumer.join().unwrap();
    }
}

impl<T: Send> BackpressureTx<T> for DroppingBackpressureChannel<T> {
    fn send(&self, message: T) -> Result<(), T> { Self::send(self, message) }
}

impl<T: Send> BackpressureRx<T> for DroppingBackpressureChannel<T> {
    fn recv(&self) -> Option<T> { Self::recv(self) }
}

/// 自适应背压通道
/// 
/// 根据系统负载动态调整背压策略
pub struct AdaptiveBackpressureChannel<T> {
    sender: Sender<T>,
    receiver: Receiver<T>,
    buffer_size: usize,
    current_size: AtomicUsize,
    dropped_count: AtomicUsize,
    config: BackpressureConfig,
    last_adaptation: Arc<Mutex<Instant>>,
    current_strategy: Arc<Mutex<BackpressureStrategy>>,
}

impl<T> AdaptiveBackpressureChannel<T> {
    /// 创建新的自适应背压通道
    pub fn new(config: BackpressureConfig) -> Self {
        let (sender, receiver) = bounded(config.buffer_size);
        
        Self {
            sender,
            receiver,
            buffer_size: config.buffer_size,
            current_size: AtomicUsize::new(0),
            dropped_count: AtomicUsize::new(0),
            config,
            last_adaptation: Arc::new(Mutex::new(Instant::now())),
            current_strategy: Arc::new(Mutex::new(BackpressureStrategy::Blocking)),
        }
    }
    
    /// 发送消息（自适应策略）
    pub fn send(&self, message: T) -> Result<(), T> {
        self.adapt_strategy();
        
        let strategy = self.current_strategy.lock().unwrap().clone();
        
        match strategy {
            BackpressureStrategy::Blocking => self.send_blocking(message),
            BackpressureStrategy::Dropping => self.send_dropping(message),
            BackpressureStrategy::Adaptive => self.send_adaptive(message),
            BackpressureStrategy::FlowControl => self.send_flow_control(message),
        }
    }
    
    fn send_blocking(&self, message: T) -> Result<(), T> {
        match self.sender.send(message) {
            Ok(()) => {
                self.current_size.fetch_add(1, Ordering::Relaxed);
                Ok(())
            }
            Err(e) => Err(e.into_inner()),
        }
    }
    
    fn send_dropping(&self, message: T) -> Result<(), T> {
        let usage_ratio = self.usage_ratio();
        
        if usage_ratio > self.config.drop_threshold {
            self.dropped_count.fetch_add(1, Ordering::Relaxed);
            return Err(message);
        }
        
        match self.sender.try_send(message) {
            Ok(()) => {
                self.current_size.fetch_add(1, Ordering::Relaxed);
                Ok(())
            }
            Err(TrySendError::Full(message)) => {
                self.dropped_count.fetch_add(1, Ordering::Relaxed);
                Err(message)
            }
            Err(TrySendError::Disconnected(message)) => Err(message),
        }
    }
    
    fn send_adaptive(&self, message: T) -> Result<(), T> {
        let usage_ratio = self.usage_ratio();
        
        if usage_ratio >= self.config.high_watermark {
            // 高负载，使用丢弃策略
            self.send_dropping(message)
        } else {
            // 低负载，使用阻塞策略
            self.send_blocking(message)
        }
    }
    
    fn send_flow_control(&self, message: T) -> Result<(), T> {
        // 实现流量控制逻辑
        self.send_blocking(message)
    }
    
    fn adapt_strategy(&self) {
        let mut last_adaptation = self.last_adaptation.lock().unwrap();
        if last_adaptation.elapsed() < self.config.adaptation_interval {
            return;
        }
        
        let usage_ratio = self.usage_ratio();
        let mut strategy = self.current_strategy.lock().unwrap();
        
        if usage_ratio >= self.config.high_watermark {
            *strategy = BackpressureStrategy::Dropping;
        } else if usage_ratio <= self.config.low_watermark {
            *strategy = BackpressureStrategy::Blocking;
        } else {
            *strategy = BackpressureStrategy::Adaptive;
        }
        
        *last_adaptation = Instant::now();
    }
    
    /// 接收消息
    pub fn recv(&self) -> Option<T> {
        let result = self.receiver.recv();
        if result.is_ok() {
            self.current_size.fetch_sub(1, Ordering::Relaxed);
        }
        result.ok()
    }
    
    /// 获取当前缓冲区使用率
    pub fn usage_ratio(&self) -> f64 {
        let current = self.current_size.load(Ordering::Relaxed);
        current as f64 / self.buffer_size as f64
    }
    
    /// 获取丢弃的消息数量
    pub fn dropped_count(&self) -> usize {
        self.dropped_count.load(Ordering::Relaxed)
    }
    
    /// 运行自适应背压示例
    pub fn run_example() {
        println!("=== 自适应背压通道示例 ===");
        
        let config = BackpressureConfig {
            strategy: BackpressureStrategy::Adaptive,
            buffer_size: 10,
            high_watermark: 0.7,
            low_watermark: 0.3,
            drop_threshold: 0.9,
            adaptation_interval: Duration::from_millis(100),
        };
        
        let channel = Arc::new(AdaptiveBackpressureChannel::new(config));
        
        // 创建快速生产者
        let producer = {
            let channel = channel.clone();
            thread::spawn(move || {
                for i in 0..30 {
                    match channel.send(i) {
                        Ok(()) => println!("成功发送消息 {}", i),
                        Err(_) => println!("丢弃消息 {}", i),
                    }
                    thread::sleep(Duration::from_millis(50));
                }
                println!("生产者完成，丢弃了 {} 条消息", channel.dropped_count());
            })
        };
        
        // 创建慢速消费者
        let consumer = {
            let channel = channel.clone();
            thread::spawn(move || {
                for _ in 0..30 {
                    if let Some(message) = channel.recv() {
                        println!("接收到消息: {}", message);
                        thread::sleep(Duration::from_millis(200));
                    }
                }
                println!("消费者完成");
            })
        };
        
        producer.join().unwrap();
        consumer.join().unwrap();
    }
}

impl<T: Send> BackpressureTx<T> for AdaptiveBackpressureChannel<T> {
    fn send(&self, message: T) -> Result<(), T> { Self::send(self, message) }
}

impl<T: Send> BackpressureRx<T> for AdaptiveBackpressureChannel<T> {
    fn recv(&self) -> Option<T> { Self::recv(self) }
}

/// 流量控制背压通道
/// 
/// 使用滑动窗口控制流量
pub struct FlowControlBackpressureChannel<T> {
    sender: Sender<T>,
    receiver: Receiver<T>,
    buffer_size: usize,
    current_size: AtomicUsize,
    window_size: usize,
    current_window: AtomicUsize,
    window_reset_time: Duration,
    last_window_reset: Arc<Mutex<Instant>>,
}

impl<T> FlowControlBackpressureChannel<T> {
    /// 创建新的流量控制背压通道
    pub fn new(buffer_size: usize, window_size: usize, window_reset_time: Duration) -> Self {
        let (sender, receiver) = bounded(buffer_size);
        
        Self {
            sender,
            receiver,
            buffer_size,
            current_size: AtomicUsize::new(0),
            window_size,
            current_window: AtomicUsize::new(0),
            window_reset_time,
            last_window_reset: Arc::new(Mutex::new(Instant::now())),
        }
    }
    
    /// 发送消息（流量控制）
    pub fn send(&self, message: T) -> Result<(), T> {
        self.reset_window_if_needed();
        
        if self.current_window.load(Ordering::Relaxed) >= self.window_size {
            return Err(message);
        }
        
        match self.sender.try_send(message) {
            Ok(()) => {
                self.current_size.fetch_add(1, Ordering::Relaxed);
                self.current_window.fetch_add(1, Ordering::Relaxed);
                Ok(())
            }
            Err(TrySendError::Full(message)) => Err(message),
            Err(TrySendError::Disconnected(message)) => Err(message),
        }
    }
    
    /// 接收消息
    pub fn recv(&self) -> Option<T> {
        let result = self.receiver.recv();
        if result.is_ok() {
            self.current_size.fetch_sub(1, Ordering::Relaxed);
        }
        result.ok()
    }
    
    fn reset_window_if_needed(&self) {
        let mut last_reset = self.last_window_reset.lock().unwrap();
        if last_reset.elapsed() >= self.window_reset_time {
            self.current_window.store(0, Ordering::Relaxed);
            *last_reset = Instant::now();
        }
    }
    
    /// 获取当前缓冲区使用率
    pub fn usage_ratio(&self) -> f64 {
        let current = self.current_size.load(Ordering::Relaxed);
        current as f64 / self.buffer_size as f64
    }
    
    /// 获取当前窗口使用率
    pub fn window_usage_ratio(&self) -> f64 {
        let current = self.current_window.load(Ordering::Relaxed);
        current as f64 / self.window_size as f64
    }
    
    /// 运行流量控制背压示例
    pub fn run_example() {
        println!("=== 流量控制背压通道示例 ===");
        
        let channel = Arc::new(FlowControlBackpressureChannel::new(
            10, 5, Duration::from_millis(500)
        ));
        
        // 创建快速生产者
        let producer = {
            let channel = channel.clone();
            thread::spawn(move || {
                for i in 0..20 {
                    match channel.send(i) {
                        Ok(()) => println!("成功发送消息 {}", i),
                        Err(_) => println!("流量控制拒绝消息 {}", i),
                    }
                    thread::sleep(Duration::from_millis(100));
                }
                println!("生产者完成");
            })
        };
        
        // 创建慢速消费者
        let consumer = {
            let channel = channel.clone();
            thread::spawn(move || {
                for _ in 0..20 {
                    if let Some(message) = channel.recv() {
                        println!("接收到消息: {}", message);
                        thread::sleep(Duration::from_millis(300));
                    }
                }
                println!("消费者完成");
            })
        };
        
        producer.join().unwrap();
        consumer.join().unwrap();
    }
}

impl<T: Send> BackpressureTx<T> for FlowControlBackpressureChannel<T> {
    fn send(&self, message: T) -> Result<(), T> { Self::send(self, message) }
}

impl<T: Send> BackpressureRx<T> for FlowControlBackpressureChannel<T> {
    fn recv(&self) -> Option<T> { Self::recv(self) }
}

/// 运行所有背压处理示例
pub fn demonstrate_backpressure_handling() {
    println!("=== 背压处理演示 ===");
    
    BlockingBackpressureChannel::<i32>::run_example();
    DroppingBackpressureChannel::<i32>::run_example();
    AdaptiveBackpressureChannel::<i32>::run_example();
    FlowControlBackpressureChannel::<i32>::run_example();
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_blocking_backpressure() {
        let channel = BlockingBackpressureChannel::new(2);
        
        // 测试发送
        assert!(channel.send(1).is_ok());
        assert!(channel.send(2).is_ok());
        
        // 测试接收
        assert_eq!(channel.recv(), Some(1));
        assert_eq!(channel.recv(), Some(2));
    }
    
    #[test]
    fn test_dropping_backpressure() {
        let channel = DroppingBackpressureChannel::new(2, 0.5);
        
        // 测试发送
        assert!(channel.send(1).is_ok());
        assert!(channel.send(2).is_ok());
        
        // 测试接收
        assert_eq!(channel.recv(), Some(1));
        assert_eq!(channel.recv(), Some(2));
    }
    
    #[test]
    fn test_adaptive_backpressure() {
        let config = BackpressureConfig::default();
        let channel = AdaptiveBackpressureChannel::new(config);
        
        // 测试发送
        assert!(channel.send(1).is_ok());
        
        // 测试接收
        assert_eq!(channel.recv(), Some(1));
    }
    
    #[test]
    fn test_flow_control_backpressure() {
        let channel = FlowControlBackpressureChannel::new(2, 1, Duration::from_millis(100));
        
        // 测试发送
        assert!(channel.send(1).is_ok());
        
        // 测试接收
        assert_eq!(channel.recv(), Some(1));
    }
}
