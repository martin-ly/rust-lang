//! 异步并发工具和示例
//!
//! 本模块提供异步并发编程的工具和示例，包括：
//! - 异步任务管理
//! - 异步通道通信
//! - 异步屏障和信号量
//! - 异步超时处理

use std::sync::Arc;
use std::time::Duration;

/// 异步任务管理器
///
/// 用于管理和调度异步任务
pub struct AsyncTaskManager {
    tasks: Vec<TaskHandle>,
}

/// 任务句柄
pub struct TaskHandle {
    id: u64,
    name: String,
}

impl AsyncTaskManager {
    /// 创建新的异步任务管理器
    pub fn new() -> Self {
        Self {
            tasks: Vec::new(),
        }
    }

    /// 注册任务
    pub fn register_task(&mut self, id: u64, name: String) -> TaskHandle {
        let handle = TaskHandle { id, name };
        self.tasks.push(handle.clone());
        handle
    }

    /// 获取任务数量
    pub fn task_count(&self) -> usize {
        self.tasks.len()
    }

    /// 获取所有任务
    pub fn get_tasks(&self) -> &[TaskHandle] {
        &self.tasks
    }
}

impl Default for AsyncTaskManager {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for TaskHandle {
    fn clone(&self) -> Self {
        Self {
            id: self.id,
            name: self.name.clone(),
        }
    }
}

impl TaskHandle {
    /// 获取任务ID
    pub fn id(&self) -> u64 {
        self.id
    }

    /// 获取任务名称
    pub fn name(&self) -> &str {
        &self.name
    }
}

/// 异步通道包装器
///
/// 提供异步发送和接收功能
pub struct AsyncChannel<T> {
    sender: Arc<std::sync::mpsc::Sender<T>>,
    receiver: Arc<std::sync::mpsc::Receiver<T>>,
}

impl<T> AsyncChannel<T> {
    /// 创建新的异步通道
    pub fn new() -> Self {
        let (sender, receiver) = std::sync::mpsc::channel();
        Self {
            sender: Arc::new(sender),
            receiver: Arc::new(receiver),
        }
    }

    /// 获取发送端
    pub fn sender(&self) -> AsyncSender<T> {
        AsyncSender {
            inner: Arc::clone(&self.sender),
        }
    }

    /// 获取接收端
    pub fn receiver(&self) -> AsyncReceiver<T> {
        AsyncReceiver {
            inner: Arc::clone(&self.receiver),
        }
    }
}

impl<T> Default for AsyncChannel<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// 异步发送端
pub struct AsyncSender<T> {
    inner: Arc<std::sync::mpsc::Sender<T>>,
}

impl<T> AsyncSender<T> {
    /// 发送消息（非阻塞）
    pub fn send(&self, msg: T) -> Result<(), String> {
        self.inner
            .send(msg)
            .map_err(|e| format!("Send error: {}", e))
    }
}

impl<T> Clone for AsyncSender<T> {
    fn clone(&self) -> Self {
        Self {
            inner: Arc::clone(&self.inner),
        }
    }
}

/// 异步接收端
pub struct AsyncReceiver<T> {
    inner: Arc<std::sync::mpsc::Receiver<T>>,
}

impl<T> AsyncReceiver<T> {
    /// 接收消息（阻塞）
    pub fn recv(&self) -> Result<T, String> {
        self.inner
            .recv()
            .map_err(|e| format!("Receive error: {}", e))
    }

    /// 尝试接收消息（非阻塞）
    pub fn try_recv(&self) -> Result<T, String> {
        self.inner
            .try_recv()
            .map_err(|e| format!("Try receive error: {}", e))
    }
}

/// 异步屏障
///
/// 用于同步多个异步任务
pub struct AsyncBarrier {
    count: Arc<std::sync::atomic::AtomicUsize>,
    target: usize,
}

impl AsyncBarrier {
    /// 创建新的异步屏障
    pub fn new(count: usize) -> Self {
        Self {
            count: Arc::new(std::sync::atomic::AtomicUsize::new(0)),
            target: count,
        }
    }

    /// 等待所有任务到达屏障
    pub fn wait(&self) -> bool {
        let current = self.count.fetch_add(1, std::sync::atomic::Ordering::SeqCst) + 1;
        current >= self.target
    }

    /// 重置屏障
    pub fn reset(&self) {
        self.count.store(0, std::sync::atomic::Ordering::SeqCst);
    }

    /// 获取当前等待的任务数
    pub fn current_count(&self) -> usize {
        self.count.load(std::sync::atomic::Ordering::SeqCst)
    }
}

/// 异步超时包装器
///
/// 为操作添加超时功能
pub struct AsyncTimeout {
    duration: Duration,
}

impl AsyncTimeout {
    /// 创建新的超时包装器
    pub fn new(duration: Duration) -> Self {
        Self { duration }
    }

    /// 获取超时时间
    pub fn duration(&self) -> Duration {
        self.duration
    }

    /// 检查是否超时（示例实现）
    pub fn is_timeout(&self, elapsed: Duration) -> bool {
        elapsed >= self.duration
    }
}

/// 异步信号量
///
/// 用于控制并发访问数量
pub struct AsyncSemaphore {
    permits: Arc<std::sync::atomic::AtomicUsize>,
    max_permits: usize,
}

impl AsyncSemaphore {
    /// 创建新的信号量
    pub fn new(permits: usize) -> Self {
        Self {
            permits: Arc::new(std::sync::atomic::AtomicUsize::new(permits)),
            max_permits: permits,
        }
    }

    /// 获取许可（非阻塞）
    pub fn try_acquire(&self) -> bool {
        let current = self.permits.load(std::sync::atomic::Ordering::SeqCst);
        if current > 0 {
            self.permits
                .compare_exchange(
                    current,
                    current - 1,
                    std::sync::atomic::Ordering::SeqCst,
                    std::sync::atomic::Ordering::SeqCst,
                )
                .is_ok()
        } else {
            false
        }
    }

    /// 释放许可
    pub fn release(&self) {
        let current = self.permits.load(std::sync::atomic::Ordering::SeqCst);
        if current < self.max_permits {
            self.permits
                .store(current + 1, std::sync::atomic::Ordering::SeqCst);
        }
    }

    /// 获取可用许可数
    pub fn available_permits(&self) -> usize {
        self.permits.load(std::sync::atomic::Ordering::SeqCst)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_async_task_manager() {
        let mut manager = AsyncTaskManager::new();
        assert_eq!(manager.task_count(), 0);

        let handle1 = manager.register_task(1, "Task1".to_string());
        let handle2 = manager.register_task(2, "Task2".to_string());

        assert_eq!(manager.task_count(), 2);
        assert_eq!(handle1.id(), 1);
        assert_eq!(handle1.name(), "Task1");
        assert_eq!(handle2.id(), 2);
        assert_eq!(handle2.name(), "Task2");
    }

    #[test]
    fn test_async_channel() {
        let channel = AsyncChannel::new();
        let sender = channel.sender();
        let receiver = channel.receiver();

        assert!(sender.send(42).is_ok());
        assert_eq!(receiver.recv().unwrap(), 42);
    }

    #[test]
    fn test_async_barrier() {
        let barrier = AsyncBarrier::new(3);
        assert_eq!(barrier.current_count(), 0);

        assert!(!barrier.wait()); // 1/3
        assert_eq!(barrier.current_count(), 1);
        assert!(!barrier.wait()); // 2/3
        assert_eq!(barrier.current_count(), 2);
        assert!(barrier.wait()); // 3/3, 达到目标

        barrier.reset();
        assert_eq!(barrier.current_count(), 0);
    }

    #[test]
    fn test_async_semaphore() {
        let semaphore = AsyncSemaphore::new(3);
        assert_eq!(semaphore.available_permits(), 3);

        assert!(semaphore.try_acquire());
        assert_eq!(semaphore.available_permits(), 2);

        assert!(semaphore.try_acquire());
        assert_eq!(semaphore.available_permits(), 1);

        semaphore.release();
        assert_eq!(semaphore.available_permits(), 2);
    }

    #[test]
    fn test_async_timeout() {
        let timeout = AsyncTimeout::new(Duration::from_secs(5));
        assert_eq!(timeout.duration(), Duration::from_secs(5));

        assert!(!timeout.is_timeout(Duration::from_secs(3)));
        assert!(timeout.is_timeout(Duration::from_secs(5)));
        assert!(timeout.is_timeout(Duration::from_secs(10)));
    }
}
