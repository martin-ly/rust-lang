//! Embassy异步嵌入式框架
//! 
//! Embassy是一个专为嵌入式系统设计的异步框架，提供了高效的异步运行时。

use super::{EmbeddedOSError, SystemInfo, SystemStatus, TaskInfo, TaskPriority, TaskStatus};
use std::sync::Arc;
use tokio::sync::RwLock;
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

/// Embassy任务句柄
pub struct EmbassyTask {
    id: u32,
    name: String,
    priority: TaskPriority,
    status: TaskStatus,
    future: Pin<Box<dyn Future<Output = ()> + Send + 'static>>,
}

/// Embassy管理器
pub struct EmbassyManager {
    initialized: bool,
    system_info: Option<SystemInfo>,
    tasks: Arc<RwLock<Vec<EmbassyTask>>>,
    executor: Arc<RwLock<EmbassyExecutor>>,
}

/// Embassy执行器
pub struct EmbassyExecutor {
    tasks: Vec<EmbassyTask>,
    current_task: Option<usize>,
}

impl EmbassyExecutor {
    fn new() -> Self {
        Self {
            tasks: Vec::new(),
            current_task: None,
        }
    }

    fn add_task(&mut self, task: _task) {
        self.tasks.push(task);
    }

    fn run(&mut self) {
        // 简化的任务调度逻辑
        for (i, task) in self.tasks.iter_mut().enumerate() {
            if task.status == TaskStatus::Ready {
                self.current_task = Some(i);
                // 这里应该实际执行异步任务
                task.status = TaskStatus::Running;
                break;
            }
        }
    }
}

impl EmbassyManager {
    /// 创建新的Embassy管理器
    pub fn new() -> Self {
        Self {
            initialized: false,
            system_info: None,
            tasks: Arc::new(RwLock::new(Vec::new())),
            executor: Arc::new(RwLock::new(EmbassyExecutor::new())),
        }
    }

    /// 初始化Embassy
    pub async fn initialize(&mut self) -> Result<(), EmbeddedOSError> {
        if self.initialized {
            return Ok(());
        }

        // 模拟Embassy初始化过程
        tokio::time::sleep(std::time::Duration::from_millis(50)).await;

        // 获取系统信息
        self.system_info = Some(SystemInfo {
            os_type: super::EmbeddedOSType::Embassy,
            version: "0.1.0".to_string(),
            memory_total: 128 * 1024, // 128KB
            memory_used: 32 * 1024,   // 32KB
            cpu_cores: 1,
            uptime: std::time::Duration::from_secs(0),
        });

        self.initialized = true;
        Ok(())
    }

    /// 创建异步任务
    pub async fn spawn<F>(&self, name: String, priority: TaskPriority, future: _future) -> Result<u32, EmbeddedOSError>
    where
        F: Future<Output = ()> + Send + 'static,
    {
        if !self.initialized {
            return Err(EmbeddedOSError::InitializationFailed("Embassy未初始化".to_string()));
        }

        let task_id = self.generate_task_id().await;
        let task = EmbassyTask {
            id: task_id,
            name,
            priority,
            status: TaskStatus::Ready,
            future: Box::pin(future),
        };

        let mut tasks = self.tasks.write().await;
        tasks.push(task);

        let mut executor = self.executor.write().await;
        executor.add_task(EmbassyTask {
            id: task_id,
            name: tasks.last().unwrap().name.clone(),
            priority,
            status: TaskStatus::Ready,
            future: Box::pin(async {}), // 简化版本
        });

        Ok(task_id)
    }

    /// 运行Embassy执行器
    pub async fn run(&self) -> Result<(), EmbeddedOSError> {
        if !self.initialized {
            return Err(EmbeddedOSError::InitializationFailed("Embassy未初始化".to_string()));
        }

        let mut executor = self.executor.write().await;
        executor.run();
        Ok(())
    }

    /// 创建定时器
    pub async fn create_timer(&self, duration: std::time::Duration) -> Result<EmbassyTimer, EmbeddedOSError> {
        if !self.initialized {
            return Err(EmbeddedOSError::InitializationFailed("Embassy未初始化".to_string()));
        }

        Ok(EmbassyTimer {
            duration,
            start_time: std::time::Instant::now(),
        })
    }

    /// 创建信号量
    pub async fn create_semaphore(&self, initial_count: _initial_count) -> Result<EmbassySemaphore, EmbeddedOSError> {
        if !self.initialized {
            return Err(EmbeddedOSError::InitializationFailed("Embassy未初始化".to_string()));
        }

        Ok(EmbassySemaphore {
            count: initial_count,
            waiters: Vec::new(),
        })
    }

    /// 创建互斥锁
    pub async fn create_mutex<T>(&self, value: _value) -> Result<EmbassyMutex<T>, EmbeddedOSError> {
        if !self.initialized {
            return Err(EmbeddedOSError::InitializationFailed("Embassy未初始化".to_string()));
        }

        Ok(EmbassyMutex {
            value: Some(value),
            locked: false,
        })
    }

    /// 获取任务列表
    pub async fn get_tasks(&self) -> Result<Vec<TaskInfo>, EmbeddedOSError> {
        let tasks = self.tasks.read().await;
        let task_infos: Vec<TaskInfo> = tasks.iter().map(|task| TaskInfo {
            id: task.id,
            name: task.name.clone(),
            priority: task.priority,
            status: task.status,
            stack_size: 1024, // 默认栈大小
            stack_used: 0,
            cpu_time: std::time::Duration::ZERO,
        }).collect();

        Ok(task_infos)
    }

    /// 获取系统状态
    pub async fn get_system_status(&self) -> Result<SystemStatus, EmbeddedOSError> {
        if !self.initialized {
            return Err(EmbeddedOSError::InitializationFailed("Embassy未初始化".to_string()));
        }

        let tasks = self.tasks.read().await;
        let running_tasks = tasks.iter().filter(|t| t.status == TaskStatus::Running).count();

        Ok(SystemStatus {
            cpu_usage: (running_tasks as f32 / 8.0) * 100.0, // 假设最多8个并发任务
            memory_usage: 15.0, // 15%内存使用率
            task_count: tasks.len() as u32,
            interrupt_count: 0,
            context_switches: 0,
        })
    }

    /// 获取系统信息
    pub fn get_system_info(&self) -> Result<&SystemInfo, EmbeddedOSError> {
        self.system_info.as_ref()
            .ok_or_else(|| EmbeddedOSError::InitializationFailed("系统信息未初始化".to_string()))
    }

    /// 生成任务ID
    async fn generate_task_id(&self) -> u32 {
        let tasks = self.tasks.read().await;
        let max_id = tasks.iter().map(|t| t.id).max().unwrap_or(0);
        max_id + 1
    }
}

/// Embassy定时器
pub struct EmbassyTimer {
    duration: std::time::Duration,
    start_time: std::time::Instant,
}

impl EmbassyTimer {
    /// 检查定时器是否到期
    pub fn is_elapsed(&self) -> bool {
        self.start_time.elapsed() >= self.duration
    }

    /// 重置定时器
    pub fn reset(&mut self) {
        self.start_time = std::time::Instant::now();
    }

    /// 获取剩余时间
    pub fn remaining(&self) -> std::time::Duration {
        let elapsed = self.start_time.elapsed();
        if elapsed >= self.duration {
            std::time::Duration::ZERO
        } else {
            self.duration - elapsed
        }
    }
}

impl Future for EmbassyTimer {
    type Output = ();

    fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        if self.is_elapsed() {
            Poll::Ready(())
        } else {
            Poll::Pending
        }
    }
}

/// Embassy信号量
pub struct EmbassySemaphore {
    count: usize,
    waiters: Vec<tokio::sync::oneshot::Sender<()>>,
}

impl EmbassySemaphore {
    /// 获取信号量
    pub async fn acquire(&mut self) -> Result<(), EmbeddedOSError> {
        if self.count > 0 {
            self.count -= 1;
            Ok(())
        } else {
            let (sender, receiver) = tokio::sync::oneshot::channel();
            self.waiters.push(sender);
            receiver.await.map_err(|_| EmbeddedOSError::SchedulerError("信号量等待失败".to_string()))?;
            Ok(())
        }
    }

    /// 释放信号量
    pub fn release(&mut self) {
        if let Some(waiter) = self.waiters.pop() {
            let _ = waiter.send(());
        } else {
            self.count += 1;
        }
    }

    /// 尝试获取信号量
    pub fn try_acquire(&mut self) -> bool {
        if self.count > 0 {
            self.count -= 1;
            true
        } else {
            false
        }
    }
}

/// Embassy互斥锁
pub struct EmbassyMutex<T> {
    value: Option<T>,
    locked: bool,
}

impl<T> EmbassyMutex<T> {
    /// 锁定互斥锁
    pub async fn lock(&mut self) -> Result<EmbassyMutexGuard<T>, EmbeddedOSError> {
        while self.locked {
            tokio::time::sleep(std::time::Duration::from_millis(1)).await;
        }
        
        self.locked = true;
        Ok(EmbassyMutexGuard {
            mutex: self,
        })
    }

    /// 尝试锁定互斥锁
    pub fn try_lock(&mut self) -> Result<EmbassyMutexGuard<T>, EmbeddedOSError> {
        if self.locked {
            Err(EmbeddedOSError::SchedulerError("互斥锁已被锁定".to_string()))
        } else {
            self.locked = true;
            Ok(EmbassyMutexGuard {
                mutex: self,
            })
        }
    }
}

/// Embassy互斥锁守卫
pub struct EmbassyMutexGuard<'a, T> {
    mutex: &'a mut EmbassyMutex<T>,
}

impl<'a, T> Drop for EmbassyMutexGuard<'a, T> {
    fn drop(&mut self) {
        self.mutex.locked = false;
    }
}

impl<'a, T> std::ops::Deref for EmbassyMutexGuard<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.mutex.value.as_ref().unwrap()
    }
}

impl<'a, T> std::ops::DerefMut for EmbassyMutexGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.mutex.value.as_mut().unwrap()
    }
}

impl Default for EmbassyManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_embassy_initialization() {
        let mut manager = EmbassyManager::new();
        assert!(!manager.initialized);
        
        let result = manager.initialize().await;
        assert!(result.is_ok());
        assert!(manager.initialized);
    }

    #[tokio::test]
    async fn test_embassy_spawn() {
        let mut manager = EmbassyManager::new();
        manager.initialize().await.unwrap();

        let task_id = manager.spawn(
            "test_task".to_string(),
            TaskPriority::Normal,
            async {
                println!("Hello from Embassy task!");
            }
        ).await.unwrap();

        assert_eq!(task_id, 1);

        let tasks = manager.get_tasks().await.unwrap();
        assert_eq!(tasks.len(), 1);
        assert_eq!(tasks[0].name, "test_task");
    }

    #[tokio::test]
    async fn test_embassy_timer() {
        let mut manager = EmbassyManager::new();
        manager.initialize().await.unwrap();

        let mut timer = manager.create_timer(std::time::Duration::from_millis(100)).await.unwrap();
        assert!(!timer.is_elapsed());

        tokio::time::sleep(std::time::Duration::from_millis(150)).await;
        assert!(timer.is_elapsed());
    }

    #[tokio::test]
    async fn test_embassy_semaphore() {
        let mut manager = EmbassyManager::new();
        manager.initialize().await.unwrap();

        let mut semaphore = manager.create_semaphore(1).await.unwrap();
        
        // 第一次获取应该成功
        assert!(semaphore.try_acquire());
        
        // 第二次获取应该失败
        assert!(!semaphore.try_acquire());
        
        // 释放后应该可以再次获取
        semaphore.release();
        assert!(semaphore.try_acquire());
    }

    #[tokio::test]
    async fn test_embassy_mutex() {
        let mut manager = EmbassyManager::new();
        manager.initialize().await.unwrap();

        let mut mutex = manager.create_mutex(42).await.unwrap();
        
        {
            let guard = mutex.lock().await.unwrap();
            assert_eq!(*guard, 42);
        }
        
        // 锁应该已经释放
        let guard = mutex.try_lock().unwrap();
        assert_eq!(*guard, 42);
    }
}
