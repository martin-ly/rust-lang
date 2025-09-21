//! RTIC (Real-Time Interrupt-driven Concurrency) 模块
//! 
//! RTIC是一个用于嵌入式系统的实时中断驱动并发框架。

use super::{EmbeddedOSError, SystemInfo, SystemStatus, TaskInfo, TaskPriority, TaskStatus};
use std::sync::Arc;
use tokio::sync::RwLock;
use std::collections::HashMap;

/// RTIC中断优先级
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum InterruptPriority {
    Level0 = 0,
    Level1 = 1,
    Level2 = 2,
    Level3 = 3,
    Level4 = 4,
    Level5 = 5,
    Level6 = 6,
    Level7 = 7,
}

/// RTIC任务
pub struct RTICTask {
    pub id: u32,
    pub name: String,
    pub priority: TaskPriority,
    pub interrupt_priority: InterruptPriority,
    pub status: TaskStatus,
    pub handler: Box<dyn Fn() + Send + Sync>,
}

/// RTIC资源
pub struct RTICResource<T> {
    pub name: String,
    pub value: T,
    pub locked: bool,
    pub lock_holder: Option<u32>,
}

/// RTIC管理器
pub struct RTICManager {
    initialized: bool,
    system_info: Option<SystemInfo>,
    tasks: Arc<RwLock<HashMap<u32, RTICTask>>>,
    resources: Arc<RwLock<HashMap<String, Box<dyn std::any::Any + Send + Sync>>>>,
    interrupt_handlers: Arc<RwLock<HashMap<u32, Box<dyn Fn() + Send + Sync>>>>,
}

impl RTICManager {
    /// 创建新的RTIC管理器
    pub fn new() -> Self {
        Self {
            initialized: false,
            system_info: None,
            tasks: Arc::new(RwLock::new(HashMap::new())),
            resources: Arc::new(RwLock::new(HashMap::new())),
            interrupt_handlers: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 初始化RTIC
    pub async fn initialize(&mut self) -> Result<(), EmbeddedOSError> {
        if self.initialized {
            return Ok(());
        }

        // 模拟RTIC初始化过程
        tokio::time::sleep(std::time::Duration::from_millis(75)).await;

        // 获取系统信息
        self.system_info = Some(SystemInfo {
            os_type: super::EmbeddedOSType::RTIC,
            version: "0.6.0".to_string(),
            memory_total: 64 * 1024, // 64KB
            memory_used: 16 * 1024,  // 16KB
            cpu_cores: 1,
            uptime: std::time::Duration::from_secs(0),
        });

        self.initialized = true;
        Ok(())
    }

    /// 创建RTIC任务
    pub async fn create_task<F>(
        &self,
        name: String,
        priority: TaskPriority,
        interrupt_priority: InterruptPriority,
        handler: F,
    ) -> Result<u32, EmbeddedOSError>
    where
        F: Fn() + Send + Sync + 'static,
    {
        if !self.initialized {
            return Err(EmbeddedOSError::InitializationFailed("RTIC未初始化".to_string()));
        }

        let task_id = self.generate_task_id().await;
        let task = RTICTask {
            id: task_id,
            name,
            priority,
            interrupt_priority,
            status: TaskStatus::Ready,
            handler: Box::new(handler),
        };

        let mut tasks = self.tasks.write().await;
        tasks.insert(task_id, task);

        Ok(task_id)
    }

    /// 创建共享资源
    pub async fn create_resource<T>(&self, name: String, initial_value: _initial_value) -> Result<(), EmbeddedOSError>
    where
        T: Send + Sync + 'static,
    {
        if !self.initialized {
            return Err(EmbeddedOSError::InitializationFailed("RTIC未初始化".to_string()));
        }

        let resource = RTICResource {
            name: name.clone(),
            value: initial_value,
            locked: false,
            lock_holder: None,
        };

        let mut resources = self.resources.write().await;
        resources.insert(name, Box::new(resource));

        Ok(())
    }

    /// 锁定资源
    pub async fn lock_resource<T>(&self, name: &str, task_id: _task_id) -> Result<RTICResourceGuard<T>, EmbeddedOSError>
    where
        T: Send + Sync + 'static,
    {
        let mut resources = self.resources.write().await;
        
        if let Some(resource) = resources.get_mut(name) {
            if let Some(rtic_resource) = resource.downcast_mut::<RTICResource<T>>() {
                if rtic_resource.locked && rtic_resource.lock_holder != Some(task_id) {
                    return Err(EmbeddedOSError::SchedulerError(
                        format!("资源 {} 已被其他任务锁定", name)
                    ));
                }

                rtic_resource.locked = true;
                rtic_resource.lock_holder = Some(task_id);

                Ok(RTICResourceGuard {
                    resource: rtic_resource,
                    task_id,
                })
            } else {
                Err(EmbeddedOSError::SchedulerError(
                    format!("资源 {} 类型不匹配", name)
                ))
            }
        } else {
            Err(EmbeddedOSError::SchedulerError(
                format!("资源 {} 不存在", name)
            ))
        }
    }

    /// 注册中断处理器
    pub async fn register_interrupt_handler<F>(
        &self,
        interrupt_number: u32,
        handler: F,
    ) -> Result<(), EmbeddedOSError>
    where
        F: Fn() + Send + Sync + 'static,
    {
        if !self.initialized {
            return Err(EmbeddedOSError::InitializationFailed("RTIC未初始化".to_string()));
        }

        let mut handlers = self.interrupt_handlers.write().await;
        handlers.insert(interrupt_number, Box::new(handler));

        Ok(())
    }

    /// 触发中断
    pub async fn trigger_interrupt(&self, interrupt_number: _interrupt_number) -> Result<(), EmbeddedOSError> {
        let handlers = self.interrupt_handlers.read().await;
        
        if let Some(handler) = handlers.get(&interrupt_number) {
            handler();
            Ok(())
        } else {
            Err(EmbeddedOSError::SchedulerError(
                format!("中断 {} 未注册处理器", interrupt_number)
            ))
        }
    }

    /// 启动任务
    pub async fn start_task(&self, task_id: _task_id) -> Result<(), EmbeddedOSError> {
        let mut tasks = self.tasks.write().await;
        
        if let Some(task) = tasks.get_mut(&task_id) {
            if task.status == TaskStatus::Ready {
                task.status = TaskStatus::Running;
                Ok(())
            } else {
                Err(EmbeddedOSError::SchedulerError(
                    format!("任务 {} 状态不正确: {:?}", task_id, task.status)
                ))
            }
        } else {
            Err(EmbeddedOSError::SchedulerError(
                format!("任务 {} 不存在", task_id)
            ))
        }
    }

    /// 执行任务
    pub async fn execute_task(&self, task_id: _task_id) -> Result<(), EmbeddedOSError> {
        let tasks = self.tasks.read().await;
        
        if let Some(task) = tasks.get(&task_id) {
            if task.status == TaskStatus::Running {
                (task.handler)();
                Ok(())
            } else {
                Err(EmbeddedOSError::SchedulerError(
                    format!("任务 {} 未运行", task_id)
                ))
            }
        } else {
            Err(EmbeddedOSError::SchedulerError(
                format!("任务 {} 不存在", task_id)
            ))
        }
    }

    /// 获取任务列表
    pub async fn get_tasks(&self) -> Result<Vec<TaskInfo>, EmbeddedOSError> {
        let tasks = self.tasks.read().await;
        let task_infos: Vec<TaskInfo> = tasks.values().map(|task| TaskInfo {
            id: task.id,
            name: task.name.clone(),
            priority: task.priority,
            status: task.status,
            stack_size: 512, // RTIC默认栈大小
            stack_used: 0,
            cpu_time: std::time::Duration::ZERO,
        }).collect();

        Ok(task_infos)
    }

    /// 获取系统状态
    pub async fn get_system_status(&self) -> Result<SystemStatus, EmbeddedOSError> {
        if !self.initialized {
            return Err(EmbeddedOSError::InitializationFailed("RTIC未初始化".to_string()));
        }

        let tasks = self.tasks.read().await;
        let running_tasks = tasks.values().filter(|t| t.status == TaskStatus::Running).count();

        Ok(SystemStatus {
            cpu_usage: (running_tasks as f32 / 2.0) * 100.0, // RTIC通常运行少量高优先级任务
            memory_usage: 8.0, // 8%内存使用率
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
        let max_id = tasks.keys().max().unwrap_or(&0);
        max_id + 1
    }
}

/// RTIC资源守卫
pub struct RTICResourceGuard<'a, T> {
    resource: &'a mut RTICResource<T>,
    task_id: u32,
}

impl<'a, T> Drop for RTICResourceGuard<'a, T> {
    fn drop(&mut self) {
        self.resource.locked = false;
        self.resource.lock_holder = None;
    }
}

impl<'a, T> std::ops::Deref for RTICResourceGuard<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.resource.value
    }
}

impl<'a, T> std::ops::DerefMut for RTICResourceGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.resource.value
    }
}

impl Default for RTICManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_rtic_initialization() {
        let mut manager = RTICManager::new();
        assert!(!manager.initialized);
        
        let result = manager.initialize().await;
        assert!(result.is_ok());
        assert!(manager.initialized);
    }

    #[tokio::test]
    async fn test_rtic_task_creation() {
        let mut manager = RTICManager::new();
        manager.initialize().await.unwrap();

        let task_id = manager.create_task(
            "test_task".to_string(),
            TaskPriority::High,
            InterruptPriority::Level1,
            || {
                println!("RTIC task executed!");
            }
        ).await.unwrap();

        assert_eq!(task_id, 1);

        let tasks = manager.get_tasks().await.unwrap();
        assert_eq!(tasks.len(), 1);
        assert_eq!(tasks[0].name, "test_task");
    }

    #[tokio::test]
    async fn test_rtic_resource_management() {
        let mut manager = RTICManager::new();
        manager.initialize().await.unwrap();

        // 创建资源
        manager.create_resource("shared_data".to_string(), 42i32).await.unwrap();

        // 锁定资源
        let guard = manager.lock_resource::<i32>("shared_data", 1).await.unwrap();
        assert_eq!(*guard, 42);

        // 释放资源（通过drop）
        drop(guard);

        // 再次锁定应该成功
        let guard = manager.lock_resource::<i32>("shared_data", 2).await.unwrap();
        assert_eq!(*guard, 42);
    }

    #[tokio::test]
    async fn test_rtic_interrupt_handling() {
        let mut manager = RTICManager::new();
        manager.initialize().await.unwrap();

        let mut interrupt_triggered = false;

        // 注册中断处理器
        manager.register_interrupt_handler(1, move || {
            interrupt_triggered = true;
        }).await.unwrap();

        // 触发中断
        manager.trigger_interrupt(1).await.unwrap();
        assert!(interrupt_triggered);
    }

    #[tokio::test]
    async fn test_rtic_task_execution() {
        let mut manager = RTICManager::new();
        manager.initialize().await.unwrap();

        let mut execution_count = 0;

        let task_id = manager.create_task(
            "counter_task".to_string(),
            TaskPriority::Normal,
            InterruptPriority::Level2,
            move || {
                execution_count += 1;
            }
        ).await.unwrap();

        // 启动任务
        manager.start_task(task_id).await.unwrap();

        // 执行任务
        manager.execute_task(task_id).await.unwrap();
        assert_eq!(execution_count, 1);

        // 再次执行
        manager.execute_task(task_id).await.unwrap();
        assert_eq!(execution_count, 2);
    }
}
