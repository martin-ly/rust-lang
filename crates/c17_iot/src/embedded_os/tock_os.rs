//! TockOS集成模块
//! 
//! TockOS是一个内存安全的嵌入式操作系统，专为微控制器设计。
//! 本模块提供了与TockOS的集成接口。

use super::{EmbeddedOSError, SystemInfo, SystemStatus, TaskInfo, TaskPriority, TaskStatus};
use std::sync::Arc;
use tokio::sync::RwLock;

/// TockOS管理器
pub struct TockOSManager {
    initialized: bool,
    system_info: Option<SystemInfo>,
    tasks: Arc<RwLock<Vec<TaskInfo>>>,
}

impl TockOSManager {
    /// 创建新的TockOS管理器
    pub fn new() -> Self {
        Self {
            initialized: false,
            system_info: None,
            tasks: Arc::new(RwLock::new(Vec::new())),
        }
    }

    /// 初始化TockOS
    pub async fn initialize(&mut self) -> Result<(), EmbeddedOSError> {
        if self.initialized {
            return Ok(());
        }

        // 模拟TockOS初始化过程
        tokio::time::sleep(std::time::Duration::from_millis(100)).await;

        // 获取系统信息
        self.system_info = Some(SystemInfo {
            os_type: super::EmbeddedOSType::TockOS,
            version: "2.1.0".to_string(),
            memory_total: 256 * 1024, // 256KB
            memory_used: 64 * 1024,   // 64KB
            cpu_cores: 1,
            uptime: std::time::Duration::from_secs(0),
        });

        self.initialized = true;
        Ok(())
    }

    /// 创建新任务
    pub async fn create_task(
        &self,
        name: String,
        priority: TaskPriority,
        stack_size: usize,
    ) -> Result<u32, EmbeddedOSError> {
        if !self.initialized {
            return Err(EmbeddedOSError::InitializationFailed("TockOS未初始化".to_string()));
        }

        let task_id = self.generate_task_id().await;
        let task_info = TaskInfo {
            id: task_id,
            name,
            priority,
            status: TaskStatus::Ready,
            stack_size,
            stack_used: 0,
            cpu_time: std::time::Duration::ZERO,
        };

        let mut tasks = self.tasks.write().await;
        tasks.push(task_info);

        Ok(task_id)
    }

    /// 启动任务
    pub async fn start_task(&self, task_id: _task_id) -> Result<(), EmbeddedOSError> {
        let mut tasks = self.tasks.write().await;
        
        if let Some(task) = tasks.iter_mut().find(|t| t.id == task_id) {
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

    /// 挂起任务
    pub async fn suspend_task(&self, task_id: _task_id) -> Result<(), EmbeddedOSError> {
        let mut tasks = self.tasks.write().await;
        
        if let Some(task) = tasks.iter_mut().find(|t| t.id == task_id) {
            if task.status == TaskStatus::Running {
                task.status = TaskStatus::Suspended;
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

    /// 恢复任务
    pub async fn resume_task(&self, task_id: _task_id) -> Result<(), EmbeddedOSError> {
        let mut tasks = self.tasks.write().await;
        
        if let Some(task) = tasks.iter_mut().find(|t| t.id == task_id) {
            if task.status == TaskStatus::Suspended {
                task.status = TaskStatus::Ready;
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

    /// 终止任务
    pub async fn terminate_task(&self, task_id: _task_id) -> Result<(), EmbeddedOSError> {
        let mut tasks = self.tasks.write().await;
        
        if let Some(task) = tasks.iter_mut().find(|t| t.id == task_id) {
            task.status = TaskStatus::Terminated;
            Ok(())
        } else {
            Err(EmbeddedOSError::SchedulerError(
                format!("任务 {} 不存在", task_id)
            ))
        }
    }

    /// 获取任务列表
    pub async fn get_tasks(&self) -> Result<Vec<TaskInfo>, EmbeddedOSError> {
        let tasks = self.tasks.read().await;
        Ok(tasks.clone())
    }

    /// 获取系统状态
    pub async fn get_system_status(&self) -> Result<SystemStatus, EmbeddedOSError> {
        if !self.initialized {
            return Err(EmbeddedOSError::InitializationFailed("TockOS未初始化".to_string()));
        }

        let tasks = self.tasks.read().await;
        let running_tasks = tasks.iter().filter(|t| t.status == TaskStatus::Running).count();

        Ok(SystemStatus {
            cpu_usage: (running_tasks as f32 / 4.0) * 100.0, // 假设最多4个并发任务
            memory_usage: 25.0, // 25%内存使用率
            task_count: tasks.len() as u32,
            interrupt_count: 0, // 需要从系统获取
            context_switches: 0, // 需要从系统获取
        })
    }

    /// 获取系统信息
    pub fn get_system_info(&self) -> Result<&SystemInfo, EmbeddedOSError> {
        self.system_info.as_ref()
            .ok_or_else(|| EmbeddedOSError::InitializationFailed("系统信息未初始化".to_string()))
    }

    /// 内存分配
    pub async fn allocate_memory(&self, size: _size) -> Result<*mut u8, EmbeddedOSError> {
        if !self.initialized {
            return Err(EmbeddedOSError::InitializationFailed("TockOS未初始化".to_string()));
        }

        // 模拟内存分配
        let ptr = unsafe {
            std::alloc::alloc(std::alloc::Layout::from_size_align(size, 4).unwrap())
        };

        if ptr.is_null() {
            Err(EmbeddedOSError::MemoryAllocationFailed(
                format!("无法分配 {} 字节内存", size)
            ))
        } else {
            Ok(ptr)
        }
    }

    /// 内存释放
    pub async fn deallocate_memory(&self, ptr: *mut u8, size: _size) -> Result<(), EmbeddedOSError> {
        if !self.initialized {
            return Err(EmbeddedOSError::InitializationFailed("TockOS未初始化".to_string()));
        }

        if ptr.is_null() {
            return Err(EmbeddedOSError::MemoryAllocationFailed("空指针".to_string()));
        }

        unsafe {
            std::alloc::dealloc(ptr, std::alloc::Layout::from_size_align(size, 4).unwrap());
        }

        Ok(())
    }

    /// 生成任务ID
    async fn generate_task_id(&self) -> u32 {
        let tasks = self.tasks.read().await;
        let max_id = tasks.iter().map(|t| t.id).max().unwrap_or(0);
        max_id + 1
    }
}

impl Default for TockOSManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_tock_os_initialization() {
        let mut manager = TockOSManager::new();
        assert!(!manager.initialized);
        
        let result = manager.initialize().await;
        assert!(result.is_ok());
        assert!(manager.initialized);
    }

    #[tokio::test]
    async fn test_task_creation() {
        let mut manager = TockOSManager::new();
        manager.initialize().await.unwrap();

        let task_id = manager.create_task(
            "test_task".to_string(),
            TaskPriority::Normal,
            1024,
        ).await.unwrap();

        assert_eq!(task_id, 1);

        let tasks = manager.get_tasks().await.unwrap();
        assert_eq!(tasks.len(), 1);
        assert_eq!(tasks[0].name, "test_task");
    }

    #[tokio::test]
    async fn test_task_lifecycle() {
        let mut manager = TockOSManager::new();
        manager.initialize().await.unwrap();

        let task_id = manager.create_task(
            "lifecycle_test".to_string(),
            TaskPriority::High,
            2048,
        ).await.unwrap();

        // 启动任务
        manager.start_task(task_id).await.unwrap();
        let tasks = manager.get_tasks().await.unwrap();
        assert_eq!(tasks[0].status, TaskStatus::Running);

        // 挂起任务
        manager.suspend_task(task_id).await.unwrap();
        let tasks = manager.get_tasks().await.unwrap();
        assert_eq!(tasks[0].status, TaskStatus::Suspended);

        // 恢复任务
        manager.resume_task(task_id).await.unwrap();
        let tasks = manager.get_tasks().await.unwrap();
        assert_eq!(tasks[0].status, TaskStatus::Ready);

        // 终止任务
        manager.terminate_task(task_id).await.unwrap();
        let tasks = manager.get_tasks().await.unwrap();
        assert_eq!(tasks[0].status, TaskStatus::Terminated);
    }

    #[tokio::test]
    async fn test_memory_management() {
        let mut manager = TockOSManager::new();
        manager.initialize().await.unwrap();

        let size = 1024;
        let ptr = manager.allocate_memory(size).await.unwrap();
        assert!(!ptr.is_null());

        let result = manager.deallocate_memory(ptr, size).await;
        assert!(result.is_ok());
    }
}
