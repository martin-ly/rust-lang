//! 嵌入式操作系统模块
//! 
//! 本模块提供了基于Rust 1.90的嵌入式操作系统支持，包括：
//! - TockOS集成
//! - RIOT操作系统支持
//! - Hubris微内核
//! - OpenHarmony集成
//! - RTIC实时中断驱动并发
//! - Embassy异步框架

// pub mod tock_os;
// pub mod riot_os;
// pub mod hubris;
// pub mod openharmony;
// pub mod rtic;
// pub mod embassy;
// pub mod scheduler;
// pub mod memory_management;
// pub mod device_drivers;

// pub use tock_os::TockOSManager;
// pub use riot_os::RiotOSManager;
// pub use hubris::HubrisManager;
// pub use openharmony::OpenHarmonyManager;
// pub use rtic::RTICManager;
// pub use embassy::EmbassyManager;
// pub use scheduler::EmbeddedScheduler;
// pub use memory_management::MemoryManager;
// pub use device_drivers::DeviceDriverManager;

/// 嵌入式操作系统类型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EmbeddedOSType {
    /// TockOS - 内存安全的嵌入式操作系统
    TockOS,
    /// RIOT - 实时多线程操作系统
    RiotOS,
    /// Hubris - 微内核操作系统
    Hubris,
    /// OpenHarmony - 开源鸿蒙系统
    OpenHarmony,
    /// RTIC - 实时中断驱动并发
    RTIC,
    /// Embassy - 异步嵌入式框架
    Embassy,
}

/// 嵌入式操作系统管理器
pub struct EmbeddedOSManager {
    os_type: EmbeddedOSType,
    initialized: bool,
}

impl EmbeddedOSManager {
    /// 创建新的嵌入式操作系统管理器
    pub fn new(os_type: EmbeddedOSType) -> Self {
        Self {
            os_type,
            initialized: false,
        }
    }

    /// 初始化嵌入式操作系统
    pub async fn initialize(&mut self) -> Result<(), EmbeddedOSError> {
        // 暂时注释掉具体的操作系统初始化代码
        // match self.os_type {
        //     EmbeddedOSType::TockOS => {
        //         let mut tock_manager = TockOSManager::new();
        //         tock_manager.initialize().await?;
        //     }
        //     EmbeddedOSType::RiotOS => {
        //         let mut riot_manager = RiotOSManager::new();
        //         riot_manager.initialize().await?;
        //     }
        //     EmbeddedOSType::Hubris => {
        //         let mut hubris_manager = HubrisManager::new();
        //         hubris_manager.initialize().await?;
        //     }
        //     EmbeddedOSType::OpenHarmony => {
        //         let mut oh_manager = OpenHarmonyManager::new();
        //         oh_manager.initialize().await?;
        //     }
        //     EmbeddedOSType::RTIC => {
        //         let mut rtic_manager = RTICManager::new();
        //         rtic_manager.initialize().await?;
        //     }
        //     EmbeddedOSType::Embassy => {
        //         let mut embassy_manager = EmbassyManager::new();
        //         embassy_manager.initialize().await?;
        //     }
        // }
        
        self.initialized = true;
        Ok(())
    }

    /// 获取操作系统类型
    pub fn os_type(&self) -> EmbeddedOSType {
        self.os_type
    }

    /// 检查是否已初始化
    pub fn is_initialized(&self) -> bool {
        self.initialized
    }
}

/// 嵌入式操作系统错误类型
#[derive(Debug, thiserror::Error)]
pub enum EmbeddedOSError {
    #[error("操作系统初始化失败: {0}")]
    InitializationFailed(String),
    
    #[error("内存分配失败: {0}")]
    MemoryAllocationFailed(String),
    
    #[error("设备驱动错误: {0}")]
    DeviceDriverError(String),
    
    #[error("调度器错误: {0}")]
    SchedulerError(String),
    
    #[error("系统调用失败: {0}")]
    SystemCallFailed(String),
    
    #[error("权限不足: {0}")]
    PermissionDenied(String),
    
    #[error("资源不可用: {0}")]
    ResourceUnavailable(String),
    
    #[error("超时错误: {0}")]
    TimeoutError(String),
}

/// 系统信息
#[derive(Debug, Clone)]
pub struct SystemInfo {
    pub os_type: EmbeddedOSType,
    pub version: String,
    pub memory_total: usize,
    pub memory_used: usize,
    pub cpu_cores: u32,
    pub uptime: std::time::Duration,
}

/// 系统状态
#[derive(Debug, Clone)]
pub struct SystemStatus {
    pub cpu_usage: f32,
    pub memory_usage: f32,
    pub task_count: u32,
    pub interrupt_count: u64,
    pub context_switches: u64,
}

/// 任务优先级
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum TaskPriority {
    Low = 1,
    Normal = 5,
    High = 10,
    Critical = 15,
}

/// 任务状态
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TaskStatus {
    Ready,
    Running,
    Blocked,
    Suspended,
    Terminated,
}

/// 任务信息
#[derive(Debug, Clone)]
pub struct TaskInfo {
    pub id: u32,
    pub name: String,
    pub priority: TaskPriority,
    pub status: TaskStatus,
    pub stack_size: usize,
    pub stack_used: usize,
    pub cpu_time: std::time::Duration,
}
