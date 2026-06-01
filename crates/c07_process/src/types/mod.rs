use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::{Duration, SystemTime};

/// 进程状态枚举
/// process state enum
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProcessStatus {
    /// 正在运行
    /// in Run
    Running,
    /// 睡眠中
    /// in
    Sleeping,
    /// 已停止
    Stopped,
    /// 僵尸进程
    /// process
    Zombie,
    /// 未知状态
    /// state
    Unknown,
}

/// 进程信息结构
/// process structure
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProcessInfo {
    /// 进程ID
    /// process ID
    pub pid: u32,
    /// 进程名称
    /// process
    pub name: String,
    /// 进程状态
    /// process state
    pub status: ProcessStatus,
    /// 内存使用量（字节）
    /// memory （）
    pub memory_usage: u64,
    /// CPU使用率（百分比）
    /// CPU（）
    pub cpu_usage: f64,
    /// 创建时间
    /// time
    pub created_at: SystemTime,
    /// 父进程ID
    /// process ID
    pub parent_pid: Option<u32>,
    /// 子进程ID列表
    /// process ID
    pub children_pids: Vec<u32>,
}

/// IPC协议类型
/// IP Ctype
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum IpcProtocol {
    /// 管道通信
    /// pipe
    Pipe,
    /// 套接字通信
    /// socket
    Socket,
    /// 共享内存
    /// shared memory
    SharedMemory,
    /// 消息队列
    MessageQueue,
    /// 文件系统
    /// file system
    FileSystem,
}

/// IPC配置结构
/// IP Cstructure
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct IpcConfig {
    /// 通信协议
    pub protocol: IpcProtocol,
    /// 超时时间
    /// time
    pub timeout: Duration,
    /// 重试次数
    pub retry_count: u32,
    /// 缓冲区大小
    /// buffering
    pub buffer_size: usize,
    /// 是否启用加密
    pub encrypted: bool,
}

/// 同步原语类型
/// synchronous type
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SyncPrimitive {
    /// 互斥锁
    /// mutex
    Mutex,
    /// 读写锁
    /// rwlock
    RwLock,
    /// 条件变量
    /// condition variable
    CondVar,
    /// 信号量
    /// semaphore
    Semaphore,
    /// 屏障
    /// barrier
    Barrier,
    /// 原子操作
    /// atomic operation
    Atomic,
}

/// 同步配置结构
/// synchronous structure
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SyncConfig {
    /// 同步原语类型
    /// synchronous type
    pub primitive: SyncPrimitive,
    /// 超时时间
    /// time
    pub timeout: Duration,
    /// 是否公平
    pub fair: bool,
    /// 最大等待者数量
    /// maximum etc. quantity
    pub max_waiters: Option<usize>,
}

/// 进程配置结构
/// process structure
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProcessConfig {
    /// 程序路径
    /// program
    pub program: String,
    /// 命令行参数
    /// command parameter
    pub args: Vec<String>,
    /// 环境变量
    /// environment variable
    pub env: HashMap<String, String>,
    /// 工作目录
    pub working_dir: Option<String>,
    /// 用户ID
    /// ID
    pub user_id: Option<u32>,
    /// 组ID
    /// ID
    pub group_id: Option<u32>,
    /// 优先级
    pub priority: Option<i32>,
    /// 资源限制
    pub resource_limits: ResourceLimits,
}

/// 资源限制结构
/// structure
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct ResourceLimits {
    /// 最大内存使用量（字节）
    /// maximum memory （）
    pub max_memory: Option<u64>,
    /// 最大文件描述符数量
    /// maximum file descriptor quantity
    pub max_file_descriptors: Option<u64>,
    /// 最大CPU时间（秒）
    /// maximum CPUtime （）
    pub max_cpu_time: Option<u64>,
    /// 最大文件大小（字节）
    /// maximum （）
    pub max_file_size: Option<u64>,
}

impl Default for IpcConfig {
    fn default() -> Self {
        Self {
            protocol: IpcProtocol::Pipe,
            timeout: Duration::from_secs(30),
            retry_count: 3,
            buffer_size: 8192,
            encrypted: false,
        }
    }
}

impl Default for SyncConfig {
    fn default() -> Self {
        Self {
            primitive: SyncPrimitive::Mutex,
            timeout: Duration::from_secs(10),
            fair: true,
            max_waiters: None,
        }
    }
}

/// 消息结构
/// structure
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Message<T> {
    /// 消息ID
    /// ID
    pub id: u64,
    /// 消息类型
    /// type
    pub message_type: String,
    /// 消息数据
    pub data: T,
    /// 时间戳
    /// time
    pub timestamp: SystemTime,
    /// 源进程ID
    /// process ID
    pub source_pid: u32,
    /// 目标进程ID
    /// goal process ID
    pub target_pid: Option<u32>,
    /// 消息优先级
    pub priority: u8,
}

impl<T> Message<T> {
    /// 创建新消息
    pub fn new(id: u64, message_type: impl Into<String>, data: T, source_pid: u32) -> Self {
        Self {
            id,
            message_type: message_type.into(),
            data,
            timestamp: SystemTime::now(),
            source_pid,
            target_pid: None,
            priority: 0,
        }
    }

    /// 设置目标进程
    /// goal process
    pub fn with_target(mut self, target_pid: u32) -> Self {
        self.target_pid = Some(target_pid);
        self
    }

    /// 设置优先级
    pub fn with_priority(mut self, priority: u8) -> Self {
        self.priority = priority;
        self
    }
}

/// 进程组信息
/// process
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProcessGroup {
    /// 进程组ID
    /// process ID
    pub pgid: u32,
    /// 组长进程ID
    /// process ID
    pub leader_pid: u32,
    /// 成员进程ID列表
    /// process ID
    pub member_pids: Vec<u32>,
    /// 进程组名称
    /// process
    pub name: String,
    /// 创建时间
    /// time
    pub created_at: SystemTime,
}

/// 系统资源使用情况
/// system situation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SystemResources {
    /// 总内存（字节）
    /// memory （）
    pub total_memory: u64,
    /// 可用内存（字节）
    /// memory （）
    pub available_memory: u64,
    /// 总CPU核心数
    /// CPUcore
    pub cpu_cores: u32,
    /// 当前CPU使用率
    /// when before CPU
    pub cpu_usage: f64,
    /// 总磁盘空间（字节）
    /// space （）
    pub total_disk: u64,
    /// 可用磁盘空间（字节）
    /// space （）
    pub available_disk: u64,
    /// 当前时间
    /// when before time
    pub timestamp: SystemTime,
}

impl SystemResources {
    /// 获取内存使用率
    /// memory
    pub fn memory_usage_percent(&self) -> f64 {
        if self.total_memory == 0 {
            return 0.0;
        }
        let used = self.total_memory - self.available_memory;
        (used as f64 / self.total_memory as f64) * 100.0
    }

    /// 获取磁盘使用率
    pub fn disk_usage_percent(&self) -> f64 {
        if self.total_disk == 0 {
            return 0.0;
        }
        let used = self.total_disk - self.available_disk;
        (used as f64 / self.total_disk as f64) * 100.0
    }
}
