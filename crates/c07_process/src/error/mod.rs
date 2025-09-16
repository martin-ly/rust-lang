use std::io;
use std::process::ExitStatus;
use thiserror::Error;

/// 进程管理相关错误
#[derive(Error, Debug)]
pub enum ProcessError {
    /// 进程创建失败
    #[error("Failed to create process: {0}")]
    CreationFailed(String),

    /// 进程启动失败
    #[error("Failed to start process: {0}")]
    StartFailed(String),

    /// 进程等待失败
    #[error("Failed to wait for process: {0}")]
    WaitFailed(String),

    /// 进程终止失败
    #[error("Failed to terminate process: {0}")]
    TerminationFailed(String),

    /// 进程不存在
    #[error("Process not found: {0}")]
    NotFound(u32),

    /// 权限不足
    #[error("Insufficient permissions: {0}")]
    PermissionDenied(String),

    /// 资源不足
    #[error("Insufficient resources: {0}")]
    ResourceExhausted(String),

    /// 无效的进程配置
    #[error("Invalid process configuration: {0}")]
    InvalidConfig(String),

    /// 进程已终止
    #[error("Process already terminated")]
    AlreadyTerminated,

    /// 子进程错误
    #[error("Child process error: {0}")]
    ChildError(#[from] ChildProcessError),

    /// IO错误
    #[error("IO error: {0}")]
    Io(#[from] io::Error),
}

/// 子进程相关错误
#[derive(Error, Debug)]
pub enum ChildProcessError {
    /// 子进程异常退出
    #[error("Child process exited abnormally: {0:?}")]
    AbnormalExit(ExitStatus),

    /// 子进程超时
    #[error("Child process timeout after {0:?}")]
    Timeout(std::time::Duration),

    /// 子进程信号中断
    #[error("Child process interrupted by signal: {0}")]
    SignalInterrupted(i32),

    /// 子进程资源限制
    #[error("Child process resource limit exceeded: {0}")]
    ResourceLimitExceeded(String),
}

/// IPC相关错误
#[derive(Error, Debug)]
pub enum IpcError {
    /// 连接失败
    #[error("Failed to establish IPC connection: {0}")]
    ConnectionFailed(String),

    /// 通信超时
    #[error("IPC communication timeout: {0:?}")]
    Timeout(std::time::Duration),

    /// 消息发送失败
    #[error("Failed to send message: {0}")]
    SendFailed(String),

    /// 消息接收失败
    #[error("Failed to receive message: {0}")]
    ReceiveFailed(String),

    /// 协议不支持
    #[error("Protocol not supported: {0}")]
    ProtocolNotSupported(String),

    /// 通道已关闭
    #[error("IPC channel is closed")]
    ChannelClosed,

    /// 通道未找到
    #[error("IPC channel not found: {0}")]
    ChannelNotFound(String),

    /// 序列化错误
    #[error("Serialization error: {0}")]
    SerializationError(String),

    /// 反序列化错误
    #[error("Deserialization error: {0}")]
    DeserializationError(String),

    /// 共享内存错误
    #[error("Shared memory error: {0}")]
    SharedMemoryError(String),

    /// 信号处理错误
    #[error("Signal handling error: {0}")]
    SignalError(String),
}

/// 同步相关错误
#[derive(Error, Debug)]
pub enum SyncError {
    /// 锁获取失败
    #[error("Failed to acquire lock: {0}")]
    LockAcquisitionFailed(String),

    /// 锁释放失败
    #[error("Failed to release lock: {0}")]
    LockReleaseFailed(String),

    /// 死锁检测
    #[error("Deadlock detected: {0}")]
    DeadlockDetected(String),

    /// 超时错误
    #[error("Synchronization timeout: {0:?}")]
    Timeout(std::time::Duration),

    /// 条件变量错误
    #[error("Condition variable error: {0}")]
    CondVarError(String),

    /// 信号量错误
    #[error("Semaphore error: {0}")]
    SemaphoreError(String),

    /// 屏障错误
    #[error("Barrier error: {0}")]
    BarrierError(String),

    /// 原子操作错误
    #[error("Atomic operation error: {0}")]
    AtomicError(String),
}

/// 系统资源错误
#[derive(Error, Debug)]
pub enum ResourceError {
    /// 内存不足
    #[error("Insufficient memory: requested {0}, available {1}")]
    InsufficientMemory(u64, u64),

    /// 文件描述符不足
    #[error("Insufficient file descriptors: requested {0}, available {1}")]
    InsufficientFileDescriptors(u64, u64),

    /// CPU时间不足
    #[error("Insufficient CPU time: requested {0}, available {1}")]
    InsufficientCpuTime(u64, u64),

    /// 磁盘空间不足
    #[error("Insufficient disk space: requested {0}, available {1}")]
    InsufficientDiskSpace(u64, u64),

    /// 资源限制设置失败
    #[error("Failed to set resource limits: {0}")]
    LimitSettingFailed(String),
}

/// 平台特定错误
#[derive(Error, Debug)]
pub enum PlatformError {
    /// Unix系统错误
    #[error("Unix system error: {0}")]
    Unix(String),

    /// Windows系统错误
    #[error("Windows system error: {0}")]
    Windows(String),

    /// 跨平台不支持
    #[error("Cross-platform not supported: {0}")]
    NotSupported(String),

    /// 平台特定功能缺失
    #[error("Platform-specific feature missing: {0}")]
    FeatureMissing(String),
}

/// 配置错误
#[derive(Error, Debug)]
pub enum ConfigError {
    /// 配置文件不存在
    #[error("Configuration file not found: {0}")]
    FileNotFound(String),

    /// 配置文件格式错误
    #[error("Configuration file format error: {0}")]
    FormatError(String),

    /// 配置项缺失
    #[error("Missing configuration item: {0}")]
    MissingItem(String),

    /// 配置项无效
    #[error("Invalid configuration item: {0}")]
    InvalidItem(String),

    /// 配置验证失败
    #[error("Configuration validation failed: {0}")]
    ValidationFailed(String),
}

/// 通用错误类型
#[derive(Error, Debug)]
pub enum C07ProcessError {
    /// 进程错误
    #[error("Process error: {0}")]
    Process(#[from] ProcessError),

    /// IPC错误
    #[error("IPC error: {0}")]
    Ipc(#[from] IpcError),

    /// 同步错误
    #[error("Synchronization error: {0}")]
    Sync(#[from] SyncError),

    /// 资源错误
    #[error("Resource error: {0}")]
    Resource(#[from] ResourceError),

    /// 平台错误
    #[error("Platform error: {0}")]
    Platform(#[from] PlatformError),

    /// 配置错误
    #[error("Configuration error: {0}")]
    Config(#[from] ConfigError),

    /// IO错误
    #[error("IO error: {0}")]
    Io(#[from] io::Error),

    /// 其他错误
    #[error("Other error: {0}")]
    Other(String),
}

impl From<String> for C07ProcessError {
    fn from(err: String) -> Self {
        C07ProcessError::Other(err)
    }
}

impl From<&str> for C07ProcessError {
    fn from(err: &str) -> Self {
        C07ProcessError::Other(err.to_string())
    }
}

impl From<serde_json::Error> for C07ProcessError {
    fn from(err: serde_json::Error) -> Self {
        C07ProcessError::Other(format!("Serialization error: {}", err))
    }
}

impl From<std::time::SystemTimeError> for C07ProcessError {
    fn from(err: std::time::SystemTimeError) -> Self {
        C07ProcessError::Other(format!("Time error: {}", err))
    }
}

/// 错误结果类型别名
pub type Result<T> = std::result::Result<T, C07ProcessError>;

/// 进程结果类型别名
pub type ProcessResult<T> = std::result::Result<T, ProcessError>;

/// IPC结果类型别名
pub type IpcResult<T> = std::result::Result<T, IpcError>;

/// 同步结果类型别名
pub type SyncResult<T> = std::result::Result<T, SyncError>;

/// 资源结果类型别名
pub type ResourceResult<T> = std::result::Result<T, ResourceError>;
