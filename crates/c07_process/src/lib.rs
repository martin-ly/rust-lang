//! # C07 Process Management Library
//!
//! 一个功能完整的 Rust 进程管理和 IPC 通信库。
//!
//! ## 快速开始
//!
//! ```rust
//! use c07_process::prelude::*;
//! use std::collections::HashMap;
//!
//! fn main() -> c07_process::Result<()> {
//!     // 创建进程管理器
//!     let pm = ProcessManager::new();
//!     
//!     // 创建进程配置
//!     let mut env = HashMap::new();
//!     env.insert("PATH".to_string(), "/usr/bin:/bin".to_string());
//!     
//!     let config = ProcessConfig {
//!         program: "echo".to_string(),
//!         args: vec!["Hello, World!".to_string()],
//!         env,
//!         working_dir: Some("/tmp".to_string()),
//!         user_id: None,
//!         group_id: None,
//!         priority: None,
//!         resource_limits: ResourceLimits::default(),
//!     };
//!     
//!     // 注意：在实际使用中，需要确保程序存在
//!     // 这里只是演示配置的创建
//!     println!("进程配置创建成功: {:?}", config);
//!     
//!     Ok(())
//! }
//! ```

use serde::{Deserialize, Serialize};

// 核心模块
pub mod error;
pub mod types;

// 进程管理模块
pub mod process;

// 进程间通信模块
pub mod inter_process_communication;

// 同步机制模块
pub mod concurrency;

// 管道模块
pub mod pipe;

// 共享内存模块
pub mod shared_memory;

// Fork模块
pub mod fork;

// 异步运行时模块
pub mod async_runtime;

// 重新导出关键类型
pub use types::{
    IpcConfig, IpcProtocol, Message, ProcessConfig, ProcessGroup, ProcessInfo, ProcessStatus,
    ResourceLimits, SyncConfig, SyncPrimitive, SystemResources,
};

pub use error::{IpcResult, ProcessResult, ResourceResult, Result, SyncResult};

pub use process::{
    ProcessBuilder, ProcessGroupManager, ProcessManager,
    pool::{AutoScalingConfig, LoadBalancingStrategy, ProcessPool, ProcessPoolConfig},
};

#[cfg(feature = "async")]
pub use async_runtime::{AsyncProcessManager, AsyncProcessPool, AsyncTask, AsyncTaskScheduler};

pub use inter_process_communication::{
    AsyncIpcManager, ChannelStats, IpcChannel, IpcConnector, IpcManager,
};

pub use concurrency::{PrimitiveStats, SyncManager, SyncPrimitiveTrait};

pub use pipe::NamedPipe;
pub use shared_memory::SharedMemoryRegion;

// 库版本和元数据
pub const VERSION: &str = env!("CARGO_PKG_VERSION");
pub const AUTHORS: &str = env!("CARGO_PKG_AUTHORS");
pub const DESCRIPTION: &str = env!("CARGO_PKG_DESCRIPTION");

/// 初始化库
pub fn init() -> Result<()> {
    // 初始化日志系统
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::INFO)
        .init();

    tracing::info!("C07 Process Management Library initialized");
    Ok(())
}

/// 库清理函数
///
/// 清理全局资源和状态
pub fn cleanup() -> Result<()> {
    tracing::info!("Cleaning up C07 Process Management Library");

    // 在这里可以添加清理逻辑
    // 比如关闭全局连接池、清理临时文件等

    Ok(())
}

/// 获取库信息
pub fn get_library_info() -> LibraryInfo {
    LibraryInfo {
        name: "c07_process".to_string(),
        version: VERSION.to_string(),
        authors: AUTHORS.to_string(),
        description: DESCRIPTION.to_string(),
        features: get_enabled_features(),
    }
}

/// 库信息结构
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LibraryInfo {
    pub name: String,
    pub version: String,
    pub authors: String,
    pub description: String,
    pub features: Vec<String>,
}

/// 获取启用的特性列表
fn get_enabled_features() -> Vec<String> {
    let features = vec!["std".to_string()];

    #[cfg(feature = "async")]
    features.push("async".to_string());

    #[cfg(feature = "unix")]
    features.push("unix".to_string());

    #[cfg(feature = "windows")]
    features.push("windows".to_string());

    features
}

// 预导入常用类型
pub mod prelude {
    pub use super::{
        AutoScalingConfig,

        IpcConfig,
        IpcManager,
        IpcProtocol,
        IpcResult,
        LoadBalancingStrategy,
        Message,
        ProcessBuilder,
        // 类型定义
        ProcessConfig,
        ProcessInfo,
        // 管理器
        ProcessManager,
        ProcessPool,
        ProcessPoolConfig,
        ProcessResult,
        ProcessStatus,
        ResourceLimits,
        ResourceResult,

        // 错误类型
        Result,
        SyncConfig,
        SyncManager,
        SyncPrimitive,

        SyncResult,
        concurrency::barrier::ProcessBarrier,
        concurrency::condvar::ProcessCondVar,
        // 同步原语 - 使用正确的路径
        concurrency::mutex::ProcessMutex,
        concurrency::rwlock::ProcessRwLock,
        concurrency::semaphore::ProcessSemaphore,
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_library_info() {
        let info = get_library_info();
        assert_eq!(info.name, "c07_process");
        assert!(!info.version.is_empty());
        assert!(!info.authors.is_empty());
        assert!(!info.description.is_empty());
        assert!(!info.features.is_empty());
    }

    #[test]
    fn test_enabled_features() {
        let features = get_enabled_features();
        assert!(features.contains(&"std".to_string()));
    }

    #[test]
    fn test_init_and_cleanup() {
        assert!(init().is_ok());
        assert!(cleanup().is_ok());
    }
}
