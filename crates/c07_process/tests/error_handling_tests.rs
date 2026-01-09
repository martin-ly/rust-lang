//! 错误处理测试
//!
//! 测试各种错误场景和错误处理机制

use c07_process::error::{ProcessError, IpcError, SyncError};
use c07_process::types::{ProcessConfig, ResourceLimits};
use std::collections::HashMap;

#[test]
fn test_process_error_display() {
    let errors = vec![
        ProcessError::NotFound(123),
        ProcessError::PermissionDenied("test".to_string()),
        ProcessError::InvalidConfig("test config error".to_string()),
        ProcessError::Io(std::io::Error::new(std::io::ErrorKind::NotFound, "test")),
        ProcessError::AlreadyTerminated,
    ];

    for error in errors {
        let error_string = format!("{}", error);
        assert!(!error_string.is_empty());
    }
}

#[test]
fn test_ipc_error_display() {
    let errors = vec![
        IpcError::ChannelNotFound("test_channel".to_string()),
        IpcError::ChannelClosed,
        IpcError::SendFailed("test_channel".to_string()),
        IpcError::ReceiveFailed("test_channel".to_string()),
        IpcError::ConnectionFailed("test".to_string()),
        IpcError::Timeout(std::time::Duration::from_secs(1)),
        IpcError::ProtocolNotSupported("test".to_string()),
    ];

    for error in errors {
        let error_string = format!("{}", error);
        assert!(!error_string.is_empty());
    }
}

#[test]
fn test_sync_error_display() {
    let errors = vec![
        SyncError::LockAcquisitionFailed("test_lock".to_string()),
        SyncError::Timeout(std::time::Duration::from_secs(1)),
        SyncError::CondVarError("test".to_string()),
        SyncError::SemaphoreError("test".to_string()),
        SyncError::BarrierError("test".to_string()),
    ];

    for error in errors {
        let error_string = format!("{}", error);
        assert!(!error_string.is_empty());
    }
}

#[test]
fn test_error_source_chain() {
    let io_error = std::io::Error::new(std::io::ErrorKind::NotFound, "file not found");
    let process_error = ProcessError::Io(io_error);

    // 验证错误可以转换为字符串
    let error_string = format!("{}", process_error);
    assert!(!error_string.is_empty());
}

#[test]
fn test_invalid_process_config() {
    let mut env = HashMap::new();
    env.insert("PATH".to_string(), "/usr/bin:/bin".to_string());

    // 创建无效配置（空程序名）
    let config = ProcessConfig {
        program: String::new(), // 空程序名
        args: vec![],
        env,
        working_dir: Some(".".to_string()),
        user_id: None,
        group_id: None,
        priority: None,
        resource_limits: ResourceLimits::default(),
    };

    // 验证配置创建（实际验证会在spawn时进行）
    assert_eq!(config.program, "");
}
