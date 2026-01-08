use c07_process::prelude::*;
use std::collections::HashMap;

#[test]
fn test_basic_functionality() {
    // 测试进程管理器创建
    let pm = ProcessManager::new();
    assert_eq!(pm.process_count(), 0);

    // 测试IPC管理器创建
    let ipc = IpcManager::new(IpcConfig::default());
    let channels = ipc.list_channels();
    assert_eq!(channels.len(), 0);

    // 测试同步管理器创建
    let sync = SyncManager::new(SyncConfig::default());
    let primitives = sync.get_primitive_names();
    assert_eq!(primitives.len(), 0);
}

#[test]
fn test_message_creation() {
    let message = Message::new(1, "test", "Hello".as_bytes().to_vec(), 1234);
    assert_eq!(message.id, 1);
    assert_eq!(message.message_type, "test");
    assert_eq!(message.source_pid, 1234);
    assert_eq!(message.priority, 0);
}

#[test]
fn test_process_config_creation() {
    let mut env = HashMap::new();
    env.insert("PATH".to_string(), "/usr/bin".to_string());

    let config = ProcessConfig {
        program: "echo".to_string(),
        args: vec!["hello".to_string()],
        env,
        working_dir: Some("/tmp".to_string()),
        user_id: None,
        group_id: None,
        priority: None,
        resource_limits: ResourceLimits::default(),
    };

    assert_eq!(config.program, "echo");
    assert_eq!(config.args.len(), 1);
    assert_eq!(config.working_dir, Some("/tmp".to_string()));
}

#[test]
fn test_config_defaults() {
    let ipc_config = IpcConfig::default();
    assert_eq!(ipc_config.protocol, IpcProtocol::Pipe);
    assert_eq!(ipc_config.retry_count, 3);
    assert_eq!(ipc_config.buffer_size, 8192);
    assert_eq!(ipc_config.encrypted, false);

    let sync_config = SyncConfig::default();
    assert_eq!(sync_config.primitive, SyncPrimitive::Mutex);
    assert_eq!(sync_config.fair, true);
    assert_eq!(sync_config.max_waiters, None);
}

#[cfg(feature = "async")]
mod async_tests {
    use super::*;
    use c07_process::AsyncProcessManager;
    use std::collections::HashMap;

    #[tokio::test]
    async fn test_async_process_manager_creation() {
        let manager = AsyncProcessManager::new().await;
        let processes = manager.list_all().await;
        assert_eq!(processes.len(), 0);
    }

    #[tokio::test]
    async fn test_async_process_spawn_and_kill() {
        let manager = AsyncProcessManager::new().await;
        let mut env = HashMap::new();
        if cfg!(windows) {
            env.insert("PATH".to_string(), "C:\\Windows\\System32".to_string());
        } else {
            env.insert("PATH".to_string(), "/usr/bin:/bin".to_string());
        }

        let config = if cfg!(windows) {
            ProcessConfig {
                program: "cmd".to_string(),
                args: vec!["/c".to_string(), "echo test".to_string()],
                env,
                working_dir: Some(".".to_string()),
                user_id: None,
                group_id: None,
                priority: None,
                resource_limits: ResourceLimits::default(),
            }
        } else {
            ProcessConfig {
                program: "echo".to_string(),
                args: vec!["test".to_string()],
                env,
                working_dir: Some(".".to_string()),
                user_id: None,
                group_id: None,
                priority: None,
                resource_limits: ResourceLimits::default(),
            }
        };

        let pid = manager.spawn(config).await.unwrap();
        assert!(pid > 0);

        // 获取进程信息
        let info = manager.get_info(pid).await.unwrap();
        assert_eq!(info.pid, pid);

        // 列出所有进程
        let processes = manager.list_all().await;
        assert!(processes.iter().any(|p| p.pid == pid));

        // 终止进程
        let result = manager.kill(pid).await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_async_process_not_found() {
        let manager = AsyncProcessManager::new().await;
        let invalid_pid = 99999;

        assert!(manager.get_info(invalid_pid).await.is_err());
        assert!(manager.kill(invalid_pid).await.is_err());
    }

    #[tokio::test]
    async fn test_async_process_list_all() {
        let manager = AsyncProcessManager::new().await;
        let processes = manager.list_all().await;
        assert_eq!(processes.len(), 0);

        let mut env = HashMap::new();
        if cfg!(windows) {
            env.insert("PATH".to_string(), "C:\\Windows\\System32".to_string());
        } else {
            env.insert("PATH".to_string(), "/usr/bin:/bin".to_string());
        }

        let config = if cfg!(windows) {
            ProcessConfig {
                program: "cmd".to_string(),
                args: vec!["/c".to_string(), "echo test".to_string()],
                env,
                working_dir: Some(".".to_string()),
                user_id: None,
                group_id: None,
                priority: None,
                resource_limits: ResourceLimits::default(),
            }
        } else {
            ProcessConfig {
                program: "echo".to_string(),
                args: vec!["test".to_string()],
                env,
                working_dir: Some(".".to_string()),
                user_id: None,
                group_id: None,
                priority: None,
                resource_limits: ResourceLimits::default(),
            }
        };

        let pid1 = manager.spawn(config.clone()).await.unwrap();
        let pid2 = manager.spawn(config).await.unwrap();

        let processes = manager.list_all().await;
        assert!(processes.len() >= 2);
        assert!(processes.iter().any(|p| p.pid == pid1));
        assert!(processes.iter().any(|p| p.pid == pid2));

        // 清理
        let _ = manager.kill(pid1).await;
        let _ = manager.kill(pid2).await;
    }
}
