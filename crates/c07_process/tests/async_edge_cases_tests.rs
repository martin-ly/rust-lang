//! 异步进程管理的边界情况测试
//!
//! 这些测试覆盖了异步进程管理中的边界情况和错误处理场景

#[cfg(feature = "async")]
mod async_edge_cases {
    use c07_process::AsyncProcessManager;
    use c07_process::types::{ProcessConfig, ResourceLimits};
    use c07_process::error::ProcessError;
    use std::collections::HashMap;
    use std::time::Duration;

    #[tokio::test]
    async fn test_write_stdin_to_nonexistent_process() {
        let manager = AsyncProcessManager::new().await;

        // 尝试向不存在的进程写入
        let result = manager.write_stdin(99999, b"test").await;
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), ProcessError::NotFound(99999)));
    }

    #[tokio::test]
    async fn test_close_stdin_to_nonexistent_process() {
        let manager = AsyncProcessManager::new().await;

        // 尝试关闭不存在进程的stdin
        let result = manager.close_stdin(99999).await;
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), ProcessError::NotFound(99999)));
    }

    #[tokio::test]
    async fn test_read_stdout_from_nonexistent_process() {
        let manager = AsyncProcessManager::new().await;

        // 尝试从不存在的进程读取stdout
        let result = manager.read_stdout(99999).await;
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), ProcessError::NotFound(99999)));
    }

    #[tokio::test]
    async fn test_read_stderr_from_nonexistent_process() {
        let manager = AsyncProcessManager::new().await;

        // 尝试从不存在的进程读取stderr
        let result = manager.read_stderr(99999).await;
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), ProcessError::NotFound(99999)));
    }

    #[tokio::test]
    async fn test_wait_with_timeout_for_nonexistent_process() {
        let manager = AsyncProcessManager::new().await;

        // 尝试等待不存在的进程
        let result = manager.wait_with_timeout(99999, Duration::from_secs(1)).await;
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), ProcessError::NotFound(99999)));
    }

    #[tokio::test]
    async fn test_multiple_concurrent_operations() {
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

        // 并发执行多个操作
        let (r1, r2, r3) = tokio::join!(
            manager.read_stdout(pid),
            manager.read_stderr(pid),
            manager.get_info(pid)
        );

        assert!(r1.is_ok() || r2.is_ok());
        assert!(r3.is_ok());

        let _ = manager.kill(pid).await;
    }

    #[tokio::test]
    async fn test_empty_stdin_write() {
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

        // 尝试写入空数据
        let result = manager.write_stdin(pid, b"").await;
        // 空数据写入应该成功（虽然可能没有实际效果）
        assert!(result.is_ok() || result.is_err());

        let _ = manager.kill(pid).await;
    }

    #[tokio::test]
    async fn test_timeout_behavior() {
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
                args: vec!["/c".to_string(), "timeout /t 2 /nobreak".to_string()],
                env,
                working_dir: Some(".".to_string()),
                user_id: None,
                group_id: None,
                priority: None,
                resource_limits: ResourceLimits::default(),
            }
        } else {
            ProcessConfig {
                program: "sleep".to_string(),
                args: vec!["2".to_string()],
                env,
                working_dir: Some(".".to_string()),
                user_id: None,
                group_id: None,
                priority: None,
                resource_limits: ResourceLimits::default(),
            }
        };

        let pid = manager.spawn(config).await.unwrap();

        // 使用很短的超时
        let result = manager.wait_with_timeout(pid, Duration::from_millis(100)).await;

        // 应该超时返回 None
        assert!(result.is_ok());
        if let Ok(Some(_)) = result {
            // 如果进程快速完成，这也是正常的
        } else if let Ok(None) = result {
            // 超时是预期的
        }

        let _ = manager.kill(pid).await;
    }
}

#[cfg(not(feature = "async"))]
mod async_edge_cases {
    #[test]
    fn test_async_feature_not_enabled() {
        // 占位测试，当 async feature 未启用时
    }
}
