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
