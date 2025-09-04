use super::*;

#[test]
fn test_process_manager_creation() {
    let pm = ProcessManager::new();
    assert_eq!(pm.process_count(), 0);
}

#[test]
fn test_ipc_manager_creation() {
    let ipc = IpcManager::new(IpcConfig::default());
    let channels = ipc.list_channels();
    assert_eq!(channels.len(), 0);
}

#[test]
fn test_sync_manager_creation() {
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
fn test_ipc_config_default() {
    let config = IpcConfig::default();
    assert_eq!(config.protocol, IpcProtocol::Pipe);
    assert_eq!(config.timeout, Duration::from_secs(30));
    assert_eq!(config.retry_count, 3);
    assert_eq!(config.buffer_size, 8192);
    assert_eq!(config.encrypted, false);
}

#[test]
fn test_sync_config_default() {
    let config = SyncConfig::default();
    assert_eq!(config.primitive, SyncPrimitive::Mutex);
    assert_eq!(config.timeout, Duration::from_secs(10));
    assert_eq!(config.fair, true);
    assert_eq!(config.max_waiters, None);
}
