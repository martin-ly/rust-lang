use c07_process::prelude::*;
use std::collections::HashMap;

fn main() -> Result<()> {
    println!("Process Demo - 进程管理演示");

    // 创建进程管理器
    let mut pm = ProcessManager::new();

    // 创建进程配置 - 使用Windows兼容的命令
    let mut env = HashMap::new();
    env.insert("PATH".to_string(), "C:\\Windows\\System32".to_string());

    let config = ProcessConfig {
        program: "cmd".to_string(),
        args: vec!["/c".to_string(), "echo Hello, World!".to_string()],
        env,
        working_dir: Some(".".to_string()), // 使用当前目录
        user_id: None,
        group_id: None,
        priority: None,
        resource_limits: ResourceLimits::default(),
    };

    // 启动进程
    let pid = pm.spawn(config)?;
    println!("✅ 启动进程成功，PID: {}", pid);

    // 获取进程信息
    if let Ok(info) = pm.get_process_info(pid) {
        println!("📋 进程信息: {:?}", info);
    }

    // 等待进程完成
    if let Ok(output) = pm.get_output(pid) {
        println!("📤 进程输出: {:?}", output);
    }

    // 获取进程数量
    let process_count = pm.process_count();
    println!("📋 当前进程数量: {}", process_count);

    // 创建IPC管理器
    let mut ipc = IpcManager::new(IpcConfig::default());

    // 创建命名管道
    ipc.create_named_pipe("demo_pipe")?;
    println!("✅ 创建命名管道: demo_pipe");

    // 创建Unix套接字（在Windows上会使用TCP套接字）
    ipc.create_unix_socket("demo_socket")?;
    println!("✅ 创建套接字: demo_socket");

    // 创建TCP套接字
    ipc.create_tcp_socket("127.0.0.1", 8080)?;
    println!("✅ 创建TCP套接字: 127.0.0.1:8080");

    // 创建共享内存区域
    ipc.create_shared_memory("demo_memory", 1024)?;
    println!("✅ 创建共享内存: demo_memory (1024 bytes)");

    // 创建消息队列
    ipc.create_message_queue("demo_queue", 100)?;
    println!("✅ 创建消息队列: demo_queue (容量: 100)");

    // 创建文件系统通道
    ipc.create_file_system_channel("demo_file")?;
    println!("✅ 创建文件系统通道: demo_file");

    // 列出所有通道
    let channels = ipc.list_channels();
    println!("📋 当前通道列表: {:?}", channels);

    // 发送消息
    let message = Message::new(1, "demo", "Hello Process!".as_bytes().to_vec(), 1234);
    ipc.send_message("demo_pipe", &message)?;
    println!("📤 发送消息到 demo_pipe");

    // 接收消息
    if let Ok(received) = ipc.receive_message("demo_pipe") {
        println!("📥 从 demo_pipe 接收消息: {:?}", received);
    }

    // 获取通道统计信息
    if let Some(stats) = ipc.get_channel_stats("demo_pipe") {
        println!("📊 通道统计: {:?}", stats);
    }

    // 创建同步管理器
    let mut sync = SyncManager::new(SyncConfig::default());

    // 创建互斥锁
    let mutex = sync.create_mutex("demo_mutex")?;
    println!("✅ 创建互斥锁: demo_mutex");

    // 创建读写锁
    let rwlock = sync.create_rwlock("demo_rwlock")?;
    println!("✅ 创建读写锁: demo_rwlock");

    // 创建条件变量
    let _condvar = sync.create_condvar("demo_condvar")?;
    println!("✅ 创建条件变量: demo_condvar");

    // 创建信号量
    let semaphore = sync.create_semaphore("demo_semaphore", 3)?;
    println!("✅ 创建信号量: demo_semaphore (许可数: 3)");

    // 创建屏障
    let _barrier = sync.create_barrier("demo_barrier", 2)?;
    println!("✅ 创建屏障: demo_barrier (参与者数: 2)");

    // 列出所有同步原语
    let primitives = sync.get_primitive_names();
    println!("📋 当前同步原语列表: {:?}", primitives);

    // 测试互斥锁
    if let Ok(guard) = mutex.lock() {
        println!("🔒 获取互斥锁成功");
        drop(guard);
        println!("🔓 释放互斥锁");
    }

    // 测试读写锁
    if let Ok(read_guard) = rwlock.read() {
        println!("📖 获取读锁成功");
        drop(read_guard);
        println!("📖 释放读锁");
    }

    if let Ok(write_guard) = rwlock.write() {
        println!("✍️ 获取写锁成功");
        drop(write_guard);
        println!("✍️ 释放写锁");
    }

    // 测试信号量
    if let Some(permit) = semaphore.try_acquire() {
        println!("🎫 获取信号量许可成功");
        drop(permit);
        println!("🎫 释放信号量许可");
    }

    // 清理资源
    ipc.cleanup()?;
    println!("🔒 所有IPC通道已关闭");

    println!("🎉 进程管理演示完成!");
    Ok(())
}
