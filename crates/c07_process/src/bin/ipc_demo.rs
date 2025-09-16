use c07_process::prelude::*;

fn main() -> Result<()> {
    println!("IPC Demo - 进程间通信演示");

    // 创建IPC管理器
    let mut ipc = IpcManager::new(IpcConfig::default());

    // 创建命名管道
    ipc.create_named_pipe("demo_pipe")?;
    println!("✅ 创建命名管道: demo_pipe");

    // 创建Unix套接字
    ipc.create_unix_socket("/tmp/demo_socket")?;
    println!("✅ 创建Unix套接字: /tmp/demo_socket");

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
    let message = Message::new(1, "demo", "Hello IPC!".as_bytes().to_vec(), 1234);
    ipc.send_message("demo_pipe", &message)?;
    println!("📤 发送消息到 demo_pipe");

    // 接收消息
    if let Ok(received) = ipc.receive_message("demo_pipe") {
        println!("📥 从 demo_pipe 接收消息: {:?}", received);
    }

    // 关闭所有通道
    ipc.cleanup()?;
    println!("🔒 所有通道已关闭");

    println!("🎉 IPC演示完成!");
    Ok(())
}
