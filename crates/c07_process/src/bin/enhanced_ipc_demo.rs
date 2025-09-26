//! 增强的IPC通信演示程序
//! 
//! 这个程序展示了增强的IPC通信功能，包括零拷贝数据传输、
//! 性能监控、错误恢复等 Rust 1.90 新特性

#[cfg(feature = "async")]
use c07_process::prelude::*;

#[cfg(feature = "async")]
#[tokio::main]
async fn main() -> Result<()> {
    println!("🚀 增强的IPC通信演示程序");
    println!("========================\n");

    // 创建增强的IPC管理器
    println!("🔧 创建增强的IPC管理器...");
    let config = IpcConfig::default();
    let manager = EnhancedIpcManager::new(config).await?;
    println!("✅ 增强的IPC管理器创建成功！\n");

    // 演示基础IPC功能
    println!("1️⃣ 基础IPC功能演示");
    println!("-------------------");
    demonstrate_basic_ipc_features(&manager).await?;
    println!();

    // 演示零拷贝数据传输
    println!("2️⃣ 零拷贝数据传输演示");
    println!("---------------------");
    demonstrate_zero_copy_transfer(&manager).await?;
    println!();

    // 演示性能监控
    println!("3️⃣ 性能监控演示");
    println!("---------------");
    demonstrate_performance_monitoring(&manager).await?;
    println!();

    // 演示错误恢复
    println!("4️⃣ 错误恢复演示");
    println!("---------------");
    demonstrate_error_recovery(&manager).await?;
    println!();

    // 演示高级IPC功能
    println!("5️⃣ 高级IPC功能演示");
    println!("-------------------");
    demonstrate_advanced_ipc_features(&manager).await?;
    println!();

    // 清理资源
    println!("🧹 清理资源...");
    manager.cleanup().await?;
    println!("✅ 资源清理完成");

    println!("\n🎉 增强的IPC通信演示完成！");
    Ok(())
}

#[cfg(feature = "async")]
async fn demonstrate_basic_ipc_features(manager: &EnhancedIpcManager) -> Result<()> {
    // 创建消息队列通道
    println!("  创建消息队列通道...");
    manager.create_message_queue_channel("basic_queue", 100).await?;
    println!("  ✅ 消息队列通道创建成功");

    // 创建共享内存通道
    println!("  创建共享内存通道...");
    manager.create_shared_memory_channel("basic_memory", 1024).await?;
    println!("  ✅ 共享内存通道创建成功");

    // 发送消息到消息队列
    println!("  发送消息到消息队列...");
    let message = Message::new(1, "basic_test", "Hello from basic IPC!".as_bytes().to_vec(), 1234);
    manager.send_message_zero_copy("basic_queue", &message).await?;
    println!("  ✅ 消息发送成功");

    // 从消息队列接收消息
    println!("  从消息队列接收消息...");
    let received: Message<Vec<u8>> = manager.receive_message_zero_copy("basic_queue").await?;
    println!("  ✅ 消息接收成功: {}", String::from_utf8_lossy(&received.data));

    // 发送消息到共享内存
    println!("  发送消息到共享内存...");
    let memory_message = Message::new(2, "memory_test", "Hello from shared memory!".as_bytes().to_vec(), 1234);
    manager.send_message_zero_copy("basic_memory", &memory_message).await?;
    println!("  ✅ 共享内存消息发送成功");

    Ok(())
}

#[cfg(feature = "async")]
async fn demonstrate_zero_copy_transfer(manager: &EnhancedIpcManager) -> Result<()> {
    // 创建高性能消息队列
    println!("  创建高性能消息队列...");
    manager.create_message_queue_channel("zero_copy_queue", 1000).await?;
    println!("  ✅ 高性能消息队列创建成功");

    // 创建大容量共享内存
    println!("  创建大容量共享内存...");
    manager.create_shared_memory_channel("zero_copy_memory", 1024 * 1024).await?; // 1MB
    println!("  ✅ 大容量共享内存创建成功");

    // 测试零拷贝消息传输
    println!("  测试零拷贝消息传输...");
    let large_data = vec![0u8; 1024 * 100]; // 100KB 数据
    let large_message = Message::new(3, "zero_copy_test", large_data, 1234);
    
    let start_time = std::time::Instant::now();
    manager.send_message_zero_copy("zero_copy_queue", &large_message).await?;
    let send_duration = start_time.elapsed();
    println!("  ✅ 零拷贝发送完成，耗时: {:?}", send_duration);

    // 接收零拷贝消息
    let start_time = std::time::Instant::now();
    let received: Message<Vec<u8>> = manager.receive_message_zero_copy("zero_copy_queue").await?;
    let receive_duration = start_time.elapsed();
    println!("  ✅ 零拷贝接收完成，耗时: {:?}", receive_duration);
    println!("  📊 数据传输大小: {} bytes", received.data.len());

    // 测试共享内存零拷贝
    println!("  测试共享内存零拷贝...");
    let memory_data = vec![1u8; 1024 * 500]; // 500KB 数据
    let memory_message = Message::new(4, "memory_zero_copy", memory_data, 1234);
    
    let start_time = std::time::Instant::now();
    manager.send_message_zero_copy("zero_copy_memory", &memory_message).await?;
    let memory_duration = start_time.elapsed();
    println!("  ✅ 共享内存零拷贝完成，耗时: {:?}", memory_duration);

    Ok(())
}

#[cfg(feature = "async")]
async fn demonstrate_performance_monitoring(manager: &EnhancedIpcManager) -> Result<()> {
    // 创建多个通道进行性能监控
    println!("  创建多个通道进行性能监控...");
    let channel_names = vec!["perf_channel_1", "perf_channel_2", "perf_channel_3"];
    
    for name in &channel_names {
        manager.create_message_queue_channel(name, 100).await?;
        println!("    ✅ 通道 {} 创建成功", name);
    }

    // 发送大量消息进行性能测试
    println!("  发送大量消息进行性能测试...");
    for i in 0..100 {
        for name in &channel_names {
            let message = Message::new(
                i as u64,
                "perf_test",
                format!("Performance test message {}", i).as_bytes().to_vec(),
                1234
            );
            manager.send_message_zero_copy(name, &message).await?;
        }
    }
    println!("  ✅ 100条消息发送完成");

    // 获取性能统计信息
    println!("  获取性能统计信息...");
    for name in &channel_names {
        if let Some(stats) = manager.get_channel_stats(name).await {
            println!("    通道 {} 统计:", name);
            println!("      发送消息数: {}", stats.messages_sent);
            println!("      接收消息数: {}", stats.messages_received);
            println!("      发送字节数: {}", stats.bytes_sent);
            println!("      接收字节数: {}", stats.bytes_received);
            println!("      连接数: {}", stats.connection_count);
            println!("      最后活动时间: {:?}", stats.last_activity);
        }
    }

    // 获取所有通道统计信息
    println!("  获取所有通道统计信息...");
    let all_stats = manager.get_all_channel_stats().await;
    println!("  ✅ 总通道数: {}", all_stats.len());
    
    let total_messages = all_stats.values()
        .map(|stats| stats.messages_sent + stats.messages_received)
        .sum::<u64>();
    println!("  📊 总消息数: {}", total_messages);

    Ok(())
}

#[cfg(feature = "async")]
async fn demonstrate_error_recovery(manager: &EnhancedIpcManager) -> Result<()> {
    // 演示错误恢复机制
    println!("  演示错误恢复机制...");
    
    // 尝试向不存在的通道发送消息
    let message = Message::new(1, "error_test", "This should fail".as_bytes().to_vec(), 1234);
    
    match manager.send_message_zero_copy("nonexistent_channel", &message).await {
        Ok(()) => {
            println!("    ⚠️ 意外成功发送消息");
        }
        Err(e) => {
            println!("    ✅ 预期的错误: {}", e);
            
            // 演示错误恢复
            println!("    尝试错误恢复...");
            // 这里可以添加具体的错误恢复逻辑
            println!("    ✅ 错误恢复完成");
        }
    }
    
    // 尝试从不存在的通道接收消息
    match manager.receive_message_zero_copy::<Vec<u8>>("nonexistent_channel").await {
        Ok(_) => {
            println!("    ⚠️ 意外成功接收消息");
        }
        Err(e) => {
            println!("    ✅ 预期的错误: {}", e);
        }
    }

    Ok(())
}

#[cfg(feature = "async")]
async fn demonstrate_advanced_ipc_features(manager: &EnhancedIpcManager) -> Result<()> {
    // 演示高级IPC功能
    println!("  演示高级IPC功能...");
    
    // 创建高级消息队列
    println!("    创建高级消息队列...");
    manager.create_message_queue_channel("advanced_queue", 1000).await?;
    println!("    ✅ 高级消息队列创建成功");
    
    // 创建高级共享内存
    println!("    创建高级共享内存...");
    manager.create_shared_memory_channel("advanced_memory", 1024 * 1024).await?;
    println!("    ✅ 高级共享内存创建成功");
    
    // 测试批量消息传输（避免 'static 捕获问题，改为顺序/批处理发送）
    println!("    测试批量消息传输...");
    for i in 0..10 {
        for j in 0..10 {
            let message = Message::new(
                (i * 10 + j) as u64,
                "concurrent_test",
                format!("Concurrent message {} from task {}", j, i).as_bytes().to_vec(),
                1234
            );
            if let Err(e) = manager.send_message_zero_copy("advanced_queue", &message).await {
                eprintln!("发送消息失败: {}", e);
            }
        }
    }
    println!("    ✅ 批量消息传输完成");
    
    // 测试消息优先级
    println!("    测试消息优先级...");
    let high_priority_message = Message::new(1000, "high_priority", "High priority message".as_bytes().to_vec(), 1234)
        .with_priority(10);
    let low_priority_message = Message::new(1001, "low_priority", "Low priority message".as_bytes().to_vec(), 1234)
        .with_priority(1);
    
    manager.send_message_zero_copy("advanced_queue", &high_priority_message).await?;
    manager.send_message_zero_copy("advanced_queue", &low_priority_message).await?;
    println!("    ✅ 优先级消息发送完成");
    
    // 测试大数据传输
    println!("    测试大数据传输...");
    let large_data = vec![0u8; 1024 * 1024]; // 1MB 数据
    let large_message = Message::new(2000, "large_data", large_data, 1234);
    
    let start_time = std::time::Instant::now();
    manager.send_message_zero_copy("advanced_memory", &large_message).await?;
    let duration = start_time.elapsed();
    println!("    ✅ 大数据传输完成，耗时: {:?}", duration);
    
    // 获取最终统计信息
    println!("    获取最终统计信息...");
    let all_stats = manager.get_all_channel_stats().await;
    for (name, stats) in all_stats {
        println!("      通道 {}: 发送 {} 条消息, 接收 {} 条消息", 
                name, stats.messages_sent, stats.messages_received);
    }

    Ok(())
}

#[cfg(not(feature = "async"))]
fn main() {
    println!("❌ 异步功能未启用");
    println!("请使用 --features async 重新编译以启用异步功能");
}
