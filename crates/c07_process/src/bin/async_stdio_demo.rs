#[cfg(feature = "async")]
use c07_process::AsyncProcessManager;
#[cfg(feature = "async")]
use c07_process::prelude::*;
#[cfg(feature = "async")]
use std::collections::HashMap;

#[cfg(feature = "async")]
#[tokio::main]
async fn main() -> Result<()> {
    println!("🧪 异步标准IO演示（已实现完整功能）");

    let mut env = HashMap::new();
    if cfg!(windows) {
        env.insert("PATH".to_string(), "C:\\Windows\\System32".to_string());
    } else {
        env.insert("PATH".to_string(), "/usr/bin:/bin".to_string());
    }

    let config = if cfg!(windows) {
        ProcessConfig {
            program: "cmd".to_string(),
            args: vec!["/c".to_string(), "echo async".to_string()],
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
            args: vec!["async".to_string()],
            env,
            working_dir: Some(".".to_string()),
            user_id: None,
            group_id: None,
            priority: None,
            resource_limits: ResourceLimits::default(),
        }
    };

    let manager = AsyncProcessManager::new().await;
    let pid = manager.spawn(config).await?;
    println!("✅ 启动异步进程，PID: {}", pid);

    // 使用新实现的异步 stdio API
    println!("📝 写入标准输入...");
    match manager.write_stdin(pid, b"hello from async\n").await {
        Ok(()) => println!("✅ 成功写入标准输入"),
        Err(e) => println!("⚠️ 写入标准输入失败: {}", e),
    }

    println!("🔒 关闭标准输入...");
    match manager.close_stdin(pid).await {
        Ok(()) => println!("✅ 成功关闭标准输入"),
        Err(e) => println!("⚠️ 关闭标准输入失败: {}", e),
    }

    // 等待进程完成
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;

    println!("📖 读取标准输出...");
    match manager.read_stdout(pid).await {
        Ok(output) => {
            let output_str = String::from_utf8_lossy(&output);
            println!("✅ 标准输出: {}", output_str);
        }
        Err(e) => println!("⚠️ 读取标准输出失败: {}", e),
    }

    println!("📖 读取标准错误...");
    match manager.read_stderr(pid).await {
        Ok(output) => {
            let output_str = String::from_utf8_lossy(&output);
            if !output_str.is_empty() {
                println!("✅ 标准错误: {}", output_str);
            } else {
                println!("ℹ️ 标准错误为空");
            }
        }
        Err(e) => println!("⚠️ 读取标准错误失败: {}", e),
    }

    println!("✅ 异步 stdio API 演示完成");
    Ok(())
}

#[cfg(not(feature = "async"))]
fn main() {
    println!("❌ 异步功能未启用");
    println!("请使用 --features async 重新编译以启用异步功能");
}
