#[cfg(feature = "async")]
use c07_process::AsyncProcessManager;
#[cfg(feature = "async")]
use c07_process::prelude::*;
#[cfg(feature = "async")]
use std::collections::HashMap;

#[cfg(feature = "async")]
#[tokio::main]
async fn main() -> Result<()> {
    println!("🧪 异步标准IO演示（占位API，将返回未实现错误）");

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

    // 以下API当前为占位，将返回未实现错误
    let _ = manager.write_stdin(pid, b"hello\n").await.err();
    let _ = manager.close_stdin(pid).await.err();
    let _ = manager.read_stdout(pid).await.err();
    let _ = manager.read_stderr(pid).await.err();

    println!("ℹ️ 异步 stdio API 尚未实现，接口预留完毕");
    Ok(())
}

#[cfg(not(feature = "async"))]
fn main() {
    println!("❌ 异步功能未启用");
    println!("请使用 --features async 重新编译以启用异步功能");
}
