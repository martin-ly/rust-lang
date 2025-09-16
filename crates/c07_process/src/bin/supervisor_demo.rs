use c07_process::prelude::*;
use std::collections::HashMap;
use std::env;
use std::time::{
    Duration,
    //Instant,
};

fn main() -> Result<()> {
    println!("🛡️ 进程监控与重启策略演示");

    // 构建一个会快速退出的命令，用于触发重启
    let mut env = HashMap::new();
    if cfg!(windows) {
        env.insert("PATH".to_string(), "C:\\Windows\\System32".to_string());
    } else {
        env.insert("PATH".to_string(), "/usr/bin:/bin".to_string());
    }

    let make_config = || -> ProcessConfig {
        if cfg!(windows) {
            ProcessConfig {
                program: "cmd".to_string(),
                args: vec!["/c".to_string(), "exit 1".to_string()],
                env: env.clone(),
                working_dir: Some(".".to_string()),
                user_id: None,
                group_id: None,
                priority: None,
                resource_limits: ResourceLimits::default(),
            }
        } else {
            ProcessConfig {
                program: "sh".to_string(),
                args: vec!["-c".to_string(), "exit 1".to_string()],
                env: env.clone(),
                working_dir: Some(".".to_string()),
                user_id: None,
                group_id: None,
                priority: None,
                resource_limits: ResourceLimits::default(),
            }
        }
    };

    let mut pm = ProcessManager::new();

    // 指数退避参数（可配置）
    let max_restarts: u32 = env::var("MAX_RESTARTS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(5);
    let mut attempt = 0u32;
    let mut backoff_ms: u64 = env::var("BACKOFF_START_MS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(100);
    let backoff_max_ms: u64 = env::var("BACKOFF_MAX_MS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(2000);

    while attempt < max_restarts {
        attempt += 1;
        println!("🚀 启动子进程（尝试 {}）", attempt);
        let pid = pm.spawn(make_config())?;
        println!("✅ 子进程 PID: {}", pid);

        // 等待最多 500ms，若仍在运行则演示强杀
        match pm.wait_with_timeout(pid, Duration::from_millis(500))? {
            Some(status) => {
                println!("⚠️ 子进程提前退出，状态: {:?}", status);
            }
            None => {
                println!("⌛ 仍在运行，执行终止...");
                let _ = pm.kill(pid);
            }
        }

        // 退避等待
        println!("⏳ 退避等待 {} ms 后重启...", backoff_ms);
        std::thread::sleep(Duration::from_millis(backoff_ms));
        backoff_ms = (backoff_ms * 2).min(backoff_max_ms);
    }

    println!("🎉 监控与重启演示完成");
    Ok(())
}
