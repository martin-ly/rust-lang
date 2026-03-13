use c07_process::prelude::*;
use std::collections::HashMap;
use std::env;
use std::time::Duration;

fn main() -> Result<()> {
    println!("⏱️ 超时与取消演示");

    let mut env = HashMap::new();
    if cfg!(windows) {
        env.insert("PATH".to_string(), "C:Windows\\System32".to_string()); // 占位，不依赖 PATH
    } else {
        env.insert("PATH".to_string(), "/usr/bin:/bin".to_string());
    }

    // 构造一个可延迟的命令：
    // Windows: cmd /c ping -n 5 127.0.0.1 >NUL  (约4秒)
    // Unix:    sh -c "sleep 4"
    let config = if cfg!(windows) {
        ProcessConfig {
            program: "cmd".to_string(),
            args: vec!["/c".to_string(), "ping -n 5 127.0.0.1 >NUL".to_string()],
            env,
            working_dir: Some(".".to_string()),
            user_id: None,
            group_id: None,
            priority: None,
            resource_limits: ResourceLimits::default(),
        }
    } else {
        ProcessConfig {
            program: "sh".to_string(),
            args: vec!["-c".to_string(), "sleep 4".to_string()],
            env,
            working_dir: Some(".".to_string()),
            user_id: None,
            group_id: None,
            priority: None,
            resource_limits: ResourceLimits::default(),
        }
    };

    let mut pm = ProcessManager::new();
    let pid = pm.spawn(config)?;
    println!("✅ 启动长任务进程，PID: {}", pid);

    // 支持通过环境变量 TIMEOUT_MS 配置超时时间
    let timeout_ms: u64 = env::var("TIMEOUT_MS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(1000);
    // 等待超时
    match pm.wait_with_timeout(pid, Duration::from_millis(timeout_ms))? {
        Some(status) => {
            println!("⚠️ 预期外：进程过早退出，状态: {:?}", status);
        }
        None => {
            println!("⌛ 已超时，尝试终止进程...");
            pm.kill(pid)?;
            println!("🛑 进程已终止");
        }
    }

    Ok(())
}
