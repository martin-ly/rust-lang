use c07_process::prelude::*;
use std::collections::HashMap;
// use std::io::{
//     //Read, 
//     //Write
// };

fn main() -> Result<()> {
    println!("🧪 标准IO管道演示");

    let mut env = HashMap::new();
    if cfg!(windows) {
        env.insert("PATH".to_string(), "C:\\Windows\\System32".to_string());
    } else {
        env.insert("PATH".to_string(), "/usr/bin:/bin".to_string());
    }

    // 目标：向子进程 stdin 写入一行，再读取回显到 stdout。
    // Windows 使用 powershell -Command "$input | ForEach-Object { $_ }"
    // Unix    使用 sh -c "cat"
    let config = if cfg!(windows) {
        ProcessConfig {
            program: "powershell".to_string(),
            args: vec!["-NoProfile".to_string(), "-Command".to_string(), "$input | ForEach-Object { $_ }".to_string()],
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
            args: vec!["-c".to_string(), "cat".to_string()],
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
    println!("✅ 启动管道回显进程，PID: {}", pid);

    // 实际交互：写入一行并关闭stdin，然后读取stdout与stderr
    pm.write_stdin(pid, b"hello from parent\n")?;
    pm.close_stdin(pid)?; // 通知子进程输入结束

    // 读取输出（阻塞直到EOF）
    let out = pm.read_stdout(pid)?;
    let err = pm.read_stderr(pid)?;

    println!("📤 子进程stdout: {}", String::from_utf8_lossy(&out));
    if !err.is_empty() { println!("⚠️ 子进程stderr: {}", String::from_utf8_lossy(&err)); }

    // 确保进程退出
    let _ = pm.wait_with_timeout(pid, std::time::Duration::from_secs(1))?;

    println!("🎉 标准IO演示完成");
    Ok(())
}


