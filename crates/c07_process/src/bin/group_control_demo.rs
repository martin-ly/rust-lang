use c07_process::prelude::*;
use c07_process::ProcessGroupManager;
use std::collections::HashMap;
use std::time::Duration;

fn main() -> Result<()> {
    println!("🧨 进程组控制演示（按组终止）");

    let mut env = HashMap::new();
    if cfg!(windows) {
        env.insert("PATH".to_string(), "C:\\Windows\\System32".to_string());
    } else {
        env.insert("PATH".to_string(), "/usr/bin:/bin".to_string());
    }

    // 使用一个可阻塞的命令，方便观察终止效果
    let mk_config = || -> ProcessConfig {
        if cfg!(windows) {
            ProcessConfig {
                program: "cmd".to_string(),
                args: vec!["/c".to_string(), "ping -n 10 127.0.0.1 >NUL".to_string()],
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
                args: vec!["-c".to_string(), "sleep 10".to_string()],
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
    let pid1 = pm.spawn(mk_config())?;
    let pid2 = pm.spawn(mk_config())?;
    let pid3 = pm.spawn(mk_config())?;
    println!("✅ 启动进程: {}, {}, {}", pid1, pid2, pid3);

    let mut pgm = ProcessGroupManager::new();
    let pgid = pgm.create_group("to_kill", pid1);
    let _ = pgm.add_to_group(pgid, pid2);
    let _ = pgm.add_to_group(pgid, pid3);

    // 简易按组终止：遍历成员逐个 kill
    if let Some(group) = pgm.get_group(pgid) {
        for member in group.member_pids {
            let _ = pm.kill(member);
        }
    }

    // 验证都已停止
    let _ = pm.wait_with_timeout(pid1, Duration::from_millis(200))?;
    let _ = pm.wait_with_timeout(pid2, Duration::from_millis(200))?;
    let _ = pm.wait_with_timeout(pid3, Duration::from_millis(200))?;

    println!("🎉 按组终止演示完成");
    Ok(())
}
