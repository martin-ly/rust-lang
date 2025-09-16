use c07_process::ProcessGroupManager;
use c07_process::prelude::*;
use std::collections::HashMap;

fn main() -> Result<()> {
    println!("👥 进程组管理演示");

    let mut env = HashMap::new();
    if cfg!(windows) {
        env.insert("PATH".to_string(), "C:\\Windows\\System32".to_string());
    } else {
        env.insert("PATH".to_string(), "/usr/bin:/bin".to_string());
    }

    // 基础命令
    let mk_config = |msg: &str| -> ProcessConfig {
        if cfg!(windows) {
            ProcessConfig {
                program: "cmd".to_string(),
                args: vec!["/c".to_string(), format!("echo {}", msg)],
                env: env.clone(),
                working_dir: Some(".".to_string()),
                user_id: None,
                group_id: None,
                priority: None,
                resource_limits: ResourceLimits::default(),
            }
        } else {
            ProcessConfig {
                program: "echo".to_string(),
                args: vec![msg.to_string()],
                env: env.clone(),
                working_dir: Some(".".to_string()),
                user_id: None,
                group_id: None,
                priority: None,
                resource_limits: ResourceLimits::default(),
            }
        }
    };

    // 启动三个进程
    let mut pm = ProcessManager::new();
    let pid1 = pm.spawn(mk_config("group member 1"))?;
    let pid2 = pm.spawn(mk_config("group member 2"))?;
    let pid3 = pm.spawn(mk_config("group member 3"))?;
    println!("✅ 启动进程: {}, {}, {}", pid1, pid2, pid3);

    // 创建进程组并加入成员
    let mut pgm = ProcessGroupManager::new();
    let pgid = pgm.create_group("demo", pid1);
    let _ = pgm.add_to_group(pgid, pid2);
    let _ = pgm.add_to_group(pgid, pid3);

    if let Some(group) = pgm.get_group(pgid) {
        println!(
            "📋 进程组 {}: leader={}, members={:?}",
            group.pgid, group.leader_pid, group.member_pids
        );
    }

    // 等待退出
    let _ = pm.wait_with_timeout(pid1, std::time::Duration::from_secs(1))?;
    let _ = pm.wait_with_timeout(pid2, std::time::Duration::from_secs(1))?;
    let _ = pm.wait_with_timeout(pid3, std::time::Duration::from_secs(1))?;

    println!("🎉 进程组演示完成");
    Ok(())
}
