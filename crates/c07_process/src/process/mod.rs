pub mod attributes;
pub mod control;
pub mod lifecycle;
pub mod monitor;
pub mod pool;

use crate::error::{ProcessError, ProcessResult};
use crate::types::{ProcessConfig, ProcessInfo, ProcessStatus, ResourceLimits};
use std::collections::HashMap;
use std::io::{Read, Write};
use std::process::{Child, Command, ExitStatus, Stdio};
use std::sync::{Arc, Mutex};
use std::time::SystemTime;
use std::time::{Duration, Instant};

/// 进程管理器
pub struct ProcessManager {
    processes: Arc<Mutex<HashMap<u32, ManagedProcess>>>,
    next_pid: Arc<Mutex<u32>>,
}

/// 被管理的进程
struct ManagedProcess {
    child: Child,
    info: ProcessInfo,
}

impl ProcessManager {
    /// 创建新的进程管理器
    pub fn new() -> Self {
        Self {
            processes: Arc::new(Mutex::new(HashMap::new())),
            next_pid: Arc::new(Mutex::new(1000)), // 避免与系统PID冲突
        }
    }

    /// 生成新的进程ID
    fn generate_pid(&self) -> u32 {
        let mut next_pid = self.next_pid.lock().unwrap();
        *next_pid += 1;
        *next_pid
    }

    /// 启动新进程
    pub fn spawn(&mut self, config: ProcessConfig) -> ProcessResult<u32> {
        let mut command = Command::new(&config.program);

        // 设置命令行参数
        for arg in &config.args {
            command.arg(arg);
        }

        // 设置环境变量
        for (key, value) in &config.env {
            command.env(key, value);
        }

        // 设置工作目录
        if let Some(dir) = &config.working_dir {
            command.current_dir(dir);
        }

        // 设置标准IO
        command.stdin(Stdio::piped());
        command.stdout(Stdio::piped());
        command.stderr(Stdio::piped());

        // 启动进程
        let child = command
            .spawn()
            .map_err(|e| ProcessError::StartFailed(e.to_string()))?;

        let pid = self.generate_pid();
        let info = ProcessInfo {
            pid,
            name: config.program.clone(),
            status: ProcessStatus::Running,
            memory_usage: 0,
            cpu_usage: 0.0,
            created_at: SystemTime::now(),
            parent_pid: None,
            children_pids: Vec::new(),
        };

        let managed_process = ManagedProcess { child, info };

        self.processes.lock().unwrap().insert(pid, managed_process);

        Ok(pid)
    }

    /// 异步启动进程（简化版本，不使用tokio）
    pub fn spawn_async(&mut self, config: ProcessConfig) -> ProcessResult<u32> {
        // 简化实现，直接调用同步版本
        self.spawn(config)
    }

    /// 等待进程完成
    pub fn wait(&mut self, pid: u32) -> ProcessResult<ExitStatus> {
        let mut processes = self.processes.lock().unwrap();

        if let Some(managed_process) = processes.get_mut(&pid) {
            let status = managed_process
                .child
                .wait()
                .map_err(|e| ProcessError::WaitFailed(e.to_string()))?;

            // 更新进程状态
            managed_process.info.status = ProcessStatus::Stopped;

            // 从管理列表中移除已完成的进程
            processes.remove(&pid);

            Ok(status)
        } else {
            Err(ProcessError::NotFound(pid))
        }
    }

    /// 异步等待进程完成
    pub async fn wait_async(&mut self, pid: u32) -> ProcessResult<ExitStatus> {
        let mut processes = self.processes.lock().unwrap();

        if let Some(managed_process) = processes.get_mut(&pid) {
            // 简化实现，直接等待
            let status = managed_process
                .child
                .wait()
                .map_err(|e| ProcessError::WaitFailed(e.to_string()))?;

            // 更新进程状态
            managed_process.info.status = ProcessStatus::Stopped;

            Ok(status)
        } else {
            Err(ProcessError::NotFound(pid))
        }
    }

    /// 获取进程输出（阻塞直到进程退出，返回实际 stdout/stderr）
    pub fn get_output(&mut self, pid: u32) -> ProcessResult<std::process::Output> {
        let mut processes = self.processes.lock().unwrap();
        if let Some(managed_process) = processes.get_mut(&pid) {
            // 先读取 stdout/stderr 再等待退出，避免移动 Child
            let stdout_bytes = if let Some(stdout) = managed_process.child.stdout.as_mut() {
                let mut buf = Vec::new();
                let _ = stdout.read_to_end(&mut buf); // 读取失败不致命
                buf
            } else {
                Vec::new()
            };

            let stderr_bytes = if let Some(stderr) = managed_process.child.stderr.as_mut() {
                let mut buf = Vec::new();
                let _ = stderr.read_to_end(&mut buf);
                buf
            } else {
                Vec::new()
            };

            let status = managed_process
                .child
                .wait()
                .map_err(|e| ProcessError::WaitFailed(e.to_string()))?;

            managed_process.info.status = ProcessStatus::Stopped;
            processes.remove(&pid);

            Ok(std::process::Output {
                status,
                stdout: stdout_bytes,
                stderr: stderr_bytes,
            })
        } else {
            Err(ProcessError::NotFound(pid))
        }
    }

    /// 带超时等待进程完成
    /// 返回 Ok(Some(status)) 表示在超时时间内进程已退出；
    /// 返回 Ok(None) 表示超时未退出；Err 表示等待过程中出错或找不到进程。
    pub fn wait_with_timeout(
        &mut self,
        pid: u32,
        timeout: Duration,
    ) -> ProcessResult<Option<ExitStatus>> {
        let start = Instant::now();
        loop {
            {
                let mut processes = self.processes.lock().unwrap();
                if let Some(managed_process) = processes.get_mut(&pid) {
                    match managed_process.child.try_wait() {
                        Ok(Some(status)) => {
                            managed_process.info.status = ProcessStatus::Stopped;
                            processes.remove(&pid);
                            return Ok(Some(status));
                        }
                        Ok(None) => {
                            // 继续等待
                        }
                        Err(e) => {
                            return Err(ProcessError::WaitFailed(e.to_string()));
                        }
                    }
                } else {
                    return Err(ProcessError::NotFound(pid));
                }
            }

            if start.elapsed() >= timeout {
                return Ok(None);
            }

            std::thread::sleep(Duration::from_millis(20));
        }
    }

    /// 向子进程标准输入写入数据（不自动关闭stdin）
    pub fn write_stdin(&mut self, pid: u32, data: &[u8]) -> ProcessResult<()> {
        let mut processes = self.processes.lock().unwrap();
        if let Some(managed_process) = processes.get_mut(&pid) {
            if let Some(stdin) = managed_process.child.stdin.as_mut() {
                stdin.write_all(data).map_err(ProcessError::Io)?;
                stdin.flush().map_err(ProcessError::Io)?;
                Ok(())
            } else {
                Err(ProcessError::InvalidConfig(
                    "stdin not available".to_string(),
                ))
            }
        } else {
            Err(ProcessError::NotFound(pid))
        }
    }

    /// 关闭子进程标准输入，向子进程发出EOF
    pub fn close_stdin(&mut self, pid: u32) -> ProcessResult<()> {
        let mut processes = self.processes.lock().unwrap();
        if let Some(managed_process) = processes.get_mut(&pid) {
            // 将stdin设置为None即关闭
            managed_process.child.stdin.take();
            Ok(())
        } else {
            Err(ProcessError::NotFound(pid))
        }
    }

    /// 读取子进程标准输出的全部可用数据（阻塞直到EOF或无数据可读）
    pub fn read_stdout(&mut self, pid: u32) -> ProcessResult<Vec<u8>> {
        let mut processes = self.processes.lock().unwrap();
        if let Some(managed_process) = processes.get_mut(&pid) {
            if let Some(stdout) = managed_process.child.stdout.as_mut() {
                let mut buf = Vec::new();
                stdout.read_to_end(&mut buf).map_err(ProcessError::Io)?;
                Ok(buf)
            } else {
                Err(ProcessError::InvalidConfig(
                    "stdout not available".to_string(),
                ))
            }
        } else {
            Err(ProcessError::NotFound(pid))
        }
    }

    /// 读取子进程标准错误的全部可用数据
    pub fn read_stderr(&mut self, pid: u32) -> ProcessResult<Vec<u8>> {
        let mut processes = self.processes.lock().unwrap();
        if let Some(managed_process) = processes.get_mut(&pid) {
            if let Some(stderr) = managed_process.child.stderr.as_mut() {
                let mut buf = Vec::new();
                stderr.read_to_end(&mut buf).map_err(ProcessError::Io)?;
                Ok(buf)
            } else {
                Err(ProcessError::InvalidConfig(
                    "stderr not available".to_string(),
                ))
            }
        } else {
            Err(ProcessError::NotFound(pid))
        }
    }

    /// 终止进程
    pub fn kill(&mut self, pid: u32) -> ProcessResult<()> {
        let mut processes = self.processes.lock().unwrap();

        if let Some(managed_process) = processes.get_mut(&pid) {
            managed_process
                .child
                .kill()
                .map_err(|e| ProcessError::TerminationFailed(e.to_string()))?;

            // 更新进程状态
            managed_process.info.status = ProcessStatus::Stopped;

            Ok(())
        } else {
            Err(ProcessError::NotFound(pid))
        }
    }

    /// 获取进程信息
    pub fn get_process_info(&self, pid: u32) -> ProcessResult<ProcessInfo> {
        let processes = self.processes.lock().unwrap();

        if let Some(managed_process) = processes.get(&pid) {
            Ok(managed_process.info.clone())
        } else {
            Err(ProcessError::NotFound(pid))
        }
    }

    /// 获取所有进程信息
    pub fn get_all_processes(&self) -> Vec<ProcessInfo> {
        let processes = self.processes.lock().unwrap();
        processes.values().map(|p| p.info.clone()).collect()
    }

    /// 检查进程是否运行
    pub fn is_running(&self, pid: u32) -> bool {
        let processes = self.processes.lock().unwrap();
        processes
            .get(&pid)
            .map(|p| p.info.status == ProcessStatus::Running)
            .unwrap_or(false)
    }

    /// 获取进程数量
    pub fn process_count(&self) -> usize {
        let processes = self.processes.lock().unwrap();
        processes.len()
    }

    /// 清理已终止的进程
    pub fn cleanup_terminated(&mut self) {
        let mut processes = self.processes.lock().unwrap();
        processes
            .retain(|_, managed_process| managed_process.info.status == ProcessStatus::Running);
    }
}

impl Default for ProcessManager {
    fn default() -> Self {
        Self::new()
    }
}

/// 进程构建器
pub struct ProcessBuilder {
    config: ProcessConfig,
}

impl ProcessBuilder {
    /// 创建新的进程构建器
    pub fn new(program: impl Into<String>) -> Self {
        Self {
            config: ProcessConfig {
                program: program.into(),
                args: Vec::new(),
                env: HashMap::new(),
                working_dir: None,
                user_id: None,
                group_id: None,
                priority: None,
                resource_limits: ResourceLimits::default(),
            },
        }
    }

    /// 添加命令行参数
    pub fn arg(mut self, arg: impl Into<String>) -> Self {
        self.config.args.push(arg.into());
        self
    }

    /// 添加多个命令行参数
    pub fn args(mut self, args: impl IntoIterator<Item = impl Into<String>>) -> Self {
        for arg in args {
            self.config.args.push(arg.into());
        }
        self
    }

    /// 设置环境变量
    pub fn env(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.config.env.insert(key.into(), value.into());
        self
    }

    /// 设置工作目录
    pub fn working_dir(mut self, dir: impl Into<String>) -> Self {
        self.config.working_dir = Some(dir.into());
        self
    }

    /// 设置用户ID
    pub fn user_id(mut self, uid: u32) -> Self {
        self.config.user_id = Some(uid);
        self
    }

    /// 设置组ID
    pub fn group_id(mut self, gid: u32) -> Self {
        self.config.group_id = Some(gid);
        self
    }

    /// 设置优先级
    pub fn priority(mut self, priority: i32) -> Self {
        self.config.priority = Some(priority);
        self
    }

    /// 设置资源限制
    pub fn resource_limits(mut self, limits: ResourceLimits) -> Self {
        self.config.resource_limits = limits;
        self
    }

    /// 构建进程配置
    pub fn build(self) -> ProcessConfig {
        self.config
    }
}

/// 进程组管理器
pub struct ProcessGroupManager {
    groups: Arc<Mutex<HashMap<u32, ProcessGroup>>>,
    next_pgid: Arc<Mutex<u32>>,
}

/// 进程组
struct ProcessGroup {
    pgid: u32,
    leader_pid: u32,
    member_pids: Vec<u32>,
    name: String,
    created_at: SystemTime,
}

impl ProcessGroupManager {
    /// 创建新的进程组管理器
    pub fn new() -> Self {
        Self {
            groups: Arc::new(Mutex::new(HashMap::new())),
            next_pgid: Arc::new(Mutex::new(10000)),
        }
    }

    /// 创建进程组
    pub fn create_group(&mut self, name: impl Into<String>, leader_pid: u32) -> u32 {
        let mut next_pgid = self.next_pgid.lock().unwrap();
        *next_pgid += 1;
        let pgid = *next_pgid;

        let group = ProcessGroup {
            pgid,
            leader_pid,
            member_pids: vec![leader_pid],
            name: name.into(),
            created_at: SystemTime::now(),
        };

        self.groups.lock().unwrap().insert(pgid, group);
        pgid
    }

    /// 向进程组添加进程
    pub fn add_to_group(&mut self, pgid: u32, pid: u32) -> bool {
        let mut groups = self.groups.lock().unwrap();

        if let Some(group) = groups.get_mut(&pgid) {
            if !group.member_pids.contains(&pid) {
                group.member_pids.push(pid);
                true
            } else {
                false
            }
        } else {
            false
        }
    }

    /// 从进程组移除进程
    pub fn remove_from_group(&mut self, pgid: u32, pid: u32) -> bool {
        let mut groups = self.groups.lock().unwrap();

        if let Some(group) = groups.get_mut(&pgid) {
            if let Some(pos) = group.member_pids.iter().position(|&p| p == pid) {
                group.member_pids.remove(pos);
                true
            } else {
                false
            }
        } else {
            false
        }
    }

    /// 获取进程组信息
    pub fn get_group(&self, pgid: u32) -> Option<crate::types::ProcessGroup> {
        let groups = self.groups.lock().unwrap();

        groups.get(&pgid).map(|g| crate::types::ProcessGroup {
            pgid: g.pgid,
            leader_pid: g.leader_pid,
            member_pids: g.member_pids.clone(),
            name: g.name.clone(),
            created_at: g.created_at,
        })
    }
}

impl Default for ProcessGroupManager {
    fn default() -> Self {
        Self::new()
    }
}
