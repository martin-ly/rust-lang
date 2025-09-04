use crate::types::{ProcessConfig, ProcessInfo, ProcessStatus};
use crate::error::{ProcessResult, ProcessError};
use std::process::{Command, Stdio};
use std::sync::{Arc, Mutex};

/// 进程控制器
pub struct ProcessController {
    processes: Arc<Mutex<std::collections::HashMap<u32, ProcessInfo>>>,
}

impl ProcessController {
    /// 创建新的进程控制器
    pub fn new() -> Self {
        Self {
            processes: Arc::new(Mutex::new(std::collections::HashMap::new())),
        }
    }

    /// 启动进程
    pub fn start(&mut self, config: ProcessConfig) -> ProcessResult<u32> {
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
        let child = command.spawn()
            .map_err(|e| ProcessError::StartFailed(e.to_string()))?;
        
        let pid = child.id() as u32;
        let info = ProcessInfo {
            pid,
            name: config.program.clone(),
            status: ProcessStatus::Running,
            memory_usage: 0,
            cpu_usage: 0.0,
            created_at: std::time::SystemTime::now(),
            parent_pid: None,
            children_pids: Vec::new(),
        };
        
        self.processes.lock().unwrap().insert(pid, info);
        
        Ok(pid)
    }

    /// 停止进程
    pub fn stop(&mut self, pid: u32) -> ProcessResult<()> {
        let mut processes = self.processes.lock().unwrap();
        
        if let Some(info) = processes.get_mut(&pid) {
            info.status = ProcessStatus::Stopped;
            Ok(())
        } else {
            Err(ProcessError::NotFound(pid))
        }
    }

    /// 终止进程
    pub fn terminate(&mut self, pid: u32) -> ProcessResult<()> {
        let mut processes = self.processes.lock().unwrap();
        
        if let Some(info) = processes.get_mut(&pid) {
            info.status = ProcessStatus::Stopped;
            Ok(())
        } else {
            Err(ProcessError::NotFound(pid))
        }
    }

    /// 获取进程信息
    pub fn get_process_info(&self, pid: u32) -> ProcessResult<ProcessInfo> {
        let processes = self.processes.lock().unwrap();
        
        processes.get(&pid)
            .cloned()
            .ok_or(ProcessError::NotFound(pid))
    }

    /// 获取所有进程信息
    pub fn get_all_processes(&self) -> Vec<ProcessInfo> {
        let processes = self.processes.lock().unwrap();
        processes.values().cloned().collect()
    }
}
