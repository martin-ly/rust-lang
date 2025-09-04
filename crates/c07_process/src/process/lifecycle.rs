use crate::types::{ProcessInfo, ProcessStatus};
use crate::error::ProcessResult;

/// 进程生命周期管理器
pub struct ProcessLifecycleManager {
    processes: std::collections::HashMap<u32, ProcessInfo>,
}

impl ProcessLifecycleManager {
    /// 创建新的生命周期管理器
    pub fn new() -> Self {
        Self {
            processes: std::collections::HashMap::new(),
        }
    }
    
    /// 注册进程
    pub fn register_process(&mut self, info: ProcessInfo) -> ProcessResult<()> {
        self.processes.insert(info.pid, info);
        Ok(())
    }
    
    /// 更新进程状态
    pub fn update_status(&mut self, pid: u32, status: ProcessStatus) -> ProcessResult<()> {
        if let Some(process) = self.processes.get_mut(&pid) {
            process.status = status;
            Ok(())
        } else {
            Err(crate::error::ProcessError::NotFound(pid))
        }
    }
    
    /// 获取进程信息
    pub fn get_process(&self, pid: u32) -> Option<&ProcessInfo> {
        self.processes.get(&pid)
    }
    
    /// 获取所有进程
    pub fn get_all_processes(&self) -> Vec<&ProcessInfo> {
        self.processes.values().collect()
    }
    
    /// 清理已终止的进程
    pub fn cleanup_terminated(&mut self) {
        self.processes.retain(|_, process| {
            process.status != ProcessStatus::Stopped && 
            process.status != ProcessStatus::Zombie
        });
    }
}

impl Default for ProcessLifecycleManager {
    fn default() -> Self {
        Self::new()
    }
}
