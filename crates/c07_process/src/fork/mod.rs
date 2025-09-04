// Fork模块
// 这个模块提供了进程分叉功能
// 主要用于Unix系统

#[cfg(unix)]
pub mod unix_fork;

#[cfg(unix)]
pub use unix_fork::UnixFork;

#[cfg(not(unix))]
pub mod windows_fork;

#[cfg(not(unix))]
pub use windows_fork::WindowsFork;

/// Fork trait，提供跨平台的进程分叉接口
pub trait Fork {
    /// 分叉当前进程
    fn fork(&self) -> crate::error::Result<ForkResult>;
    
    /// 检查是否为子进程
    fn is_child(&self) -> bool;
    
    /// 检查是否为父进程
    fn is_parent(&self) -> bool;
}

/// Fork结果
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ForkResult {
    /// 父进程
    Parent,
    /// 子进程
    Child,
    /// 分叉失败
    Failed,
}

impl ForkResult {
    /// 检查是否为父进程
    pub fn is_parent(&self) -> bool {
        matches!(self, ForkResult::Parent)
    }
    
    /// 检查是否为子进程
    pub fn is_child(&self) -> bool {
        matches!(self, ForkResult::Child)
    }
    
    /// 检查是否失败
    pub fn is_failed(&self) -> bool {
        matches!(self, ForkResult::Failed)
    }
}
