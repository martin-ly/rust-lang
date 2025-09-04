use super::{Fork, ForkResult};
use crate::error::Result;

/// Unix平台的fork实现
pub struct UnixFork {
    is_child: bool,
}

impl UnixFork {
    /// 创建新的Unix fork实例
    pub fn new() -> Self {
        Self { is_child: false }
    }
    
    /// 执行fork操作
    pub fn do_fork(&self) -> Result<ForkResult> {
        // 这里应该调用libc::fork()
        // 但由于我们在Windows上编译，这里返回模拟结果
        Ok(ForkResult::Parent)
    }
}

impl Fork for UnixFork {
    fn fork(&self) -> Result<ForkResult> {
        self.do_fork()
    }
    
    fn is_child(&self) -> bool {
        self.is_child
    }
    
    fn is_parent(&self) -> bool {
        !self.is_child
    }
}

impl Default for UnixFork {
    fn default() -> Self {
        Self::new()
    }
}
