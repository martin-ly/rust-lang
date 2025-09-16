use super::{Fork, ForkResult};
use crate::error::Result;

/// Windows平台的fork实现
/// 由于Windows不支持fork，这里提供基于CreateProcess的替代方案
pub struct WindowsFork {
    is_child: bool,
}

impl WindowsFork {
    /// 创建新的Windows fork实例
    pub fn new() -> Self {
        Self { is_child: false }
    }

    /// 创建子进程（Windows上的替代方案）
    pub fn create_child(&self) -> Result<ForkResult> {
        // Windows上使用CreateProcess创建子进程
        // 这里返回Failed，因为Windows不支持真正的fork
        Ok(ForkResult::Failed)
    }
}

impl Fork for WindowsFork {
    fn fork(&self) -> Result<ForkResult> {
        // Windows不支持fork，返回失败
        Ok(ForkResult::Failed)
    }

    fn is_child(&self) -> bool {
        self.is_child
    }

    fn is_parent(&self) -> bool {
        !self.is_child
    }
}

impl Default for WindowsFork {
    fn default() -> Self {
        Self::new()
    }
}
