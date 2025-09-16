use crate::error::ProcessResult;
use crate::types::{ProcessConfig, ResourceLimits};
use std::collections::HashMap;

/// 进程属性管理器
pub struct ProcessAttributesManager {
    configs: HashMap<u32, ProcessConfig>,
}

impl ProcessAttributesManager {
    /// 创建新的属性管理器
    pub fn new() -> Self {
        Self {
            configs: HashMap::new(),
        }
    }

    /// 设置进程配置
    pub fn set_config(&mut self, pid: u32, config: ProcessConfig) -> ProcessResult<()> {
        self.configs.insert(pid, config);
        Ok(())
    }

    /// 获取进程配置
    pub fn get_config(&self, pid: u32) -> Option<&ProcessConfig> {
        self.configs.get(&pid)
    }

    /// 更新资源限制
    pub fn update_resource_limits(
        &mut self,
        pid: u32,
        limits: ResourceLimits,
    ) -> ProcessResult<()> {
        if let Some(config) = self.configs.get_mut(&pid) {
            config.resource_limits = limits;
            Ok(())
        } else {
            Err(crate::error::ProcessError::NotFound(pid))
        }
    }

    /// 设置环境变量
    pub fn set_env_var(&mut self, pid: u32, key: String, value: String) -> ProcessResult<()> {
        if let Some(config) = self.configs.get_mut(&pid) {
            config.env.insert(key, value);
            Ok(())
        } else {
            Err(crate::error::ProcessError::NotFound(pid))
        }
    }

    /// 获取环境变量
    pub fn get_env_var(&self, pid: u32, key: &str) -> Option<&String> {
        self.configs.get(&pid)?.env.get(key)
    }
}

impl Default for ProcessAttributesManager {
    fn default() -> Self {
        Self::new()
    }
}
