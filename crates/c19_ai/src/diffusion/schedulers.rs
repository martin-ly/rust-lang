//! 扩散调度器
//! 
//! 提供各种扩散模型的调度器

use serde::{Deserialize, Serialize};
use anyhow::Result;

/// 调度器类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SchedulerType {
    DDIM,
    DDPM,
    Euler,
    Heun,
    DPMPlusPlus,
}

/// 调度器配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SchedulerConfig {
    pub scheduler_type: SchedulerType,
    pub num_steps: usize,
    pub beta_start: f32,
    pub beta_end: f32,
}

/// 扩散调度器
pub struct DiffusionScheduler {
    config: SchedulerConfig,
}

impl DiffusionScheduler {
    pub fn new(config: SchedulerConfig) -> Self {
        Self { config }
    }
    
    pub fn get_timesteps(&self) -> Vec<usize> {
        (0..self.config.num_steps).collect()
    }
}
