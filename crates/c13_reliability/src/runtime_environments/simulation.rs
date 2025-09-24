//! # 运行时环境模拟 (Simulation)
//!
//! 提供轻量级的环境模拟能力，用于本地开发、离线演示和CI测试。

use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use crate::error_handling::UnifiedError;
use super::{
	RuntimeEnvironment, RuntimeEnvironmentAdapter, EnvironmentCapabilities,
	SystemInfo, ResourceUsage, HealthStatus, HealthLevel, RecoveryType,
};

/// 模拟模式
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum SimulationMode {
	LowResources,
	Normal,
	HighLoad,
}

/// 模拟配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SimulationConfig {
	pub environment: RuntimeEnvironment,
	pub mode: SimulationMode,
	pub system_name: String,
	pub total_memory: u64,
	pub total_cpu_cores: u32,
	pub total_disk_space: u64,
}

impl Default for SimulationConfig {
	fn default() -> Self {
		Self {
			environment: RuntimeEnvironment::OperatingSystem,
			mode: SimulationMode::Normal,
			system_name: "Simulated System".to_string(),
			total_memory: 1024 * 1024 * 1024,
			total_cpu_cores: 2,
			total_disk_space: 10 * 1024 * 1024 * 1024,
		}
	}
}

/// 模拟环境适配器（通用）
pub struct SimulatedEnvironmentAdapter {
	config: SimulationConfig,
}

impl SimulatedEnvironmentAdapter {
	pub fn new(config: SimulationConfig) -> Self {
		Self { config }
	}
}

#[async_trait]
impl RuntimeEnvironmentAdapter for SimulatedEnvironmentAdapter {
	fn environment_type(&self) -> RuntimeEnvironment {
		self.config.environment
	}

	fn capabilities(&self) -> EnvironmentCapabilities {
		self.config.environment.capabilities()
	}

	async fn initialize(&mut self) -> Result<(), UnifiedError> {
		Ok(())
	}

	async fn cleanup(&mut self) -> Result<(), UnifiedError> {
		Ok(())
	}

	async fn get_system_info(&self) -> Result<SystemInfo, UnifiedError> {
		let mut extra = HashMap::new();
		extra.insert("sim_mode".to_string(), format!("{:?}", self.config.mode));
		extra.insert("simulated".to_string(), "true".to_string());
		Ok(SystemInfo {
			environment: self.config.environment,
			system_name: self.config.system_name.clone(),
			system_version: "sim-1.0".to_string(),
			architecture: std::env::consts::ARCH.to_string(),
			total_memory: self.config.total_memory,
			total_cpu_cores: self.config.total_cpu_cores,
			total_disk_space: self.config.total_disk_space,
			uptime: std::time::Duration::from_secs(1234),
			extra_info: extra,
		})
	}

	async fn get_resource_usage(&self) -> Result<ResourceUsage, UnifiedError> {
		let (cpu, mem_pct, net_rate) = match self.config.mode {
			SimulationMode::LowResources => (15.0, 20.0, 100.0),
			SimulationMode::Normal => (35.0, 40.0, 500.0),
			SimulationMode::HighLoad => (85.0, 90.0, 2_000.0),
		};
		Ok(ResourceUsage {
			cpu_usage_percent: cpu,
			memory_usage_bytes: (mem_pct / 100.0 * self.config.total_memory as f64) as u64,
			memory_usage_percent: mem_pct,
			disk_usage_bytes: (0.5 * self.config.total_disk_space as f64) as u64,
			disk_usage_percent: 50.0,
			network_rx_bytes: 10_000,
			network_tx_bytes: 5_000,
			network_rx_rate: net_rate,
			network_tx_rate: net_rate / 2.0,
			timestamp: chrono::Utc::now(),
		})
	}

	async fn check_health(&self) -> Result<HealthStatus, UnifiedError> {
		let level = match self.config.mode {
			SimulationMode::LowResources => HealthLevel::Healthy,
			SimulationMode::Normal => HealthLevel::Healthy,
			SimulationMode::HighLoad => HealthLevel::Warning,
		};
		let mut details = HashMap::new();
		details.insert("cpu".to_string(), level.clone());
		Ok(HealthStatus {
			overall_health: level,
			details,
			check_time: chrono::Utc::now(),
			environment_specific: HashMap::new(),
		})
	}

	async fn perform_recovery(&self, recovery_type: RecoveryType) -> Result<(), UnifiedError> {
		match recovery_type {
			RecoveryType::MemoryCleanup => Ok(()),
			RecoveryType::ConnectionReset => Ok(()),
			_ => Ok(()),
		}
	}
}
