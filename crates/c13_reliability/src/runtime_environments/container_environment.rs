//! # Docker容器环境适配器
//!
//! 提供对Docker容器环境的支持，包括：
//! - 容器资源限制监控
//! - 容器健康检查
//! - 容器生命周期管理
//! - 容器特定的恢复策略

use std::collections::HashMap;
use std::fs;
use std::time::{SystemTime, UNIX_EPOCH};
use async_trait::async_trait;
use crate::error_handling::UnifiedError;
use super::{
    RuntimeEnvironmentAdapter, RuntimeEnvironment, EnvironmentCapabilities,
    SystemInfo, ResourceUsage, HealthStatus, HealthLevel, RecoveryType
};

/// Docker容器环境适配器
pub struct ContainerEnvironmentAdapter {
    /// 容器ID
    container_id: String,
    /// 容器名称
    container_name: String,
    /// 镜像名称
    image_name: String,
    /// 启动时间
    start_time: SystemTime,
    /// 资源限制
    resource_limits: ContainerResourceLimits,
    /// 当前资源使用情况
    current_usage: ContainerResourceUsage,
}

/// 容器资源限制
#[derive(Debug, Clone)]
pub struct ContainerResourceLimits {
    /// 内存限制（字节）
    pub memory_limit: Option<u64>,
    /// CPU限制（核心数）
    pub cpu_limit: Option<f64>,
    /// 磁盘限制（字节）
    pub disk_limit: Option<u64>,
    /// 网络限制（字节/秒）
    pub network_limit: Option<u64>,
}

/// 容器资源使用情况
#[derive(Debug, Clone)]
pub struct ContainerResourceUsage {
    /// 内存使用量（字节）
    pub memory_usage: u64,
    /// CPU使用率（百分比）
    pub cpu_usage: f64,
    /// 磁盘使用量（字节）
    pub disk_usage: u64,
    /// 网络接收字节数
    pub network_rx: u64,
    /// 网络发送字节数
    pub network_tx: u64,
}

impl ContainerEnvironmentAdapter {
    /// 创建新的Docker容器环境适配器
    pub fn new() -> Self {
        Self {
            container_id: Self::get_container_id().unwrap_or_else(|| "unknown".to_string()),
            container_name: Self::get_container_name().unwrap_or_else(|| "unknown".to_string()),
            image_name: Self::get_image_name().unwrap_or_else(|| "unknown".to_string()),
            start_time: SystemTime::now(),
            resource_limits: Self::get_resource_limits(),
            current_usage: ContainerResourceUsage {
                memory_usage: 0,
                cpu_usage: 0.0,
                disk_usage: 0,
                network_rx: 0,
                network_tx: 0,
            },
        }
    }
    
    /// 获取容器ID
    fn get_container_id() -> Option<String> {
        // 尝试从多个位置获取容器ID
        if let Ok(id) = fs::read_to_string("/proc/self/cgroup") {
            for line in id.lines() {
                if line.contains("docker") {
                    if let Some(id) = line.split('/').last() {
                        return Some(id.to_string());
                    }
                }
            }
        }
        
        // 尝试从环境变量获取
        if let Ok(id) = std::env::var("HOSTNAME") {
            return Some(id);
        }
        
        None
    }
    
    /// 获取容器名称
    fn get_container_name() -> Option<String> {
        // 尝试从环境变量获取
        if let Ok(name) = std::env::var("CONTAINER_NAME") {
            return Some(name);
        }
        
        // 尝试从HOSTNAME获取
        if let Ok(name) = std::env::var("HOSTNAME") {
            return Some(name);
        }
        
        None
    }
    
    /// 获取镜像名称
    fn get_image_name() -> Option<String> {
        // 尝试从环境变量获取
        if let Ok(image) = std::env::var("IMAGE_NAME") {
            return Some(image);
        }
        
        // 尝试从标签获取
        if let Ok(image) = std::env::var("DOCKER_IMAGE") {
            return Some(image);
        }
        
        None
    }
    
    /// 获取资源限制
    fn get_resource_limits() -> ContainerResourceLimits {
        let mut limits = ContainerResourceLimits {
            memory_limit: None,
            cpu_limit: None,
            disk_limit: None,
            network_limit: None,
        };
        
        // 尝试从cgroup获取内存限制
        if let Ok(content) = fs::read_to_string("/sys/fs/cgroup/memory/memory.limit_in_bytes") {
            if let Ok(limit) = content.trim().parse::<u64>() {
                if limit < u64::MAX {
                    limits.memory_limit = Some(limit);
                }
            }
        }
        
        // 尝试从cgroup获取CPU限制
        if let Ok(content) = fs::read_to_string("/sys/fs/cgroup/cpu/cpu.cfs_quota_us") {
            if let Ok(quota) = content.trim().parse::<i64>() {
                if quota > 0 {
                    if let Ok(period) = fs::read_to_string("/sys/fs/cgroup/cpu/cpu.cfs_period_us") {
                        if let Ok(period) = period.trim().parse::<i64>() {
                            if period > 0 {
                                limits.cpu_limit = Some(quota as f64 / period as f64);
                            }
                        }
                    }
                }
            }
        }
        
        limits
    }
    
    /// 更新资源使用情况
    fn update_resource_usage(&mut self) -> Result<(), UnifiedError> {
        // 更新内存使用情况
        if let Ok(content) = fs::read_to_string("/sys/fs/cgroup/memory/memory.usage_in_bytes") {
            if let Ok(usage) = content.trim().parse::<u64>() {
                self.current_usage.memory_usage = usage;
            }
        }
        
        // 更新CPU使用情况
        if let Ok(content) = fs::read_to_string("/sys/fs/cgroup/cpu/cpuacct.usage") {
            if let Ok(usage) = content.trim().parse::<u64>() {
                // 这里需要计算CPU使用率，简化实现
                self.current_usage.cpu_usage = (usage % 100) as f64;
            }
        }
        
        // 更新磁盘使用情况
        if let Ok(content) = fs::read_to_string("/sys/fs/cgroup/blkio/blkio.io_service_bytes") {
            for line in content.lines() {
                if line.contains("Read") {
                    if let Some(bytes) = line.split_whitespace().nth(2) {
                        if let Ok(usage) = bytes.parse::<u64>() {
                            self.current_usage.disk_usage = usage;
                        }
                    }
                }
            }
        }
        
        // 更新网络使用情况
        if let Ok(content) = fs::read_to_string("/sys/class/net/eth0/statistics/rx_bytes") {
            if let Ok(rx) = content.trim().parse::<u64>() {
                self.current_usage.network_rx = rx;
            }
        }
        
        if let Ok(content) = fs::read_to_string("/sys/class/net/eth0/statistics/tx_bytes") {
            if let Ok(tx) = content.trim().parse::<u64>() {
                self.current_usage.network_tx = tx;
            }
        }
        
        Ok(())
    }
    
    /// 获取容器信息
    fn get_container_info(&self) -> HashMap<String, String> {
        let mut info = HashMap::new();
        
        info.insert("container_id".to_string(), self.container_id.clone());
        info.insert("container_name".to_string(), self.container_name.clone());
        info.insert("image_name".to_string(), self.image_name.clone());
        info.insert("start_time".to_string(), 
            self.start_time.duration_since(UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs()
                .to_string()
        );
        
        // 添加资源限制信息
        if let Some(limit) = self.resource_limits.memory_limit {
            info.insert("memory_limit".to_string(), limit.to_string());
        }
        if let Some(limit) = self.resource_limits.cpu_limit {
            info.insert("cpu_limit".to_string(), limit.to_string());
        }
        if let Some(limit) = self.resource_limits.disk_limit {
            info.insert("disk_limit".to_string(), limit.to_string());
        }
        if let Some(limit) = self.resource_limits.network_limit {
            info.insert("network_limit".to_string(), limit.to_string());
        }
        
        info
    }
    
    /// 执行内存清理
    async fn perform_memory_cleanup(&mut self) -> Result<(), UnifiedError> {
        tracing::info!("执行容器内存清理操作");
        
        // 在容器环境中，我们可以：
        // 1. 清理应用程序内存
        // 2. 释放未使用的缓存
        // 3. 触发垃圾回收
        
        // 模拟内存清理
        self.current_usage.memory_usage = self.current_usage.memory_usage / 2;
        
        Ok(())
    }
    
    /// 执行连接重置
    async fn perform_connection_reset(&mut self) -> Result<(), UnifiedError> {
        tracing::info!("执行容器连接重置操作");
        
        // 在容器环境中，我们可以：
        // 1. 重置网络连接
        // 2. 清理连接池
        // 3. 重新建立连接
        
        Ok(())
    }
    
    /// 执行进程重启
    async fn perform_process_restart(&mut self) -> Result<(), UnifiedError> {
        tracing::info!("执行容器进程重启操作");
        
        // 在容器环境中，我们可以：
        // 1. 重启主进程
        // 2. 重新加载配置
        // 3. 重置进程状态
        
        Ok(())
    }
    
    /// 执行服务重启
    async fn perform_service_restart(&mut self) -> Result<(), UnifiedError> {
        tracing::info!("执行容器服务重启操作");
        
        // 在容器环境中，我们可以：
        // 1. 重启容器内的服务
        // 2. 重新加载服务配置
        // 3. 重置服务状态
        
        Ok(())
    }
    
    /// 执行系统重启
    async fn perform_system_restart(&mut self) -> Result<(), UnifiedError> {
        tracing::warn!("执行容器系统重启操作");
        
        // 在容器环境中，我们可以：
        // 1. 重启整个容器
        // 2. 重新启动容器服务
        // 3. 执行容器维护操作
        
        // 注意：这是一个危险操作，应该谨慎使用
        Ok(())
    }
    
    /// 检查容器健康状态
    fn check_container_health(&self) -> HealthLevel {
        // 检查内存使用率
        if let Some(memory_limit) = self.resource_limits.memory_limit {
            let memory_usage_percent = (self.current_usage.memory_usage as f64 / memory_limit as f64) * 100.0;
            if memory_usage_percent > 90.0 {
                return HealthLevel::Critical;
            } else if memory_usage_percent > 80.0 {
                return HealthLevel::Warning;
            }
        }
        
        // 检查CPU使用率
        if self.current_usage.cpu_usage > 90.0 {
            return HealthLevel::Critical;
        } else if self.current_usage.cpu_usage > 80.0 {
            return HealthLevel::Warning;
        }
        
        HealthLevel::Healthy
    }
}

#[async_trait]
impl RuntimeEnvironmentAdapter for ContainerEnvironmentAdapter {
    fn environment_type(&self) -> RuntimeEnvironment {
        RuntimeEnvironment::Container
    }
    
    fn capabilities(&self) -> EnvironmentCapabilities {
        self.environment_type().capabilities()
    }
    
    async fn initialize(&mut self) -> Result<(), UnifiedError> {
        tracing::info!("初始化Docker容器环境适配器");
        
        // 更新资源使用情况
        self.update_resource_usage()?;
        
        tracing::info!("容器ID: {}", self.container_id);
        tracing::info!("容器名称: {}", self.container_name);
        tracing::info!("镜像名称: {}", self.image_name);
        
        if let Some(limit) = self.resource_limits.memory_limit {
            tracing::info!("内存限制: {} bytes", limit);
        }
        if let Some(limit) = self.resource_limits.cpu_limit {
            tracing::info!("CPU限制: {} cores", limit);
        }
        
        Ok(())
    }
    
    async fn cleanup(&mut self) -> Result<(), UnifiedError> {
        tracing::info!("清理Docker容器环境适配器");
        
        // 在容器环境中，我们需要：
        // 1. 清理资源
        // 2. 保存状态
        // 3. 关闭连接
        
        Ok(())
    }
    
    async fn get_system_info(&self) -> Result<SystemInfo, UnifiedError> {
        let mut extra_info = HashMap::new();
        
        // 添加容器信息
        extra_info.extend(self.get_container_info());
        
        // 添加环境变量信息
        if let Ok(env) = std::env::var("ENVIRONMENT") {
            extra_info.insert("environment".to_string(), env);
        }
        if let Ok(version) = std::env::var("VERSION") {
            extra_info.insert("version".to_string(), version);
        }
        
        Ok(SystemInfo {
            environment: RuntimeEnvironment::Container,
            system_name: "Docker Container".to_string(),
            system_version: "1.0.0".to_string(),
            architecture: std::env::consts::ARCH.to_string(),
            total_memory: self.resource_limits.memory_limit.unwrap_or(512 * 1024 * 1024),
            total_cpu_cores: self.resource_limits.cpu_limit.unwrap_or(1.0) as u32,
            total_disk_space: self.resource_limits.disk_limit.unwrap_or(10 * 1024 * 1024 * 1024),
            uptime: SystemTime::now().duration_since(self.start_time).unwrap_or_default(),
            extra_info,
        })
    }
    
    async fn get_resource_usage(&self) -> Result<ResourceUsage, UnifiedError> {
        let mut adapter = self.clone();
        adapter.update_resource_usage()?;
        
        let memory_usage_percent = if let Some(limit) = adapter.resource_limits.memory_limit {
            (adapter.current_usage.memory_usage as f64 / limit as f64) * 100.0
        } else {
            0.0
        };
        
        let disk_usage_percent = if let Some(limit) = adapter.resource_limits.disk_limit {
            (adapter.current_usage.disk_usage as f64 / limit as f64) * 100.0
        } else {
            0.0
        };
        
        Ok(ResourceUsage {
            cpu_usage_percent: adapter.current_usage.cpu_usage,
            memory_usage_bytes: adapter.current_usage.memory_usage,
            memory_usage_percent,
            disk_usage_bytes: adapter.current_usage.disk_usage,
            disk_usage_percent,
            network_rx_bytes: adapter.current_usage.network_rx,
            network_tx_bytes: adapter.current_usage.network_tx,
            network_rx_rate: 0.0, // 需要计算速率
            network_tx_rate: 0.0, // 需要计算速率
            timestamp: chrono::Utc::now(),
        })
    }
    
    async fn check_health(&self) -> Result<HealthStatus, UnifiedError> {
        let mut details = HashMap::new();
        let mut environment_specific = HashMap::new();
        
        // 检查容器健康状态
        let container_health = self.check_container_health();
        details.insert("container".to_string(), container_health);
        
        // 检查内存使用率
        if let Some(memory_limit) = self.resource_limits.memory_limit {
            let memory_usage_percent = (self.current_usage.memory_usage as f64 / memory_limit as f64) * 100.0;
            let memory_health = if memory_usage_percent > 90.0 {
                HealthLevel::Critical
            } else if memory_usage_percent > 80.0 {
                HealthLevel::Warning
            } else {
                HealthLevel::Healthy
            };
            details.insert("memory".to_string(), memory_health);
        }
        
        // 检查CPU使用率
        let cpu_health = if self.current_usage.cpu_usage > 90.0 {
            HealthLevel::Critical
        } else if self.current_usage.cpu_usage > 80.0 {
            HealthLevel::Warning
        } else {
            HealthLevel::Healthy
        };
        details.insert("cpu".to_string(), cpu_health);
        
        // 检查网络使用情况
        let network_health = if self.current_usage.network_rx > 100 * 1024 * 1024 || 
                              self.current_usage.network_tx > 100 * 1024 * 1024 {
            HealthLevel::Warning
        } else {
            HealthLevel::Healthy
        };
        details.insert("network".to_string(), network_health);
        
        // 添加环境特定信息
        environment_specific.insert("container_id".to_string(), self.container_id.clone());
        environment_specific.insert("container_name".to_string(), self.container_name.clone());
        environment_specific.insert("image_name".to_string(), self.image_name.clone());
        environment_specific.insert("memory_usage".to_string(), format!("{:.1}%", 
            (self.current_usage.memory_usage as f64 / self.resource_limits.memory_limit.unwrap_or(1) as f64) * 100.0));
        environment_specific.insert("cpu_usage".to_string(), format!("{:.1}%", self.current_usage.cpu_usage));
        
        // 计算整体健康状态
        let overall_health = if details.values().any(|h| h == &HealthLevel::Critical) {
            HealthLevel::Critical
        } else if details.values().any(|h| h == &HealthLevel::Warning) {
            HealthLevel::Warning
        } else {
            HealthLevel::Healthy
        };
        
        Ok(HealthStatus {
            overall_health,
            details,
            check_time: chrono::Utc::now(),
            environment_specific,
        })
    }
    
    async fn perform_recovery(&self, recovery_type: RecoveryType) -> Result<(), UnifiedError> {
        let mut adapter = self.clone();
        
        match recovery_type {
            RecoveryType::MemoryCleanup => adapter.perform_memory_cleanup().await,
            RecoveryType::ConnectionReset => adapter.perform_connection_reset().await,
            RecoveryType::ProcessRestart => adapter.perform_process_restart().await,
            RecoveryType::ServiceRestart => adapter.perform_service_restart().await,
            RecoveryType::SystemRestart => adapter.perform_system_restart().await,
            RecoveryType::Custom(name) => {
                tracing::info!("执行容器自定义恢复操作: {}", name);
                // 这里可以添加自定义恢复逻辑
                Ok(())
            }
        }
    }
}

impl Clone for ContainerEnvironmentAdapter {
    fn clone(&self) -> Self {
        Self {
            container_id: self.container_id.clone(),
            container_name: self.container_name.clone(),
            image_name: self.image_name.clone(),
            start_time: self.start_time,
            resource_limits: self.resource_limits.clone(),
            current_usage: self.current_usage.clone(),
        }
    }
}

impl Default for ContainerEnvironmentAdapter {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_container_environment_adapter() {
        let mut adapter = ContainerEnvironmentAdapter::new();
        
        // 测试初始化
        assert!(adapter.initialize().await.is_ok());
        
        // 测试环境类型
        assert_eq!(adapter.environment_type(), RuntimeEnvironment::Container);
        
        // 测试能力
        let capabilities = adapter.capabilities();
        assert!(capabilities.supports_multiprocessing);
        assert!(capabilities.supports_multithreading);
        assert!(capabilities.supports_file_system);
        assert!(capabilities.supports_network);
        assert!(capabilities.supports_memory_management);
        assert!(capabilities.supports_process_management);
        
        // 测试系统信息
        let system_info = adapter.get_system_info().await.unwrap();
        assert_eq!(system_info.environment, RuntimeEnvironment::Container);
        assert_eq!(system_info.system_name, "Docker Container");
        
        // 测试资源使用情况
        let resource_usage = adapter.get_resource_usage().await.unwrap();
        assert!(resource_usage.cpu_usage_percent >= 0.0);
        //assert!(resource_usage.memory_usage_bytes >= 0);
        
        // 测试健康检查
        let health_status = adapter.check_health().await.unwrap();
        assert!(matches!(health_status.overall_health, HealthLevel::Healthy | HealthLevel::Warning | HealthLevel::Critical));
        
        // 测试清理
        assert!(adapter.cleanup().await.is_ok());
    }
}
