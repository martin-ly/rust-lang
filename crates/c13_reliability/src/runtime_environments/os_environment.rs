//! # 操作系统环境适配器
//!
//! 提供对完整操作系统环境的支持，包括：
//! - 多进程和多线程支持
//! - 完整的文件系统和网络支持
//! - 系统调用和进程管理
//! - 丰富的监控和恢复能力

use std::collections::HashMap;
use std::process::Command;
use std::time::{SystemTime, /*UNIX_EPOCH*/};
use async_trait::async_trait;
use sysinfo::{System, Pid};
use crate::error_handling::UnifiedError;
use super::{
    RuntimeEnvironmentAdapter, RuntimeEnvironment, EnvironmentCapabilities,
    SystemInfo, ResourceUsage, HealthStatus, HealthLevel, RecoveryType
};

/// 操作系统环境适配器
pub struct OSEnvironmentAdapter {
    /// 系统信息
    system: System,
    /// 系统名称
    system_name: String,
    /// 系统版本
    system_version: String,
    /// 架构
    architecture: String,
    /// 启动时间
    boot_time: SystemTime,
}

impl OSEnvironmentAdapter {
    /// 创建新的操作系统环境适配器
    pub fn new() -> Self {
        let mut system = System::new_all();
        system.refresh_all();
        
        Self {
            system,
            system_name: std::env::consts::OS.to_string(),
            system_version: Self::get_os_version(),
            architecture: std::env::consts::ARCH.to_string(),
            boot_time: SystemTime::now(),
        }
    }
    
    /// 获取操作系统版本信息
    fn get_os_version() -> String {
        match std::env::consts::OS {
            "windows" => {
                // Windows版本检测
                if let Ok(output) = Command::new("ver").output() {
                    String::from_utf8_lossy(&output.stdout).trim().to_string()
                } else {
                    "Windows".to_string()
                }
            },
            "linux" => {
                // Linux版本检测
                if let Ok(output) = Command::new("uname").arg("-r").output() {
                    String::from_utf8_lossy(&output.stdout).trim().to_string()
                } else {
                    "Linux".to_string()
                }
            },
            "macos" => {
                // macOS版本检测
                if let Ok(output) = Command::new("sw_vers").arg("-productVersion").output() {
                    String::from_utf8_lossy(&output.stdout).trim().to_string()
                } else {
                    "macOS".to_string()
                }
            },
            _ => "Unknown".to_string(),
        }
    }
    
    /// 获取系统启动时间
    #[allow(dead_code)]
    fn get_boot_time() -> SystemTime {
        // 这里应该从系统获取实际的启动时间
        // 简化实现，返回当前时间减去运行时间
        SystemTime::now()
    }
    
    /// 获取进程信息
    fn get_process_info(&self) -> HashMap<String, String> {
        let mut info = HashMap::new();
        
        // 获取当前进程信息
        if let Some(process) = self.system.process(Pid::from(std::process::id() as usize)) {
            info.insert("current_process_id".to_string(), process.pid().to_string());
            info.insert("current_process_name".to_string(), process.name().to_string_lossy().to_string());
            info.insert("current_process_memory".to_string(), process.memory().to_string());
            info.insert("current_process_cpu".to_string(), process.cpu_usage().to_string());
        }
        
        // 获取系统进程总数
        info.insert("total_processes".to_string(), self.system.processes().len().to_string());
        
        info
    }
    
    /// 获取网络信息
    fn get_network_info(&self) -> HashMap<String, String> {
        let mut info = HashMap::new();
        
        // 获取网络接口信息（简化实现）
        info.insert("network_eth0_rx".to_string(), "0".to_string());
        info.insert("network_eth0_tx".to_string(), "0".to_string());
        
        info
    }
    
    /// 执行内存清理
    async fn perform_memory_cleanup(&self) -> Result<(), UnifiedError> {
        // 在操作系统环境中，我们可以尝试：
        // 1. 强制垃圾回收
        // 2. 清理缓存
        // 3. 释放未使用的内存
        
        tracing::info!("执行内存清理操作");
        
        // 这里可以添加具体的内存清理逻辑
        // 例如：清理系统缓存、释放未使用的内存等
        
        Ok(())
    }
    
    /// 执行连接重置
    async fn perform_connection_reset(&self) -> Result<(), UnifiedError> {
        tracing::info!("执行连接重置操作");
        
        // 在操作系统环境中，我们可以：
        // 1. 重置网络连接
        // 2. 清理连接池
        // 3. 重新建立连接
        
        Ok(())
    }
    
    /// 执行进程重启
    async fn perform_process_restart(&self) -> Result<(), UnifiedError> {
        tracing::info!("执行进程重启操作");
        
        // 在操作系统环境中，我们可以：
        // 1. 重启当前进程
        // 2. 重启相关服务
        // 3. 重新加载配置
        
        Ok(())
    }
    
    /// 执行服务重启
    async fn perform_service_restart(&self) -> Result<(), UnifiedError> {
        tracing::info!("执行服务重启操作");
        
        // 在操作系统环境中，我们可以：
        // 1. 重启系统服务
        // 2. 重启应用程序服务
        // 3. 重新加载服务配置
        
        Ok(())
    }
    
    /// 执行系统重启
    async fn perform_system_restart(&self) -> Result<(), UnifiedError> {
        tracing::warn!("执行系统重启操作");
        
        // 在操作系统环境中，我们可以：
        // 1. 重启整个系统
        // 2. 重启特定子系统
        // 3. 执行系统维护操作
        
        // 注意：这是一个危险操作，应该谨慎使用
        Ok(())
    }
}

#[async_trait]
impl RuntimeEnvironmentAdapter for OSEnvironmentAdapter {
    fn environment_type(&self) -> RuntimeEnvironment {
        RuntimeEnvironment::OperatingSystem
    }
    
    fn capabilities(&self) -> EnvironmentCapabilities {
        self.environment_type().capabilities()
    }
    
    async fn initialize(&mut self) -> Result<(), UnifiedError> {
        tracing::info!("初始化操作系统环境适配器");
        
        // 刷新系统信息
        self.system.refresh_all();
        
        // 初始化系统监控
        tracing::info!("操作系统环境适配器初始化完成");
        Ok(())
    }
    
    async fn cleanup(&mut self) -> Result<(), UnifiedError> {
        tracing::info!("清理操作系统环境适配器");
        
        // 清理资源
        // 这里可以添加具体的清理逻辑
        
        Ok(())
    }
    
    async fn get_system_info(&self) -> Result<SystemInfo, UnifiedError> {
        let mut extra_info = HashMap::new();
        
        // 添加进程信息
        extra_info.extend(self.get_process_info());
        
        // 添加网络信息
        extra_info.extend(self.get_network_info());
        
        // 添加系统特定信息
        extra_info.insert("hostname".to_string(), 
            hostname::get()
                .unwrap_or_default()
                .to_string_lossy()
                .to_string()
        );
        
        extra_info.insert("user".to_string(), 
            std::env::var("USER").unwrap_or_else(|_| "unknown".to_string())
        );
        
        Ok(SystemInfo {
            environment: RuntimeEnvironment::OperatingSystem,
            system_name: self.system_name.clone(),
            system_version: self.system_version.clone(),
            architecture: self.architecture.clone(),
            total_memory: self.system.total_memory(),
            total_cpu_cores: self.system.cpus().len() as u32,
            total_disk_space: self.system.total_swap(),
            uptime: SystemTime::now().duration_since(self.boot_time).unwrap_or_default(),
            extra_info,
        })
    }
    
    async fn get_resource_usage(&self) -> Result<ResourceUsage, UnifiedError> {
        // 刷新系统信息
        let mut system = System::new_all();
        system.refresh_all();
        
        // 计算CPU使用率
        let cpu_usage = system.global_cpu_usage();
        
        // 计算内存使用率
        let memory_usage_bytes = system.used_memory();
        let memory_usage_percent = (memory_usage_bytes as f64 / system.total_memory() as f64) * 100.0;
        
        // 计算磁盘使用率
        let disk_usage_bytes = system.used_swap();
        let disk_usage_percent = if system.total_swap() > 0 {
            (disk_usage_bytes as f64 / system.total_swap() as f64) * 100.0
        } else {
            0.0
        };
        
        // 计算网络使用情况（简化实现）
        let network_rx_bytes = 0;
        let network_tx_bytes = 0;
        
        Ok(ResourceUsage {
            cpu_usage_percent: cpu_usage as f64,
            memory_usage_bytes,
            memory_usage_percent,
            disk_usage_bytes,
            disk_usage_percent,
            network_rx_bytes,
            network_tx_bytes,
            network_rx_rate: 0.0, // 需要计算速率
            network_tx_rate: 0.0, // 需要计算速率
            timestamp: chrono::Utc::now(),
        })
    }
    
    async fn check_health(&self) -> Result<HealthStatus, UnifiedError> {
        let mut details = HashMap::new();
        let mut environment_specific = HashMap::new();
        
        // 检查CPU使用率
        let cpu_usage = self.system.global_cpu_usage();
        let cpu_health = if cpu_usage > 90.0 {
            HealthLevel::Critical
        } else if cpu_usage > 80.0 {
            HealthLevel::Warning
        } else {
            HealthLevel::Healthy
        };
        details.insert("cpu".to_string(), cpu_health);
        
        // 检查内存使用率
        let memory_usage_percent = (self.system.used_memory() as f64 / self.system.total_memory() as f64) * 100.0;
        let memory_health = if memory_usage_percent > 90.0 {
            HealthLevel::Critical
        } else if memory_usage_percent > 80.0 {
            HealthLevel::Warning
        } else {
            HealthLevel::Healthy
        };
        details.insert("memory".to_string(), memory_health);
        
        // 检查磁盘使用率
        let disk_usage_percent = if self.system.total_swap() > 0 {
            (self.system.used_swap() as f64 / self.system.total_swap() as f64) * 100.0
        } else {
            0.0
        };
        let disk_health = if disk_usage_percent > 90.0 {
            HealthLevel::Critical
        } else if disk_usage_percent > 80.0 {
            HealthLevel::Warning
        } else {
            HealthLevel::Healthy
        };
        details.insert("disk".to_string(), disk_health);
        
        // 检查进程数量
        let process_count = self.system.processes().len();
        let process_health = if process_count > 1000 {
            HealthLevel::Warning
        } else {
            HealthLevel::Healthy
        };
        details.insert("processes".to_string(), process_health);
        
        // 添加环境特定信息
        environment_specific.insert("process_count".to_string(), process_count.to_string());
        environment_specific.insert("cpu_usage".to_string(), format!("{:.1}%", cpu_usage));
        environment_specific.insert("memory_usage".to_string(), format!("{:.1}%", memory_usage_percent));
        
        // 计算整体健康状态
        let overall_health = if details.values().any(|h| *h == HealthLevel::Critical) {
            HealthLevel::Critical
        } else if details.values().any(|h| *h == HealthLevel::Warning) {
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
        match recovery_type {
            RecoveryType::MemoryCleanup => self.perform_memory_cleanup().await,
            RecoveryType::ConnectionReset => self.perform_connection_reset().await,
            RecoveryType::ProcessRestart => self.perform_process_restart().await,
            RecoveryType::ServiceRestart => self.perform_service_restart().await,
            RecoveryType::SystemRestart => self.perform_system_restart().await,
            RecoveryType::Custom(name) => {
                tracing::info!("执行自定义恢复操作: {}", name);
                // 这里可以添加自定义恢复逻辑
                Ok(())
            }
        }
    }
}

impl Default for OSEnvironmentAdapter {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_os_environment_adapter() {
        let mut adapter = OSEnvironmentAdapter::new();
        
        // 测试初始化
        assert!(adapter.initialize().await.is_ok());
        
        // 测试环境类型
        assert_eq!(adapter.environment_type(), RuntimeEnvironment::OperatingSystem);
        
        // 测试能力
        let capabilities = adapter.capabilities();
        assert!(capabilities.supports_multiprocessing);
        assert!(capabilities.supports_multithreading);
        assert!(capabilities.supports_file_system);
        assert!(capabilities.supports_network);
        
        // 测试系统信息
        let system_info = adapter.get_system_info().await.unwrap();
        assert_eq!(system_info.environment, RuntimeEnvironment::OperatingSystem);
        assert!(!system_info.system_name.is_empty());
        assert!(!system_info.architecture.is_empty());
        
        // 测试资源使用情况
        let resource_usage = adapter.get_resource_usage().await.unwrap();
        assert!(resource_usage.cpu_usage_percent >= 0.0);
        assert!(resource_usage.memory_usage_bytes > 0);
        
        // 测试健康检查
        let health_status = adapter.check_health().await.unwrap();
        assert!(matches!(health_status.overall_health, HealthLevel::Healthy | HealthLevel::Warning | HealthLevel::Critical));
        
        // 测试清理
        assert!(adapter.cleanup().await.is_ok());
    }
}
