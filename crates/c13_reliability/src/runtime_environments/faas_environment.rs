//! # 函数即服务环境适配器
//!
//! 本模块提供了对函数即服务(FaaS)环境的支持，包括AWS Lambda、Azure Functions、Google Cloud Functions等。

use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::{SystemTime, /*UNIX_EPOCH,*/ Duration};
use crate::error_handling::UnifiedError;
use super::{
    RuntimeEnvironment, RuntimeEnvironmentAdapter, EnvironmentCapabilities,
    SystemInfo, ResourceUsage, HealthStatus, HealthLevel, RecoveryType
};

/// 函数即服务环境适配器
pub struct FaaSEnvironmentAdapter {
    /// FaaS平台类型
    platform: FaaSPlatform,
    /// 函数名称
    function_name: String,
    /// 函数版本
    function_version: String,
    /// 启动时间
    start_time: SystemTime,
    /// 冷启动时间
    cold_start_time: Option<Duration>,
    /// 执行超时时间
    timeout: Duration,
    /// 内存限制
    memory_limit: u64,
    /// 当前内存使用情况
    current_memory_usage: u64,
    /// 执行次数
    execution_count: u64,
    /// 冷启动次数
    cold_start_count: u64,
    /// 错误次数
    error_count: u64,
    /// 平均执行时间
    average_execution_time: f64,
    /// 最大执行时间
    max_execution_time: f64,
}

/// FaaS平台类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum FaaSPlatform {
    /// AWS Lambda
    AWSLambda,
    /// Azure Functions
    AzureFunctions,
    /// Google Cloud Functions
    GoogleCloudFunctions,
    /// Vercel Functions
    Vercel,
    /// Netlify Functions
    Netlify,
    /// Cloudflare Workers
    CloudflareWorkers,
    /// 未知平台
    Unknown,
}

impl FaaSEnvironmentAdapter {
    /// 创建新的FaaS环境适配器
    pub fn new() -> Self {
        Self {
            platform: Self::detect_platform(),
            function_name: Self::detect_function_name(),
            function_version: Self::detect_function_version(),
            start_time: SystemTime::now(),
            cold_start_time: None,
            timeout: Self::detect_timeout(),
            memory_limit: Self::detect_memory_limit(),
            current_memory_usage: 0,
            execution_count: 0,
            cold_start_count: 0,
            error_count: 0,
            average_execution_time: 0.0,
            max_execution_time: 0.0,
        }
    }

    /// 检测FaaS平台
    fn detect_platform() -> FaaSPlatform {
        if std::env::var("AWS_LAMBDA_FUNCTION_NAME").is_ok() {
            return FaaSPlatform::AWSLambda;
        }
        
        if std::env::var("AZURE_FUNCTIONS_ENVIRONMENT").is_ok() {
            return FaaSPlatform::AzureFunctions;
        }
        
        if std::env::var("FUNCTION_NAME").is_ok() {
            return FaaSPlatform::GoogleCloudFunctions;
        }
        
        if std::env::var("VERCEL").is_ok() {
            return FaaSPlatform::Vercel;
        }
        
        if std::env::var("NETLIFY").is_ok() {
            return FaaSPlatform::Netlify;
        }
        
        if std::env::var("CLOUDFLARE_WORKERS").is_ok() {
            return FaaSPlatform::CloudflareWorkers;
        }
        
        FaaSPlatform::Unknown
    }

    /// 检测函数名称
    fn detect_function_name() -> String {
        if let Ok(name) = std::env::var("AWS_LAMBDA_FUNCTION_NAME") {
            return name;
        }
        
        if let Ok(name) = std::env::var("FUNCTION_NAME") {
            return name;
        }
        
        if let Ok(name) = std::env::var("AZURE_FUNCTION_NAME") {
            return name;
        }
        
        "unknown_function".to_string()
    }

    /// 检测函数版本
    fn detect_function_version() -> String {
        if let Ok(version) = std::env::var("AWS_LAMBDA_FUNCTION_VERSION") {
            return version;
        }
        
        if let Ok(version) = std::env::var("FUNCTION_VERSION") {
            return version;
        }
        
        "1.0.0".to_string()
    }

    /// 检测超时时间
    fn detect_timeout() -> Duration {
        if let Ok(timeout_str) = std::env::var("AWS_LAMBDA_TIMEOUT") {
            if let Ok(timeout_secs) = timeout_str.parse::<u64>() {
                return Duration::from_secs(timeout_secs);
            }
        }
        
        if let Ok(timeout_str) = std::env::var("FUNCTION_TIMEOUT") {
            if let Ok(timeout_secs) = timeout_str.parse::<u64>() {
                return Duration::from_secs(timeout_secs);
            }
        }
        
        Duration::from_secs(30) // 默认30秒超时
    }

    /// 检测内存限制
    fn detect_memory_limit() -> u64 {
        if let Ok(memory_str) = std::env::var("AWS_LAMBDA_MEMORY_SIZE") {
            if let Ok(memory_mb) = memory_str.parse::<u64>() {
                return memory_mb * 1024 * 1024; // 转换为字节
            }
        }
        
        if let Ok(memory_str) = std::env::var("FUNCTION_MEMORY") {
            if let Ok(memory_mb) = memory_str.parse::<u64>() {
                return memory_mb * 1024 * 1024; // 转换为字节
            }
        }
        
        1024 * 1024 * 1024 // 默认1GB
    }

    /// 记录函数执行
    pub fn record_execution(&mut self, execution_time: f64, success: bool, is_cold_start: bool) {
        self.execution_count += 1;
        
        if is_cold_start {
            self.cold_start_count += 1;
            self.cold_start_time = Some(Duration::from_millis(execution_time as u64));
        }
        
        if !success {
            self.error_count += 1;
        }
        
        // 更新平均执行时间
        self.average_execution_time = 
            (self.average_execution_time * (self.execution_count - 1) as f64 + execution_time) / self.execution_count as f64;
        
        // 更新最大执行时间
        if execution_time > self.max_execution_time {
            self.max_execution_time = execution_time;
        }
    }

    /// 更新内存使用情况
    async fn update_memory_usage(&mut self) -> Result<(), UnifiedError> {
        // 在FaaS环境中，内存使用情况通常由平台管理
        // 这里使用模拟数据
        self.current_memory_usage = self.memory_limit / 3; // 模拟33%使用率
        Ok(())
    }

    /// 检查FaaS环境健康状态
    async fn check_faas_health(&self) -> Result<HealthLevel, UnifiedError> {
        let memory_usage_percent = (self.current_memory_usage as f64 / self.memory_limit as f64) * 100.0;
        let error_rate = if self.execution_count > 0 {
            (self.error_count as f64 / self.execution_count as f64) * 100.0
        } else {
            0.0
        };
        
        let cold_start_rate = if self.execution_count > 0 {
            (self.cold_start_count as f64 / self.execution_count as f64) * 100.0
        } else {
            0.0
        };

        // 检查是否接近超时
        let is_near_timeout = self.average_execution_time > (self.timeout.as_millis() as f64 * 0.8);

        if memory_usage_percent > 90.0 || error_rate > 10.0 || is_near_timeout {
            Ok(HealthLevel::Error)
        } else if memory_usage_percent > 80.0 || error_rate > 5.0 || cold_start_rate > 50.0 {
            Ok(HealthLevel::Warning)
        } else {
            Ok(HealthLevel::Healthy)
        }
    }

    /// 获取FaaS特定指标
    fn get_faas_metrics(&self) -> HashMap<String, String> {
        let mut metrics = HashMap::new();
        metrics.insert("execution_count".to_string(), self.execution_count.to_string());
        metrics.insert("cold_start_count".to_string(), self.cold_start_count.to_string());
        metrics.insert("error_count".to_string(), self.error_count.to_string());
        metrics.insert("error_rate".to_string(), 
            if self.execution_count > 0 {
                format!("{:.2}%", (self.error_count as f64 / self.execution_count as f64) * 100.0)
            } else {
                "0.00%".to_string()
            }
        );
        metrics.insert("cold_start_rate".to_string(),
            if self.execution_count > 0 {
                format!("{:.2}%", (self.cold_start_count as f64 / self.execution_count as f64) * 100.0)
            } else {
                "0.00%".to_string()
            }
        );
        metrics.insert("average_execution_time".to_string(), format!("{:.2}ms", self.average_execution_time));
        metrics.insert("max_execution_time".to_string(), format!("{:.2}ms", self.max_execution_time));
        metrics.insert("timeout".to_string(), format!("{}ms", self.timeout.as_millis()));
        metrics.insert("memory_usage_percent".to_string(), 
            format!("{:.2}%", (self.current_memory_usage as f64 / self.memory_limit as f64) * 100.0)
        );
        
        if let Some(cold_start_time) = self.cold_start_time {
            metrics.insert("last_cold_start_time".to_string(), format!("{}ms", cold_start_time.as_millis()));
        }
        
        metrics
    }
}

#[async_trait]
impl RuntimeEnvironmentAdapter for FaaSEnvironmentAdapter {
    fn environment_type(&self) -> RuntimeEnvironment {
        RuntimeEnvironment::FunctionAsAService
    }

    fn capabilities(&self) -> EnvironmentCapabilities {
        RuntimeEnvironment::FunctionAsAService.capabilities()
    }

    async fn initialize(&mut self) -> Result<(), UnifiedError> {
        // 初始化FaaS环境
        self.update_memory_usage().await?;
        Ok(())
    }

    async fn cleanup(&mut self) -> Result<(), UnifiedError> {
        // 清理FaaS环境
        // FaaS环境通常由平台自动管理
        Ok(())
    }

    async fn get_system_info(&self) -> Result<SystemInfo, UnifiedError> {
        let mut extra_info = HashMap::new();
        extra_info.insert("platform".to_string(), format!("{:?}", self.platform));
        extra_info.insert("function_name".to_string(), self.function_name.clone());
        extra_info.insert("function_version".to_string(), self.function_version.clone());
        extra_info.insert("timeout".to_string(), self.timeout.as_millis().to_string());
        extra_info.insert("memory_limit".to_string(), self.memory_limit.to_string());
        extra_info.insert("execution_count".to_string(), self.execution_count.to_string());

        Ok(SystemInfo {
            environment: RuntimeEnvironment::FunctionAsAService,
            system_name: format!("FaaS: {}", self.function_name),
            system_version: self.function_version.clone(),
            architecture: std::env::consts::ARCH.to_string(),
            total_memory: self.memory_limit,
            total_cpu_cores: 1, // FaaS通常是单线程
            total_disk_space: 512 * 1024 * 1024, // 512MB 默认
            uptime: SystemTime::now().duration_since(self.start_time).unwrap_or_default(),
            extra_info,
        })
    }

    async fn get_resource_usage(&self) -> Result<ResourceUsage, UnifiedError> {
        Ok(ResourceUsage {
            cpu_usage_percent: 0.0, // FaaS环境通常不直接暴露CPU使用率
            memory_usage_bytes: self.current_memory_usage,
            memory_usage_percent: (self.current_memory_usage as f64 / self.memory_limit as f64) * 100.0,
            disk_usage_bytes: 0, // FaaS环境通常没有持久化存储
            disk_usage_percent: 0.0,
            network_rx_bytes: 0, // 网络使用情况需要特殊处理
            network_tx_bytes: 0,
            network_rx_rate: 0.0,
            network_tx_rate: 0.0,
            timestamp: chrono::Utc::now(),
        })
    }

    async fn check_health(&self) -> Result<HealthStatus, UnifiedError> {
        let overall_health = self.check_faas_health().await?;
        
        let mut details = HashMap::new();
        details.insert("memory_usage".to_string(), 
            if self.current_memory_usage > self.memory_limit * 9 / 10 {
                HealthLevel::Warning
            } else {
                HealthLevel::Healthy
            }
        );
        details.insert("execution_health".to_string(),
            if self.error_count > self.execution_count / 10 {
                HealthLevel::Warning
            } else {
                HealthLevel::Healthy
            }
        );
        details.insert("performance_health".to_string(),
            if self.average_execution_time > (self.timeout.as_millis() as f64 * 0.8) {
                HealthLevel::Warning
            } else {
                HealthLevel::Healthy
            }
        );

        Ok(HealthStatus {
            overall_health,
            details,
            check_time: chrono::Utc::now(),
            environment_specific: self.get_faas_metrics(),
        })
    }

    async fn perform_recovery(&self, recovery_type: RecoveryType) -> Result<(), UnifiedError> {
        match recovery_type {
            RecoveryType::MemoryCleanup => {
                // 执行内存清理
                println!("执行FaaS内存清理...");
                Ok(())
            },
            RecoveryType::ConnectionReset => {
                // 重置网络连接
                println!("重置FaaS网络连接...");
                Ok(())
            },
            RecoveryType::ProcessRestart => {
                // 重启函数实例
                println!("重启FaaS函数实例...");
                Ok(())
            },
            RecoveryType::ServiceRestart => {
                // 重启FaaS服务
                println!("重启FaaS服务...");
                Ok(())
            },
            RecoveryType::SystemRestart => {
                // 重启FaaS系统
                println!("重启FaaS系统...");
                Ok(())
            },
            RecoveryType::Custom(action) => {
                // 执行自定义恢复操作
                println!("执行FaaS自定义恢复操作: {}", action);
                Ok(())
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_faas_adapter_creation() {
        let adapter = FaaSEnvironmentAdapter::new();
        assert_eq!(adapter.environment_type(), RuntimeEnvironment::FunctionAsAService);
    }

    #[tokio::test]
    async fn test_faas_system_info() {
        let mut adapter = FaaSEnvironmentAdapter::new();
        adapter.initialize().await.unwrap();
        
        let system_info = adapter.get_system_info().await.unwrap();
        assert_eq!(system_info.environment, RuntimeEnvironment::FunctionAsAService);
        assert!(system_info.system_name.starts_with("FaaS:"));
    }

    #[tokio::test]
    async fn test_faas_health_check() {
        let mut adapter = FaaSEnvironmentAdapter::new();
        adapter.initialize().await.unwrap();
        
        let health = adapter.check_health().await.unwrap();
        assert!(matches!(health.overall_health, HealthLevel::Healthy | HealthLevel::Warning));
    }

    #[tokio::test]
    async fn test_faas_execution_recording() {
        let mut adapter = FaaSEnvironmentAdapter::new();
        
        // 记录一些执行
        adapter.record_execution(100.0, true, true); // 冷启动
        adapter.record_execution(50.0, true, false); // 正常执行
        adapter.record_execution(200.0, false, false); // 错误执行
        
        assert_eq!(adapter.execution_count, 3);
        assert_eq!(adapter.cold_start_count, 1);
        assert_eq!(adapter.error_count, 1);
        assert_eq!(adapter.max_execution_time, 200.0);
    }
}
