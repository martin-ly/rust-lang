//! 故障注入实现
//!
//! 提供各种故障注入功能，包括网络故障、服务故障、资源故障等。

use std::collections::HashMap;
use std::time::Duration;
use serde::{Serialize, Deserialize};
use tracing::{error, info};

use crate::error_handling::{UnifiedError, ErrorSeverity, ErrorContext};

/// 故障注入配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FaultInjectionConfig {
    /// 是否启用故障注入
    pub enabled: bool,
    /// 故障注入间隔
    pub injection_interval: Duration,
    /// 故障持续时间
    pub fault_duration: Duration,
    /// 故障类型
    pub fault_types: Vec<FaultType>,
    /// 故障概率
    pub fault_probability: f64,
    /// 最大故障数
    pub max_faults: usize,
}

impl Default for FaultInjectionConfig {
    fn default() -> Self {
        Self {
            enabled: false,
            injection_interval: Duration::from_secs(60),
            fault_duration: Duration::from_secs(30),
            fault_types: vec![
                FaultType::NetworkLatency,
                FaultType::ServiceUnavailable,
                FaultType::ResourceExhaustion,
            ],
            fault_probability: 0.1, // 10%的概率
            max_faults: 10,
        }
    }
}

/// 故障类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum FaultType {
    /// 网络延迟
    NetworkLatency,
    /// 网络丢包
    NetworkPacketLoss,
    /// 服务不可用
    ServiceUnavailable,
    /// 服务响应慢
    ServiceSlowResponse,
    /// 资源耗尽
    ResourceExhaustion,
    /// 内存泄漏
    MemoryLeak,
    /// CPU占用高
    HighCpuUsage,
    /// 磁盘空间不足
    DiskSpaceExhaustion,
    /// 数据库连接失败
    DatabaseConnectionFailure,
    /// 自定义故障
    Custom {
        name: String,
        parameters: HashMap<String, String>,
    },
}

/// 故障注入结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FaultInjectionResult {
    /// 测试时间
    pub timestamp: chrono::DateTime<chrono::Utc>,
    /// 总测试数
    pub total_tests: usize,
    /// 成功测试数
    pub successful_tests: usize,
    /// 失败测试数
    pub failed_tests: usize,
    /// 恢复测试数
    pub recovery_tests: usize,
    /// 故障注入详情
    pub fault_details: Vec<FaultDetail>,
    /// 平均恢复时间
    pub average_recovery_time: Duration,
    /// 成功率
    pub success_rate: f64,
    /// 恢复率
    pub recovery_rate: f64,
}

/// 故障详情
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FaultDetail {
    /// 故障ID
    pub fault_id: String,
    /// 故障类型
    pub fault_type: FaultType,
    /// 注入时间
    pub injection_time: chrono::DateTime<chrono::Utc>,
    /// 恢复时间
    pub recovery_time: Option<chrono::DateTime<chrono::Utc>>,
    /// 持续时间
    pub duration: Duration,
    /// 是否成功恢复
    pub recovery_successful: bool,
    /// 故障参数
    pub parameters: HashMap<String, String>,
    /// 影响范围
    pub impact_scope: Vec<String>,
}

/// 故障注入器
pub struct FaultInjector {
    config: FaultInjectionConfig,
    active_faults: std::sync::Mutex<HashMap<String, FaultDetail>>,
    fault_history: std::sync::Mutex<Vec<FaultDetail>>,
    is_running: std::sync::atomic::AtomicBool,
}

impl FaultInjector {
    /// 创建新的故障注入器
    pub fn new(config: FaultInjectionConfig) -> Self {
        Self {
            config,
            active_faults: std::sync::Mutex::new(HashMap::new()),
            fault_history: std::sync::Mutex::new(Vec::new()),
            is_running: std::sync::atomic::AtomicBool::new(false),
        }
    }

    /// 启动故障注入
    pub async fn start(&self) -> Result<(), UnifiedError> {
        if !self.config.enabled {
            return Err(UnifiedError::new(
                "故障注入未启用",
                ErrorSeverity::Medium,
                "fault_injection",
                ErrorContext::new("fault_injection", "start", file!(), line!(), ErrorSeverity::Medium, "fault_injection")
            ));
        }

        self.is_running.store(true, std::sync::atomic::Ordering::Relaxed);
        info!("故障注入器启动");
        Ok(())
    }

    /// 停止故障注入
    pub async fn stop(&self) -> Result<(), UnifiedError> {
        self.is_running.store(false, std::sync::atomic::Ordering::Relaxed);
        
        // 清理所有活动故障
        self.clear_all_faults().await;
        
        info!("故障注入器停止");
        Ok(())
    }

    /// 注入故障
    pub async fn inject_faults(&self) -> Result<FaultInjectionResult, UnifiedError> {
        let timestamp = chrono::Utc::now();
        let mut total_tests = 0;
        let mut successful_tests = 0;
        let mut failed_tests = 0;
        let mut recovery_tests = 0;
        let mut fault_details = Vec::new();
        let mut total_recovery_time = Duration::ZERO;

        // 检查是否应该注入故障
        if self.should_inject_fault() {
            for fault_type in &self.config.fault_types {
                total_tests += 1;
                
                match self.inject_single_fault(fault_type.clone()).await {
                    Ok(fault_detail) => {
                        successful_tests += 1;
                        if fault_detail.recovery_successful {
                            recovery_tests += 1;
                            total_recovery_time += fault_detail.duration;
                        }
                        fault_details.push(fault_detail);
                    }
                    Err(error) => {
                        failed_tests += 1;
                        error!("故障注入失败: {}", error);
                    }
                }
            }
        }

        // 计算成功率
        let success_rate = if total_tests > 0 {
            successful_tests as f64 / total_tests as f64
        } else {
            0.0
        };

        // 计算恢复率
        let recovery_rate = if successful_tests > 0 {
            recovery_tests as f64 / successful_tests as f64
        } else {
            0.0
        };

        // 计算平均恢复时间
        let average_recovery_time = if recovery_tests > 0 {
            total_recovery_time / recovery_tests as u32
        } else {
            Duration::ZERO
        };

        let result = FaultInjectionResult {
            timestamp,
            total_tests,
            successful_tests,
            failed_tests,
            recovery_tests,
            fault_details,
            average_recovery_time,
            success_rate,
            recovery_rate,
        };

        info!("故障注入测试完成，成功率: {:.2}%，恢复率: {:.2}%", 
              success_rate * 100.0, recovery_rate * 100.0);

        Ok(result)
    }

    /// 注入单个故障
    async fn inject_single_fault(&self, fault_type: FaultType) -> Result<FaultDetail, UnifiedError> {
        let fault_id = self.generate_fault_id();
        let injection_time = chrono::Utc::now();
        
        info!("注入故障: {} (ID: {})", self.fault_type_to_string(&fault_type), fault_id);

        // 创建故障详情
        let mut fault_detail = FaultDetail {
            fault_id: fault_id.clone(),
            fault_type: fault_type.clone(),
            injection_time,
            recovery_time: None,
            duration: Duration::ZERO,
            recovery_successful: false,
            parameters: HashMap::new(),
            impact_scope: Vec::new(),
        };

        // 执行故障注入
        match self.execute_fault_injection(&fault_type, &mut fault_detail).await {
            Ok(()) => {
                // 等待故障持续时间
                tokio::time::sleep(self.config.fault_duration).await;
                
                // 尝试恢复
                let recovery_result = self.recover_from_fault(&fault_type, &mut fault_detail).await;
                fault_detail.recovery_successful = recovery_result.is_ok();
                
                if let Ok(recovery_time) = recovery_result {
                    fault_detail.recovery_time = Some(recovery_time);
                    fault_detail.duration = recovery_time.signed_duration_since(injection_time).to_std().unwrap_or(Duration::ZERO);
                }
                
                // 添加到历史记录
                self.add_to_history(fault_detail.clone());
                
                Ok(fault_detail)
            }
            Err(error) => {
                error!("故障注入执行失败: {}", error);
                Err(error)
            }
        }
    }

    /// 执行故障注入
    async fn execute_fault_injection(&self, fault_type: &FaultType, fault_detail: &mut FaultDetail) -> Result<(), UnifiedError> {
        match fault_type {
            FaultType::NetworkLatency => {
                self.inject_network_latency(fault_detail).await
            }
            FaultType::NetworkPacketLoss => {
                self.inject_network_packet_loss(fault_detail).await
            }
            FaultType::ServiceUnavailable => {
                self.inject_service_unavailable(fault_detail).await
            }
            FaultType::ServiceSlowResponse => {
                self.inject_service_slow_response(fault_detail).await
            }
            FaultType::ResourceExhaustion => {
                self.inject_resource_exhaustion(fault_detail).await
            }
            FaultType::MemoryLeak => {
                self.inject_memory_leak(fault_detail).await
            }
            FaultType::HighCpuUsage => {
                self.inject_high_cpu_usage(fault_detail).await
            }
            FaultType::DiskSpaceExhaustion => {
                self.inject_disk_space_exhaustion(fault_detail).await
            }
            FaultType::DatabaseConnectionFailure => {
                self.inject_database_connection_failure(fault_detail).await
            }
            FaultType::Custom { name, parameters } => {
                self.inject_custom_fault(name, parameters, fault_detail).await
            }
        }
    }

    /// 注入网络延迟故障
    async fn inject_network_latency(&self, fault_detail: &mut FaultDetail) -> Result<(), UnifiedError> {
        fault_detail.parameters.insert("latency_ms".to_string(), "1000".to_string());
        fault_detail.impact_scope.push("network".to_string());
        
        // 模拟网络延迟
        tokio::time::sleep(Duration::from_millis(100)).await;
        
        info!("网络延迟故障注入完成");
        Ok(())
    }

    /// 注入网络丢包故障
    async fn inject_network_packet_loss(&self, fault_detail: &mut FaultDetail) -> Result<(), UnifiedError> {
        fault_detail.parameters.insert("packet_loss_rate".to_string(), "0.1".to_string());
        fault_detail.impact_scope.push("network".to_string());
        
        // 模拟网络丢包
        tokio::time::sleep(Duration::from_millis(50)).await;
        
        info!("网络丢包故障注入完成");
        Ok(())
    }

    /// 注入服务不可用故障
    async fn inject_service_unavailable(&self, fault_detail: &mut FaultDetail) -> Result<(), UnifiedError> {
        fault_detail.parameters.insert("service_name".to_string(), "test_service".to_string());
        fault_detail.impact_scope.push("service".to_string());
        
        // 模拟服务不可用
        tokio::time::sleep(Duration::from_millis(200)).await;
        
        info!("服务不可用故障注入完成");
        Ok(())
    }

    /// 注入服务响应慢故障
    async fn inject_service_slow_response(&self, fault_detail: &mut FaultDetail) -> Result<(), UnifiedError> {
        fault_detail.parameters.insert("response_delay_ms".to_string(), "5000".to_string());
        fault_detail.impact_scope.push("service".to_string());
        
        // 模拟服务响应慢
        tokio::time::sleep(Duration::from_millis(150)).await;
        
        info!("服务响应慢故障注入完成");
        Ok(())
    }

    /// 注入资源耗尽故障
    async fn inject_resource_exhaustion(&self, fault_detail: &mut FaultDetail) -> Result<(), UnifiedError> {
        fault_detail.parameters.insert("resource_type".to_string(), "memory".to_string());
        fault_detail.impact_scope.push("resource".to_string());
        
        // 模拟资源耗尽
        tokio::time::sleep(Duration::from_millis(100)).await;
        
        info!("资源耗尽故障注入完成");
        Ok(())
    }

    /// 注入内存泄漏故障
    async fn inject_memory_leak(&self, fault_detail: &mut FaultDetail) -> Result<(), UnifiedError> {
        fault_detail.parameters.insert("leak_rate_mb_per_sec".to_string(), "10".to_string());
        fault_detail.impact_scope.push("memory".to_string());
        
        // 模拟内存泄漏
        tokio::time::sleep(Duration::from_millis(80)).await;
        
        info!("内存泄漏故障注入完成");
        Ok(())
    }

    /// 注入CPU占用高故障
    async fn inject_high_cpu_usage(&self, fault_detail: &mut FaultDetail) -> Result<(), UnifiedError> {
        fault_detail.parameters.insert("cpu_usage_percent".to_string(), "90".to_string());
        fault_detail.impact_scope.push("cpu".to_string());
        
        // 模拟CPU占用高
        tokio::time::sleep(Duration::from_millis(120)).await;
        
        info!("CPU占用高故障注入完成");
        Ok(())
    }

    /// 注入磁盘空间不足故障
    async fn inject_disk_space_exhaustion(&self, fault_detail: &mut FaultDetail) -> Result<(), UnifiedError> {
        fault_detail.parameters.insert("disk_usage_percent".to_string(), "95".to_string());
        fault_detail.impact_scope.push("disk".to_string());
        
        // 模拟磁盘空间不足
        tokio::time::sleep(Duration::from_millis(90)).await;
        
        info!("磁盘空间不足故障注入完成");
        Ok(())
    }

    /// 注入数据库连接失败故障
    async fn inject_database_connection_failure(&self, fault_detail: &mut FaultDetail) -> Result<(), UnifiedError> {
        fault_detail.parameters.insert("connection_pool_size".to_string(), "0".to_string());
        fault_detail.impact_scope.push("database".to_string());
        
        // 模拟数据库连接失败
        tokio::time::sleep(Duration::from_millis(110)).await;
        
        info!("数据库连接失败故障注入完成");
        Ok(())
    }

    /// 注入自定义故障
    async fn inject_custom_fault(&self, name: &str, parameters: &HashMap<String, String>, fault_detail: &mut FaultDetail) -> Result<(), UnifiedError> {
        fault_detail.parameters = parameters.clone();
        fault_detail.impact_scope.push("custom".to_string());
        
        // 模拟自定义故障
        tokio::time::sleep(Duration::from_millis(100)).await;
        
        info!("自定义故障注入完成: {}", name);
        Ok(())
    }

    /// 从故障中恢复
    async fn recover_from_fault(&self, fault_type: &FaultType, _fault_detail: &mut FaultDetail) -> Result<chrono::DateTime<chrono::Utc>, UnifiedError> {
        info!("开始从故障中恢复: {}", self.fault_type_to_string(fault_type));
        
        // 模拟恢复过程
        tokio::time::sleep(Duration::from_millis(200)).await;
        
        let recovery_time = chrono::Utc::now();
        info!("故障恢复完成");
        
        Ok(recovery_time)
    }

    /// 清理所有故障
    async fn clear_all_faults(&self) {
        let mut active_faults = self.active_faults.lock().unwrap();
        active_faults.clear();
        info!("所有活动故障已清理");
    }

    /// 检查是否应该注入故障
    fn should_inject_fault(&self) -> bool {
        use rand::Rng;
        let mut rng = rand::rng();
        rng.random_bool(self.config.fault_probability)
    }

    /// 生成故障ID
    fn generate_fault_id(&self) -> String {
        use rand::Rng;
        let mut rng = rand::rng();
        format!("fault_{}", rng.random_range(0..u32::MAX))
    }

    /// 故障类型转字符串
    fn fault_type_to_string(&self, fault_type: &FaultType) -> String {
        match fault_type {
            FaultType::NetworkLatency => "网络延迟".to_string(),
            FaultType::NetworkPacketLoss => "网络丢包".to_string(),
            FaultType::ServiceUnavailable => "服务不可用".to_string(),
            FaultType::ServiceSlowResponse => "服务响应慢".to_string(),
            FaultType::ResourceExhaustion => "资源耗尽".to_string(),
            FaultType::MemoryLeak => "内存泄漏".to_string(),
            FaultType::HighCpuUsage => "CPU占用高".to_string(),
            FaultType::DiskSpaceExhaustion => "磁盘空间不足".to_string(),
            FaultType::DatabaseConnectionFailure => "数据库连接失败".to_string(),
            FaultType::Custom { name, .. } => format!("自定义故障: {}", name),
        }
    }

    /// 添加到历史记录
    fn add_to_history(&self, fault_detail: FaultDetail) {
        let mut history = self.fault_history.lock().unwrap();
        history.push(fault_detail);
        
        // 保持最近1000个故障记录
        if history.len() > 1000 {
            let len = history.len();
            history.drain(0..len - 1000);
        }
    }

    /// 获取故障历史
    pub fn get_fault_history(&self) -> Vec<FaultDetail> {
        self.fault_history.lock().unwrap().clone()
    }

    /// 获取活动故障
    pub fn get_active_faults(&self) -> Vec<FaultDetail> {
        self.active_faults.lock().unwrap().values().cloned().collect()
    }

    /// 获取配置
    pub fn get_config(&self) -> &FaultInjectionConfig {
        &self.config
    }

    /// 更新配置
    pub fn update_config(&mut self, config: FaultInjectionConfig) {
        self.config = config;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fault_injection_config_default() {
        let config = FaultInjectionConfig::default();
        assert!(!config.enabled);
        assert_eq!(config.injection_interval, Duration::from_secs(60));
        assert_eq!(config.fault_duration, Duration::from_secs(30));
        assert!(!config.fault_types.is_empty());
        assert_eq!(config.fault_probability, 0.1);
        assert_eq!(config.max_faults, 10);
    }

    #[test]
    fn test_fault_type() {
        let fault_type = FaultType::NetworkLatency;
        assert!(matches!(fault_type, FaultType::NetworkLatency));
    }

    #[test]
    fn test_fault_detail() {
        let fault_detail = FaultDetail {
            fault_id: "test_fault".to_string(),
            fault_type: FaultType::NetworkLatency,
            injection_time: chrono::Utc::now(),
            recovery_time: None,
            duration: Duration::ZERO,
            recovery_successful: false,
            parameters: HashMap::new(),
            impact_scope: Vec::new(),
        };
        
        assert_eq!(fault_detail.fault_id, "test_fault");
        assert!(!fault_detail.recovery_successful);
    }

    #[test]
    fn test_fault_injector_creation() {
        let config = FaultInjectionConfig::default();
        let injector = FaultInjector::new(config);
        
        assert!(injector.get_fault_history().is_empty());
        assert!(injector.get_active_faults().is_empty());
    }

    #[test]
    fn test_fault_injection_result() {
        let result = FaultInjectionResult {
            timestamp: chrono::Utc::now(),
            total_tests: 10,
            successful_tests: 8,
            failed_tests: 2,
            recovery_tests: 7,
            fault_details: Vec::new(),
            average_recovery_time: Duration::from_secs(5),
            success_rate: 0.8,
            recovery_rate: 0.875,
        };
        
        assert_eq!(result.total_tests, 10);
        assert_eq!(result.successful_tests, 8);
        assert_eq!(result.failed_tests, 2);
        assert_eq!(result.recovery_tests, 7);
        assert_eq!(result.success_rate, 0.8);
        assert_eq!(result.recovery_rate, 0.875);
    }
}
