//! 混沌场景实现
//!
//! 提供各种混沌工程场景，包括系统级故障、网络分区、服务降级等。

use std::collections::HashMap;
use std::time::Duration;
use serde::{Serialize, Deserialize};
use tracing::{error, info};

use crate::error_handling::{UnifiedError, ErrorSeverity, ErrorContext};

/// 混沌场景配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ChaosScenariosConfig {
    /// 是否启用混沌场景
    pub enabled: bool,
    /// 场景执行间隔
    pub scenario_interval: Duration,
    /// 场景持续时间
    pub scenario_duration: Duration,
    /// 场景类型
    pub scenario_types: Vec<ChaosScenarioType>,
    /// 场景概率
    pub scenario_probability: f64,
    /// 最大并发场景数
    pub max_concurrent_scenarios: usize,
}

impl Default for ChaosScenariosConfig {
    fn default() -> Self {
        Self {
            enabled: false,
            scenario_interval: Duration::from_secs(300), // 5分钟
            scenario_duration: Duration::from_secs(120), // 2分钟
            scenario_types: vec![
                ChaosScenarioType::NetworkPartition,
                ChaosScenarioType::ServiceDegradation,
                ChaosScenarioType::ResourceExhaustion,
                ChaosScenarioType::CascadingFailure,
            ],
            scenario_probability: 0.05, // 5%的概率
            max_concurrent_scenarios: 3,
        }
    }
}

/// 混沌场景类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ChaosScenarioType {
    /// 网络分区
    NetworkPartition,
    /// 服务降级
    ServiceDegradation,
    /// 资源耗尽
    ResourceExhaustion,
    /// 级联故障
    CascadingFailure,
    /// 数据损坏
    DataCorruption,
    /// 时钟漂移
    ClockSkew,
    /// 依赖服务故障
    DependencyFailure,
    /// 自定义场景
    Custom {
        name: String,
        parameters: HashMap<String, String>,
    },
}

/// 混沌场景结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ChaosScenariosResult {
    /// 测试时间
    pub timestamp: chrono::DateTime<chrono::Utc>,
    /// 总场景数
    pub total_scenarios: usize,
    /// 成功场景数
    pub successful_scenarios: usize,
    /// 失败场景数
    pub failed_scenarios: usize,
    /// 恢复场景数
    pub recovery_scenarios: usize,
    /// 场景详情
    pub scenario_details: Vec<ChaosScenarioDetail>,
    /// 平均恢复时间
    pub average_recovery_time: Duration,
    /// 成功率
    pub success_rate: f64,
    /// 恢复率
    pub recovery_rate: f64,
}

/// 混沌场景详情
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ChaosScenarioDetail {
    /// 场景ID
    pub scenario_id: String,
    /// 场景类型
    pub scenario_type: ChaosScenarioType,
    /// 开始时间
    pub start_time: chrono::DateTime<chrono::Utc>,
    /// 结束时间
    pub end_time: Option<chrono::DateTime<chrono::Utc>>,
    /// 持续时间
    pub duration: Duration,
    /// 是否成功恢复
    pub recovery_successful: bool,
    /// 场景参数
    pub parameters: HashMap<String, String>,
    /// 影响范围
    pub impact_scope: Vec<String>,
    /// 影响程度
    pub impact_severity: ImpactSeverity,
}

/// 影响程度
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ImpactSeverity {
    /// 低
    Low,
    /// 中
    Medium,
    /// 高
    High,
    /// 严重
    Critical,
}

impl ImpactSeverity {
    /// 获取影响程度的数值
    pub fn as_numeric(&self) -> u8 {
        match self {
            ImpactSeverity::Low => 1,
            ImpactSeverity::Medium => 2,
            ImpactSeverity::High => 3,
            ImpactSeverity::Critical => 4,
        }
    }
}

/// 混沌场景执行器
pub struct ChaosScenarios {
    config: ChaosScenariosConfig,
    active_scenarios: std::sync::Mutex<HashMap<String, ChaosScenarioDetail>>,
    scenario_history: std::sync::Mutex<Vec<ChaosScenarioDetail>>,
    is_running: std::sync::atomic::AtomicBool,
}

impl ChaosScenarios {
    /// 创建新的混沌场景执行器
    pub fn new(config: ChaosScenariosConfig) -> Self {
        Self {
            config,
            active_scenarios: std::sync::Mutex::new(HashMap::new()),
            scenario_history: std::sync::Mutex::new(Vec::new()),
            is_running: std::sync::atomic::AtomicBool::new(false),
        }
    }

    /// 启动混沌场景
    pub async fn start(&self) -> Result<(), UnifiedError> {
        if !self.config.enabled {
            return Err(UnifiedError::new(
                "混沌场景未启用",
                ErrorSeverity::Medium,
                "chaos_scenarios",
                ErrorContext::new("chaos_scenarios", "start", file!(), line!(), ErrorSeverity::Medium, "chaos_scenarios")
            ));
        }

        self.is_running.store(true, std::sync::atomic::Ordering::Relaxed);
        info!("混沌场景执行器启动");
        Ok(())
    }

    /// 停止混沌场景
    pub async fn stop(&self) -> Result<(), UnifiedError> {
        self.is_running.store(false, std::sync::atomic::Ordering::Relaxed);
        
        // 清理所有活动场景
        self.clear_all_scenarios().await;
        
        info!("混沌场景执行器停止");
        Ok(())
    }

    /// 运行混沌场景
    pub async fn run_scenarios(&self) -> Result<ChaosScenariosResult, UnifiedError> {
        let timestamp = chrono::Utc::now();
        let mut total_scenarios = 0;
        let mut successful_scenarios = 0;
        let mut failed_scenarios = 0;
        let mut recovery_scenarios = 0;
        let mut scenario_details = Vec::new();
        let mut total_recovery_time = Duration::ZERO;

        // 检查是否应该执行场景
        if self.should_execute_scenario() {
            for scenario_type in &self.config.scenario_types {
                total_scenarios += 1;
                
                match self.execute_single_scenario(scenario_type.clone()).await {
                    Ok(scenario_detail) => {
                        successful_scenarios += 1;
                        if scenario_detail.recovery_successful {
                            recovery_scenarios += 1;
                            total_recovery_time += scenario_detail.duration;
                        }
                        scenario_details.push(scenario_detail);
                    }
                    Err(error) => {
                        failed_scenarios += 1;
                        error!("混沌场景执行失败: {}", error);
                    }
                }
            }
        }

        // 计算成功率
        let success_rate = if total_scenarios > 0 {
            successful_scenarios as f64 / total_scenarios as f64
        } else {
            0.0
        };

        // 计算恢复率
        let recovery_rate = if successful_scenarios > 0 {
            recovery_scenarios as f64 / successful_scenarios as f64
        } else {
            0.0
        };

        // 计算平均恢复时间
        let average_recovery_time = if recovery_scenarios > 0 {
            total_recovery_time / recovery_scenarios as u32
        } else {
            Duration::ZERO
        };

        let result = ChaosScenariosResult {
            timestamp,
            total_scenarios,
            successful_scenarios,
            failed_scenarios,
            recovery_scenarios,
            scenario_details,
            average_recovery_time,
            success_rate,
            recovery_rate,
        };

        info!("混沌场景测试完成，成功率: {:.2}%，恢复率: {:.2}%", 
              success_rate * 100.0, recovery_rate * 100.0);

        Ok(result)
    }

    /// 执行单个场景
    async fn execute_single_scenario(&self, scenario_type: ChaosScenarioType) -> Result<ChaosScenarioDetail, UnifiedError> {
        let scenario_id = self.generate_scenario_id();
        let start_time = chrono::Utc::now();
        
        info!("执行混沌场景: {} (ID: {})", self.scenario_type_to_string(&scenario_type), scenario_id);

        // 创建场景详情
        let mut scenario_detail = ChaosScenarioDetail {
            scenario_id: scenario_id.clone(),
            scenario_type: scenario_type.clone(),
            start_time,
            end_time: None,
            duration: Duration::ZERO,
            recovery_successful: false,
            parameters: HashMap::new(),
            impact_scope: Vec::new(),
            impact_severity: ImpactSeverity::Medium,
        };

        // 执行场景
        match self.execute_scenario(&scenario_type, &mut scenario_detail).await {
            Ok(()) => {
                // 等待场景持续时间
                tokio::time::sleep(self.config.scenario_duration).await;
                
                // 尝试恢复
                let recovery_result = self.recover_from_scenario(&scenario_type, &mut scenario_detail).await;
                scenario_detail.recovery_successful = recovery_result.is_ok();
                
                if let Ok(end_time) = recovery_result {
                    scenario_detail.end_time = Some(end_time);
                    scenario_detail.duration = end_time.signed_duration_since(start_time).to_std().unwrap_or(Duration::ZERO);
                }
                
                // 添加到历史记录
                self.add_to_history(scenario_detail.clone());
                
                Ok(scenario_detail)
            }
            Err(error) => {
                error!("混沌场景执行失败: {}", error);
                Err(error)
            }
        }
    }

    /// 执行场景
    async fn execute_scenario(&self, scenario_type: &ChaosScenarioType, scenario_detail: &mut ChaosScenarioDetail) -> Result<(), UnifiedError> {
        match scenario_type {
            ChaosScenarioType::NetworkPartition => {
                self.execute_network_partition(scenario_detail).await
            }
            ChaosScenarioType::ServiceDegradation => {
                self.execute_service_degradation(scenario_detail).await
            }
            ChaosScenarioType::ResourceExhaustion => {
                self.execute_resource_exhaustion(scenario_detail).await
            }
            ChaosScenarioType::CascadingFailure => {
                self.execute_cascading_failure(scenario_detail).await
            }
            ChaosScenarioType::DataCorruption => {
                self.execute_data_corruption(scenario_detail).await
            }
            ChaosScenarioType::ClockSkew => {
                self.execute_clock_skew(scenario_detail).await
            }
            ChaosScenarioType::DependencyFailure => {
                self.execute_dependency_failure(scenario_detail).await
            }
            ChaosScenarioType::Custom { name, parameters } => {
                self.execute_custom_scenario(name, parameters, scenario_detail).await
            }
        }
    }

    /// 执行网络分区场景
    async fn execute_network_partition(&self, scenario_detail: &mut ChaosScenarioDetail) -> Result<(), UnifiedError> {
        scenario_detail.parameters.insert("partition_type".to_string(), "network".to_string());
        scenario_detail.parameters.insert("partition_duration".to_string(), "120".to_string());
        scenario_detail.impact_scope.push("network".to_string());
        scenario_detail.impact_scope.push("communication".to_string());
        scenario_detail.impact_severity = ImpactSeverity::High;
        
        // 模拟网络分区
        tokio::time::sleep(Duration::from_millis(200)).await;
        
        info!("网络分区场景执行完成");
        Ok(())
    }

    /// 执行服务降级场景
    async fn execute_service_degradation(&self, scenario_detail: &mut ChaosScenarioDetail) -> Result<(), UnifiedError> {
        scenario_detail.parameters.insert("degradation_level".to_string(), "50".to_string());
        scenario_detail.parameters.insert("affected_services".to_string(), "3".to_string());
        scenario_detail.impact_scope.push("service".to_string());
        scenario_detail.impact_scope.push("performance".to_string());
        scenario_detail.impact_severity = ImpactSeverity::Medium;
        
        // 模拟服务降级
        tokio::time::sleep(Duration::from_millis(150)).await;
        
        info!("服务降级场景执行完成");
        Ok(())
    }

    /// 执行资源耗尽场景
    async fn execute_resource_exhaustion(&self, scenario_detail: &mut ChaosScenarioDetail) -> Result<(), UnifiedError> {
        scenario_detail.parameters.insert("resource_type".to_string(), "memory".to_string());
        scenario_detail.parameters.insert("exhaustion_rate".to_string(), "0.8".to_string());
        scenario_detail.impact_scope.push("resource".to_string());
        scenario_detail.impact_scope.push("performance".to_string());
        scenario_detail.impact_severity = ImpactSeverity::Critical;
        
        // 模拟资源耗尽
        tokio::time::sleep(Duration::from_millis(180)).await;
        
        info!("资源耗尽场景执行完成");
        Ok(())
    }

    /// 执行级联故障场景
    async fn execute_cascading_failure(&self, scenario_detail: &mut ChaosScenarioDetail) -> Result<(), UnifiedError> {
        scenario_detail.parameters.insert("failure_chain_length".to_string(), "5".to_string());
        scenario_detail.parameters.insert("failure_propagation_delay".to_string(), "1000".to_string());
        scenario_detail.impact_scope.push("service".to_string());
        scenario_detail.impact_scope.push("system".to_string());
        scenario_detail.impact_severity = ImpactSeverity::Critical;
        
        // 模拟级联故障
        tokio::time::sleep(Duration::from_millis(250)).await;
        
        info!("级联故障场景执行完成");
        Ok(())
    }

    /// 执行数据损坏场景
    async fn execute_data_corruption(&self, scenario_detail: &mut ChaosScenarioDetail) -> Result<(), UnifiedError> {
        scenario_detail.parameters.insert("corruption_type".to_string(), "bit_flip".to_string());
        scenario_detail.parameters.insert("corruption_rate".to_string(), "0.01".to_string());
        scenario_detail.impact_scope.push("data".to_string());
        scenario_detail.impact_scope.push("integrity".to_string());
        scenario_detail.impact_severity = ImpactSeverity::High;
        
        // 模拟数据损坏
        tokio::time::sleep(Duration::from_millis(120)).await;
        
        info!("数据损坏场景执行完成");
        Ok(())
    }

    /// 执行时钟漂移场景
    async fn execute_clock_skew(&self, scenario_detail: &mut ChaosScenarioDetail) -> Result<(), UnifiedError> {
        scenario_detail.parameters.insert("skew_amount_seconds".to_string(), "300".to_string());
        scenario_detail.parameters.insert("skew_direction".to_string(), "forward".to_string());
        scenario_detail.impact_scope.push("time".to_string());
        scenario_detail.impact_scope.push("synchronization".to_string());
        scenario_detail.impact_severity = ImpactSeverity::Medium;
        
        // 模拟时钟漂移
        tokio::time::sleep(Duration::from_millis(100)).await;
        
        info!("时钟漂移场景执行完成");
        Ok(())
    }

    /// 执行依赖服务故障场景
    async fn execute_dependency_failure(&self, scenario_detail: &mut ChaosScenarioDetail) -> Result<(), UnifiedError> {
        scenario_detail.parameters.insert("dependency_name".to_string(), "database".to_string());
        scenario_detail.parameters.insert("failure_type".to_string(), "timeout".to_string());
        scenario_detail.impact_scope.push("dependency".to_string());
        scenario_detail.impact_scope.push("service".to_string());
        scenario_detail.impact_severity = ImpactSeverity::High;
        
        // 模拟依赖服务故障
        tokio::time::sleep(Duration::from_millis(160)).await;
        
        info!("依赖服务故障场景执行完成");
        Ok(())
    }

    /// 执行自定义场景
    async fn execute_custom_scenario(&self, name: &str, parameters: &HashMap<String, String>, scenario_detail: &mut ChaosScenarioDetail) -> Result<(), UnifiedError> {
        scenario_detail.parameters = parameters.clone();
        scenario_detail.impact_scope.push("custom".to_string());
        scenario_detail.impact_severity = ImpactSeverity::Medium;
        
        // 模拟自定义场景
        tokio::time::sleep(Duration::from_millis(140)).await;
        
        info!("自定义场景执行完成: {}", name);
        Ok(())
    }

    /// 从场景中恢复
    #[allow(unused_variables)]
    async fn recover_from_scenario(&self, scenario_type: &ChaosScenarioType, scenario_detail: &mut ChaosScenarioDetail) -> Result<chrono::DateTime<chrono::Utc>, UnifiedError> {
        info!("开始从混沌场景中恢复: {}", self.scenario_type_to_string(scenario_type));
        
        // 模拟恢复过程
        tokio::time::sleep(Duration::from_millis(300)).await;
        
        let end_time = chrono::Utc::now();
        info!("混沌场景恢复完成");
        
        Ok(end_time)
    }

    /// 清理所有场景
    async fn clear_all_scenarios(&self) {
        let mut active_scenarios = self.active_scenarios.lock().unwrap();
        active_scenarios.clear();
        info!("所有活动场景已清理");
    }

    /// 检查是否应该执行场景
    fn should_execute_scenario(&self) -> bool {
        use rand::Rng;
        let mut rng = rand::rng();
        rng.random_bool(self.config.scenario_probability)
    }

    /// 生成场景ID
    fn generate_scenario_id(&self) -> String {
        use rand::Rng;
        let mut rng = rand::rng();
        format!("scenario_{}", rng.random::<u32>())
    }

    /// 场景类型转字符串
    fn scenario_type_to_string(&self, scenario_type: &ChaosScenarioType) -> String {
        match scenario_type {
            ChaosScenarioType::NetworkPartition => "网络分区".to_string(),
            ChaosScenarioType::ServiceDegradation => "服务降级".to_string(),
            ChaosScenarioType::ResourceExhaustion => "资源耗尽".to_string(),
            ChaosScenarioType::CascadingFailure => "级联故障".to_string(),
            ChaosScenarioType::DataCorruption => "数据损坏".to_string(),
            ChaosScenarioType::ClockSkew => "时钟漂移".to_string(),
            ChaosScenarioType::DependencyFailure => "依赖服务故障".to_string(),
            ChaosScenarioType::Custom { name, .. } => format!("自定义场景: {}", name),
        }
    }

    /// 添加到历史记录
    fn add_to_history(&self, scenario_detail: ChaosScenarioDetail) {
        let mut history = self.scenario_history.lock().unwrap();
        history.push(scenario_detail);
        
        // 保持最近1000个场景记录
        let len = history.len();
        if len > 1000 {
            history.drain(0..len - 1000);
        }
    }

    /// 获取场景历史
    pub fn get_scenario_history(&self) -> Vec<ChaosScenarioDetail> {
        self.scenario_history.lock().unwrap().clone()
    }

    /// 获取活动场景
    pub fn get_active_scenarios(&self) -> Vec<ChaosScenarioDetail> {
        self.active_scenarios.lock().unwrap().values().cloned().collect()
    }

    /// 获取配置
    pub fn get_config(&self) -> &ChaosScenariosConfig {
        &self.config
    }

    /// 更新配置
    pub fn update_config(&mut self, config: ChaosScenariosConfig) {
        self.config = config;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_chaos_scenarios_config_default() {
        let config = ChaosScenariosConfig::default();
        assert!(!config.enabled);
        assert_eq!(config.scenario_interval, Duration::from_secs(300));
        assert_eq!(config.scenario_duration, Duration::from_secs(120));
        assert!(!config.scenario_types.is_empty());
        assert_eq!(config.scenario_probability, 0.05);
        assert_eq!(config.max_concurrent_scenarios, 3);
    }

    #[test]
    fn test_chaos_scenario_type() {
        let scenario_type = ChaosScenarioType::NetworkPartition;
        assert!(matches!(scenario_type, ChaosScenarioType::NetworkPartition));
    }

    #[test]
    fn test_impact_severity() {
        assert_eq!(ImpactSeverity::Low.as_numeric(), 1);
        assert_eq!(ImpactSeverity::Medium.as_numeric(), 2);
        assert_eq!(ImpactSeverity::High.as_numeric(), 3);
        assert_eq!(ImpactSeverity::Critical.as_numeric(), 4);
    }

    #[test]
    fn test_chaos_scenario_detail() {
        let scenario_detail = ChaosScenarioDetail {
            scenario_id: "test_scenario".to_string(),
            scenario_type: ChaosScenarioType::NetworkPartition,
            start_time: chrono::Utc::now(),
            end_time: None,
            duration: Duration::ZERO,
            recovery_successful: false,
            parameters: HashMap::new(),
            impact_scope: Vec::new(),
            impact_severity: ImpactSeverity::Medium,
        };
        
        assert_eq!(scenario_detail.scenario_id, "test_scenario");
        assert!(!scenario_detail.recovery_successful);
        assert_eq!(scenario_detail.impact_severity.as_numeric(), 2);
    }

    #[test]
    fn test_chaos_scenarios_creation() {
        let config = ChaosScenariosConfig::default();
        let scenarios = ChaosScenarios::new(config);
        
        assert!(scenarios.get_scenario_history().is_empty());
        assert!(scenarios.get_active_scenarios().is_empty());
    }

    #[test]
    fn test_chaos_scenarios_result() {
        let result = ChaosScenariosResult {
            timestamp: chrono::Utc::now(),
            total_scenarios: 5,
            successful_scenarios: 4,
            failed_scenarios: 1,
            recovery_scenarios: 3,
            scenario_details: Vec::new(),
            average_recovery_time: Duration::from_secs(10),
            success_rate: 0.8,
            recovery_rate: 0.75,
        };
        
        assert_eq!(result.total_scenarios, 5);
        assert_eq!(result.successful_scenarios, 4);
        assert_eq!(result.failed_scenarios, 1);
        assert_eq!(result.recovery_scenarios, 3);
        assert_eq!(result.success_rate, 0.8);
        assert_eq!(result.recovery_rate, 0.75);
    }
}
