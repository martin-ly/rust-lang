//! 混沌工程模块
//!
//! 提供混沌工程测试功能，包括故障注入、弹性测试和恢复验证。

use std::sync::Arc;
use serde::{Serialize, Deserialize};
use tracing::info;

use crate::error_handling::{UnifiedError, ErrorSeverity, ErrorContext};

pub mod fault_injection;
pub mod chaos_scenarios;
pub mod resilience_testing;
pub mod recovery_testing;

pub use fault_injection::*;
pub use chaos_scenarios::*;
pub use resilience_testing::*;
pub use recovery_testing::*;

/// 混沌工程配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ChaosEngineeringConfig {
    /// 是否启用混沌工程
    pub enabled: bool,
    /// 故障注入配置
    pub fault_injection: FaultInjectionConfig,
    /// 混沌场景配置
    pub chaos_scenarios: ChaosScenariosConfig,
    /// 弹性测试配置
    pub resilience_testing: ResilienceTestingConfig,
    /// 恢复测试配置
    pub recovery_testing: RecoveryTestingConfig,
}

impl Default for ChaosEngineeringConfig {
    fn default() -> Self {
        Self {
            enabled: false, // 默认禁用，需要显式启用
            fault_injection: FaultInjectionConfig::default(),
            chaos_scenarios: ChaosScenariosConfig::default(),
            resilience_testing: ResilienceTestingConfig::default(),
            recovery_testing: RecoveryTestingConfig::default(),
        }
    }
}


/// 混沌工程状态
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum ChaosEngineeringState {
    /// 未启动
    Stopped,
    /// 运行中
    Running,
    /// 暂停
    Paused,
    /// 错误
    Error,
}

impl ChaosEngineeringState {
    /// 获取状态的字符串表示
    pub fn as_str(&self) -> &'static str {
        match self {
            ChaosEngineeringState::Stopped => "STOPPED",
            ChaosEngineeringState::Running => "RUNNING",
            ChaosEngineeringState::Paused => "PAUSED",
            ChaosEngineeringState::Error => "ERROR",
        }
    }
}

/// 混沌工程结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ChaosEngineeringResult {
    /// 测试时间
    pub timestamp: chrono::DateTime<chrono::Utc>,
    /// 测试状态
    pub state: ChaosEngineeringState,
    /// 故障注入结果
    pub fault_injection: FaultInjectionResult,
    /// 混沌场景结果
    pub chaos_scenarios: ChaosScenariosResult,
    /// 弹性测试结果
    pub resilience_testing: ResilienceTestingResult,
    /// 恢复测试结果
    pub recovery_testing: RecoveryTestingResult,
    /// 总体评估
    pub overall_assessment: OverallAssessment,
}

/// 总体评估
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OverallAssessment {
    /// 系统弹性评分
    pub resilience_score: f64,
    /// 恢复能力评分
    pub recovery_score: f64,
    /// 整体评分
    pub overall_score: f64,
    /// 建议
    pub recommendations: Vec<String>,
}

/// 混沌工程管理器
pub struct ChaosEngineeringManager {
    config: ChaosEngineeringConfig,
    state: std::sync::Mutex<ChaosEngineeringState>,
    fault_injector: Arc<FaultInjector>,
    chaos_scenarios: Arc<ChaosScenarios>,
    resilience_tester: Arc<ResilienceTester>,
    recovery_tester: Arc<RecoveryTester>,
    last_result: std::sync::Mutex<Option<ChaosEngineeringResult>>,
}

impl ChaosEngineeringManager {
    /// 创建新的混沌工程管理器
    pub fn new(config: ChaosEngineeringConfig) -> Self {
        Self {
            fault_injector: Arc::new(FaultInjector::new(config.fault_injection.clone())),
            chaos_scenarios: Arc::new(ChaosScenarios::new(config.chaos_scenarios.clone())),
            resilience_tester: Arc::new(ResilienceTester::new(config.resilience_testing.clone())),
            recovery_tester: Arc::new(RecoveryTester::new(config.recovery_testing.clone())),
            config,
            state: std::sync::Mutex::new(ChaosEngineeringState::Stopped),
            last_result: std::sync::Mutex::new(None),
        }
    }

    /// 启动混沌工程测试
    pub async fn start(&self) -> Result<(), UnifiedError> {
        if !self.config.enabled {
            return Err(UnifiedError::new(
                "混沌工程未启用",
                ErrorSeverity::Medium,
                "chaos_engineering",
                ErrorContext::new("chaos_engineering", "start", file!(), line!(), ErrorSeverity::Medium, "chaos_engineering")
            ));
        }

        *self.state.lock().unwrap() = ChaosEngineeringState::Running;
        info!("混沌工程测试启动");
        Ok(())
    }

    /// 停止混沌工程测试
    pub async fn stop(&self) -> Result<(), UnifiedError> {
        *self.state.lock().unwrap() = ChaosEngineeringState::Stopped;
        info!("混沌工程测试停止");
        Ok(())
    }

    /// 暂停混沌工程测试
    pub async fn pause(&self) -> Result<(), UnifiedError> {
        *self.state.lock().unwrap() = ChaosEngineeringState::Paused;
        info!("混沌工程测试暂停");
        Ok(())
    }

    /// 恢复混沌工程测试
    pub async fn resume(&self) -> Result<(), UnifiedError> {
        *self.state.lock().unwrap() = ChaosEngineeringState::Running;
        info!("混沌工程测试恢复");
        Ok(())
    }

    /// 执行混沌工程测试
    pub async fn run_tests(&self) -> Result<ChaosEngineeringResult, UnifiedError> {
        let timestamp = chrono::Utc::now();
        let current_state = self.get_state();

        if current_state != ChaosEngineeringState::Running {
            return Err(UnifiedError::new(
                "混沌工程测试未在运行状态",
                ErrorSeverity::Medium,
                "chaos_engineering",
                ErrorContext::new("chaos_engineering", "run_tests", file!(), line!(), ErrorSeverity::Medium, "chaos_engineering")
            ));
        }

        info!("开始执行混沌工程测试");

        // 执行故障注入测试
        let fault_injection_result = self.fault_injector.inject_faults().await?;

        // 执行混沌场景测试
        let chaos_scenarios_result = self.chaos_scenarios.run_scenarios().await?;

        // 执行弹性测试
        let resilience_testing_result = self.resilience_tester.test_resilience().await?;

        // 执行恢复测试
        let recovery_testing_result = self.recovery_tester.test_recovery().await?;

        // 计算总体评估
        let overall_assessment = self.calculate_overall_assessment(
            &fault_injection_result,
            &chaos_scenarios_result,
            &resilience_testing_result,
            &recovery_testing_result,
        );

        let result = ChaosEngineeringResult {
            timestamp,
            state: current_state,
            fault_injection: fault_injection_result,
            chaos_scenarios: chaos_scenarios_result,
            resilience_testing: resilience_testing_result,
            recovery_testing: recovery_testing_result,
            overall_assessment,
        };

        // 保存结果
        *self.last_result.lock().unwrap() = Some(result.clone());

        info!("混沌工程测试完成，总体评分: {:.2}", result.overall_assessment.overall_score);
        Ok(result)
    }

    /// 计算总体评估
    fn calculate_overall_assessment(
        &self,
        fault_injection: &FaultInjectionResult,
        chaos_scenarios: &ChaosScenariosResult,
        resilience_testing: &ResilienceTestingResult,
        recovery_testing: &RecoveryTestingResult,
    ) -> OverallAssessment {
        // 计算弹性评分
        let resilience_score = self.calculate_resilience_score(
            fault_injection,
            chaos_scenarios,
            resilience_testing,
        );

        // 计算恢复评分
        let recovery_score = self.calculate_recovery_score(
            fault_injection,
            chaos_scenarios,
            recovery_testing,
        );

        // 计算整体评分
        let overall_score = (resilience_score + recovery_score) / 2.0;

        // 生成建议
        let recommendations = self.generate_recommendations(
            resilience_score,
            recovery_score,
            overall_score,
        );

        OverallAssessment {
            resilience_score,
            recovery_score,
            overall_score,
            recommendations,
        }
    }

    /// 计算弹性评分
    fn calculate_resilience_score(
        &self,
        fault_injection: &FaultInjectionResult,
        chaos_scenarios: &ChaosScenariosResult,
        resilience_testing: &ResilienceTestingResult,
    ) -> f64 {
        let mut score = 0.0;
        let mut weight = 0.0;

        // 故障注入测试权重
        if fault_injection.total_tests > 0 {
            let fault_score = fault_injection.successful_tests as f64 / fault_injection.total_tests as f64;
            score += fault_score * 0.3;
            weight += 0.3;
        }

        // 混沌场景测试权重
        if chaos_scenarios.total_scenarios > 0 {
            let scenario_score = chaos_scenarios.successful_scenarios as f64 / chaos_scenarios.total_scenarios as f64;
            score += scenario_score * 0.4;
            weight += 0.4;
        }

        // 弹性测试权重
        if resilience_testing.total_tests > 0 {
            let resilience_score = resilience_testing.successful_tests as f64 / resilience_testing.total_tests as f64;
            score += resilience_score * 0.3;
            weight += 0.3;
        }

        if weight > 0.0 {
            score / weight
        } else {
            0.0
        }
    }

    /// 计算恢复评分
    fn calculate_recovery_score(
        &self,
        fault_injection: &FaultInjectionResult,
        chaos_scenarios: &ChaosScenariosResult,
        recovery_testing: &RecoveryTestingResult,
    ) -> f64 {
        let mut score = 0.0;
        let mut weight = 0.0;

        // 故障注入恢复权重
        if fault_injection.total_tests > 0 {
            let recovery_score = fault_injection.recovery_tests as f64 / fault_injection.total_tests as f64;
            score += recovery_score * 0.4;
            weight += 0.4;
        }

        // 混沌场景恢复权重
        if chaos_scenarios.total_scenarios > 0 {
            let scenario_recovery_score = chaos_scenarios.recovery_scenarios as f64 / chaos_scenarios.total_scenarios as f64;
            score += scenario_recovery_score * 0.3;
            weight += 0.3;
        }

        // 恢复测试权重
        if recovery_testing.total_tests > 0 {
            let recovery_test_score = recovery_testing.successful_tests as f64 / recovery_testing.total_tests as f64;
            score += recovery_test_score * 0.3;
            weight += 0.3;
        }

        if weight > 0.0 {
            score / weight
        } else {
            0.0
        }
    }

    /// 生成建议
    fn generate_recommendations(
        &self,
        resilience_score: f64,
        recovery_score: f64,
        overall_score: f64,
    ) -> Vec<String> {
        let mut recommendations = Vec::new();

        if overall_score < 0.6 {
            recommendations.push("系统整体弹性不足，建议加强容错机制设计".to_string());
        }

        if resilience_score < 0.6 {
            recommendations.push("系统弹性能力不足，建议增加断路器、重试等机制".to_string());
        }

        if recovery_score < 0.6 {
            recommendations.push("系统恢复能力不足，建议优化自动恢复策略".to_string());
        }

        if overall_score >= 0.8 {
            recommendations.push("系统弹性表现良好，建议定期进行混沌工程测试".to_string());
        }

        if recommendations.is_empty() {
            recommendations.push("系统弹性表现正常，建议继续监控和维护".to_string());
        }

        recommendations
    }

    /// 获取当前状态
    pub fn get_state(&self) -> ChaosEngineeringState {
        self.state.lock().unwrap().clone()
    }

    /// 获取最后测试结果
    pub fn get_last_result(&self) -> Option<ChaosEngineeringResult> {
        self.last_result.lock().unwrap().clone()
    }

    /// 获取配置
    pub fn get_config(&self) -> &ChaosEngineeringConfig {
        &self.config
    }

    /// 更新配置
    pub fn update_config(&mut self, config: ChaosEngineeringConfig) {
        self.config = config;
    }
}

/// 全局混沌工程管理器
pub struct GlobalChaosEngineeringManager {
    manager: Arc<ChaosEngineeringManager>,
}

impl GlobalChaosEngineeringManager {
    /// 创建全局混沌工程管理器
    pub fn new() -> Self {
        Self {
            manager: Arc::new(ChaosEngineeringManager::new(ChaosEngineeringConfig::default())),
        }
    }

    /// 获取混沌工程管理器实例
    pub fn get_manager(&self) -> Arc<ChaosEngineeringManager> {
        self.manager.clone()
    }

    /// 启动全局混沌工程测试
    pub async fn start(&self) -> Result<(), UnifiedError> {
        self.manager.start().await
    }

    /// 停止全局混沌工程测试
    pub async fn stop(&self) -> Result<(), UnifiedError> {
        self.manager.stop().await
    }

    /// 执行全局混沌工程测试
    pub async fn run_tests(&self) -> Result<ChaosEngineeringResult, UnifiedError> {
        self.manager.run_tests().await
    }

    /// 获取全局状态
    pub fn get_state(&self) -> ChaosEngineeringState {
        self.manager.get_state()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_chaos_engineering_config_default() {
        let config = ChaosEngineeringConfig::default();
        assert!(!config.enabled); // 默认禁用
        assert!(matches!(config.fault_injection, FaultInjectionConfig { .. }));
        assert!(matches!(config.chaos_scenarios, ChaosScenariosConfig { .. }));
        assert!(matches!(config.resilience_testing, ResilienceTestingConfig { .. }));
        assert!(matches!(config.recovery_testing, RecoveryTestingConfig { .. }));
    }

    #[test]
    fn test_chaos_engineering_state() {
        assert_eq!(ChaosEngineeringState::Stopped.as_str(), "STOPPED");
        assert_eq!(ChaosEngineeringState::Running.as_str(), "RUNNING");
        assert_eq!(ChaosEngineeringState::Paused.as_str(), "PAUSED");
        assert_eq!(ChaosEngineeringState::Error.as_str(), "ERROR");
    }

    #[test]
    fn test_chaos_engineering_manager_creation() {
        let config = ChaosEngineeringConfig::default();
        let manager = ChaosEngineeringManager::new(config);
        
        assert_eq!(manager.get_state(), ChaosEngineeringState::Stopped);
        assert!(manager.get_last_result().is_none());
    }

    #[test]
    fn test_overall_assessment() {
        let assessment = OverallAssessment {
            resilience_score: 0.8,
            recovery_score: 0.7,
            overall_score: 0.75,
            recommendations: vec!["建议1".to_string(), "建议2".to_string()],
        };
        
        assert_eq!(assessment.resilience_score, 0.8);
        assert_eq!(assessment.recovery_score, 0.7);
        assert_eq!(assessment.overall_score, 0.75);
        assert_eq!(assessment.recommendations.len(), 2);
    }

    #[test]
    fn test_global_chaos_engineering_manager() {
        let global_manager = GlobalChaosEngineeringManager::new();
        let state = global_manager.get_state();
        
        assert_eq!(state, ChaosEngineeringState::Stopped);
    }
}
