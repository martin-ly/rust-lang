//! 运行时监控和自愈
//!
//! 提供系统运行时监控、健康检查、性能监控和自动恢复功能。

use std::sync::Arc;
use serde::{Serialize, Deserialize};
use tracing::info;

use crate::error_handling::{UnifiedError, ErrorSeverity};

pub mod health_check;
pub mod resource_monitor;
pub mod performance_monitor;
pub mod anomaly_detection;
pub mod auto_recovery;

pub use health_check::*;
pub use resource_monitor::*;
pub use performance_monitor::*;
pub use anomaly_detection::*;
pub use auto_recovery::*;

/// 监控配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MonitoringConfig {
    /// 健康检查配置
    pub health_check: HealthCheckConfig,
    /// 资源监控配置
    pub resource_monitor: ResourceMonitorConfig,
    /// 性能监控配置
    pub performance_monitor: PerformanceMonitorConfig,
    /// 异常检测配置
    pub anomaly_detection: AnomalyDetectionConfig,
    /// 自动恢复配置
    pub auto_recovery: AutoRecoveryConfig,
}


impl Default for MonitoringConfig {
    fn default() -> Self {
        Self {
            health_check: HealthCheckConfig::default(),
            resource_monitor: ResourceMonitorConfig::default(),
            performance_monitor: PerformanceMonitorConfig::default(),
            anomaly_detection: AnomalyDetectionConfig::default(),
            auto_recovery: AutoRecoveryConfig::default(),
        }
    }
}

/// 监控状态
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum MonitoringState {
    /// 正常状态
    Healthy,
    /// 警告状态
    Warning,
    /// 错误状态
    Error,
    /// 严重状态
    Critical,
}

impl MonitoringState {
    /// 获取状态的字符串表示
    pub fn as_str(&self) -> &'static str {
        match self {
            MonitoringState::Healthy => "HEALTHY",
            MonitoringState::Warning => "WARNING",
            MonitoringState::Error => "ERROR",
            MonitoringState::Critical => "CRITICAL",
        }
    }

    /// 获取状态的严重程度
    pub fn severity(&self) -> ErrorSeverity {
        match self {
            MonitoringState::Healthy => ErrorSeverity::Low,
            MonitoringState::Warning => ErrorSeverity::Medium,
            MonitoringState::Error => ErrorSeverity::High,
            MonitoringState::Critical => ErrorSeverity::Critical,
        }
    }
}

/// 监控报告
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MonitoringReport {
    /// 报告时间
    pub timestamp: chrono::DateTime<chrono::Utc>,
    /// 整体状态
    pub overall_state: MonitoringState,
    /// 健康检查结果
    pub health_check: HealthCheckResult,
    /// 资源监控结果
    pub resource_monitor: ResourceMonitorResult,
    /// 性能监控结果
    pub performance_monitor: PerformanceMonitorResult,
    /// 异常检测结果
    pub anomaly_detection: AnomalyDetectionResult,
    /// 自动恢复结果
    pub auto_recovery: AutoRecoveryResult,
    /// 建议
    pub recommendations: Vec<String>,
}

/// 监控管理器
pub struct MonitoringManager {
    config: MonitoringConfig,
    health_checker: Arc<HealthChecker>,
    resource_monitor: Arc<ResourceMonitor>,
    performance_monitor: Arc<PerformanceMonitor>,
    anomaly_detector: Arc<AnomalyDetector>,
    auto_recovery: Arc<AutoRecovery>,
    state: std::sync::Mutex<MonitoringState>,
    last_report: std::sync::Mutex<Option<MonitoringReport>>,
}

impl MonitoringManager {
    /// 创建新的监控管理器
    pub fn new(config: MonitoringConfig) -> Self {
        Self {
            health_checker: Arc::new(HealthChecker::new(config.health_check.clone())),
            resource_monitor: Arc::new(ResourceMonitor::new(config.resource_monitor.clone())),
            performance_monitor: Arc::new(PerformanceMonitor::new(config.performance_monitor.clone())),
            anomaly_detector: Arc::new(AnomalyDetector::new(config.anomaly_detection.clone())),
            auto_recovery: Arc::new(AutoRecovery::new(config.auto_recovery.clone())),
            config,
            state: std::sync::Mutex::new(MonitoringState::Healthy),
            last_report: std::sync::Mutex::new(None),
        }
    }

    /// 启动监控
    pub async fn start(&self) -> Result<(), UnifiedError> {
        info!("启动监控管理器");

        // 启动健康检查
        self.health_checker.start().await?;

        // 启动资源监控
        self.resource_monitor.start().await?;

        // 启动性能监控
        self.performance_monitor.start().await?;

        // 启动异常检测
        self.anomaly_detector.start().await?;

        // 启动自动恢复
        self.auto_recovery.start().await?;

        info!("监控管理器启动完成");
        Ok(())
    }

    /// 停止监控
    pub async fn stop(&self) -> Result<(), UnifiedError> {
        info!("停止监控管理器");

        // 停止健康检查
        self.health_checker.stop().await?;

        // 停止资源监控
        self.resource_monitor.stop().await?;

        // 停止性能监控
        self.performance_monitor.stop().await?;

        // 停止异常检测
        self.anomaly_detector.stop().await?;

        // 停止自动恢复
        self.auto_recovery.stop().await?;

        info!("监控管理器停止完成");
        Ok(())
    }

    /// 生成监控报告
    pub async fn generate_report(&self) -> Result<MonitoringReport, UnifiedError> {
        let timestamp = chrono::Utc::now();

        // 获取健康检查结果
        let health_check = self.health_checker.check_health().await?;

        // 获取资源监控结果
        let resource_monitor = self.resource_monitor.get_status().await?;

        // 获取性能监控结果
        let performance_monitor = self.performance_monitor.get_status().await?;

        // 获取异常检测结果
        let anomaly_detection = self.anomaly_detector.detect_anomalies().await?;

        // 获取自动恢复结果
        let auto_recovery = self.auto_recovery.get_status().await?;

        // 计算整体状态
        let overall_state = self.calculate_overall_state(
            &health_check,
            &resource_monitor,
            &performance_monitor,
            &anomaly_detection,
            &auto_recovery,
        );

        // 生成建议
        let recommendations = self.generate_recommendations(
            &health_check,
            &resource_monitor,
            &performance_monitor,
            &anomaly_detection,
            &auto_recovery,
        );

        let report = MonitoringReport {
            timestamp,
            overall_state: overall_state.clone(),
            health_check,
            resource_monitor,
            performance_monitor,
            anomaly_detection,
            auto_recovery,
            recommendations,
        };

        // 更新状态和报告
        *self.state.lock().unwrap() = overall_state;
        *self.last_report.lock().unwrap() = Some(report.clone());

        Ok(report)
    }

    /// 计算整体状态
    fn calculate_overall_state(
        &self,
        health_check: &HealthCheckResult,
        resource_monitor: &ResourceMonitorResult,
        performance_monitor: &PerformanceMonitorResult,
        anomaly_detection: &AnomalyDetectionResult,
        auto_recovery: &AutoRecoveryResult,
    ) -> MonitoringState {
        let states = vec![
            health_check.state.clone(),
            resource_monitor.state.clone(),
            performance_monitor.state.clone(),
            anomaly_detection.state.clone(),
            auto_recovery.state.clone(),
        ];

        // 返回最严重的状态
        if states.contains(&MonitoringState::Critical) {
            MonitoringState::Critical
        } else if states.contains(&MonitoringState::Error) {
            MonitoringState::Error
        } else if states.contains(&MonitoringState::Warning) {
            MonitoringState::Warning
        } else {
            MonitoringState::Healthy
        }
    }

    /// 生成建议
    fn generate_recommendations(
        &self,
        health_check: &HealthCheckResult,
        resource_monitor: &ResourceMonitorResult,
        performance_monitor: &PerformanceMonitorResult,
        anomaly_detection: &AnomalyDetectionResult,
        auto_recovery: &AutoRecoveryResult,
    ) -> Vec<String> {
        let mut recommendations = Vec::new();

        // 基于健康检查结果生成建议
        if health_check.state != MonitoringState::Healthy {
            recommendations.push("检查系统健康状态，确保所有服务正常运行".to_string());
        }

        // 基于资源监控结果生成建议
        if resource_monitor.state != MonitoringState::Healthy {
            recommendations.push("检查系统资源使用情况，考虑优化资源分配".to_string());
        }

        // 基于性能监控结果生成建议
        if performance_monitor.state != MonitoringState::Healthy {
            recommendations.push("检查系统性能指标，考虑性能优化".to_string());
        }

        // 基于异常检测结果生成建议
        if anomaly_detection.state != MonitoringState::Healthy {
            recommendations.push("检查系统异常情况，分析异常原因".to_string());
        }

        // 基于自动恢复结果生成建议
        if auto_recovery.state != MonitoringState::Healthy {
            recommendations.push("检查自动恢复功能，确保恢复策略有效".to_string());
        }

        recommendations
    }

    /// 获取当前状态
    pub fn get_state(&self) -> MonitoringState {
        self.state.lock().unwrap().clone()
    }

    /// 获取最后报告
    pub fn get_last_report(&self) -> Option<MonitoringReport> {
        self.last_report.lock().unwrap().clone()
    }

    /// 获取配置
    pub fn get_config(&self) -> &MonitoringConfig {
        &self.config
    }

    /// 更新配置
    pub fn update_config(&mut self, config: MonitoringConfig) {
        self.config = config;
    }
}

/// 全局监控管理器
pub struct GlobalMonitoringManager {
    manager: Arc<MonitoringManager>,
}

impl GlobalMonitoringManager {
    /// 创建全局监控管理器
    pub fn new() -> Self {
        Self {
            manager: Arc::new(MonitoringManager::new(MonitoringConfig::default())),
        }
    }

    /// 获取监控管理器实例
    pub fn get_manager(&self) -> Arc<MonitoringManager> {
        self.manager.clone()
    }

    /// 启动全局监控
    pub async fn start(&self) -> Result<(), UnifiedError> {
        self.manager.start().await
    }

    /// 停止全局监控
    pub async fn stop(&self) -> Result<(), UnifiedError> {
        self.manager.stop().await
    }

    /// 生成全局监控报告
    pub async fn generate_report(&self) -> Result<MonitoringReport, UnifiedError> {
        self.manager.generate_report().await
    }

    /// 获取全局状态
    pub fn get_state(&self) -> MonitoringState {
        self.manager.get_state()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_monitoring_config_default() {
        let config = MonitoringConfig::default();
        assert!(matches!(config.health_check, HealthCheckConfig { .. }));
        assert!(matches!(config.resource_monitor, ResourceMonitorConfig { .. }));
        assert!(matches!(config.performance_monitor, PerformanceMonitorConfig { .. }));
        assert!(matches!(config.anomaly_detection, AnomalyDetectionConfig { .. }));
        assert!(matches!(config.auto_recovery, AutoRecoveryConfig { .. }));
    }

    #[test]
    fn test_monitoring_state() {
        assert_eq!(MonitoringState::Healthy.as_str(), "HEALTHY");
        assert_eq!(MonitoringState::Warning.as_str(), "WARNING");
        assert_eq!(MonitoringState::Error.as_str(), "ERROR");
        assert_eq!(MonitoringState::Critical.as_str(), "CRITICAL");

        assert_eq!(MonitoringState::Healthy.severity(), ErrorSeverity::Low);
        assert_eq!(MonitoringState::Warning.severity(), ErrorSeverity::Medium);
        assert_eq!(MonitoringState::Error.severity(), ErrorSeverity::High);
        assert_eq!(MonitoringState::Critical.severity(), ErrorSeverity::Critical);
    }

    #[test]
    fn test_monitoring_manager_creation() {
        let config = MonitoringConfig::default();
        let manager = MonitoringManager::new(config);
        
        assert_eq!(manager.get_state(), MonitoringState::Healthy);
        assert!(manager.get_last_report().is_none());
    }

    #[test]
    fn test_global_monitoring_manager() {
        let global_manager = GlobalMonitoringManager::new();
        let state = global_manager.get_state();
        
        assert_eq!(state, MonitoringState::Healthy);
    }
}
