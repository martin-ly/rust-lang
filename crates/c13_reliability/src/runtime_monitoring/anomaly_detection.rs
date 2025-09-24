//! 异常检测实现
//!
//! 提供系统异常检测功能，包括统计异常检测、机器学习异常检测等。

use std::sync::Arc;
use std::collections::HashMap;
use std::time::Duration;
use serde::{Serialize, Deserialize};
use tracing::{debug, error, info};

use crate::error_handling::UnifiedError;
use super::MonitoringState;

/// 异常检测配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AnomalyDetectionConfig {
    /// 检测间隔
    pub detection_interval: Duration,
    /// 是否启用异常检测
    pub enabled: bool,
    /// 检测项目
    pub detectors: Vec<AnomalyDetectorItem>,
    /// 告警阈值
    pub alert_thresholds: AnomalyAlertThresholds,
}

impl Default for AnomalyDetectionConfig {
    fn default() -> Self {
        Self {
            detection_interval: Duration::from_secs(60),
            enabled: true,
            detectors: vec![
                AnomalyDetectorItem {
                    name: "statistical".to_string(),
                    detector_type: AnomalyDetectorType::Statistical,
                    enabled: true,
                },
                AnomalyDetectorItem {
                    name: "threshold".to_string(),
                    detector_type: AnomalyDetectorType::Threshold,
                    enabled: true,
                },
            ],
            alert_thresholds: AnomalyAlertThresholds::default(),
        }
    }
}

/// 异常检测项目
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AnomalyDetectorItem {
    /// 检测器名称
    pub name: String,
    /// 检测器类型
    pub detector_type: AnomalyDetectorType,
    /// 是否启用
    pub enabled: bool,
}

/// 异常检测类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AnomalyDetectorType {
    /// 统计异常检测
    Statistical,
    /// 阈值异常检测
    Threshold,
    /// 机器学习异常检测
    MachineLearning,
    /// 自定义检测器
    Custom {
        name: String,
        parameters: HashMap<String, String>,
    },
}

/// 异常告警阈值
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AnomalyAlertThresholds {
    /// 统计异常阈值
    pub statistical_threshold: f64,
    /// 阈值异常阈值
    pub threshold_anomaly_threshold: f64,
    /// 机器学习异常阈值
    pub ml_anomaly_threshold: f64,
}

impl Default for AnomalyAlertThresholds {
    fn default() -> Self {
        Self {
            statistical_threshold: 3.0, // 3个标准差
            threshold_anomaly_threshold: 0.8, // 80%
            ml_anomaly_threshold: 0.7, // 70%
        }
    }
}

/// 异常检测结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AnomalyDetectionResult {
    /// 检测时间
    pub timestamp: chrono::DateTime<chrono::Utc>,
    /// 整体状态
    pub state: MonitoringState,
    /// 检测项目结果
    pub items: Vec<AnomalyDetectorItemResult>,
    /// 总检测数
    pub total_detectors: usize,
    /// 正常检测数
    pub normal_detectors: usize,
    /// 异常检测数
    pub anomaly_detectors: usize,
    /// 检测到的异常数
    pub anomalies_detected: usize,
}

/// 异常检测项目结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AnomalyDetectorItemResult {
    /// 检测器名称
    pub name: String,
    /// 检测器类型
    pub detector_type: AnomalyDetectorType,
    /// 状态
    pub state: MonitoringState,
    /// 异常分数
    pub anomaly_score: f64,
    /// 是否检测到异常
    pub anomaly_detected: bool,
    /// 异常详情
    pub anomaly_details: HashMap<String, String>,
}

/// 异常检测器
pub struct AnomalyDetector {
    config: AnomalyDetectionConfig,
    is_running: std::sync::atomic::AtomicBool,
    last_result: std::sync::Mutex<Option<AnomalyDetectionResult>>,
    detector_handlers: std::sync::Mutex<HashMap<String, Box<dyn AnomalyDetectorHandler + Send + Sync>>>,
    _historical_data: std::sync::Mutex<HashMap<String, Vec<f64>>>,
}

impl AnomalyDetector {
    /// 创建新的异常检测器
    pub fn new(config: AnomalyDetectionConfig) -> Self {
        Self {
            config,
            is_running: std::sync::atomic::AtomicBool::new(false),
            last_result: std::sync::Mutex::new(None),
            detector_handlers: std::sync::Mutex::new(HashMap::new()),
            _historical_data: std::sync::Mutex::new(HashMap::new()),
        }
    }

    /// 启动异常检测
    pub async fn start(&self) -> Result<(), UnifiedError> {
        if self.is_running.load(std::sync::atomic::Ordering::Relaxed) {
            return Ok(());
        }

        if !self.config.enabled {
            debug!("异常检测已禁用");
            return Ok(());
        }

        self.is_running.store(true, std::sync::atomic::Ordering::Relaxed);
        
        // 注册默认检测处理器
        self.register_default_handlers();

        // 启动检测循环
        let detector = Arc::new(self.clone());
        tokio::spawn(async move {
            detector.run_detection_loop().await;
        });

        info!("异常检测器启动完成");
        Ok(())
    }

    /// 停止异常检测
    pub async fn stop(&self) -> Result<(), UnifiedError> {
        self.is_running.store(false, std::sync::atomic::Ordering::Relaxed);
        info!("异常检测器停止完成");
        Ok(())
    }

    /// 检测异常
    pub async fn detect_anomalies(&self) -> Result<AnomalyDetectionResult, UnifiedError> {
        let mut items = Vec::new();
        let mut total_detectors = 0;
        let mut normal_detectors = 0;
        let mut anomaly_detectors = 0;
        let mut anomalies_detected = 0;

        for detector_item in &self.config.detectors {
            if !detector_item.enabled {
                continue;
            }

            total_detectors += 1;
            let item_result = self.detect_item(detector_item).await;
            
            if item_result.anomaly_detected {
                anomaly_detectors += 1;
                anomalies_detected += 1;
            } else {
                normal_detectors += 1;
            }
            
            items.push(item_result);
        }

        let overall_state = self.calculate_overall_state(&items);
        let result = AnomalyDetectionResult {
            timestamp: chrono::Utc::now(),
            state: overall_state,
            items,
            total_detectors,
            normal_detectors,
            anomaly_detectors,
            anomalies_detected,
        };

        // 保存结果
        *self.last_result.lock().unwrap() = Some(result.clone());

        Ok(result)
    }

    /// 检测单个项目
    async fn detect_item(&self, item: &AnomalyDetectorItem) -> AnomalyDetectorItemResult {
        // 直接执行检测，避免复杂的生命周期问题
        let result = match item.name.as_str() {
            "statistical" => StatisticalAnomalyDetectorHandler.detect().await,
            "threshold" => ThresholdAnomalyDetectorHandler.detect().await,
            _ => Ok(AnomalyDetectorItemResult {
                name: item.name.clone(),
                detector_type: item.detector_type.clone(),
                state: MonitoringState::Error,
                anomaly_score: 0.0,
                anomaly_detected: false,
                anomaly_details: HashMap::new(),
            })
        };

        match result {
            Ok(result) => result,
            Err(_error) => AnomalyDetectorItemResult {
                name: item.name.clone(),
                detector_type: item.detector_type.clone(),
                state: MonitoringState::Error,
                anomaly_score: 0.0,
                anomaly_detected: false,
                anomaly_details: HashMap::new(),
            }
        }
    }

    /// 计算整体状态
    fn calculate_overall_state(&self, items: &[AnomalyDetectorItemResult]) -> MonitoringState {
        if items.is_empty() {
            return MonitoringState::Healthy;
        }

        let anomaly_count = items.iter().filter(|item| item.anomaly_detected).count();
        let total_count = items.len();
        
        if anomaly_count == 0 {
            MonitoringState::Healthy
        } else if anomaly_count <= total_count / 2 {
            MonitoringState::Warning
        } else {
            MonitoringState::Error
        }
    }

    /// 注册默认检测处理器
    fn register_default_handlers(&self) {
        let mut handlers = self.detector_handlers.lock().unwrap();
        
        handlers.insert("statistical".to_string(), Box::new(StatisticalAnomalyDetectorHandler));
        handlers.insert("threshold".to_string(), Box::new(ThresholdAnomalyDetectorHandler));
    }

    /// 注册自定义检测处理器
    pub fn register_handler(&self, name: String, handler: Box<dyn AnomalyDetectorHandler + Send + Sync>) {
        let mut handlers = self.detector_handlers.lock().unwrap();
        handlers.insert(name, handler);
    }

    /// 运行检测循环
    async fn run_detection_loop(&self) {
        let mut interval = tokio::time::interval(self.config.detection_interval);
        
        while self.is_running.load(std::sync::atomic::Ordering::Relaxed) {
            interval.tick().await;
            
            if let Err(error) = self.detect_anomalies().await {
                error!("异常检测失败: {}", error);
            }
        }
    }

    /// 获取最后检测结果
    pub fn get_last_result(&self) -> Option<AnomalyDetectionResult> {
        self.last_result.lock().unwrap().clone()
    }

    /// 获取配置
    pub fn get_config(&self) -> &AnomalyDetectionConfig {
        &self.config
    }

    /// 更新配置
    pub fn update_config(&mut self, config: AnomalyDetectionConfig) {
        self.config = config;
    }
}

impl Clone for AnomalyDetector {
    fn clone(&self) -> Self {
        Self {
            config: self.config.clone(),
            is_running: std::sync::atomic::AtomicBool::new(self.is_running.load(std::sync::atomic::Ordering::Relaxed)),
            last_result: std::sync::Mutex::new(self.last_result.lock().unwrap().clone()),
            detector_handlers: std::sync::Mutex::new(HashMap::new()),
            _historical_data: std::sync::Mutex::new(HashMap::new()),
        }
    }
}

/// 异常检测处理器trait
pub trait AnomalyDetectorHandler: Send + Sync {
    /// 执行异常检测
    fn detect(&self) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<AnomalyDetectorItemResult, UnifiedError>> + Send>>;
}

/// 统计异常检测处理器
pub struct StatisticalAnomalyDetectorHandler;

impl AnomalyDetectorHandler for StatisticalAnomalyDetectorHandler {
    fn detect(&self) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<AnomalyDetectorItemResult, UnifiedError>> + Send>> {
        Box::pin(async move {
            let mut details = HashMap::new();
            let mut state = MonitoringState::Healthy;
            let anomaly_score;
            let mut anomaly_detected = false;

            // 模拟统计异常检测
            use rand::Rng;
            let mut rng = rand::rng();
            let current_value = rng.random_range(0.0..10.0);
            
            // 计算统计指标
            let mean = 5.0; // 假设的均值
            let std_dev = 1.0; // 假设的标准差
            let z_score: f64 = (current_value - mean) / std_dev;
            
            details.insert("current_value".to_string(), format!("{:.2}", current_value));
            details.insert("mean".to_string(), format!("{:.2}", mean));
            details.insert("std_dev".to_string(), format!("{:.2}", std_dev));
            details.insert("z_score".to_string(), format!("{:.2}", z_score));
            
            anomaly_score = z_score.abs();
            
            // 判断是否为异常（3个标准差规则）
            if z_score.abs() > 3.0 {
                anomaly_detected = true;
                state = MonitoringState::Error;
                details.insert("anomaly_type".to_string(), "statistical_outlier".to_string());
            }

            Ok(AnomalyDetectorItemResult {
                name: "statistical".to_string(),
                detector_type: AnomalyDetectorType::Statistical,
                state,
                anomaly_score,
                anomaly_detected,
                anomaly_details: details,
            })
        })
    }
}

/// 阈值异常检测处理器
pub struct ThresholdAnomalyDetectorHandler;

impl AnomalyDetectorHandler for ThresholdAnomalyDetectorHandler {
    fn detect(&self) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<AnomalyDetectorItemResult, UnifiedError>> + Send>> {
        Box::pin(async move {
            let mut details = HashMap::new();
            let mut state = MonitoringState::Healthy;
            let anomaly_score;
            let mut anomaly_detected = false;

            // 模拟阈值异常检测
            use rand::Rng;
            let mut rng = rand::rng();
            let current_value = rng.random_range(0.0..1.0);
            
            details.insert("current_value".to_string(), format!("{:.2}", current_value));
            details.insert("threshold".to_string(), "0.8".to_string());
            
            anomaly_score = current_value;
            
            // 判断是否超过阈值
            if current_value > 0.8 {
                anomaly_detected = true;
                state = if current_value > 0.9 {
                    MonitoringState::Error
                } else {
                    MonitoringState::Warning
                };
                details.insert("anomaly_type".to_string(), "threshold_exceeded".to_string());
            }

            Ok(AnomalyDetectorItemResult {
                name: "threshold".to_string(),
                detector_type: AnomalyDetectorType::Threshold,
                state,
                anomaly_score,
                anomaly_detected,
                anomaly_details: details,
            })
        })
    }
}

/// 全局异常检测器
pub struct GlobalAnomalyDetector {
    detector: Arc<AnomalyDetector>,
}

impl GlobalAnomalyDetector {
    /// 创建全局异常检测器
    pub fn new() -> Self {
        Self {
            detector: Arc::new(AnomalyDetector::new(AnomalyDetectionConfig::default())),
        }
    }

    /// 获取异常检测器实例
    pub fn get_detector(&self) -> Arc<AnomalyDetector> {
        self.detector.clone()
    }

    /// 启动全局异常检测
    pub async fn start(&self) -> Result<(), UnifiedError> {
        self.detector.start().await
    }

    /// 停止全局异常检测
    pub async fn stop(&self) -> Result<(), UnifiedError> {
        self.detector.stop().await
    }

    /// 获取全局异常检测状态
    pub async fn detect_anomalies(&self) -> Result<AnomalyDetectionResult, UnifiedError> {
        self.detector.detect_anomalies().await
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn test_anomaly_detection_config_default() {
        let config = AnomalyDetectionConfig::default();
        assert_eq!(config.detection_interval, Duration::from_secs(60));
        assert!(config.enabled);
        assert!(!config.detectors.is_empty());
        assert!(config.alert_thresholds.statistical_threshold > 0.0);
    }

    #[test]
    fn test_anomaly_detector_item() {
        let item = AnomalyDetectorItem {
            name: "test".to_string(),
            detector_type: AnomalyDetectorType::Statistical,
            enabled: true,
        };
        
        assert_eq!(item.name, "test");
        assert!(item.enabled);
    }

    #[test]
    fn test_anomaly_alert_thresholds() {
        let thresholds = AnomalyAlertThresholds::default();
        assert!(thresholds.statistical_threshold > 0.0);
        assert!(thresholds.threshold_anomaly_threshold > 0.0);
        assert!(thresholds.ml_anomaly_threshold > 0.0);
    }

    #[test]
    fn test_anomaly_detector_creation() {
        let config = AnomalyDetectionConfig::default();
        let detector = AnomalyDetector::new(config);
        
        assert!(detector.get_last_result().is_none());
    }

    #[tokio::test]
    async fn test_anomaly_detector_detect() {
        let config = AnomalyDetectionConfig::default();
        let detector = AnomalyDetector::new(config);
        
        let result = detector.detect_anomalies().await;
        assert!(result.is_ok());
        
        let result = result.unwrap();
        assert!(result.total_detectors > 0);
        //assert!(result.normal_detectors >= 0);
        //assert!(result.anomaly_detectors >= 0);
    }

    #[test]
    fn test_anomaly_detection_result() {
        let result = AnomalyDetectionResult {
            timestamp: chrono::Utc::now(),
            state: MonitoringState::Healthy,
            items: Vec::new(),
            total_detectors: 0,
            normal_detectors: 0,
            anomaly_detectors: 0,
            anomalies_detected: 0,
        };
        
        assert_eq!(result.state, MonitoringState::Healthy);
        assert_eq!(result.total_detectors, 0);
    }

    #[test]
    fn test_anomaly_detector_item_result() {
        let result = AnomalyDetectorItemResult {
            name: "test".to_string(),
            detector_type: AnomalyDetectorType::Statistical,
            state: MonitoringState::Healthy,
            anomaly_score: 0.0,
            anomaly_detected: false,
            anomaly_details: HashMap::new(),
        };
        
        assert_eq!(result.name, "test");
        assert_eq!(result.state, MonitoringState::Healthy);
        assert!(!result.anomaly_detected);
    }

    #[test]
    fn test_global_anomaly_detector() {
        let global_detector = GlobalAnomalyDetector::new();
        let detector = global_detector.get_detector();
        
        assert!(detector.get_last_result().is_none());
    }
}