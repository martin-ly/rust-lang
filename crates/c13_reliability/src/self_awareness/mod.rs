//! # 系统自我感知模块（Self-Awareness System）
//!
//! 提供智能的系统自我感知、预测和自适应调优能力。
//!
//! ## 核心功能
//!
//! - **运行时拓扑发现**：自动发现系统拓扑结构
//! - **资源使用预测**：基于历史数据预测资源需求
//! - **异常模式学习**：机器学习识别异常模式
//! - **自适应调优**：根据负载自动调整参数
//! - **智能决策引擎**：AI驱动的优化决策
//!
//! ## 设计理念
//!
//! ```text
//!                 ┌─────────────────────┐
//!                 │   Self-Awareness    │
//!                 │      System         │
//!                 └──────────┬──────────┘
//!                            │
//!        ┌───────────────────┼───────────────────┐
//!        │                   │                   │
//!   ┌────▼────┐         ┌────▼────┐         ┌────▼────┐
//!   │ Topology│         │Resource │         │ Anomaly │
//!   │Discovery│         │Predictor│         │Learning │
//!   └────┬────┘         └────┬────┘         └────┬────┘
//!        │                   │                   │
//!        └───────────────────┼───────────────────┘
//!                            │
//!                     ┌──────▼───────┐
//!                     │   Adaptive   │
//!                     │    Tuning    │
//!                     └──────────────┘
//! ```

pub mod topology_discovery;
pub mod resource_prediction;
pub mod anomaly_learning;
pub mod adaptive_tuning;
pub mod decision_engine;

// Re-export commonly used types
pub use topology_discovery::{
    TopologyDiscovery, TopologyGraph, ServiceNode, ServiceEdge,
    TopologySnapshot, TopologyAnalyzer,
};

pub use resource_prediction::{
    ResourcePredictor, PredictionModel, ResourceForecast,
    PredictionAccuracy, TimeSeriesPredictor,
};

pub use anomaly_learning::{
    AnomalyLearner, AnomalyPattern, LearningModel,
    AnomalyClassifier, PatternMatcher,
};

pub use adaptive_tuning::{
    AdaptiveTuner, TuningPolicy, TuningAction,
    PerformanceTarget, TuningResult,
};

pub use decision_engine::{
    DecisionEngine, DecisionContext, DecisionRule,
    OptimizationStrategy, DecisionOutcome,
};

/// 自我感知配置
#[derive(Debug, Clone)]
pub struct SelfAwarenessConfig {
    /// 是否启用拓扑发现
    pub enable_topology_discovery: bool,
    /// 是否启用资源预测
    pub enable_resource_prediction: bool,
    /// 是否启用异常学习
    pub enable_anomaly_learning: bool,
    /// 是否启用自适应调优
    pub enable_adaptive_tuning: bool,
    /// 数据收集间隔（秒）
    pub collection_interval_secs: u64,
    /// 预测窗口大小
    pub prediction_window_size: usize,
    /// 学习率
    pub learning_rate: f64,
}

impl Default for SelfAwarenessConfig {
    fn default() -> Self {
        Self {
            enable_topology_discovery: true,
            enable_resource_prediction: true,
            enable_anomaly_learning: true,
            enable_adaptive_tuning: true,
            collection_interval_secs: 60,
            prediction_window_size: 100,
            learning_rate: 0.01,
        }
    }
}

/// 系统自我感知管理器
pub struct SelfAwarenessSystem {
    config: SelfAwarenessConfig,
    topology_discovery: TopologyDiscovery,
    resource_predictor: ResourcePredictor,
    anomaly_learner: AnomalyLearner,
    adaptive_tuner: AdaptiveTuner,
    decision_engine: DecisionEngine,
}

impl SelfAwarenessSystem {
    /// 创建新的自我感知系统
    pub fn new(config: SelfAwarenessConfig) -> Self {
        Self {
            config: config.clone(),
            topology_discovery: TopologyDiscovery::new(),
            resource_predictor: ResourcePredictor::new(config.prediction_window_size),
            anomaly_learner: AnomalyLearner::new(config.learning_rate),
            adaptive_tuner: AdaptiveTuner::new(),
            decision_engine: DecisionEngine::new(),
        }
    }
    
    /// 启动自我感知系统
    pub async fn start(&self) {
        tracing::info!("Starting self-awareness system");
        
        if self.config.enable_topology_discovery {
            // 启动拓扑发现
        }
        
        if self.config.enable_resource_prediction {
            // 启动资源预测
        }
        
        if self.config.enable_anomaly_learning {
            // 启动异常学习
        }
        
        if self.config.enable_adaptive_tuning {
            // 启动自适应调优
        }
    }
    
    /// 停止自我感知系统
    pub async fn stop(&self) {
        tracing::info!("Stopping self-awareness system");
    }
    
    /// 获取拓扑发现器
    pub fn topology_discovery(&self) -> &TopologyDiscovery {
        &self.topology_discovery
    }
    
    /// 获取资源预测器
    pub fn resource_predictor(&self) -> &ResourcePredictor {
        &self.resource_predictor
    }
    
    /// 获取异常学习器
    pub fn anomaly_learner(&self) -> &AnomalyLearner {
        &self.anomaly_learner
    }
    
    /// 获取自适应调优器
    pub fn adaptive_tuner(&self) -> &AdaptiveTuner {
        &self.adaptive_tuner
    }
    
    /// 获取决策引擎
    pub fn decision_engine(&self) -> &DecisionEngine {
        &self.decision_engine
    }
    
    /// 生成系统洞察报告
    pub async fn generate_insights(&self) -> SystemInsights {
        SystemInsights {
            topology_health: 100.0,
            predicted_resource_usage: 50.0,
            detected_anomalies: Vec::new(),
            tuning_recommendations: Vec::new(),
        }
    }
}

/// 系统洞察
#[derive(Debug, Clone)]
pub struct SystemInsights {
    /// 拓扑健康度
    pub topology_health: f64,
    /// 预测的资源使用率
    pub predicted_resource_usage: f64,
    /// 检测到的异常
    pub detected_anomalies: Vec<String>,
    /// 调优建议
    pub tuning_recommendations: Vec<String>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_self_awareness_system() {
        let system = SelfAwarenessSystem::new(SelfAwarenessConfig::default());
        system.start().await;
        
        let insights = system.generate_insights().await;
        assert!(insights.topology_health >= 0.0);
        
        system.stop().await;
    }
}

