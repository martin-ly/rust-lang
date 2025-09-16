//! c18_model - Rust理论模型实现库
//!
//! 本库使用Rust语言实现各种理论模型，包括：
//! - 系统建模：排队论、性能分析、可靠性建模
//! - 机器学习：线性回归、逻辑回归、聚类、决策树
//! - 形式化方法：状态机、时序逻辑、进程代数
//! - 数学建模：概率模型、统计模型、优化算法

// 核心模型模块
pub mod formal_models; // 形式化方法模型
pub mod math_models; // 数学建模
pub mod ml_models; // 机器学习模型
pub mod performance_models;
pub mod queueing_models; // 排队论模型 // 性能分析模型

// 工具和实用程序
pub mod utils; // 通用工具函数
// 已裁剪：可视化与基准测试模块

// 核心基础设施
pub mod config; // 配置管理
pub mod error; // 统一错误处理

// 重新导出主要类型和trait
pub use queueing_models::{
    MM1Queue, MMcQueue, PerformanceAnalyzer, ReliabilityAnalyzer, ScalabilityAnalyzer,
    ScalingResult, SimulationResult,
};

pub use ml_models::{DecisionTree, DecisionTreeNode, KMeans, LinearRegression, LogisticRegression};

pub use formal_models::{
    FiniteStateMachine,
    FormalMethodsToolkit,
    ModelCheckingResult,
    ProcessAlgebraInterpreter,
    ProcessTerm,
    State,
    TemporalFormula,
    TemporalModelChecker,
    Transition,
    advanced_tools,
    // 高级形式化方法
    formal_languages,
    implementations,
    transformation,
    verification,
};

pub use math_models::{
    ExponentialDistribution, GradientDescentOptimizer, IntegrationMethod, MonteCarloSimulator,
    NormalDistribution, NumericalIntegrator, PoissonDistribution, ProbabilityDistribution,
    StatisticalTools,
};

pub use performance_models::{
    CapacityAnalysis, CapacityPlanner, LoadGenerator, LoadPattern, PerformanceMetrics,
    PerformancePredictor, PerformanceRequirements, PredictionModel, Priority,
    ScalingRecommendation, SystemConfiguration,
};

pub use utils::{
    DataUtils, LogLevel, LogMessage, Logger, MathUtils, StatisticsUtils, ValidationUtils,
};

// 核心基础设施重新导出
pub use config::{
    ConfigManager, LogLevel as ConfigLogLevel, ModelConfig, PerformanceConfig, PrecisionConfig,
    VisualizationConfig,
};

pub use error::{
    ContextualError, ContextualResult, ErrorContext, ErrorHandler, ErrorSeverity, ModelError,
    Result as ModelResult,
};

// 已裁剪：可视化、基准测试与标准合规模块的对外导出

// 并发/异步统一能力抽象（占位模块，不引入运行时依赖）
pub mod runtime_abi;

/// Rust理论模型实现库的主要入口点
pub struct ModelSystemAnalyzer {
    pub queueing_models: queueing_models::MM1Queue,
    pub ml_models: ml_models::LinearRegression,
    pub formal_models: formal_models::FormalMethodsToolkit,
    pub math_models: math_models::StatisticalTools,
    pub performance_models: PerformanceAnalyzer,
}

impl ModelSystemAnalyzer {
    /// 创建新的模型系统分析器
    pub fn new() -> Self {
        Self {
            queueing_models: queueing_models::MM1Queue::new(1.0, 2.0),
            ml_models: ml_models::LinearRegression::new(0.01, 1000),
            formal_models: formal_models::FormalMethodsToolkit::new(),
            math_models: math_models::StatisticalTools,
            performance_models: PerformanceAnalyzer::new(),
        }
    }

    /// 分析排队论模型
    pub fn analyze_queueing_models(&self) -> &queueing_models::MM1Queue {
        &self.queueing_models
    }

    /// 分析机器学习模型
    pub fn analyze_ml_models(&self) -> &ml_models::LinearRegression {
        &self.ml_models
    }

    /// 分析形式化方法模型
    pub fn analyze_formal_models(&self) -> &formal_models::FormalMethodsToolkit {
        &self.formal_models
    }

    /// 分析数学模型
    pub fn analyze_math_models(&self) -> &math_models::StatisticalTools {
        &self.math_models
    }

    /// 分析性能模型
    pub fn analyze_performance_models(&self) -> &PerformanceAnalyzer {
        &self.performance_models
    }

    // 已裁剪：基准测试入口
}

impl Default for ModelSystemAnalyzer {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_model_system_analyzer_creation() {
        let analyzer = ModelSystemAnalyzer::new();
        assert_eq!(analyzer.queueing_models.arrival_rate, 1.0);
        assert_eq!(analyzer.queueing_models.service_rate, 2.0);
    }

    #[test]
    fn test_model_system_analyzer_default() {
        let analyzer = ModelSystemAnalyzer::default();
        assert_eq!(analyzer.queueing_models.arrival_rate, 1.0);
    }

    #[test]
    fn test_queueing_models_analysis() {
        let analyzer = ModelSystemAnalyzer::new();
        let queue = analyzer.analyze_queueing_models();
        assert_eq!(queue.utilization(), 0.5);
    }

    #[test]
    fn test_ml_models_analysis() {
        let analyzer = ModelSystemAnalyzer::new();
        let ml_model = analyzer.analyze_ml_models();
        assert_eq!(ml_model.learning_rate, 0.01);
        assert_eq!(ml_model.max_iterations, 1000);
    }

    #[test]
    fn test_formal_models_analysis() {
        let analyzer = ModelSystemAnalyzer::new();
        let formal_models = analyzer.analyze_formal_models();
        assert!(formal_models.verify_algebraic_property("associativity"));
    }

    #[test]
    fn test_math_models_analysis() {
        let analyzer = ModelSystemAnalyzer::new();
        let _math_models = analyzer.analyze_math_models();
        let data = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        assert_eq!(math_models::StatisticalTools::mean(&data), 3.0);
    }

    #[test]
    fn test_performance_models_analysis() {
        let analyzer = ModelSystemAnalyzer::new();
        let performance_models = analyzer.analyze_performance_models();
        // 测试性能分析器创建
        assert_eq!(performance_models.average_metric("test"), None);
    }

    #[test]
    fn test_benchmarks() {
        // 已裁剪：基准测试相关测试
        assert!(true);
    }
}
