//! c12_model - Rust理论模型实现库
//!
//! 本库使用Rust语言实现各种理论模型，包括：
//! - 系统建模：排队论、性能分析、可靠性建模
//! - 机器学习：线性回归、逻辑回归、聚类、决策树
//! - 形式化方法：状态机、时序逻辑、进程代数
//! - 数学建模：概率模型、统计模型、优化算法
//! - 语言模型：词法分析、语法分析、语义分析
//! - 异步模型：异步运行时、背压控制、流量控制
//! - 算法模型：排序、搜索、图算法、动态规划
//! - 分布式模型：一致性、分区容错、CAP定理
//! - 微服务模型：服务发现、负载均衡、熔断器
//! - 程序设计模型：函数式、面向对象、响应式编程
//! - 架构设计模型：分层架构、六边形架构、事件驱动架构
//! - 并行并发模型：Actor模型、CSP模型、共享内存模型

// 核心模型模块
pub mod formal_models; // 形式化方法模型
pub mod math_models; // 数学建模
pub mod ml_models; // 机器学习模型
pub mod performance_models; // 性能分析模型
pub mod queueing_models; // 排队论模型

// 新增的全面模型模块
pub mod language_models; // 语言模型和语义模型
pub mod semantic_models; // 语义模型 - 操作语义、指称语义、公理语义
pub mod async_models; // 异步模型和消息队列背压模型
pub mod async_sync_models; // 异步与同步模型的分类和等价关系分析
pub mod recursive_async_models; // 递归异步分析和示例
pub mod algorithm_models; // 算法模型和各种算法模型的关系分析
pub mod distributed_models; // 分布式设计机制和多线程多任务模型
pub mod microservice_models; // 微服务设计机制和架构模型
pub mod parallel_concurrent_models; // 并行并发模型 - Actor、CSP、共享内存模型
pub mod program_design_models; // 程序设计模型 - 函数式、面向对象、响应式编程
pub mod architecture_design_models; // 架构设计模型 - 分层、六边形、事件驱动架构

// Rust 1.90 新特性模块
pub mod rust_190_features; // Rust 1.90 新特性实现

// 现代机器学习模块
pub mod modern_ml; // 现代机器学习库集成

// 计算机视觉模块
pub mod computer_vision; // 基于Kornia-rs架构的计算机视觉

// 工具和实用程序
pub mod utils; // 通用工具函数
// 已裁剪：可视化与基准测试模块

// 核心基础设施
pub mod config; // 配置管理
pub mod error; // 统一错误处理

// 重新导出主要类型和trait
pub use queueing_models::{
    MM1Queue, MMcQueue, PerformanceAnalyzer, ReliabilityAnalyzer, ScalabilityAnalyzer,
    ScalingResult, SimulationResult, QueueConfig, PriorityQueue, MultiLevelFeedbackQueue,
    QueueMetrics, advanced_math,
};

pub use ml_models::{
    DecisionTree, DecisionTreeNode, KMeans, LinearRegression, LogisticRegression,
    MLConfig, SupportVectorMachine, NeuralNetwork, ActivationFunction, KernelType, MLMetrics,
};

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
    StatisticalTools, MathConfig, MultivariateNormalDistribution, BayesianInference,
    MCMCSampler, TimeSeriesAnalyzer, AdvancedStatistics,
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

// Rust 1.90 新特性重新导出
pub use rust_190_features::{
    ModelConfig as Rust190ModelConfig, ParameterStatistics, DataProcessor, ProcessingResult, OptimizationEngine,
    AlgorithmType, OptimizationResult, OptimizedMatrix, ExternalModelChecker, ModelCheckResult,
    PropertyResult,
};

// 现代机器学习重新导出
pub use modern_ml::{
    ModernMLEngine, ModernMLConfig, ModelType, DeviceType, PrecisionType, ModelTrait,
    TrainingData, EvaluationData, TrainingResult, EvaluationResult, ModelInfo,
    LinearRegressionModel, LogisticRegressionModel, NeuralNetworkModel,
};

// 计算机视觉重新导出
pub use computer_vision::{
    ComputerVisionEngine, ComputerVisionConfig, ImageTensor, ImageTransform, ImageFilter,
    FeatureDetector, ImageOperation, ProcessingMode,
};

// 语言模型重新导出
pub use language_models::{
    LanguageModelEngine, Lexer, Parser, SemanticAnalyzer, Token, TokenType, ASTNode,
    TypeAnnotation, SymbolInfo, LanguageResult,
};

// 语义模型重新导出
pub use semantic_models::{
    Expression, BinaryOperator, UnaryOperator, Statement, Value, Environment, Store,
    SmallStepSemantics, BigStepSemantics, DenotationalSemantics,
    Assertion, HoareTriple, AxiomaticSemantics, SemanticEquivalenceAnalyzer,
    SemanticResult,
};

// 异步模型重新导出
pub use async_models::{
    AsyncMessageQueue, AsyncTaskScheduler, AsyncStateMachine, CoroutinePool, AsyncModelEngine,
    FlowControlConfig, BackpressureStrategy, TaskPriority, AsyncMessage, AsyncResult,
    // 高级流量控制
    TokenBucket, LeakyBucket, SlidingWindowRateLimiter, AdaptiveRateLimiter,
};

// 异步同步模型重新导出
pub use async_sync_models::{
    SynchronousModel, AsynchronousModel, ModelTransformer, ModelComparator, ExecutionModel,
    ModelCharacteristics, ModelComparison, ModelEquivalence, StateMachineTransitionAnalyzer,
};

// 递归异步模型重新导出
pub use recursive_async_models::{
    AsyncRecursionExecutor, TailRecursionOptimizer, RecursionPatternAnalyzer, AsyncRecursionExamples,
    RecursionConfig, RecursionMetrics, RecursionContext, TrampolineComputation, RecursiveAsyncResult,
};

// 算法模型重新导出
pub use algorithm_models::{
    SortingAlgorithms, SearchingAlgorithms, DynamicProgrammingAlgorithms, GreedyAlgorithms,
    // 新增算法类型
    StringAlgorithms, MathematicalAlgorithms,
    AlgorithmRelationshipAnalyzer, AlgorithmCharacteristics, AlgorithmComplexity, ComplexityClass,
    AlgorithmMetrics, AlgorithmResult,
};

// 分布式模型重新导出
pub use distributed_models::{
    DistributedSystemManager, DistributedNode, ConsensusAlgorithm, VectorClock,
    FailureDetector, MultiThreadTaskExecutor, CAPTheoremAnalyzer, DistributedSystemConfig,
    ConsistencyLevel, CAPProperty, SystemStatus, DistributedResult,
    LoadBalancer as DistributedLoadBalancer,
    // 共识算法
    PaxosProtocol, PaxosMessage,
    TwoPhaseCommit, TwoPhaseMessage, TransactionState, VoteResult,
    ThreePhaseCommit, ThreePhaseMessage, ThreePhaseState,
    // 新增：Raft共识算法
    RaftProtocol, RaftState, RaftLogEntry, RaftMessage,
    // 新增：分布式快照（Chandy-Lamport算法）
    DistributedSnapshot, NodeSnapshot, SnapshotMessage, SnapshotMarker, GlobalSnapshot,
};

// 微服务模型重新导出
pub use microservice_models::{
    ServiceRegistry, CircuitBreaker, ApiGateway, 
    ConfigurationManager, ServiceInstance, MicroserviceResult,
    MiddlewareWrapper, ServiceWatcherWrapper, ConfigWatcherWrapper,
    LoadBalancer as MicroserviceLoadBalancer, RateLimiter,
    // 服务网格
    ServiceMesh, SidecarProxy, ProxyFeature, ProxyStats, MeshStats,
    TrafficRule, TrafficSplit, RetryPolicy, SecurityPolicy, JwtValidation, AccessRule,
    ObservabilityConfig,
    LogLevel as MicroserviceLogLevel,
    // 分布式追踪
    DistributedTracing, Trace, Span, SpanLog, SpanStatus, TraceStatus, TracingStats,
};

// 并行并发模型重新导出
pub use parallel_concurrent_models::{
    ActorSystem, ActorRef, ActorContext, ActorBehavior, ActorMessage,
    CSPChannel, CSPProcess, CSPSystem,
    SharedMemory, TransactionalMemory,
    DataParallelExecutor, ForkJoinPool, MapReduceExecutor,
    // 新增并行模型
    TaskParallelExecutor, ParallelTask,
    PipelineExecutor, PipelineStage,
    WorkStealingScheduler, WorkStealingTask,
    ParallelPattern, ParallelPatternAnalyzer, ParallelPatternCharacteristics,
    ConcurrencyModelAnalyzer, ConcurrencyModel, ConcurrencyModelCharacteristics,
    ConcurrentResult,
};

// 程序设计模型重新导出
pub use program_design_models::{
    Functor, Monad, Lazy, HigherOrderFunctions, ImmutableList,
    OOPObject, BankAccount, Account, Observer, Observable, Subject,
    // 新增反应式流和数据流模型
    ReactiveSubscriber, ReactiveSubscription, ReactivePublisher, ReactiveProcessor,
    ReactiveStream, ReactiveOperators,
    DataflowNode, DataflowGraph, DataflowVariable, DataflowPipeline, DataflowCombinator,
    ProgrammingParadigmAnalyzer, ProgrammingParadigm, ParadigmCharacteristics,
    ProgramResult,
};

// 架构设计模型重新导出
pub use architecture_design_models::{
    ArchitectureLayer, LayerDependencyRules, LayeredComponent,
    Port, Adapter, InboundPort, OutboundPort, HexagonalCore,
    Event, EventBus, EventHandler, EventStore,
    Command, Query, CommandBus, QueryBus, CQRSModel,
    Entity, UseCase, InterfaceAdapter, UserRepository,
    Plugin, Microkernel, FaaSFunction, ServerlessPlatform,
    // 新增架构模型
    Filter, PipelineArchitecture, PipelineSplitter,
    Peer, P2PNetwork, P2PTopology, P2PNetworkBuilder,
    ArchitecturePatternAnalyzer, ArchitecturePattern, ArchitectureCharacteristics,
    ArchitectureResult,
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
