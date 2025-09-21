//! IoT库 - 基于Rust 1.90的完整IoT开发解决方案
//! 
//! 本库提供了完整的IoT开发功能，包括：
//! - 设备管理和传感器网络
//! - 边缘计算和规则引擎
//! - 通信协议和硬件抽象
//! - 数据存储和安全认证
//! - 监控告警和开发工具
//! - 嵌入式操作系统支持
//! - 示例和演示代码

// 核心模块
pub mod device_management;
pub mod sensor_network;
pub mod edge_computing;
pub mod security;
pub mod monitoring;
// pub mod embedded;
// pub mod observability_enhanced;
// pub mod power;
// pub mod scheduler;
// pub mod security_enhanced;
// pub mod tools;
pub mod types;
// pub mod university_research;

// 新增模块
pub mod embedded_os;
pub mod hardware_abstraction;
pub mod communication;
pub mod data_storage;
pub mod examples_demos;
pub mod error_handling;
pub mod benchmarking;
pub mod protocols;
pub mod memory_optimization;
pub mod ai_integration;
pub mod blockchain_integration;
pub mod quantum_computing;
pub mod edge_computing_advanced;
pub mod iot_security_advanced;
pub mod digital_twin_integration;
pub mod network_5g_integration;
pub mod iot_analytics_advanced;

// 重新导出主要类型和功能
pub use device_management::{
    DeviceManager,
    DeviceConfig,
    DeviceType,
    DeviceStatus,
    DeviceData,
    SensorCollector,
    SensorConfig,
    SensorType,
    SensorReading,
    Status, 
    DataQuality,
    DeviceManagementError,
};
pub use sensor_network::{
    Route, 
    RoutingAlgorithm, 
    NetworkTopology, 
    NetworkNode, 
    NodeType, 
    Capability,
    SensorNetworkError,
};
pub use edge_computing::{
    RuleEngine, 
    Rule, 
    Condition, 
    Action, 
    RuleContext,
    EdgeComputingError
};
pub use security::{
    DeviceAuthenticator,
    SecurityError,
};
pub use monitoring::{
    MetricsCollector, 
    AlertManager, 
    MonitoringDashboard, 
    PerformanceMonitor,
    PerformanceMetric, 
    PerformanceStats, 
    PerformanceAnalysis, 
    PerformanceBottleneck,
    OptimizationRecommendation, 
    PerformanceMonitorConfig, 
    PerformanceThresholds,
    MonitoringError,
    PerformanceMonitorError,
};
pub use embedded_os::{
    EmbeddedOSManager, 
    TaskStatus as EmbeddedTaskStatus, 
    SystemStatus as EmbeddedSystemStatus,
};
pub use hardware_abstraction::{
    GPIOManager, 
    HALManager, 
    HALError, 
    HardwareInfo,
};
pub use communication::{
    ProtocolManager, 
    ProtocolInfo, 
    CommunicationError,
};
pub use error_handling::{
    ErrorHandler, 
    ErrorRecord, 
    ErrorType, 
    ErrorSeverity, 
    RecoveryStrategy, 
    RecoveryConfig,
    ErrorStats, 
    ErrorHandlingError,
};
pub use benchmarking::{
    Benchmarker, 
    BenchmarkConfig, 
    BenchmarkResult, 
    BenchmarkType, 
    ComparisonResult,
    DetailedStats, 
    BenchmarkError,
};
pub use protocols::advanced_protocols::{
    AdvancedProtocolManager, 
    AdvancedProtocolConfig, 
    AdvancedProtocolType, 
    ConnectionStatus,
    Message, 
    MessageType, 
    ConnectionStats, 
    AuthInfo, AdvancedProtocolError,
};
pub use memory_optimization::{
    MemoryOptimizer, 
    MemoryPool, 
    MemoryPoolConfig, 
    MemoryStats, 
    MemoryPoolStats,
    OptimizationConfig, 
    OptimizationResult, 
    MemoryOptimizationError,
};
pub use ai_integration::{
    AIIntegrationManager, 
    AIModelConfig, 
    AIModelType, 
    AIPrediction, 
    AIAnalysis,
    AnalysisType, 
    AnalysisResults, 
    AIConfig, 
    AIStats, 
    AIIntegrationError,
};
pub use blockchain_integration::{
    BlockchainIntegrationManager, 
    BlockchainConfig, 
    BlockchainType, 
    SmartContractConfig,
    BlockchainTransaction, 
    DigitalIdentity, 
    SupplyChainRecord, 
    BlockchainStats,
    BlockchainIntegrationError,
};
pub use quantum_computing::{
    QuantumComputingManager, 
    QuantumConfig, 
    QuantumComputingType, 
    QuantumCircuit,
    QuantumAlgorithmConfig, 
    QuantumTask, 
    QuantumResult, 
    QuantumStats,
    QuantumComputingError,
};
pub use edge_computing_advanced::{
    EdgeComputingManager, 
    EdgeComputingConfig, 
    EdgeNode, 
    EdgeCluster, 
    EdgeTask,
    EdgeNodeType, 
    EdgeTaskType, 
    EdgeNodeStatus, 
    EdgeTaskStatus, 
    TaskPriority,
    ComputeCapacity, 
    NetworkCapacity, 
    StorageCapacity, 
    LoadBalancingStrategy,
    FaultToleranceStrategy, 
    EdgeStats,
};
pub use iot_security_advanced::{
    AdvancedIoTSecurityManager, 
    SecurityConfig, 
    SecurityEvent, 
    ZeroTrustPolicy,
    QuantumEncryptionConfig, 
    SecurityAuditRecord, 
    SecurityThreatType, 
    ThreatLevel,
    SecurityEventType, 
    SecurityEventStatus, 
    SecurityResponseType, 
    ZeroTrustPolicyType,
    QuantumEncryptionAlgorithm, 
    QKDProtocol, 
    AuditType, 
    AuditResult, 
    ComplianceStatus,
    ZeroTrustRule, 
    RuleCondition, 
    RuleAction, 
    ConditionType, 
    ConditionOperator, 
    ActionType, 
    RuleStatus, 
    PolicyStatus, 
    EncryptionStatus,
    SecurityStats
};
pub use digital_twin_integration::{
    DigitalTwinManager,
    DigitalTwinConfig, 
    DigitalTwinModel, 
    RealtimeSyncConfig,
    PredictiveMaintenanceConfig, 
    DigitalTwinEvent, 
    DigitalTwinType, 
    DigitalTwinStatus,
    TwinProperty, 
    PropertyType, 
    PropertyValue, 
    TwinRelationship, 
    RelationshipType,
    TwinBehavior, 
    BehaviorType, 
    BehaviorStatus, 
    SyncMode, 
    ConflictResolutionStrategy,
    MaintenanceType, 
    PredictionModel, 
    TwinEventType, 
    EventSeverity, 
    DigitalTwinStats,
    DigitalTwinError,
};
pub use data_storage::{
    StorageManager, 
    StorageType, 
    DataPoint, 
    Query, 
    StorageError,
    StorageConfig, 
    StorageStats, 
    CacheOptimizer, 
    CacheLevel, 
    CacheStrategy,
    CacheItem, 
    CacheStats, 
    CacheConfig, 
    PrewarmingStrategy, 
    CacheOptimizationResult,
    CacheOptimization, 
    CacheOptimizationType, 
    CacheOptimizerError,
};
pub use examples_demos::{
    Example, 
    ExampleParameter, 
    ParameterType, 
    CompleteIoTAppExample,
    AdvancedIoTDemo, 
    PerformanceBenchmark,
    SecurityTest,
};
pub use types::{
    DeviceType as TypesDeviceType, 
    DeviceStatus as TypesDeviceStatus, 
    ConnectionStatus as TypesConnectionStatus, 
    HealthStatus as TypesHealthStatus,
    SystemStatus as TypesSystemStatus, 
    TaskStatus as TypesTaskStatus,
};
pub use network_5g_integration::{
    Network5GManager, 
    Network5GManagerConfig, 
    Network5GConfig, 
    NetworkSliceConfig,
    EdgeComputing5GConfig, 
    NetworkConnection, 
    Network5GType, 
    Network5GStatus,
    FrequencyBand, 
    NetworkParameters, 
    QoSConfig, 
    QoSLevel, 
    Security5GConfig,
    EncryptionAlgorithm, 
    AuthenticationMethod, 
    KeyManagement, 
    SecurityPolicy,
    PrivacyProtection, 
    SliceType, 
    ServiceType, 
    ResourceAllocation, 
    IsolationLevel,
    SliceStatus, 
    ComputeResources, 
    StorageResources, 
    NetworkResources,
    StorageRedundancy, 
    NetworkQuality, 
    DeploymentStrategy,
    EdgeComputingStatus, 
    ConnectionParameters, 
    Network5GStats, 
    Network5GError,
};
pub use iot_analytics_advanced::{
    AdvancedIoTAnalyticsManager, AnalyticsManagerConfig, DataStreamConfig, AnalyticsTaskConfig,
    RealTimeAnalyticsConfig, PredictiveAnalyticsConfig, AnalyticsResult, AnalyticsStats,
    AnalyticsDataType, AnalyticsProcessingType, AnalyticsAlgorithmType, DataStreamStatus,
    AnalyticsResultStatus, OutputConfig, MonitoringConfig, AlertConfig,
    ValidationConfig, OutputType, OutputFormat, AlertType, AlertCondition, ComparisonOperator,
    LogLevel, ValidationMethod, MonitoringStats, AlertRecord, AlertStatus, AnalyticsError,
    PredictionModel as AnalyticsPredictionModel
};
