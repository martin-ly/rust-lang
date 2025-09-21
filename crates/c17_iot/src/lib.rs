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

// 重新导出主要类型和功能
pub use device_management::{
    DeviceManager, DeviceConfig, DeviceType, DeviceStatus, DeviceData,
    SensorCollector, SensorConfig, SensorType, SensorReading, Status, DataQuality,
    DeviceManagementError
};
pub use sensor_network::{
    Route, RoutingAlgorithm, NetworkTopology, NetworkNode, NodeType, Capability,
    SensorNetworkError
};
pub use edge_computing::{
    RuleEngine, Rule, Condition, Action, RuleContext,
    EdgeComputingError
};
pub use security::{
    DeviceAuthenticator, SecurityError
};
pub use monitoring::{
    MetricsCollector, AlertManager, MonitoringDashboard, PerformanceMonitor,
    PerformanceMetric, PerformanceStats, PerformanceAnalysis, PerformanceBottleneck,
    OptimizationRecommendation, PerformanceMonitorConfig, PerformanceThresholds,
    MonitoringError, PerformanceMonitorError
};
pub use embedded_os::{
    EmbeddedOSManager, TaskStatus as EmbeddedTaskStatus, SystemStatus as EmbeddedSystemStatus
};
pub use hardware_abstraction::{
    GPIOManager, HALManager, HALError, HardwareInfo
};
pub use communication::{
    CommunicationManager, ProtocolType, Message, ConnectionStatus as CommConnectionStatus,
    CommunicationError
};
pub use data_storage::{
    StorageManager, StorageType, DataPoint, Query, StorageError,
    StorageConfig, StorageStats, CacheOptimizer, CacheLevel, CacheStrategy,
    CacheItem, CacheStats, CacheConfig, PrewarmingStrategy, CacheOptimizationResult,
    CacheOptimization, CacheOptimizationType, CacheOptimizerError
};
pub use examples_demos::{
    Example, ExampleParameter, ParameterType, CompleteIoTAppExample,
    AdvancedIoTDemo, PerformanceBenchmark
};
pub use types::{
    DeviceType as TypesDeviceType, DeviceStatus as TypesDeviceStatus, 
    ConnectionStatus as TypesConnectionStatus, HealthStatus as TypesHealthStatus,
    SystemStatus as TypesSystemStatus, TaskStatus as TypesTaskStatus
};
