//! # IoT系统核心类型定义 / IoT System Core Type Definitions
//! 
//! 本模块定义了IoT系统的核心数据类型和结构。
//! This module defines the core data types and structures for the IoT system.

use serde::{Deserialize, Serialize};
// use std::collections::HashMap;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

/// 实时任务 / Real-time Task
/// 
/// 表示IoT系统中的实时任务。
/// Represents a real-time task in the IoT system.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RealTimeTask {
    /// 任务ID / Task ID
    pub id: TaskId,
    /// 任务名称 / Task Name
    pub name: String,
    /// 任务类型 / Task Type
    pub task_type: TaskType,
    /// 优先级 / Priority
    pub priority: Priority,
    /// 执行时间 / Execution Time
    pub execution_time: Duration,
    /// 截止时间 / Deadline
    pub deadline: Duration,
    /// 周期 / Period
    pub period: Option<Duration>,
    /// 任务状态 / Task Status
    pub status: TaskStatus,
    /// 创建时间 / Creation Time
    pub created_at: u64,
}

impl RealTimeTask {
    /// 创建新的实时任务 / Create New Real-time Task
    pub fn new(name: String, task_type: TaskType, priority: Priority, execution_time: Duration, deadline: Duration) -> Self {
        Self {
            id: TaskId::new(),
            name,
            task_type,
            priority,
            execution_time,
            deadline,
            period: None,
            status: TaskStatus::Ready,
            created_at: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs(),
        }
    }
    
    /// 创建周期性任务 / Create Periodic Task
    pub fn new_periodic(name: String, task_type: TaskType, priority: Priority, execution_time: Duration, period: Duration) -> Self {
        Self {
            id: TaskId::new(),
            name,
            task_type,
            priority,
            execution_time,
            deadline: period,
            period: Some(period),
            status: TaskStatus::Ready,
            created_at: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs(),
        }
    }
    
    /// 检查是否满足截止时间 / Check Deadline Satisfaction
    pub fn meets_deadline(&self, completion_time: Duration) -> bool {
        completion_time <= self.deadline
    }
    
    /// 获取剩余时间 / Get Remaining Time
    pub fn get_remaining_time(&self, current_time: Duration) -> Duration {
        if current_time >= self.deadline {
            Duration::from_secs(0)
        } else {
            self.deadline - current_time
        }
    }
    
    /// 验证任务 / Validate Task
    pub fn validate(&self) -> ValidationResult {
        let mut errors = Vec::new();
        
        // 检查执行时间 / Check Execution Time
        if self.execution_time.is_zero() {
            errors.push(ValidationError::InvalidExecutionTime);
        }
        
        // 检查截止时间 / Check Deadline
        if self.deadline.is_zero() {
            errors.push(ValidationError::InvalidDeadline);
        }
        
        // 检查执行时间是否超过截止时间 / Check if Execution Time Exceeds Deadline
        if self.execution_time > self.deadline {
            errors.push(ValidationError::ExecutionTimeExceedsDeadline);
        }
        
        // 检查周期性任务的周期 / Check Periodic Task Period
        if let Some(period) = self.period {
            if period.is_zero() {
                errors.push(ValidationError::InvalidPeriod);
            }
            if period < self.execution_time {
                errors.push(ValidationError::PeriodLessThanExecutionTime);
            }
        }
        
        ValidationResult {
            is_valid: errors.is_empty(),
            errors,
        }
    }
}

/// 任务ID / Task ID
/// 
/// 唯一标识一个实时任务。
/// Uniquely identifies a real-time task.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct TaskId {
    /// 唯一标识符 / Unique Identifier
    pub id: u64,
}

impl TaskId {
    /// 创建新任务ID / Create New Task ID
    pub fn new() -> Self {
        use std::sync::atomic::{AtomicU64, Ordering};
        static COUNTER: AtomicU64 = AtomicU64::new(1);
        
        Self {
            id: COUNTER.fetch_add(1, Ordering::Relaxed),
        }
    }
}

/// 任务类型 / Task Type
/// 
/// 定义实时任务的类型。
/// Defines the type of a real-time task.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TaskType {
    /// 传感器读取任务 / Sensor Reading Task
    SensorReading,
    /// 控制任务 / Control Task
    Control,
    /// 通信任务 / Communication Task
    Communication,
    /// 数据处理任务 / Data Processing Task
    DataProcessing,
    /// 监控任务 / Monitoring Task
    Monitoring,
    /// 系统维护任务 / System Maintenance Task
    SystemMaintenance,
}

/// 任务优先级 / Task Priority
/// 
/// 定义任务的优先级。
/// Defines the priority of a task.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
pub enum Priority {
    /// 最高优先级 / Highest Priority
    Critical = 0,
    /// 高优先级 / High Priority
    High = 1,
    /// 中等优先级 / Medium Priority
    Medium = 2,
    /// 低优先级 / Low Priority
    Low = 3,
    /// 最低优先级 / Lowest Priority
    Idle = 4,
}

/// 任务状态 / Task Status
/// 
/// 定义任务的执行状态。
/// Defines the execution status of a task.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TaskStatus {
    /// 就绪 / Ready
    Ready,
    /// 运行中 / Running
    Running,
    /// 阻塞 / Blocked
    Blocked,
    /// 挂起 / Suspended
    Suspended,
    /// 完成 / Completed
    Completed,
    /// 超时 / Timeout
    Timeout,
}

/// 调度策略 / Scheduling Policy
/// 
/// 定义实时调度器的调度策略。
/// Defines the scheduling policy of a real-time scheduler.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SchedulingPolicy {
    /// 最早截止时间优先 / Earliest Deadline First
    EarliestDeadlineFirst,
    /// 速率单调 / Rate Monotonic
    RateMonotonic,
    /// 最小松弛时间 / Least Slack Time
    LeastSlackTime,
    /// 优先级调度 / Priority Scheduling
    PriorityScheduling,
    /// 轮转调度 / Round Robin
    RoundRobin,
}

/// 调度决策 / Scheduling Decision
/// 
/// 表示调度器的决策结果。
/// Represents the decision result of a scheduler.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SchedulingDecision {
    /// 选中的任务 / Selected Task
    pub selected_task: Option<RealTimeTask>,
    /// 当前时间 / Current Time
    pub current_time: Duration,
    /// 队列大小 / Queue Size
    pub queue_size: usize,
    /// 调度原因 / Scheduling Reason
    pub reason: SchedulingReason,
}

/// 调度原因 / Scheduling Reason
/// 
/// 定义任务被选中的原因。
/// Defines the reason why a task was selected.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SchedulingReason {
    /// 最高优先级 / Highest Priority
    HighestPriority,
    /// 最早截止时间 / Earliest Deadline
    EarliestDeadline,
    /// 最小松弛时间 / Least Slack Time
    LeastSlackTime,
    /// 时间片到期 / Time Slice Expired
    TimeSliceExpired,
    /// 任务完成 / Task Completed
    TaskCompleted,
}

/// 电源状态 / Power State
/// 
/// 定义设备的电源状态。
/// Defines the power state of a device.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum PowerState {
    /// 活跃状态 / Active State
    Active,
    /// 空闲状态 / Idle State
    Idle,
    /// 睡眠状态 / Sleep State
    Sleep,
    /// 深度睡眠 / Deep Sleep
    DeepSleep,
    /// 关机状态 / Shutdown State
    Shutdown,
}

/// 电源配置 / Power Configuration
/// 
/// 定义电源状态的配置参数。
/// Defines configuration parameters for power states.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PowerConfig {
    /// CPU频率 / CPU Frequency
    pub cpu_frequency: u32,
    /// 电压 / Voltage
    pub voltage: f32,
    /// 功耗 / Power Consumption
    pub power_consumption: f32,
    /// 唤醒时间 / Wake-up Time
    pub wake_up_time: Duration,
    /// 状态转换时间 / State Transition Time
    pub transition_time: Duration,
}

impl PowerConfig {
    /// 创建活跃状态配置 / Create Active State Configuration
    pub fn active() -> Self {
        Self {
            cpu_frequency: 100_000_000, // 100MHz
            voltage: 3.3,
            power_consumption: 100.0, // 100mW
            wake_up_time: Duration::from_micros(1),
            transition_time: Duration::from_micros(10),
        }
    }
    
    /// 创建空闲状态配置 / Create Idle State Configuration
    pub fn idle() -> Self {
        Self {
            cpu_frequency: 10_000_000, // 10MHz
            voltage: 2.5,
            power_consumption: 10.0, // 10mW
            wake_up_time: Duration::from_micros(10),
            transition_time: Duration::from_micros(100),
        }
    }
    
    /// 创建睡眠状态配置 / Create Sleep State Configuration
    pub fn sleep() -> Self {
        Self {
            cpu_frequency: 1_000_000, // 1MHz
            voltage: 1.8,
            power_consumption: 1.0, // 1mW
            wake_up_time: Duration::from_millis(1),
            transition_time: Duration::from_millis(10),
        }
    }
    
    /// 创建深度睡眠状态配置 / Create Deep Sleep State Configuration
    pub fn deep_sleep() -> Self {
        Self {
            cpu_frequency: 0,
            voltage: 0.9,
            power_consumption: 0.1, // 0.1mW
            wake_up_time: Duration::from_millis(100),
            transition_time: Duration::from_millis(1000),
        }
    }
}

/// 节能策略 / Energy Saving Strategy
/// 
/// 定义节能策略的类型。
/// Defines the type of energy saving strategy.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum EnergySavingStrategy {
    /// 动态频率调节 / Dynamic Frequency Scaling
    DynamicFrequencyScaling,
    /// 动态电压调节 / Dynamic Voltage Scaling
    DynamicVoltageScaling,
    /// 选择性关闭 / Selective Shutdown
    SelectiveShutdown,
    /// 任务调度优化 / Task Scheduling Optimization
    TaskSchedulingOptimization,
    /// 通信优化 / Communication Optimization
    CommunicationOptimization,
}

/// 策略结果 / Strategy Result
/// 
/// 表示节能策略的执行结果。
/// Represents the execution result of an energy saving strategy.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StrategyResult {
    /// 策略名称 / Strategy Name
    pub strategy: String,
    /// 节省的能量 / Energy Saved
    pub energy_saved: f32,
    /// 性能影响 / Performance Impact
    pub performance_impact: PerformanceImpact,
}

/// 性能影响 / Performance Impact
/// 
/// 定义策略对性能的影响。
/// Defines the impact of a strategy on performance.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceImpact {
    /// 响应时间影响 / Response Time Impact
    pub response_time_impact: f32,
    /// 吞吐量影响 / Throughput Impact
    pub throughput_impact: f32,
    /// 可靠性影响 / Reliability Impact
    pub reliability_impact: f32,
}

/// 功耗优化结果 / Power Optimization Result
/// 
/// 表示功耗优化的结果。
/// Represents the result of power optimization.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PowerOptimizationResult {
    /// 策略结果列表 / Strategy Results
    pub strategy_results: Vec<StrategyResult>,
    /// 总节省能量 / Total Energy Saved
    pub total_energy_saved: f32,
    /// 总体性能影响 / Overall Performance Impact
    pub overall_performance_impact: PerformanceImpact,
}

impl PowerOptimizationResult {
    /// 创建新的功耗优化结果 / Create New Power Optimization Result
    pub fn new() -> Self {
        Self {
            strategy_results: Vec::new(),
            total_energy_saved: 0.0,
            overall_performance_impact: PerformanceImpact {
                response_time_impact: 0.0,
                throughput_impact: 0.0,
                reliability_impact: 0.0,
            },
        }
    }
    
    /// 添加策略结果 / Add Strategy Result
    pub fn add_strategy_result(&mut self, _strategy: EnergySavingStrategy, result: StrategyResult) {
        self.strategy_results.push(result.clone());
        self.total_energy_saved += result.energy_saved;
        
        // 更新总体性能影响 / Update Overall Performance Impact
        self.overall_performance_impact.response_time_impact += result.performance_impact.response_time_impact;
        self.overall_performance_impact.throughput_impact += result.performance_impact.throughput_impact;
        self.overall_performance_impact.reliability_impact += result.performance_impact.reliability_impact;
    }
}

/// 系统状态 / System Status
/// 
/// 表示IoT系统的运行状态。
/// Represents the operational status of an IoT system.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SystemStatus {
    /// CPU使用率 / CPU Usage
    pub cpu_usage: f32,
    /// 内存使用率 / Memory Usage
    pub memory_usage: f32,
    /// 功耗 / Power Consumption
    pub power_consumption: f32,
    /// 设备状态 / Device Status
    pub device_status: DeviceStatus,
    /// 通信状态 / Communication Status
    pub communication_status: CommunicationStatus,
    /// 任务状态 / Task Status
    pub task_status: TaskStatusSummary,
}

/// 设备状态 / Device Status
/// 
/// 表示IoT设备的状态。
/// Represents the status of an IoT device.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeviceStatus {
    /// 设备ID / Device ID
    pub device_id: String,
    /// 设备类型 / Device Type
    pub device_type: DeviceType,
    /// 连接状态 / Connection Status
    pub connection_status: ConnectionStatus,
    /// 健康状态 / Health Status
    pub health_status: HealthStatus,
    /// 最后更新时间 / Last Update Time
    pub last_update: u64,
}

/// 设备类型 / Device Type
/// 
/// 定义IoT设备的类型。
/// Defines the type of an IoT device.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DeviceType {
    /// 传感器 / Sensor
    Sensor,
    /// 执行器 / Actuator
    Actuator,
    /// 网关 / Gateway
    Gateway,
    /// 控制器 / Controller
    Controller,
    /// 边缘设备 / Edge Device
    EdgeDevice,
}

/// 连接状态 / Connection Status
/// 
/// 定义设备的连接状态。
/// Defines the connection status of a device.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ConnectionStatus {
    /// 已连接 / Connected
    Connected,
    /// 断开连接 / Disconnected
    Disconnected,
    /// 连接中 / Connecting
    Connecting,
    /// 连接失败 / Connection Failed
    ConnectionFailed,
}

/// 健康状态 / Health Status
/// 
/// 定义设备的健康状态。
/// Defines the health status of a device.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum HealthStatus {
    /// 健康 / Healthy
    Healthy,
    /// 警告 / Warning
    Warning,
    /// 错误 / Error
    Error,
    /// 离线 / Offline
    Offline,
}

/// 通信状态 / Communication Status
/// 
/// 表示通信系统的状态。
/// Represents the status of the communication system.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CommunicationStatus {
    /// 协议类型 / Protocol Type
    pub protocol: CommunicationProtocol,
    /// 连接数量 / Connection Count
    pub connection_count: u32,
    /// 数据传输率 / Data Transfer Rate
    pub data_transfer_rate: f32,
    /// 错误率 / Error Rate
    pub error_rate: f32,
    /// 延迟 / Latency
    pub latency: Duration,
}

/// 通信协议 / Communication Protocol
/// 
/// 定义IoT通信协议。
/// Defines IoT communication protocols.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum CommunicationProtocol {
    /// MQTT / MQTT
    MQTT,
    /// CoAP / CoAP
    CoAP,
    /// HTTP / HTTP
    HTTP,
    /// WebSocket / WebSocket
    WebSocket,
    /// Bluetooth / Bluetooth
    Bluetooth,
    /// Zigbee / Zigbee
    Zigbee,
    /// LoRaWAN / LoRaWAN
    LoRaWAN,
}

/// 任务状态摘要 / Task Status Summary
/// 
/// 表示任务状态的摘要信息。
/// Represents summary information of task status.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TaskStatusSummary {
    /// 总任务数 / Total Task Count
    pub total_tasks: u32,
    /// 运行中任务数 / Running Task Count
    pub running_tasks: u32,
    /// 就绪任务数 / Ready Task Count
    pub ready_tasks: u32,
    /// 阻塞任务数 / Blocked Task Count
    pub blocked_tasks: u32,
    /// 完成任务数 / Completed Task Count
    pub completed_tasks: u32,
    /// 超时任务数 / Timeout Task Count
    pub timeout_tasks: u32,
}

/// 验证结果 / Validation Result
/// 
/// 表示验证操作的结果。
/// Represents the result of a validation operation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ValidationResult {
    /// 是否有效 / Is Valid
    pub is_valid: bool,
    /// 错误列表 / Error List
    pub errors: Vec<ValidationError>,
}

/// 验证错误 / Validation Error
/// 
/// 定义验证过程中可能出现的错误。
/// Defines errors that may occur during validation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ValidationError {
    /// 无效执行时间 / Invalid Execution Time
    InvalidExecutionTime,
    /// 无效截止时间 / Invalid Deadline
    InvalidDeadline,
    /// 执行时间超过截止时间 / Execution Time Exceeds Deadline
    ExecutionTimeExceedsDeadline,
    /// 无效周期 / Invalid Period
    InvalidPeriod,
    /// 周期小于执行时间 / Period Less Than Execution Time
    PeriodLessThanExecutionTime,
    /// 无效优先级 / Invalid Priority
    InvalidPriority,
    /// 资源不足 / Insufficient Resources
    InsufficientResources,
}

/// 调度器错误 / Scheduler Error
/// 
/// 定义调度器可能出现的错误。
/// Defines errors that may occur in the scheduler.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SchedulerError {
    /// 任务不可行 / Task Not Feasible
    TaskNotFeasible,
    /// 资源不足 / Insufficient Resources
    InsufficientResources,
    /// 调度失败 / Scheduling Failed
    SchedulingFailed,
    /// 任务超时 / Task Timeout
    TaskTimeout,
    /// 优先级冲突 / Priority Conflict
    PriorityConflict,
}

/// 电源错误 / Power Error
/// 
/// 定义电源管理可能出现的错误。
/// Defines errors that may occur in power management.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PowerError {
    /// 无效电源状态 / Invalid Power State
    InvalidPowerState,
    /// 无效状态转换 / Invalid State Transition
    InvalidStateTransition,
    /// 电源配置错误 / Power Configuration Error
    PowerConfigurationError,
    /// 功耗过高 / Power Consumption Too High
    PowerConsumptionTooHigh,
    /// 电池电量不足 / Insufficient Battery
    InsufficientBattery,
}

/// 系统错误 / System Error
/// 
/// 定义IoT系统可能出现的错误。
/// Defines errors that may occur in the IoT system.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SystemError {
    /// 初始化失败 / Initialization Failed
    InitializationFailed,
    /// 启动失败 / Startup Failed
    StartupFailed,
    /// 配置错误 / Configuration Error
    ConfigurationError,
    /// 硬件错误 / Hardware Error
    HardwareError,
    /// 通信错误 / Communication Error
    CommunicationError,
    /// 调度器错误 / Scheduler Error
    Scheduler(SchedulerError),
    /// 电源错误 / Power Error
    Power(PowerError),
    /// 验证错误 / Validation Error
    Validation(ValidationError),
    /// 其他错误 / Other Error
    Other(String),
}

/// IoT错误 / IoT Error
/// 
/// 定义IoT系统的通用错误。
/// Defines common errors for the IoT system.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum IoTError {
    /// 系统错误 / System Error
    System(SystemError),
    /// 调度器错误 / Scheduler Error
    Scheduler(SchedulerError),
    /// 电源错误 / Power Error
    Power(PowerError),
    /// 验证错误 / Validation Error
    Validation(ValidationError),
    /// 其他错误 / Other Error
    Other(String),
}

// 常量定义 / Constant Definitions
pub const MAX_TASK_PRIORITY: u32 = 255;
pub const MIN_TASK_PRIORITY: u32 = 0;
pub const DEFAULT_TIME_SLICE: Duration = Duration::from_millis(10);
pub const MAX_TASK_EXECUTION_TIME: Duration = Duration::from_secs(60);
pub const MIN_TASK_PERIOD: Duration = Duration::from_millis(1);
pub const MAX_TASK_PERIOD: Duration = Duration::from_secs(3600); 