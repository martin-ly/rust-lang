//! 高级边缘计算模块
//! 
//! 提供分布式计算、边缘AI推理、实时决策引擎等高级边缘计算功能
#[allow(unused_imports)]
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{
    Duration,
    //Instant,
};
use tokio::sync::{
    RwLock,
    //Semaphore,
};
use serde::{
    Deserialize,
    Serialize,
};
use chrono::{
    DateTime, Utc,
};
use thiserror::Error;

/// 边缘计算节点类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum EdgeNodeType {
    /// 传感器节点
    SensorNode,
    /// 网关节点
    GatewayNode,
    /// 边缘服务器
    EdgeServer,
    /// 边缘AI节点
    EdgeAINode,
    /// 边缘存储节点
    EdgeStorageNode,
    /// 边缘网络节点
    EdgeNetworkNode,
    /// 自定义节点
    Custom(String),
}

/// 边缘计算任务类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum EdgeTaskType {
    /// 数据处理任务
    DataProcessing,
    /// AI推理任务
    AIInference,
    /// 实时决策任务
    RealTimeDecision,
    /// 数据聚合任务
    DataAggregation,
    /// 边缘存储任务
    EdgeStorage,
    /// 网络路由任务
    NetworkRouting,
    /// 安全验证任务
    SecurityValidation,
    /// 自定义任务
    Custom(String),
}

/// 边缘计算节点
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EdgeNode {
    /// 节点ID
    pub node_id: String,
    /// 节点名称
    pub node_name: String,
    /// 节点类型
    pub node_type: EdgeNodeType,
    /// 节点状态
    pub status: EdgeNodeStatus,
    /// 计算能力
    pub compute_capacity: ComputeCapacity,
    /// 网络能力
    pub network_capacity: NetworkCapacity,
    /// 存储能力
    pub storage_capacity: StorageCapacity,
    /// 地理位置
    pub location: Location,
    /// 创建时间
    pub created_at: DateTime<Utc>,
    /// 最后更新时间
    pub last_updated: DateTime<Utc>,
    /// 节点配置
    pub config: EdgeNodeConfig,
}

/// 边缘节点状态
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum EdgeNodeStatus {
    /// 在线
    Online,
    /// 离线
    Offline,
    /// 忙碌
    Busy,
    /// 维护中
    Maintenance,
    /// 错误
    Error(String),
}

/// 计算能力
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComputeCapacity {
    /// CPU核心数
    pub cpu_cores: u32,
    /// CPU频率 (MHz)
    pub cpu_frequency: u32,
    /// 内存大小 (MB)
    pub memory_size: u64,
    /// GPU数量
    pub gpu_count: u32,
    /// GPU内存 (MB)
    pub gpu_memory: u64,
    /// 计算性能评分
    pub performance_score: f64,
}

/// 网络能力
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NetworkCapacity {
    /// 带宽 (Mbps)
    pub bandwidth: u32,
    /// 延迟 (ms)
    pub latency: u32,
    /// 支持的协议
    pub supported_protocols: Vec<String>,
    /// 网络质量评分
    pub quality_score: f64,
}

/// 存储能力
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StorageCapacity {
    /// 存储大小 (GB)
    pub storage_size: u64,
    /// 可用存储 (GB)
    pub available_storage: u64,
    /// 存储类型
    pub storage_type: StorageType,
    /// 读写速度 (MB/s)
    pub read_write_speed: u32,
}

/// 存储类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum StorageType {
    /// SSD
    SSD,
    /// HDD
    HDD,
    /// NVMe
    NVMe,
    /// 内存
    Memory,
    /// 网络存储
    Network,
}

/// 地理位置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Location {
    /// 纬度
    pub latitude: f64,
    /// 经度
    pub longitude: f64,
    /// 海拔 (米)
    pub altitude: f64,
    /// 区域ID
    pub region_id: String,
    /// 区域名称
    pub region_name: String,
}

/// 边缘节点配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EdgeNodeConfig {
    /// 最大并发任务数
    pub max_concurrent_tasks: u32,
    /// 任务超时时间
    pub task_timeout: Duration,
    /// 是否启用AI推理
    pub enable_ai_inference: bool,
    /// 是否启用实时决策
    pub enable_realtime_decision: bool,
    /// 是否启用数据缓存
    pub enable_data_cache: bool,
    /// 缓存大小 (MB)
    pub cache_size: u64,
    /// 自定义参数
    pub custom_params: HashMap<String, String>,
}

/// 边缘计算任务
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EdgeTask {
    /// 任务ID
    pub task_id: String,
    /// 任务类型
    pub task_type: EdgeTaskType,
    /// 任务状态
    pub status: EdgeTaskStatus,
    /// 任务优先级
    pub priority: TaskPriority,
    /// 输入数据
    pub input_data: HashMap<String, String>,
    /// 输出数据
    pub output_data: Option<HashMap<String, String>>,
    /// 分配的节点
    pub assigned_node: Option<String>,
    /// 创建时间
    pub created_at: DateTime<Utc>,
    /// 开始时间
    pub started_at: Option<DateTime<Utc>>,
    /// 完成时间
    pub completed_at: Option<DateTime<Utc>>,
    /// 执行时间
    pub execution_time: Option<Duration>,
    /// 错误信息
    pub error_message: Option<String>,
    /// 任务配置
    pub config: EdgeTaskConfig,
}

/// 任务状态
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum EdgeTaskStatus {
    /// 等待中
    Pending,
    /// 运行中
    Running,
    /// 已完成
    Completed,
    /// 失败
    Failed,
    /// 已取消
    Cancelled,
    /// 暂停
    Paused,
}

/// 任务优先级
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
pub enum TaskPriority {
    /// 低优先级
    Low = 1,
    /// 普通优先级
    Normal = 2,
    /// 高优先级
    High = 3,
    /// 紧急优先级
    Critical = 4,
}

/// 边缘任务配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EdgeTaskConfig {
    /// 最大执行时间
    pub max_execution_time: Duration,
    /// 重试次数
    pub retry_count: u32,
    /// 是否启用容错
    pub enable_fault_tolerance: bool,
    /// 是否启用负载均衡
    pub enable_load_balancing: bool,
    /// 资源需求
    pub resource_requirements: ResourceRequirements,
    /// 自定义参数
    pub custom_params: HashMap<String, String>,
}

/// 资源需求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceRequirements {
    /// CPU需求 (核心数)
    pub cpu_cores: u32,
    /// 内存需求 (MB)
    pub memory: u64,
    /// GPU需求
    pub gpu_required: bool,
    /// 存储需求 (MB)
    pub storage: u64,
    /// 网络需求 (Mbps)
    pub network_bandwidth: u32,
}

/// 边缘计算集群
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EdgeCluster {
    /// 集群ID
    pub cluster_id: String,
    /// 集群名称
    pub cluster_name: String,
    /// 节点列表
    pub nodes: Vec<EdgeNode>,
    /// 集群状态
    pub status: ClusterStatus,
    /// 负载均衡策略
    pub load_balancing_strategy: LoadBalancingStrategy,
    /// 容错策略
    pub fault_tolerance_strategy: FaultToleranceStrategy,
    /// 创建时间
    pub created_at: DateTime<Utc>,
    /// 最后更新时间
    pub last_updated: DateTime<Utc>,
}

/// 集群状态
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum ClusterStatus {
    /// 健康
    Healthy,
    /// 警告
    Warning,
    /// 错误
    Error,
    /// 维护中
    Maintenance,
}

/// 负载均衡策略
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum LoadBalancingStrategy {
    /// 轮询
    RoundRobin,
    /// 最少连接
    LeastConnections,
    /// 加权轮询
    WeightedRoundRobin,
    /// 基于资源
    ResourceBased,
    /// 基于地理位置
    LocationBased,
    /// 自定义策略
    Custom(String),
}

/// 容错策略
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum FaultToleranceStrategy {
    /// 无容错
    None,
    /// 任务重试
    TaskRetry,
    /// 节点切换
    NodeFailover,
    /// 数据复制
    DataReplication,
    /// 多副本
    MultiReplica,
    /// 自定义策略
    Custom(String),
}

/// 边缘计算管理器
pub struct EdgeComputingManager {
    /// 边缘集群
    clusters: Arc<RwLock<HashMap<String, EdgeCluster>>>,
    /// 任务队列
    task_queue: Arc<RwLock<Vec<EdgeTask>>>,
    /// 运行中的任务
    running_tasks: Arc<RwLock<HashMap<String, EdgeTask>>>,
    /// 任务历史
    task_history: Arc<RwLock<Vec<EdgeTask>>>,
    /// 统计信息
    stats: Arc<RwLock<EdgeStats>>,
    /// 配置
    config: EdgeComputingConfig,
    /// 任务调度器
    task_scheduler: Arc<RwLock<TaskScheduler>>,
}

/// 边缘计算配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EdgeComputingConfig {
    /// 是否启用边缘计算
    pub enable_edge_computing: bool,
    /// 最大集群数
    pub max_clusters: u32,
    /// 最大节点数
    pub max_nodes_per_cluster: u32,
    /// 任务调度间隔
    pub task_scheduling_interval: Duration,
    /// 负载均衡策略
    pub default_load_balancing_strategy: LoadBalancingStrategy,
    /// 容错策略
    pub default_fault_tolerance_strategy: FaultToleranceStrategy,
    /// 是否启用自动扩展
    pub enable_auto_scaling: bool,
    /// 自动扩展阈值
    pub auto_scaling_threshold: f64,
    /// 自定义参数
    pub custom_params: HashMap<String, String>,
}

impl Default for EdgeComputingConfig {
    fn default() -> Self {
        Self {
            enable_edge_computing: true,
            max_clusters: 10,
            max_nodes_per_cluster: 100,
            task_scheduling_interval: Duration::from_secs(5),
            default_load_balancing_strategy: LoadBalancingStrategy::RoundRobin,
            default_fault_tolerance_strategy: FaultToleranceStrategy::TaskRetry,
            enable_auto_scaling: true,
            auto_scaling_threshold: 0.8,
            custom_params: HashMap::new(),
        }
    }
}

/// 任务调度器
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TaskScheduler {
    /// 调度策略
    pub scheduling_strategy: SchedulingStrategy,
    /// 调度历史
    pub scheduling_history: Vec<SchedulingRecord>,
    /// 性能指标
    pub performance_metrics: SchedulingMetrics,
}

/// 调度策略
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum SchedulingStrategy {
    /// 先进先出
    FIFO,
    /// 优先级调度
    Priority,
    /// 最短作业优先
    ShortestJobFirst,
    /// 轮转调度
    RoundRobin,
    /// 多级反馈队列
    MultilevelFeedbackQueue,
    /// 自定义策略
    Custom(String),
}

/// 调度记录
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SchedulingRecord {
    /// 任务ID
    pub task_id: String,
    /// 调度时间
    pub scheduled_at: DateTime<Utc>,
    /// 分配的节点
    pub assigned_node: String,
    /// 调度策略
    pub strategy_used: SchedulingStrategy,
    /// 调度延迟
    pub scheduling_delay: Duration,
}

/// 调度性能指标
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SchedulingMetrics {
    /// 平均调度延迟
    pub avg_scheduling_delay: Duration,
    /// 调度成功率
    pub scheduling_success_rate: f64,
    /// 负载均衡效率
    pub load_balancing_efficiency: f64,
    /// 资源利用率
    pub resource_utilization: f64,
    /// 最后更新时间
    pub last_updated: DateTime<Utc>,
}

/// 边缘统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EdgeStats {
    /// 总集群数
    pub total_clusters: u32,
    /// 总节点数
    pub total_nodes: u32,
    /// 在线节点数
    pub online_nodes: u32,
    /// 总任务数
    pub total_tasks: u64,
    /// 成功任务数
    pub successful_tasks: u64,
    /// 失败任务数
    pub failed_tasks: u64,
    /// 平均任务执行时间
    pub avg_task_execution_time: Duration,
    /// 平均资源利用率
    pub avg_resource_utilization: f64,
    /// 最后更新时间
    pub last_updated: DateTime<Utc>,
}

#[allow(dead_code)]
impl EdgeComputingManager {
    /// 创建新的边缘计算管理器
    pub fn new(config: EdgeComputingConfig) -> Self {
        Self {
            clusters: Arc::new(RwLock::new(HashMap::new())),
            task_queue: Arc::new(RwLock::new(Vec::new())),
            running_tasks: Arc::new(RwLock::new(HashMap::new())),
            task_history: Arc::new(RwLock::new(Vec::new())),
            stats: Arc::new(RwLock::new(EdgeStats {
                total_clusters: 0,
                total_nodes: 0,
                online_nodes: 0,
                total_tasks: 0,
                successful_tasks: 0,
                failed_tasks: 0,
                avg_task_execution_time: Duration::ZERO,
                avg_resource_utilization: 0.0,
                last_updated: Utc::now(),
            })),
            config,
            task_scheduler: Arc::new(RwLock::new(TaskScheduler {
                scheduling_strategy: SchedulingStrategy::FIFO,
                scheduling_history: Vec::new(),
                performance_metrics: SchedulingMetrics {
                    avg_scheduling_delay: Duration::ZERO,
                    scheduling_success_rate: 0.0,
                    load_balancing_efficiency: 0.0,
                    resource_utilization: 0.0,
                    last_updated: Utc::now(),
                },
            })),
        }
    }

    /// 创建边缘集群
    pub async fn create_cluster(&self, cluster: EdgeCluster) -> Result<String, EdgeComputingError> {
        let cluster_id = cluster.cluster_id.clone();
        
        // 验证集群
        self.validate_cluster(&cluster).await?;
        
        // 存储集群
        {
            let mut clusters = self.clusters.write().await;
            clusters.insert(cluster_id.clone(), cluster);
        }
        
        // 更新统计
        self.update_cluster_stats().await;
        
        Ok(cluster_id)
    }

    /// 添加节点到集群
    pub async fn add_node_to_cluster(&self, cluster_id: &str, node: EdgeNode) -> Result<(), EdgeComputingError> {
        let mut clusters = self.clusters.write().await;
        let cluster = clusters.get_mut(cluster_id)
            .ok_or_else(|| EdgeComputingError::ClusterNotFound(cluster_id.to_string()))?;
        
        // 验证节点
        self.validate_node(&node).await?;
        
        cluster.nodes.push(node);
        cluster.last_updated = Utc::now();
        
        // 更新统计
        self.update_cluster_stats().await;
        
        Ok(())
    }

    /// 提交边缘计算任务
    pub async fn submit_task(&self, task: EdgeTask) -> Result<String, EdgeComputingError> {
        let task_id = task.task_id.clone();
        
        // 验证任务
        self.validate_task(&task).await?;
        
        // 添加到任务队列
        {
            let mut task_queue = self.task_queue.write().await;
            task_queue.push(task);
        }
        
        // 更新统计
        self.update_task_stats().await;
        
        // 触发任务调度
        self.schedule_tasks().await?;
        
        Ok(task_id)
    }

    /// 获取任务状态
    pub async fn get_task_status(&self, task_id: &str) -> Result<EdgeTaskStatus, EdgeComputingError> {
        // 检查运行中的任务
        {
            let running_tasks = self.running_tasks.read().await;
            if let Some(task) = running_tasks.get(task_id) {
                return Ok(task.status.clone());
            }
        }
        
        // 检查任务队列
        {
            let task_queue = self.task_queue.read().await;
            if let Some(task) = task_queue.iter().find(|t| t.task_id == task_id) {
                return Ok(task.status.clone());
            }
        }
        
        // 检查任务历史
        {
            let task_history = self.task_history.read().await;
            if let Some(task) = task_history.iter().find(|t| t.task_id == task_id) {
                return Ok(task.status.clone());
            }
        }
        
        Err(EdgeComputingError::TaskNotFound(task_id.to_string()))
    }

    /// 获取集群信息
    pub async fn get_cluster_info(&self, cluster_id: &str) -> Result<EdgeCluster, EdgeComputingError> {
        let clusters = self.clusters.read().await;
        let cluster = clusters.get(cluster_id)
            .ok_or_else(|| EdgeComputingError::ClusterNotFound(cluster_id.to_string()))?;
        Ok(cluster.clone())
    }

    /// 获取边缘统计信息
    pub async fn get_stats(&self) -> EdgeStats {
        self.stats.read().await.clone()
    }

    /// 获取任务列表
    pub async fn get_tasks(&self, status_filter: Option<EdgeTaskStatus>, limit: Option<usize>) -> Vec<EdgeTask> {
        let mut all_tasks = Vec::new();
        
        // 添加运行中的任务
        {
            let running_tasks = self.running_tasks.read().await;
            all_tasks.extend(running_tasks.values().cloned());
        }
        
        // 添加队列中的任务
        {
            let task_queue = self.task_queue.read().await;
            all_tasks.extend(task_queue.iter().cloned());
        }
        
        // 添加历史任务
        {
            let task_history = self.task_history.read().await;
            all_tasks.extend(task_history.iter().cloned());
        }
        
        // 应用状态过滤
        if let Some(status) = status_filter {
            all_tasks.retain(|task| task.status == status);
        }
        
        // 按创建时间排序
        all_tasks.sort_by(|a, b| b.created_at.cmp(&a.created_at));
        
        // 应用限制
        if let Some(limit) = limit {
            all_tasks.truncate(limit);
        }
        
        all_tasks
    }

    /// 启动任务调度器
    pub async fn start_task_scheduler(self: Arc<Self>) {
        let self_clone = self.clone();
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(self_clone.config.task_scheduling_interval);
            loop {
                interval.tick().await;
                if let Err(e) = self_clone.schedule_tasks().await {
                    eprintln!("任务调度失败: {:?}", e);
                }
            }
        });
    }

    /// 调度任务
    async fn schedule_tasks(&self) -> Result<(), EdgeComputingError> {
        let mut task_queue = self.task_queue.write().await;
        let mut running_tasks = self.running_tasks.write().await;
        let clusters = self.clusters.read().await;
        
        // 按优先级排序任务
        task_queue.sort_by(|a, b| b.priority.cmp(&a.priority));
        
        let mut tasks_to_remove = Vec::new();
        
        for (index, task) in task_queue.iter_mut().enumerate() {
            if task.status != EdgeTaskStatus::Pending {
                continue;
            }
            
            // 寻找合适的节点
            if let Some(node_id) = self.find_suitable_node(&clusters, &task).await {
                // 分配任务到节点
                task.assigned_node = Some(node_id.clone());
                task.status = EdgeTaskStatus::Running;
                task.started_at = Some(Utc::now());
                
                // 移动到运行中任务
                let task_clone = task.clone();
                running_tasks.insert(task.task_id.clone(), task_clone);
                tasks_to_remove.push(index);
                
                // 记录调度历史
                self.record_scheduling(&task, &node_id).await;
                
                // 模拟任务执行
                let task_id = task.task_id.clone();
                let running_tasks_clone = self.running_tasks.clone();
                let task_history_clone = self.task_history.clone();
                let stats_clone = self.stats.clone();
                tokio::spawn(async move {
                    // 模拟执行时间
                    let execution_time = Duration::from_millis(rand::random::<u64>() % 5000 + 1000);
                    tokio::time::sleep(execution_time).await;
                    
                    // 完成任务
                    let mut running_tasks = running_tasks_clone.write().await;
                    let mut task_history = task_history_clone.write().await;
                    
                    if let Some(mut task) = running_tasks.remove(&task_id) {
                        task.status = EdgeTaskStatus::Completed;
                        task.completed_at = Some(Utc::now());
                        task.execution_time = task.started_at.map(|start| {
                            let delta = Utc::now() - start;
                            Duration::from_millis(delta.num_milliseconds() as u64)
                        });
                        
                        // 移动到历史
                        task_history.push(task);
                        
                        // 更新统计
                        let mut stats = stats_clone.write().await;
                        stats.total_tasks += 1;
                        stats.successful_tasks += 1;
                        stats.last_updated = Utc::now();
                    }
                });
            }
        }
        
        // 移除已调度的任务
        for &index in tasks_to_remove.iter().rev() {
            task_queue.remove(index);
        }
        
        Ok(())
    }

    /// 寻找合适的节点
    async fn find_suitable_node(&self, clusters: &HashMap<String, EdgeCluster>, task: &EdgeTask) -> Option<String> {
        for cluster in clusters.values() {
            for node in &cluster.nodes {
                if node.status == EdgeNodeStatus::Online && 
                   self.can_handle_task(node, task) {
                    return Some(node.node_id.clone());
                }
            }
        }
        None
    }

    /// 检查节点是否能处理任务
    fn can_handle_task(&self, node: &EdgeNode, task: &EdgeTask) -> bool {
        let requirements = &task.config.resource_requirements;
        
        // 检查CPU
        if node.compute_capacity.cpu_cores < requirements.cpu_cores {
            return false;
        }
        
        // 检查内存
        if node.compute_capacity.memory_size < requirements.memory {
            return false;
        }
        
        // 检查GPU
        if requirements.gpu_required && node.compute_capacity.gpu_count == 0 {
            return false;
        }
        
        // 检查存储
        if node.storage_capacity.available_storage < requirements.storage {
            return false;
        }
        
        // 检查网络
        if node.network_capacity.bandwidth < requirements.network_bandwidth {
            return false;
        }
        
        true
    }

    /// 记录调度历史
    async fn record_scheduling(&self, task: &EdgeTask, node_id: &str) {
        let mut scheduler = self.task_scheduler.write().await;
        let record = SchedulingRecord {
            task_id: task.task_id.clone(),
            scheduled_at: Utc::now(),
            assigned_node: node_id.to_string(),
            strategy_used: scheduler.scheduling_strategy.clone(),
            scheduling_delay: Duration::from_millis(rand::random::<u64>() % 100),
        };
        scheduler.scheduling_history.push(record);
    }

    /// 模拟任务执行
    async fn simulate_task_execution(self: Arc<Self>, task_id: String) {
        let self_clone = self.clone();
        tokio::spawn(async move {
            // 模拟执行时间
            let execution_time = Duration::from_millis(rand::random::<u64>() % 5000 + 1000);
            tokio::time::sleep(execution_time).await;
            
            // 完成任务
            if let Err(e) = self_clone.complete_task(&task_id, true).await {
                eprintln!("完成任务失败: {:?}", e);
            }
        });
    }

    /// 完成任务
    async fn complete_task(&self, task_id: &str, success: bool) -> Result<(), EdgeComputingError> {
        let mut running_tasks = self.running_tasks.write().await;
        let mut task_history = self.task_history.write().await;
        
        if let Some(mut task) = running_tasks.remove(task_id) {
            task.status = if success {
                EdgeTaskStatus::Completed
            } else {
                EdgeTaskStatus::Failed
            };
            task.completed_at = Some(Utc::now());
            task.execution_time = task.started_at.map(|start| {
                let delta = Utc::now() - start;
                Duration::from_millis(delta.num_milliseconds() as u64)
            });
            
            // 移动到历史
            task_history.push(task);
            
            // 更新统计
            self.update_task_stats().await;
            
            Ok(())
        } else {
            Err(EdgeComputingError::TaskNotFound(task_id.to_string()))
        }
    }

    /// 验证集群
    async fn validate_cluster(&self, cluster: &EdgeCluster) -> Result<(), EdgeComputingError> {
        if cluster.nodes.len() > self.config.max_nodes_per_cluster as usize {
            return Err(EdgeComputingError::ClusterTooLarge(
                cluster.nodes.len(), 
                self.config.max_nodes_per_cluster as usize
            ));
        }
        
        for node in &cluster.nodes {
            self.validate_node(node).await?;
        }
        
        Ok(())
    }

    /// 验证节点
    async fn validate_node(&self, node: &EdgeNode) -> Result<(), EdgeComputingError> {
        if node.compute_capacity.cpu_cores == 0 {
            return Err(EdgeComputingError::InvalidNodeConfiguration("CPU核心数不能为0".to_string()));
        }
        
        if node.compute_capacity.memory_size == 0 {
            return Err(EdgeComputingError::InvalidNodeConfiguration("内存大小不能为0".to_string()));
        }
        
        Ok(())
    }

    /// 验证任务
    async fn validate_task(&self, task: &EdgeTask) -> Result<(), EdgeComputingError> {
        if task.config.max_execution_time.as_secs() == 0 {
            return Err(EdgeComputingError::InvalidTaskConfiguration("最大执行时间不能为0".to_string()));
        }
        
        Ok(())
    }

    /// 更新集群统计
    async fn update_cluster_stats(&self) {
        let clusters = self.clusters.read().await;
        let mut stats = self.stats.write().await;
        
        stats.total_clusters = clusters.len() as u32;
        stats.total_nodes = clusters.values().map(|c| c.nodes.len() as u32).sum();
        stats.online_nodes = clusters.values()
            .flat_map(|c| &c.nodes)
            .filter(|n| n.status == EdgeNodeStatus::Online)
            .count() as u32;
        stats.last_updated = Utc::now();
    }

    /// 更新任务统计
    async fn update_task_stats(&self) {
        let mut stats = self.stats.write().await;
        
        let running_tasks = self.running_tasks.read().await;
        let task_history = self.task_history.read().await;
        
        stats.total_tasks = running_tasks.len() as u64 + task_history.len() as u64;
        stats.successful_tasks = task_history.iter()
            .filter(|t| t.status == EdgeTaskStatus::Completed)
            .count() as u64;
        stats.failed_tasks = task_history.iter()
            .filter(|t| t.status == EdgeTaskStatus::Failed)
            .count() as u64;
        
        // 计算平均执行时间
        let completed_tasks: Vec<_> = task_history.iter()
            .filter(|t| t.status == EdgeTaskStatus::Completed && t.execution_time.is_some())
            .collect();
        
        if !completed_tasks.is_empty() {
            let total_time: Duration = completed_tasks.iter()
                .map(|t| t.execution_time.unwrap())
                .sum();
            stats.avg_task_execution_time = total_time / completed_tasks.len() as u32;
        }
        
        stats.last_updated = Utc::now();
    }
}

/// 边缘计算错误
#[derive(Debug, Error)]
pub enum EdgeComputingError {
    #[error("集群未找到: {0}")]
    ClusterNotFound(String),
    
    #[error("任务未找到: {0}")]
    TaskNotFound(String),
    
    #[error("集群过大: 实际 {0}, 最大 {1}")]
    ClusterTooLarge(usize, usize),
    
    #[error("节点配置无效: {0}")]
    InvalidNodeConfiguration(String),
    
    #[error("任务配置无效: {0}")]
    InvalidTaskConfiguration(String),
    
    #[error("资源不足: {0}")]
    InsufficientResources(String),
    
    #[error("调度失败: {0}")]
    SchedulingFailed(String),
    
    #[error("配置错误: {0}")]
    ConfigurationError(String),
    
    #[error("内部错误: {0}")]
    InternalError(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_edge_computing_manager_creation() {
        let config = EdgeComputingConfig::default();
        let manager = EdgeComputingManager::new(config);
        
        let stats = manager.get_stats().await;
        assert_eq!(stats.total_clusters, 0);
        assert_eq!(stats.total_nodes, 0);
    }

    #[tokio::test]
    async fn test_cluster_creation() {
        let config = EdgeComputingConfig::default();
        let manager = EdgeComputingManager::new(config);
        
        let node = EdgeNode {
            node_id: "node1".to_string(),
            node_name: "Test Node".to_string(),
            node_type: EdgeNodeType::EdgeServer,
            status: EdgeNodeStatus::Online,
            compute_capacity: ComputeCapacity {
                cpu_cores: 4,
                cpu_frequency: 2400,
                memory_size: 8192,
                gpu_count: 1,
                gpu_memory: 4096,
                performance_score: 0.8,
            },
            network_capacity: NetworkCapacity {
                bandwidth: 1000,
                latency: 10,
                supported_protocols: vec!["TCP".to_string(), "UDP".to_string()],
                quality_score: 0.9,
            },
            storage_capacity: StorageCapacity {
                storage_size: 1000,
                available_storage: 800,
                storage_type: StorageType::SSD,
                read_write_speed: 500,
            },
            location: Location {
                latitude: 39.9042,
                longitude: 116.4074,
                altitude: 50.0,
                region_id: "beijing".to_string(),
                region_name: "北京".to_string(),
            },
            created_at: Utc::now(),
            last_updated: Utc::now(),
            config: EdgeNodeConfig {
                max_concurrent_tasks: 10,
                task_timeout: Duration::from_secs(300),
                enable_ai_inference: true,
                enable_realtime_decision: true,
                enable_data_cache: true,
                cache_size: 1024,
                custom_params: HashMap::new(),
            },
        };
        
        let cluster = EdgeCluster {
            cluster_id: "cluster1".to_string(),
            cluster_name: "Test Cluster".to_string(),
            nodes: vec![node],
            status: ClusterStatus::Healthy,
            load_balancing_strategy: LoadBalancingStrategy::RoundRobin,
            fault_tolerance_strategy: FaultToleranceStrategy::TaskRetry,
            created_at: Utc::now(),
            last_updated: Utc::now(),
        };
        
        let result = manager.create_cluster(cluster).await;
        assert!(result.is_ok());
        
        let cluster_id = result.unwrap();
        assert_eq!(cluster_id, "cluster1");
    }

    #[tokio::test]
    async fn test_task_submission() {
        let config = EdgeComputingConfig::default();
        let manager = EdgeComputingManager::new(config);
        
        let task = EdgeTask {
            task_id: "task1".to_string(),
            task_type: EdgeTaskType::DataProcessing,
            status: EdgeTaskStatus::Pending,
            priority: TaskPriority::Normal,
            input_data: HashMap::from([("data".to_string(), "test_data".to_string())]),
            output_data: None,
            assigned_node: None,
            created_at: Utc::now(),
            started_at: None,
            completed_at: None,
            execution_time: None,
            error_message: None,
            config: EdgeTaskConfig {
                max_execution_time: Duration::from_secs(60),
                retry_count: 3,
                enable_fault_tolerance: true,
                enable_load_balancing: true,
                resource_requirements: ResourceRequirements {
                    cpu_cores: 2,
                    memory: 1024,
                    gpu_required: false,
                    storage: 100,
                    network_bandwidth: 100,
                },
                custom_params: HashMap::new(),
            },
        };
        
        let result = manager.submit_task(task).await;
        assert!(result.is_ok());
        
        let task_id = result.unwrap();
        assert_eq!(task_id, "task1");
    }
}
