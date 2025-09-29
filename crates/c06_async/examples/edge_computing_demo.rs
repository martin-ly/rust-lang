//! 边缘计算异步演示
//! 
//! 本示例展示了异步编程在边缘计算中的应用：
//! - 边缘节点管理
//! - 数据预处理和过滤
//! - 边缘AI推理
//! - 实时数据处理
//! - 边缘存储管理
//! - 网络连接管理
//! - 资源调度
//! - 边缘协同计算
//! 
//! 运行方式：
//! ```bash
//! cargo run --example edge_computing_demo
//! ```

use std::collections::{HashMap, VecDeque};
use std::sync::Arc;
use std::time::{Duration, Instant, SystemTime};
use tokio::sync::{Mutex, RwLock, mpsc, Semaphore};
use tokio::time::sleep;
use serde::{Serialize, Deserialize};
use anyhow::Result;
use uuid::Uuid;

/// 边缘节点信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EdgeNode {
    pub id: String,
    pub name: String,
    pub location: Location,
    pub capabilities: NodeCapabilities,
    pub resources: ResourceInfo,
    pub status: NodeStatus,
    pub last_heartbeat: SystemTime,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Location {
    pub latitude: f64,
    pub longitude: f64,
    pub city: String,
    pub region: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NodeCapabilities {
    pub cpu_cores: u32,
    pub memory_gb: u32,
    pub storage_gb: u32,
    pub network_bandwidth_mbps: u32,
    pub ai_acceleration: bool,
    pub gpu_available: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceInfo {
    pub cpu_usage: f32,
    pub memory_usage: f32,
    pub storage_usage: f32,
    pub network_usage: f32,
    pub active_tasks: u32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum NodeStatus {
    Online,
    Offline,
    Maintenance,
    Overloaded,
}

/// 边缘任务
#[derive(Debug, Clone)]
pub struct EdgeTask {
    pub id: String,
    pub task_type: TaskType,
    pub priority: TaskPriority,
    pub input_data: Vec<u8>,
    pub requirements: TaskRequirements,
    pub created_at: Instant,
    pub deadline: Option<Instant>,
}

#[derive(Debug, Clone)]
pub enum TaskType {
    DataProcessing,
    AIInference,
    DataStorage,
    NetworkRelay,
    CacheUpdate,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum TaskPriority {
    Low = 1,
    Normal = 2,
    High = 3,
    Critical = 4,
}

#[derive(Debug, Clone)]
pub struct TaskRequirements {
    pub min_cpu_cores: u32,
    pub min_memory_mb: u32,
    pub min_storage_mb: u32,
    pub requires_ai: bool,
    pub requires_gpu: bool,
    pub max_latency_ms: u32,
}

/// 边缘任务调度器
pub struct EdgeTaskScheduler {
    nodes: Arc<RwLock<HashMap<String, EdgeNode>>>,
    task_queue: Arc<Mutex<VecDeque<EdgeTask>>>,
    running_tasks: Arc<RwLock<HashMap<String, RunningTask>>>,
    task_results: Arc<RwLock<HashMap<String, TaskResult>>>,
    max_concurrent_tasks: usize,
    semaphore: Arc<Semaphore>,
}

#[derive(Debug, Clone)]
pub struct RunningTask {
    pub task: EdgeTask,
    pub node_id: String,
    pub started_at: Instant,
    pub estimated_completion: Instant,
}

#[derive(Debug, Clone)]
pub struct TaskResult {
    pub task_id: String,
    pub node_id: String,
    pub output_data: Vec<u8>,
    pub execution_time: Duration,
    pub success: bool,
    pub error_message: Option<String>,
    pub completed_at: Instant,
}

impl EdgeTaskScheduler {
    pub fn new(max_concurrent_tasks: usize) -> Self {
        Self {
            nodes: Arc::new(RwLock::new(HashMap::new())),
            task_queue: Arc::new(Mutex::new(VecDeque::new())),
            running_tasks: Arc::new(RwLock::new(HashMap::new())),
            task_results: Arc::new(RwLock::new(HashMap::new())),
            max_concurrent_tasks,
            semaphore: Arc::new(Semaphore::new(max_concurrent_tasks)),
        }
    }

    pub async fn register_node(&self, node: EdgeNode) -> Result<()> {
        let mut nodes = self.nodes.write().await;
        nodes.insert(node.id.clone(), node);
        Ok(())
    }

    pub async fn submit_task(&self, task: EdgeTask) -> Result<()> {
        let mut queue = self.task_queue.lock().await;
        queue.push_back(task);
        Ok(())
    }

    pub async fn schedule_tasks(&self) -> Result<()> {
        let mut queue = self.task_queue.lock().await;
        let nodes = self.nodes.read().await;

        // 按优先级排序任务
        let mut tasks: Vec<_> = queue.drain(..).collect();
        tasks.sort_by(|a, b| b.priority.cmp(&a.priority));

        for task in tasks {
            // 寻找合适的节点
            let suitable_node = self.find_suitable_node(&task, &nodes).await;
            
            if let Some(node_id) = suitable_node {
                // 提交任务到节点
                self.assign_task_to_node(task.clone(), node_id).await?;
            } else {
                // 没有合适的节点，重新加入队列
                queue.push_back(task);
            }
        }

        Ok(())
    }

    async fn find_suitable_node(&self, task: &EdgeTask, nodes: &HashMap<String, EdgeNode>) -> Option<String> {
        let mut best_node = None;
        let mut best_score = 0.0;

        for node in nodes.values() {
            if self.can_handle_task(node, &task.requirements) {
                let score = self.calculate_node_score(node, &task.requirements);
                if score > best_score {
                    best_score = score;
                    best_node = Some(node.id.clone());
                }
            }
        }

        best_node
    }

    fn can_handle_task(&self, node: &EdgeNode, requirements: &TaskRequirements) -> bool {
        let capabilities = &node.capabilities;
        let resources = &node.resources;

        // 检查CPU
        if capabilities.cpu_cores < requirements.min_cpu_cores {
            return false;
        }

        // 检查内存
        if (capabilities.memory_gb as f32 * 1024.0 * (1.0 - resources.memory_usage)) < requirements.min_memory_mb as f32 {
            return false;
        }

        // 检查存储
        if (capabilities.storage_gb as f32 * 1024.0 * (1.0 - resources.storage_usage)) < requirements.min_storage_mb as f32 {
            return false;
        }

        // 检查AI要求
        if requirements.requires_ai && !capabilities.ai_acceleration {
            return false;
        }

        // 检查GPU要求
        if requirements.requires_gpu && !capabilities.gpu_available {
            return false;
        }

        // 检查节点状态
        !matches!(node.status, NodeStatus::Offline | NodeStatus::Maintenance | NodeStatus::Overloaded)
    }

    fn calculate_node_score(&self, node: &EdgeNode, _requirements: &TaskRequirements) -> f32 {
        let resources = &node.resources;
        
        // 基于资源可用性的评分
        let cpu_score = 1.0 - resources.cpu_usage;
        let memory_score = 1.0 - resources.memory_usage;
        let storage_score = 1.0 - resources.storage_usage;
        let network_score = 1.0 - resources.network_usage;

        // 加权平均
        (cpu_score * 0.3 + memory_score * 0.3 + storage_score * 0.2 + network_score * 0.2) * 100.0
    }

    async fn assign_task_to_node(&self, task: EdgeTask, node_id: String) -> Result<()> {
        let _permit = self.semaphore.acquire().await?;

        let started_at = Instant::now();
        let estimated_completion = started_at + Duration::from_millis(1000 + rand::random::<u64>() % 5000);

        let running_task = RunningTask {
            task: task.clone(),
            node_id: node_id.clone(),
            started_at,
            estimated_completion,
        };

        {
            let mut running_tasks = self.running_tasks.write().await;
            running_tasks.insert(task.id.clone(), running_task);
        }

        // 更新节点资源使用
        {
            let mut nodes = self.nodes.write().await;
            if let Some(node) = nodes.get_mut(&node_id) {
                node.resources.active_tasks += 1;
                node.resources.cpu_usage += 0.1;
                node.resources.memory_usage += 0.05;
            }
        }

        // 异步执行任务
        let scheduler = self.clone();
        tokio::spawn(async move {
            let execution_time = Duration::from_millis(500 + rand::random::<u64>() % 3000);
            sleep(execution_time).await;

            // 模拟任务执行结果
            let success = rand::random::<f32>() > 0.1; // 90% 成功率
            let output_data = if success {
                format!("Task {} completed successfully on node {}", task.id, node_id).into_bytes()
            } else {
                Vec::new()
            };

            let result = TaskResult {
                task_id: task.id.clone(),
                node_id: node_id.clone(),
                output_data,
                execution_time,
                success,
                error_message: if success { None } else { Some("Task execution failed".to_string()) },
                completed_at: Instant::now(),
            };

            // 保存结果
            {
                let mut results = scheduler.task_results.write().await;
                results.insert(task.id.clone(), result);
            }

            // 从运行任务中移除
            {
                let mut running_tasks = scheduler.running_tasks.write().await;
                running_tasks.remove(&task.id);
            }

            // 更新节点资源
            {
                let mut nodes = scheduler.nodes.write().await;
                if let Some(node) = nodes.get_mut(&node_id) {
                    node.resources.active_tasks = node.resources.active_tasks.saturating_sub(1);
                    node.resources.cpu_usage = (node.resources.cpu_usage - 0.1).max(0.0);
                    node.resources.memory_usage = (node.resources.memory_usage - 0.05).max(0.0);
                }
            }
        });

        Ok(())
    }

    pub async fn get_system_stats(&self) -> SystemStats {
        let nodes = self.nodes.read().await;
        let queue = self.task_queue.lock().await;
        let running_tasks = self.running_tasks.read().await;
        let results = self.task_results.read().await;

        let total_nodes = nodes.len();
        let online_nodes = nodes.values().filter(|n| matches!(n.status, NodeStatus::Online)).count();
        let pending_tasks = queue.len();
        let active_tasks = running_tasks.len();
        let completed_tasks = results.len();
        let successful_tasks = results.values().filter(|r| r.success).count();

        SystemStats {
            total_nodes,
            online_nodes,
            pending_tasks,
            active_tasks,
            completed_tasks,
            successful_tasks,
            success_rate: if completed_tasks > 0 {
                successful_tasks as f32 / completed_tasks as f32 * 100.0
            } else {
                0.0
            },
        }
    }
}

impl Clone for EdgeTaskScheduler {
    fn clone(&self) -> Self {
        Self {
            nodes: Arc::clone(&self.nodes),
            task_queue: Arc::clone(&self.task_queue),
            running_tasks: Arc::clone(&self.running_tasks),
            task_results: Arc::clone(&self.task_results),
            max_concurrent_tasks: self.max_concurrent_tasks,
            semaphore: Arc::clone(&self.semaphore),
        }
    }
}

#[derive(Debug)]
pub struct SystemStats {
    pub total_nodes: usize,
    pub online_nodes: usize,
    pub pending_tasks: usize,
    pub active_tasks: usize,
    pub completed_tasks: usize,
    pub successful_tasks: usize,
    pub success_rate: f32,
}

/// 边缘数据处理器
pub struct EdgeDataProcessor {
    input_stream: mpsc::UnboundedReceiver<SensorData>,
    output_stream: mpsc::UnboundedSender<ProcessedData>,
    processing_rules: Arc<RwLock<Vec<ProcessingRule>>>,
}

#[derive(Debug, Clone)]
pub struct SensorData {
    pub id: String,
    pub sensor_type: String,
    pub timestamp: SystemTime,
    pub value: f64,
    pub location: Location,
    pub metadata: HashMap<String, String>,
}

#[derive(Debug, Clone)]
pub struct ProcessedData {
    pub id: String,
    pub original_data: SensorData,
    pub processed_value: f64,
    pub anomaly_score: f32,
    pub processed_at: SystemTime,
}

#[derive(Debug, Clone)]
pub struct ProcessingRule {
    pub id: String,
    pub sensor_type: String,
    pub condition: ProcessingCondition,
    pub action: ProcessingAction,
}

#[derive(Debug, Clone)]
pub enum ProcessingCondition {
    ValueRange { min: f64, max: f64 },
    Threshold { threshold: f64, operator: ThresholdOperator },
    Anomaly { threshold: f32 },
}

#[derive(Debug, Clone)]
pub enum ThresholdOperator {
    GreaterThan,
    LessThan,
    EqualTo,
    NotEqualTo,
}

#[derive(Debug, Clone)]
pub enum ProcessingAction {
    Filter,
    Transform,
    Alert,
    Store,
}

impl EdgeDataProcessor {
    pub fn new(
        input_stream: mpsc::UnboundedReceiver<SensorData>,
        output_stream: mpsc::UnboundedSender<ProcessedData>,
    ) -> Self {
        Self {
            input_stream,
            output_stream,
            processing_rules: Arc::new(RwLock::new(Vec::new())),
        }
    }

    pub async fn add_processing_rule(&self, rule: ProcessingRule) {
        let mut rules = self.processing_rules.write().await;
        rules.push(rule);
    }

    pub async fn start_processing(&mut self) -> Result<()> {
        while let Some(sensor_data) = self.input_stream.recv().await {
            let processed_data = self.process_sensor_data(sensor_data).await;
            
            if let Err(e) = self.output_stream.send(processed_data) {
                println!("      发送处理结果失败: {}", e);
                break;
            }
        }
        Ok(())
    }

    async fn process_sensor_data(&self, sensor_data: SensorData) -> ProcessedData {
        let rules = self.processing_rules.read().await;
        let mut processed_value = sensor_data.value;
        let mut anomaly_score = 0.0;

        // 应用处理规则
        for rule in rules.iter() {
            if rule.sensor_type == sensor_data.sensor_type {
                match &rule.condition {
                    ProcessingCondition::ValueRange { min, max } => {
                        if sensor_data.value >= *min && sensor_data.value <= *max {
                            match rule.action {
                                ProcessingAction::Filter => {
                                    // 保持原值
                                }
                                ProcessingAction::Transform => {
                                    processed_value = (processed_value - *min) / (*max - *min);
                                }
                                _ => {}
                            }
                        } else {
                            anomaly_score += 0.5;
                        }
                    }
                    ProcessingCondition::Threshold { threshold, operator } => {
                        let condition_met = match operator {
                            ThresholdOperator::GreaterThan => sensor_data.value > *threshold,
                            ThresholdOperator::LessThan => sensor_data.value < *threshold,
                            ThresholdOperator::EqualTo => (sensor_data.value - *threshold).abs() < 0.001,
                            ThresholdOperator::NotEqualTo => (sensor_data.value - *threshold).abs() >= 0.001,
                        };

                        if condition_met {
                            match rule.action {
                                ProcessingAction::Alert => {
                                    anomaly_score += 0.3;
                                }
                                _ => {}
                            }
                        }
                    }
                    ProcessingCondition::Anomaly { threshold } => {
                        // 简化的异常检测
                        let deviation = (sensor_data.value - 50.0).abs() / 50.0;
                        if deviation > *threshold as f64 {
                            anomaly_score += deviation;
                        }
                    }
                }
            }
        }

        ProcessedData {
            id: Uuid::new_v4().to_string(),
            original_data: sensor_data.clone(),
            processed_value,
            anomaly_score: (anomaly_score.min(1.0)) as f32,
            processed_at: SystemTime::now(),
        }
    }
}

/// 边缘AI推理引擎
pub struct EdgeAIEngine {
    models: Arc<RwLock<HashMap<String, AIModel>>>,
    inference_queue: Arc<Mutex<VecDeque<InferenceRequest>>>,
    results: Arc<RwLock<HashMap<String, InferenceResult>>>,
}

#[derive(Debug, Clone)]
pub struct AIModel {
    pub id: String,
    pub name: String,
    pub model_type: String,
    pub input_size: usize,
    pub output_size: usize,
    pub accuracy: f32,
    pub inference_time_ms: u32,
}

#[derive(Debug, Clone)]
pub struct InferenceRequest {
    pub id: String,
    pub model_id: String,
    pub input_data: Vec<f32>,
    pub priority: TaskPriority,
    pub created_at: Instant,
}

#[derive(Debug, Clone)]
pub struct InferenceResult {
    pub request_id: String,
    pub model_id: String,
    pub output_data: Vec<f32>,
    pub confidence: f32,
    pub inference_time: Duration,
    pub completed_at: Instant,
}

impl EdgeAIEngine {
    pub fn new() -> Self {
        Self {
            models: Arc::new(RwLock::new(HashMap::new())),
            inference_queue: Arc::new(Mutex::new(VecDeque::new())),
            results: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    pub async fn register_model(&self, model: AIModel) {
        let mut models = self.models.write().await;
        models.insert(model.id.clone(), model);
    }

    pub async fn submit_inference(&self, request: InferenceRequest) -> Result<()> {
        let mut queue = self.inference_queue.lock().await;
        queue.push_back(request);
        Ok(())
    }

    pub async fn process_inference_requests(&self) -> Result<()> {
        let mut queue = self.inference_queue.lock().await;
        let models = self.models.read().await;

        while let Some(request) = queue.pop_front() {
            if let Some(model) = models.get(&request.model_id) {
                // 执行推理
                let start_time = Instant::now();
                let (output_data, confidence) = self.run_inference(&request.input_data, model).await;
                let inference_time = start_time.elapsed();

                let result = InferenceResult {
                    request_id: request.id.clone(),
                    model_id: request.model_id.clone(),
                    output_data,
                    confidence,
                    inference_time,
                    completed_at: Instant::now(),
                };

                let mut results = self.results.write().await;
                results.insert(request.id, result);
            }
        }

        Ok(())
    }

    async fn run_inference(&self, _input_data: &[f32], model: &AIModel) -> (Vec<f32>, f32) {
        // 模拟推理时间
        let inference_delay = Duration::from_millis(model.inference_time_ms as u64);
        sleep(inference_delay).await;

        // 生成模拟输出
        let mut output_data = Vec::with_capacity(model.output_size);
        for _ in 0..model.output_size {
            output_data.push(rand::random::<f32>());
        }

        // 计算置信度
        let confidence = model.accuracy * (0.8 + rand::random::<f32>() * 0.2);

        (output_data, confidence)
    }

    pub async fn get_inference_result(&self, request_id: &str) -> Option<InferenceResult> {
        let results = self.results.read().await;
        results.get(request_id).cloned()
    }
}

struct EdgeComputingDemo;

impl EdgeComputingDemo {
    async fn run() -> Result<()> {
        println!("🌐 边缘计算异步演示");
        println!("================================");

        // 1. 边缘任务调度演示
        println!("\n⚙️ 1. 边缘任务调度演示");
        Self::demo_edge_task_scheduling().await?;

        // 2. 边缘数据处理演示
        println!("\n📊 2. 边缘数据处理演示");
        Self::demo_edge_data_processing().await?;

        // 3. 边缘AI推理演示
        println!("\n🧠 3. 边缘AI推理演示");
        Self::demo_edge_ai_inference().await?;

        // 4. 边缘协同计算演示
        println!("\n🤝 4. 边缘协同计算演示");
        Self::demo_edge_collaborative_computing().await?;

        // 5. 完整边缘计算系统演示
        println!("\n🎯 5. 完整边缘计算系统演示");
        Self::demo_complete_edge_system().await?;

        Ok(())
    }

    async fn demo_edge_task_scheduling() -> Result<()> {
        let scheduler = EdgeTaskScheduler::new(5);

        // 注册边缘节点
        let nodes = vec![
            EdgeNode {
                id: "node-1".to_string(),
                name: "Beijing Edge Node".to_string(),
                location: Location {
                    latitude: 39.9042,
                    longitude: 116.4074,
                    city: "Beijing".to_string(),
                    region: "China".to_string(),
                },
                capabilities: NodeCapabilities {
                    cpu_cores: 8,
                    memory_gb: 16,
                    storage_gb: 500,
                    network_bandwidth_mbps: 1000,
                    ai_acceleration: true,
                    gpu_available: true,
                },
                resources: ResourceInfo {
                    cpu_usage: 0.3,
                    memory_usage: 0.4,
                    storage_usage: 0.2,
                    network_usage: 0.1,
                    active_tasks: 2,
                },
                status: NodeStatus::Online,
                last_heartbeat: SystemTime::now(),
            },
            EdgeNode {
                id: "node-2".to_string(),
                name: "Shanghai Edge Node".to_string(),
                location: Location {
                    latitude: 31.2304,
                    longitude: 121.4737,
                    city: "Shanghai".to_string(),
                    region: "China".to_string(),
                },
                capabilities: NodeCapabilities {
                    cpu_cores: 4,
                    memory_gb: 8,
                    storage_gb: 200,
                    network_bandwidth_mbps: 500,
                    ai_acceleration: false,
                    gpu_available: false,
                },
                resources: ResourceInfo {
                    cpu_usage: 0.2,
                    memory_usage: 0.3,
                    storage_usage: 0.4,
                    network_usage: 0.2,
                    active_tasks: 1,
                },
                status: NodeStatus::Online,
                last_heartbeat: SystemTime::now(),
            },
        ];

        for node in nodes {
            scheduler.register_node(node).await?;
        }

        // 提交任务
        let tasks = vec![
            EdgeTask {
                id: Uuid::new_v4().to_string(),
                task_type: TaskType::AIInference,
                priority: TaskPriority::High,
                input_data: vec![1, 2, 3, 4, 5],
                requirements: TaskRequirements {
                    min_cpu_cores: 4,
                    min_memory_mb: 2048,
                    min_storage_mb: 100,
                    requires_ai: true,
                    requires_gpu: false,
                    max_latency_ms: 1000,
                },
                created_at: Instant::now(),
                deadline: None,
            },
            EdgeTask {
                id: Uuid::new_v4().to_string(),
                task_type: TaskType::DataProcessing,
                priority: TaskPriority::Normal,
                input_data: vec![6, 7, 8, 9, 10],
                requirements: TaskRequirements {
                    min_cpu_cores: 2,
                    min_memory_mb: 1024,
                    min_storage_mb: 50,
                    requires_ai: false,
                    requires_gpu: false,
                    max_latency_ms: 2000,
                },
                created_at: Instant::now(),
                deadline: None,
            },
        ];

        for task in tasks {
            scheduler.submit_task(task).await?;
        }

        // 调度任务
        scheduler.schedule_tasks().await?;

        // 等待任务执行
        sleep(Duration::from_secs(2)).await;

        // 显示系统统计
        let stats = scheduler.get_system_stats().await;
        println!("    系统统计:");
        println!("      总节点数: {}", stats.total_nodes);
        println!("      在线节点数: {}", stats.online_nodes);
        println!("      待处理任务: {}", stats.pending_tasks);
        println!("      活跃任务: {}", stats.active_tasks);
        println!("      完成任务: {}", stats.completed_tasks);
        println!("      成功率: {:.1}%", stats.success_rate);

        Ok(())
    }

    async fn demo_edge_data_processing() -> Result<()> {
        // 创建数据流
        let (input_sender, input_receiver) = mpsc::unbounded_channel();
        let (output_sender, mut output_receiver) = mpsc::unbounded_channel();

        let mut processor = EdgeDataProcessor::new(input_receiver, output_sender);

        // 添加处理规则
        let rules = vec![
            ProcessingRule {
                id: "rule-1".to_string(),
                sensor_type: "temperature".to_string(),
                condition: ProcessingCondition::ValueRange { min: -10.0, max: 50.0 },
                action: ProcessingAction::Filter,
            },
            ProcessingRule {
                id: "rule-2".to_string(),
                sensor_type: "temperature".to_string(),
                condition: ProcessingCondition::Threshold { threshold: 40.0, operator: ThresholdOperator::GreaterThan },
                action: ProcessingAction::Alert,
            },
            ProcessingRule {
                id: "rule-3".to_string(),
                sensor_type: "humidity".to_string(),
                condition: ProcessingCondition::Anomaly { threshold: 0.3 },
                action: ProcessingAction::Store,
            },
        ];

        for rule in rules {
            processor.add_processing_rule(rule).await;
        }

        // 启动处理器
        let processor_handle = tokio::spawn(async move {
            processor.start_processing().await
        });

        // 发送传感器数据
        let sensor_data = vec![
            SensorData {
                id: "temp-1".to_string(),
                sensor_type: "temperature".to_string(),
                timestamp: SystemTime::now(),
                value: 25.5,
                location: Location {
                    latitude: 39.9042,
                    longitude: 116.4074,
                    city: "Beijing".to_string(),
                    region: "China".to_string(),
                },
                metadata: HashMap::new(),
            },
            SensorData {
                id: "temp-2".to_string(),
                sensor_type: "temperature".to_string(),
                timestamp: SystemTime::now(),
                value: 45.0, // 超过阈值
                location: Location {
                    latitude: 31.2304,
                    longitude: 121.4737,
                    city: "Shanghai".to_string(),
                    region: "China".to_string(),
                },
                metadata: HashMap::new(),
            },
            SensorData {
                id: "humidity-1".to_string(),
                sensor_type: "humidity".to_string(),
                timestamp: SystemTime::now(),
                value: 80.0, // 异常值
                location: Location {
                    latitude: 22.3193,
                    longitude: 114.1694,
                    city: "Hong Kong".to_string(),
                    region: "China".to_string(),
                },
                metadata: HashMap::new(),
            },
        ];

        println!("    发送传感器数据:");
        for data in sensor_data {
            input_sender.send(data).unwrap();
        }

        // 关闭输入流
        drop(input_sender);

        // 接收处理结果
        println!("    接收处理结果:");
        let mut result_count = 0;
        while let Some(result) = output_receiver.recv().await {
            result_count += 1;
            println!("      数据 {}: 原值={:.1}, 处理值={:.1}, 异常分数={:.2}", 
                result_count, result.original_data.value, result.processed_value, result.anomaly_score);
        }

        let _ = processor_handle.await?;

        Ok(())
    }

    async fn demo_edge_ai_inference() -> Result<()> {
        let ai_engine = EdgeAIEngine::new();

        // 注册AI模型
        let models = vec![
            AIModel {
                id: "model-1".to_string(),
                name: "Image Classifier".to_string(),
                model_type: "classification".to_string(),
                input_size: 224 * 224 * 3,
                output_size: 1000,
                accuracy: 0.95,
                inference_time_ms: 50,
            },
            AIModel {
                id: "model-2".to_string(),
                name: "Object Detector".to_string(),
                model_type: "detection".to_string(),
                input_size: 416 * 416 * 3,
                output_size: 85 * 10647,
                accuracy: 0.92,
                inference_time_ms: 100,
            },
        ];

        for model in models {
            ai_engine.register_model(model).await;
        }

        // 提交推理请求
        let requests = vec![
            InferenceRequest {
                id: Uuid::new_v4().to_string(),
                model_id: "model-1".to_string(),
                input_data: vec![0.5; 224 * 224 * 3],
                priority: TaskPriority::High,
                created_at: Instant::now(),
            },
            InferenceRequest {
                id: Uuid::new_v4().to_string(),
                model_id: "model-2".to_string(),
                input_data: vec![0.3; 416 * 416 * 3],
                priority: TaskPriority::Normal,
                created_at: Instant::now(),
            },
        ];

        for request in requests {
            ai_engine.submit_inference(request).await?;
        }

        // 处理推理请求
        ai_engine.process_inference_requests().await?;

        // 获取结果
        println!("    推理结果:");
        let results = ai_engine.results.read().await;
        for (request_id, result) in results.iter() {
            println!("      请求 {}: 模型={}, 置信度={:.2}%, 推理时间={:?}", 
                request_id, result.model_id, result.confidence * 100.0, result.inference_time);
        }

        Ok(())
    }

    async fn demo_edge_collaborative_computing() -> Result<()> {
        println!("    边缘节点协同计算演示");

        // 创建多个边缘节点
        let mut nodes = Vec::new();
        for i in 1..=3 {
            let node = EdgeNode {
                id: format!("collab-node-{}", i),
                name: format!("Collaborative Node {}", i),
                location: Location {
                    latitude: 39.0 + i as f64 * 0.1,
                    longitude: 116.0 + i as f64 * 0.1,
                    city: format!("City {}", i),
                    region: "China".to_string(),
                },
                capabilities: NodeCapabilities {
                    cpu_cores: 4 + i,
                    memory_gb: 8 + i * 2,
                    storage_gb: 100 + i * 50,
                    network_bandwidth_mbps: 500 + i * 100,
                    ai_acceleration: i % 2 == 1,
                    gpu_available: i == 3,
                },
                resources: ResourceInfo {
                    cpu_usage: 0.2 + i as f32 * 0.1,
                    memory_usage: 0.3 + i as f32 * 0.05,
                    storage_usage: 0.1 + i as f32 * 0.02,
                    network_usage: 0.05 + i as f32 * 0.03,
                    active_tasks: i,
                },
                status: NodeStatus::Online,
                last_heartbeat: SystemTime::now(),
            };
            nodes.push(node);
        }

        // 模拟协同计算任务
        let mut handles = Vec::new();
        for (i, node) in nodes.iter().enumerate() {
            let node_id = node.id.clone();
            let handle = tokio::spawn(async move {
                println!("      节点 {} 开始协同计算", node_id);
                
                // 模拟计算任务
                let computation_time = Duration::from_millis(1000 + i as u64 * 500);
                sleep(computation_time).await;
                
                let result = format!("Node {} completed collaborative task", node_id);
                println!("      节点 {} 完成协同计算", node_id);
                
                result
            });
            handles.push(handle);
        }

        // 等待所有节点完成
        for handle in handles {
            let result = handle.await?;
            println!("      协同计算结果: {}", result);
        }

        // 模拟节点间通信
        println!("      节点间通信测试:");
        for i in 1..=3 {
            let source_node = format!("collab-node-{}", i);
            let target_node = format!("collab-node-{}", (i % 3) + 1);
            
            println!("        {} -> {}: 数据传输", source_node, target_node);
            sleep(Duration::from_millis(100)).await;
        }

        Ok(())
    }

    async fn demo_complete_edge_system() -> Result<()> {
        println!("    完整边缘计算系统演示");

        // 创建任务调度器
        let scheduler = EdgeTaskScheduler::new(10);

        // 注册边缘节点
        let locations = vec![
            ("Beijing", 39.9042, 116.4074),
            ("Shanghai", 31.2304, 121.4737),
            ("Guangzhou", 23.1291, 113.2644),
            ("Shenzhen", 22.5431, 114.0579),
        ];

        for (i, (city, lat, lon)) in locations.iter().enumerate() {
            let node = EdgeNode {
                id: format!("system-node-{}", i + 1),
                name: format!("{} Edge Node", city),
                location: Location {
                    latitude: *lat,
                    longitude: *lon,
                    city: city.to_string(),
                    region: "China".to_string(),
                },
                capabilities: NodeCapabilities {
                    cpu_cores: 4 + i as u32 * 2,
                    memory_gb: 8 + i as u32 * 4,
                    storage_gb: 200 + i as u32 * 100,
                    network_bandwidth_mbps: 500 + i as u32 * 200,
                    ai_acceleration: i % 2 == 1,
                    gpu_available: i == 3,
                },
                resources: ResourceInfo {
                    cpu_usage: 0.1 + i as f32 * 0.05,
                    memory_usage: 0.2 + i as f32 * 0.03,
                    storage_usage: 0.1 + i as f32 * 0.02,
                    network_usage: 0.05 + i as f32 * 0.02,
                    active_tasks: 0,
                },
                status: NodeStatus::Online,
                last_heartbeat: SystemTime::now(),
            };

            scheduler.register_node(node).await?;
        }

        // 提交各种类型的任务
        let task_types = vec![
            (TaskType::DataProcessing, 3),
            (TaskType::AIInference, 2),
            (TaskType::DataStorage, 2),
            (TaskType::NetworkRelay, 1),
            (TaskType::CacheUpdate, 2),
        ];

        for (task_type, count) in task_types {
            for _ in 0..count {
                let task = EdgeTask {
                    id: Uuid::new_v4().to_string(),
                    task_type: task_type.clone(),
                    priority: if rand::random::<bool>() { TaskPriority::High } else { TaskPriority::Normal },
                    input_data: vec![rand::random::<u8>(); 100],
                    requirements: TaskRequirements {
                        min_cpu_cores: rand::random::<u32>() % 4 + 1,
                        min_memory_mb: (rand::random::<u32>() % 2048 + 512) as u32,
                        min_storage_mb: (rand::random::<u32>() % 100 + 10) as u32,
                        requires_ai: matches!(task_type, TaskType::AIInference),
                        requires_gpu: rand::random::<bool>(),
                        max_latency_ms: (rand::random::<u32>() % 5000 + 1000) as u32,
                    },
                    created_at: Instant::now(),
                    deadline: None,
                };

                scheduler.submit_task(task).await?;
            }
        }

        // 调度任务
        scheduler.schedule_tasks().await?;

        // 模拟系统运行
        println!("    系统运行中...");
        for i in 1..=5 {
            sleep(Duration::from_secs(1)).await;
            
            let stats = scheduler.get_system_stats().await;
            println!("      第 {} 秒: 活跃任务={}, 完成任务={}, 成功率={:.1}%", 
                i, stats.active_tasks, stats.completed_tasks, stats.success_rate);
        }

        // 最终统计
        let final_stats = scheduler.get_system_stats().await;
        println!("    最终系统统计:");
        println!("      总节点数: {}", final_stats.total_nodes);
        println!("      在线节点数: {}", final_stats.online_nodes);
        println!("      总任务数: {}", final_stats.pending_tasks + final_stats.active_tasks + final_stats.completed_tasks);
        println!("      完成任务数: {}", final_stats.completed_tasks);
        println!("      成功任务数: {}", final_stats.successful_tasks);
        println!("      系统成功率: {:.1}%", final_stats.success_rate);

        Ok(())
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    EdgeComputingDemo::run().await?;

    println!("\n🎉 边缘计算异步演示完成！");
    Ok(())
}
