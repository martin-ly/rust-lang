//! 高级异步调试和日志系统
//! 
//! 本模块提供了完整的异步调试解决方案，重点解决以下问题：
//! 1. 异步执行流的同步化跟踪
//! 2. 跨任务上下文传播
//! 3. 性能瓶颈识别
//! 4. 分布式追踪集成
//! 5. 实时监控和可视化
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, Instant, SystemTime};
use std::collections::HashMap;
use anyhow::Result;
use tokio::sync::{Mutex, RwLock, mpsc};
use tokio::time::{sleep, timeout, interval};
use serde::{Deserialize, Serialize};
use tracing::{info, error, debug};
use uuid::Uuid;

/// 异步执行流跟踪器
/// 解决异步任务执行流难以跟踪的问题
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExecutionFlow {
    /// 执行流ID
    pub flow_id: String,
    /// 执行流名称
    pub name: String,
    /// 开始时间
    pub start_time: SystemTime,
    /// 结束时间
    pub end_time: Option<SystemTime>,
    /// 执行步骤
    pub steps: Vec<ExecutionStep>,
    /// 上下文信息
    pub context: HashMap<String, String>,
    /// 性能指标
    pub metrics: FlowMetrics,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExecutionStep {
    /// 步骤ID
    pub step_id: String,
    /// 步骤名称
    pub name: String,
    /// 步骤类型
    pub step_type: StepType,
    /// 开始时间
    pub start_time: SystemTime,
    /// 结束时间
    pub end_time: Option<SystemTime>,
    /// 执行状态
    pub status: StepStatus,
    /// 错误信息
    pub error: Option<String>,
    /// 子步骤
    pub sub_steps: Vec<ExecutionStep>,
    /// 上下文数据
    pub context: HashMap<String, String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum StepType {
    /// 异步任务
    AsyncTask,
    /// 网络请求
    NetworkRequest,
    /// 数据库操作
    DatabaseOperation,
    /// 文件操作
    FileOperation,
    /// 计算任务
    Computation,
    /// 等待操作
    Wait,
    /// 同步点
    SyncPoint,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum StepStatus {
    Pending,
    Running,
    Completed,
    Failed,
    Cancelled,
    Timeout,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FlowMetrics {
    /// 总执行时间
    pub total_duration: Duration,
    /// 异步等待时间
    pub async_wait_time: Duration,
    /// 同步执行时间
    pub sync_execution_time: Duration,
    /// 网络延迟
    pub network_latency: Duration,
    /// 数据库延迟
    pub database_latency: Duration,
    /// 内存使用峰值
    pub peak_memory_usage: u64,
    /// CPU使用率
    pub cpu_usage: f64,
}

/// 异步执行流管理器
#[allow(dead_code)]
#[derive(Clone)]
pub struct AsyncExecutionFlowManager {
    flows: Arc<RwLock<HashMap<String, ExecutionFlow>>>,
    active_flows: Arc<RwLock<HashMap<String, String>>>, // task_id -> flow_id
    metrics_collector: Arc<AsyncMetricsCollector>,
    event_sender: mpsc::UnboundedSender<FlowEvent>,
    config: FlowManagerConfig,
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct FlowManagerConfig {
    /// 最大保留流程数
    pub max_flows: usize,
    /// 流程保留时间
    pub flow_retention: Duration,
    /// 是否启用详细跟踪
    pub enable_detailed_tracking: bool,
    /// 是否启用性能监控
    pub enable_performance_monitoring: bool,
    /// 采样率 (0.0-1.0)
    pub sampling_rate: f64,
}

impl Default for FlowManagerConfig {
    fn default() -> Self {
        Self {
            max_flows: 10000,
            flow_retention: Duration::from_secs(3600), // 1小时
            enable_detailed_tracking: true,
            enable_performance_monitoring: true,
            sampling_rate: 1.0,
        }
    }
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum FlowEvent {
    FlowStarted(String, String), // flow_id, name
    FlowCompleted(String),
    FlowFailed(String, String), // flow_id, error
    StepStarted(String, String, String), // flow_id, step_id, name
    StepCompleted(String, String),
    StepFailed(String, String, String), // flow_id, step_id, error
}

impl AsyncExecutionFlowManager {
    #[allow(dead_code)]
    pub fn new(config: FlowManagerConfig) -> Self {
        let (event_sender, mut event_receiver) = mpsc::unbounded_channel();
        let flows = Arc::new(RwLock::new(HashMap::new()));
        let active_flows = Arc::new(RwLock::new(HashMap::new()));
        let metrics_collector = Arc::new(AsyncMetricsCollector::new());
        
        let manager = Self {
            flows: flows.clone(),
            active_flows: active_flows.clone(),
            metrics_collector: metrics_collector.clone(),
            event_sender,
            config,
        };
        
        // 启动事件处理任务
        let manager_clone = manager.clone();
        tokio::spawn(async move {
            while let Some(event) = event_receiver.recv().await {
                manager_clone.handle_flow_event(event).await;
            }
        });
        
        manager
    }
    
    /// 开始新的执行流
    pub async fn start_flow(
        &self,
        name: String,
        context: HashMap<String, String>,
    ) -> String {
        let flow_id = Uuid::new_v4().to_string();
        
        let flow = ExecutionFlow {
            flow_id: flow_id.clone(),
            name: name.clone(),
            start_time: SystemTime::now(),
            end_time: None,
            steps: Vec::new(),
            context,
            metrics: FlowMetrics {
                total_duration: Duration::ZERO,
                async_wait_time: Duration::ZERO,
                sync_execution_time: Duration::ZERO,
                network_latency: Duration::ZERO,
                database_latency: Duration::ZERO,
                peak_memory_usage: 0,
                cpu_usage: 0.0,
            },
        };
        
        {
            let mut flows = self.flows.write().await;
            flows.insert(flow_id.clone(), flow);
        }
        
        self.event_sender.send(FlowEvent::FlowStarted(flow_id.clone(), name.clone())).unwrap();
        
        info!(
            flow_id = %flow_id,
            flow_name = %name,
            "执行流开始"
        );
        
        flow_id
    }
    
    /// 关联任务到执行流
    pub async fn associate_task(&self, task_id: String, flow_id: String) {
        let mut active_flows = self.active_flows.write().await;
        active_flows.insert(task_id, flow_id);
    }
    
    /// 开始执行步骤
    pub async fn start_step(
        &self,
        flow_id: &str,
        name: String,
        step_type: StepType,
        context: HashMap<String, String>,
    ) -> String {
        let step_id = Uuid::new_v4().to_string();
        
        let step = ExecutionStep {
            step_id: step_id.clone(),
            name: name.clone(),
            step_type,
            start_time: SystemTime::now(),
            end_time: None,
            status: StepStatus::Running,
            error: None,
            sub_steps: Vec::new(),
            context,
        };
        
        {
            let mut flows = self.flows.write().await;
            if let Some(flow) = flows.get_mut(flow_id) {
                flow.steps.push(step);
            }
        }
        
        self.event_sender.send(FlowEvent::StepStarted(
            flow_id.to_string(),
            step_id.clone(),
            name.clone(),
        )).unwrap();
        
        debug!(
            flow_id = %flow_id,
            step_id = %step_id,
            step_name = %name,
            "执行步骤开始"
        );
        
        step_id
    }
    
    /// 完成执行步骤
    pub async fn complete_step(&self, flow_id: &str, step_id: &str) -> Result<()> {
        let end_time = SystemTime::now();
        
        {
            let mut flows = self.flows.write().await;
            if let Some(flow) = flows.get_mut(flow_id)
                && let Some(step) = flow.steps.iter_mut().find(|s| s.step_id == step_id) {
                    step.end_time = Some(end_time);
                    step.status = StepStatus::Completed;
                }
        }
        
        self.event_sender.send(FlowEvent::StepCompleted(
            flow_id.to_string(),
            step_id.to_string(),
        )).unwrap();
        
        debug!(
            flow_id = %flow_id,
            step_id = %step_id,
            "执行步骤完成"
        );
        
        Ok(())
    }
    
    /// 失败执行步骤
    pub async fn fail_step(&self, flow_id: &str, step_id: &str, error: String) -> Result<()> {
        let end_time = SystemTime::now();
        
        {
            let mut flows = self.flows.write().await;
            if let Some(flow) = flows.get_mut(flow_id)
                && let Some(step) = flow.steps.iter_mut().find(|s| s.step_id == step_id) {
                    step.end_time = Some(end_time);
                    step.status = StepStatus::Failed;
                    step.error = Some(error.clone());
                }
        }
        
        self.event_sender.send(FlowEvent::StepFailed(
            flow_id.to_string(),
            step_id.to_string(),
            error.clone(),
        )).unwrap();
        
        error!(
            flow_id = %flow_id,
            step_id = %step_id,
            error = %error,
            "执行步骤失败"
        );
        
        Ok(())
    }
    
    /// 完成执行流
    pub async fn complete_flow(&self, flow_id: &str) -> Result<()> {
        let end_time = SystemTime::now();
        
        {
            let mut flows = self.flows.write().await;
            if let Some(flow) = flows.get_mut(flow_id) {
                flow.end_time = Some(end_time);
                flow.metrics.total_duration = flow.start_time.duration_since(flow.start_time).unwrap_or(Duration::ZERO);
            }
        }
        
        self.event_sender.send(FlowEvent::FlowCompleted(flow_id.to_string())).unwrap();
        
        info!(
            flow_id = %flow_id,
            "执行流完成"
        );
        
        Ok(())
    }
    
    /// 失败执行流
    pub async fn fail_flow(&self, flow_id: &str, error: String) -> Result<()> {
        let end_time = SystemTime::now();
        
        {
            let mut flows = self.flows.write().await;
            if let Some(flow) = flows.get_mut(flow_id) {
                flow.end_time = Some(end_time);
            }
        }
        
        self.event_sender.send(FlowEvent::FlowFailed(flow_id.to_string(), error.clone())).unwrap();
        
        error!(
            flow_id = %flow_id,
            error = %error,
            "执行流失败"
        );
        
        Ok(())
    }
    
    /// 获取执行流信息
    pub async fn get_flow(&self, flow_id: &str) -> Option<ExecutionFlow> {
        let flows = self.flows.read().await;
        flows.get(flow_id).cloned()
    }
    
    /// 获取所有执行流
    pub async fn get_all_flows(&self) -> Vec<ExecutionFlow> {
        let flows = self.flows.read().await;
        flows.values().cloned().collect()
    }
    
    /// 处理流程事件
    async fn handle_flow_event(&self, event: FlowEvent) {
        match event {
            FlowEvent::FlowStarted(flow_id, name) => {
                info!("执行流开始: {} ({})", name, flow_id);
            }
            FlowEvent::FlowCompleted(flow_id) => {
                info!("执行流完成: {}", flow_id);
            }
            FlowEvent::FlowFailed(flow_id, error) => {
                error!("执行流失败: {} - {}", flow_id, error);
            }
            FlowEvent::StepStarted(flow_id, step_id, name) => {
                debug!("步骤开始: {} -> {} ({})", flow_id, name, step_id);
            }
            FlowEvent::StepCompleted(flow_id, step_id) => {
                debug!("步骤完成: {} -> {}", flow_id, step_id);
            }
            FlowEvent::StepFailed(flow_id, step_id, error) => {
                error!("步骤失败: {} -> {} - {}", flow_id, step_id, error);
            }
        }
    }
}

/// 异步指标收集器
pub struct AsyncMetricsCollector {
    metrics: Arc<Mutex<SystemMetrics>>,
    collection_interval: Duration,
    is_running: AtomicBool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SystemMetrics {
    pub timestamp: SystemTime,
    pub memory_usage: u64,
    pub cpu_usage: f64,
    pub active_tasks: u64,
    pub completed_tasks: u64,
    pub failed_tasks: u64,
    pub network_connections: u64,
    pub database_connections: u64,
}

impl Default for AsyncMetricsCollector {
    fn default() -> Self {
        Self::new()
    }
}

impl AsyncMetricsCollector {
    pub fn new() -> Self {
        Self {
            metrics: Arc::new(Mutex::new(SystemMetrics {
                timestamp: SystemTime::now(),
                memory_usage: 0,
                cpu_usage: 0.0,
                active_tasks: 0,
                completed_tasks: 0,
                failed_tasks: 0,
                network_connections: 0,
                database_connections: 0,
            })),
            collection_interval: Duration::from_secs(1),
            is_running: AtomicBool::new(false),
        }
    }
    
    pub async fn start_collection(&self) {
        if self.is_running.swap(true, Ordering::SeqCst) {
            return;
        }
        
        let metrics = self.metrics.clone();
        let interval_duration = self.collection_interval;
        
        tokio::spawn(async move {
            let mut interval = interval(interval_duration);
            
            loop {
                interval.tick().await;
                
                let system_metrics = Self::collect_system_metrics().await;
                {
                    let mut current_metrics = metrics.lock().await;
                    *current_metrics = system_metrics;
                }
            }
        });
    }
    
    async fn collect_system_metrics() -> SystemMetrics {
        // 这里应该实现实际的系统指标收集
        // 为了演示，我们返回模拟数据
        SystemMetrics {
            timestamp: SystemTime::now(),
            memory_usage: 1024 * 1024 * 100, // 100MB
            cpu_usage: 25.5,
            active_tasks: 10,
            completed_tasks: 1000,
            failed_tasks: 5,
            network_connections: 50,
            database_connections: 10,
        }
    }
    
    pub async fn get_metrics(&self) -> SystemMetrics {
        let metrics = self.metrics.lock().await;
        metrics.clone()
    }
}

/// 异步调试装饰器
/// 提供自动化的调试功能，包括执行流跟踪、性能监控等
#[allow(dead_code)]
pub struct AsyncDebugDecorator {
    flow_manager: Arc<AsyncExecutionFlowManager>,
    metrics_collector: Arc<AsyncMetricsCollector>,
    debug_config: DebugConfig,
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct DebugConfig {
    /// 是否启用自动跟踪
    pub enable_auto_tracking: bool,
    /// 是否启用性能监控
    pub enable_performance_monitoring: bool,
    /// 是否启用详细日志
    pub enable_verbose_logging: bool,
    /// 超时时间
    pub timeout: Option<Duration>,
    /// 重试次数
    pub retry_count: u32,
}

impl Default for DebugConfig {
    fn default() -> Self {
        Self {
            enable_auto_tracking: true,
            enable_performance_monitoring: true,
            enable_verbose_logging: false,
            timeout: Some(Duration::from_secs(30)),
            retry_count: 3,
        }
    }
}

impl AsyncDebugDecorator {
    pub fn new(
        flow_manager: Arc<AsyncExecutionFlowManager>,
        metrics_collector: Arc<AsyncMetricsCollector>,
        debug_config: DebugConfig,
    ) -> Self {
        Self {
            flow_manager,
            metrics_collector,
            debug_config,
        }
    }
    
    /// 装饰异步函数，自动添加调试功能
    pub async fn debug_execute<F, T>(
        &self,
        operation_name: String,
        context: HashMap<String, String>,
        future: F,
    ) -> Result<T>
    where
        F: std::future::Future<Output = Result<T>>,
    {
        let flow_id = if self.debug_config.enable_auto_tracking {
            self.flow_manager.start_flow(operation_name.clone(), context.clone()).await
        } else {
            Uuid::new_v4().to_string()
        };
        
        let step_id = if self.debug_config.enable_auto_tracking {
            self.flow_manager.start_step(
                &flow_id,
                operation_name.clone(),
                StepType::AsyncTask,
                context,
            ).await
        } else {
            Uuid::new_v4().to_string()
        };
        
        let start_time = Instant::now();
        
        let result = if let Some(timeout_duration) = self.debug_config.timeout {
            match timeout(timeout_duration, future).await {
                Ok(result) => result,
                Err(_) => {
                    if self.debug_config.enable_auto_tracking {
                        self.flow_manager.fail_step(&flow_id, &step_id, "操作超时".to_string()).await.unwrap();
                    }
                    return Err(anyhow::anyhow!("操作超时"));
                }
            }
        } else {
            future.await
        };
        
        let execution_time = start_time.elapsed();
        
        match &result {
            Ok(_) => {
                if self.debug_config.enable_auto_tracking {
                    self.flow_manager.complete_step(&flow_id, &step_id).await.unwrap();
                }
                
                if self.debug_config.enable_verbose_logging {
                    info!(
                        flow_id = %flow_id,
                        step_id = %step_id,
                        operation = %operation_name,
                        execution_time_ms = execution_time.as_millis(),
                        "操作执行成功"
                    );
                }
            }
            Err(e) => {
                if self.debug_config.enable_auto_tracking {
                    self.flow_manager.fail_step(&flow_id, &step_id, e.to_string()).await.unwrap();
                }
                
                error!(
                    flow_id = %flow_id,
                    step_id = %step_id,
                    operation = %operation_name,
                    execution_time_ms = execution_time.as_millis(),
                    error = %e,
                    "操作执行失败"
                );
            }
        }
        
        result
    }
    
    /// 装饰网络请求
    pub async fn debug_network_request<F, T>(
        &self,
        url: String,
        method: String,
        future: F,
    ) -> Result<T>
    where
        F: std::future::Future<Output = Result<T>>,
    {
        let mut context = HashMap::new();
        context.insert("url".to_string(), url.clone());
        context.insert("method".to_string(), method.clone());
        
        self.debug_execute(
            format!("{} {}", method, url),
            context,
            future,
        ).await
    }
    
    /// 装饰数据库操作
    pub async fn debug_database_operation<F, T>(
        &self,
        operation: String,
        table: String,
        future: F,
    ) -> Result<T>
    where
        F: std::future::Future<Output = Result<T>>,
    {
        let mut context = HashMap::new();
        context.insert("operation".to_string(), operation.clone());
        context.insert("table".to_string(), table.clone());
        
        self.debug_execute(
            format!("DB: {} {}", operation, table),
            context,
            future,
        ).await
    }
}

/// 执行流可视化器
pub struct ExecutionFlowVisualizer {
    flow_manager: Arc<AsyncExecutionFlowManager>,
}

impl ExecutionFlowVisualizer {
    pub fn new(flow_manager: Arc<AsyncExecutionFlowManager>) -> Self {
        Self { flow_manager }
    }
    
    /// 生成执行流图表（DOT格式）
    pub async fn generate_dot_graph(&self, flow_id: &str) -> Result<String> {
        let flow = self.flow_manager.get_flow(flow_id).await
            .ok_or_else(|| anyhow::anyhow!("执行流不存在: {}", flow_id))?;
        
        let mut dot = String::new();
        dot.push_str("digraph ExecutionFlow {\n");
        dot.push_str("  rankdir=TB;\n");
        dot.push_str("  node [shape=box, style=filled];\n");
        
        // 添加流程节点
        dot.push_str(&format!(
            "  \"{}\" [label=\"{}\", fillcolor=lightblue];\n",
            flow_id, flow.name
        ));
        
        // 添加步骤节点
        for step in &flow.steps {
            let color = match step.status {
                StepStatus::Completed => "lightgreen",
                StepStatus::Failed => "lightcoral",
                StepStatus::Running => "lightyellow",
                _ => "lightgray",
            };
            
            dot.push_str(&format!(
                "  \"{}\" [label=\"{}\", fillcolor={}];\n",
                step.step_id, step.name, color
            ));
            
            // 添加边
            dot.push_str(&format!(
                "  \"{}\" -> \"{}\";\n",
                flow_id, step.step_id
            ));
        }
        
        dot.push_str("}\n");
        
        Ok(dot)
    }
    
    /// 生成执行流报告
    pub async fn generate_flow_report(&self, flow_id: &str) -> Result<FlowReport> {
        let flow = self.flow_manager.get_flow(flow_id).await
            .ok_or_else(|| anyhow::anyhow!("执行流不存在: {}", flow_id))?;
        
        let report = FlowReport {
            flow_id: flow_id.to_string(),
            flow_name: flow.name.clone(),
            start_time: flow.start_time,
            end_time: flow.end_time,
            total_duration: flow.metrics.total_duration,
            step_count: flow.steps.len(),
            completed_steps: flow.steps.iter().filter(|s| matches!(s.status, StepStatus::Completed)).count(),
            failed_steps: flow.steps.iter().filter(|s| matches!(s.status, StepStatus::Failed)).count(),
            steps: flow.steps.clone(),
            metrics: flow.metrics.clone(),
        };
        
        Ok(report)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FlowReport {
    pub flow_id: String,
    pub flow_name: String,
    pub start_time: SystemTime,
    pub end_time: Option<SystemTime>,
    pub total_duration: Duration,
    pub step_count: usize,
    pub completed_steps: usize,
    pub failed_steps: usize,
    pub steps: Vec<ExecutionStep>,
    pub metrics: FlowMetrics,
}

/// 综合演示函数
pub async fn demonstrate_advanced_async_debugging() -> Result<()> {
    println!("🚀 高级异步调试系统演示");
    println!("================================================");
    
    // 1. 初始化系统
    let config = FlowManagerConfig::default();
    let flow_manager = Arc::new(AsyncExecutionFlowManager::new(config));
    let metrics_collector = Arc::new(AsyncMetricsCollector::new());
    let debug_config = DebugConfig::default();
    let debug_decorator = AsyncDebugDecorator::new(
        flow_manager.clone(),
        metrics_collector.clone(),
        debug_config,
    );
    
    // 2. 启动指标收集
    metrics_collector.start_collection().await;
    
    // 3. 演示执行流跟踪
    println!("\n📊 1. 执行流跟踪演示:");
    let mut context = HashMap::new();
    context.insert("user_id".to_string(), "12345".to_string());
    context.insert("request_id".to_string(), "req_001".to_string());
    
    let flow_id = flow_manager.start_flow("用户登录流程".to_string(), context).await;
    
    // 模拟异步操作
    let step1_id = flow_manager.start_step(
        &flow_id,
        "验证用户凭据".to_string(),
        StepType::DatabaseOperation,
        HashMap::new(),
    ).await;
    
    sleep(Duration::from_millis(100)).await;
    flow_manager.complete_step(&flow_id, &step1_id).await?;
    
    let step2_id = flow_manager.start_step(
        &flow_id,
        "生成访问令牌".to_string(),
        StepType::Computation,
        HashMap::new(),
    ).await;
    
    sleep(Duration::from_millis(50)).await;
    flow_manager.complete_step(&flow_id, &step2_id).await?;
    
    flow_manager.complete_flow(&flow_id).await?;
    
    // 4. 演示调试装饰器
    println!("\n🔧 2. 调试装饰器演示:");
    let result = debug_decorator.debug_execute(
        "模拟业务操作".to_string(),
        HashMap::new(),
        async {
            sleep(Duration::from_millis(200)).await;
            Ok("操作成功".to_string())
        },
    ).await?;
    
    println!("装饰器执行结果: {}", result);
    
    // 5. 演示网络请求调试
    println!("\n🌐 3. 网络请求调试演示:");
    let network_result = debug_decorator.debug_network_request(
        "https://api.example.com/users".to_string(),
        "GET".to_string(),
        async {
            sleep(Duration::from_millis(150)).await;
            Ok("网络请求成功".to_string())
        },
    ).await?;
    
    println!("网络请求结果: {}", network_result);
    
    // 6. 演示数据库操作调试
    println!("\n🗄️ 4. 数据库操作调试演示:");
    let db_result = debug_decorator.debug_database_operation(
        "SELECT".to_string(),
        "users".to_string(),
        async {
            sleep(Duration::from_millis(80)).await;
            Ok("数据库查询成功".to_string())
        },
    ).await?;
    
    println!("数据库操作结果: {}", db_result);
    
    // 7. 生成执行流报告
    println!("\n📋 5. 执行流报告生成:");
    let visualizer = ExecutionFlowVisualizer::new(flow_manager.clone());
    let report = visualizer.generate_flow_report(&flow_id).await?;
    
    println!("执行流报告:");
    println!("  流程ID: {}", report.flow_id);
    println!("  流程名称: {}", report.flow_name);
    println!("  总步骤数: {}", report.step_count);
    println!("  完成步骤: {}", report.completed_steps);
    println!("  失败步骤: {}", report.failed_steps);
    println!("  总执行时间: {:?}", report.total_duration);
    
    // 8. 生成DOT图表
    let dot_graph = visualizer.generate_dot_graph(&flow_id).await?;
    println!("\n📊 6. DOT图表生成:");
    println!("{}", dot_graph);
    
    // 9. 获取系统指标
    println!("\n📈 7. 系统指标:");
    let metrics = metrics_collector.get_metrics().await;
    println!("  内存使用: {} MB", metrics.memory_usage / 1024 / 1024);
    println!("  CPU使用率: {:.1}%", metrics.cpu_usage);
    println!("  活跃任务: {}", metrics.active_tasks);
    println!("  完成任务: {}", metrics.completed_tasks);
    
    println!("\n✅ 高级异步调试系统演示完成!");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_execution_flow_manager() {
        let config = FlowManagerConfig::default();
        let manager = AsyncExecutionFlowManager::new(config);
        
        let flow_id = manager.start_flow("测试流程".to_string(), HashMap::new()).await;
        assert!(!flow_id.is_empty());
        
        let step_id = manager.start_step(
            &flow_id,
            "测试步骤".to_string(),
            StepType::AsyncTask,
            HashMap::new(),
        ).await;
        
        manager.complete_step(&flow_id, &step_id).await.unwrap();
        manager.complete_flow(&flow_id).await.unwrap();
        
        let flow = manager.get_flow(&flow_id).await.unwrap();
        assert_eq!(flow.name, "测试流程");
        assert_eq!(flow.steps.len(), 1);
    }
    
    #[tokio::test]
    async fn test_debug_decorator() {
        let config = FlowManagerConfig::default();
        let flow_manager = Arc::new(AsyncExecutionFlowManager::new(config));
        let metrics_collector = Arc::new(AsyncMetricsCollector::new());
        let debug_config = DebugConfig::default();
        let decorator = AsyncDebugDecorator::new(flow_manager, metrics_collector, debug_config);
        
        let result = decorator.debug_execute(
            "测试操作".to_string(),
            HashMap::new(),
            async { Ok("成功".to_string()) },
        ).await.unwrap();
        
        assert_eq!(result, "成功");
    }
    
    #[tokio::test]
    async fn test_metrics_collector() {
        let collector = AsyncMetricsCollector::new();
        collector.start_collection().await;
        
        sleep(Duration::from_millis(100)).await;
        
        let metrics = collector.get_metrics().await;
        assert!(metrics.memory_usage > 0);
    }
}
