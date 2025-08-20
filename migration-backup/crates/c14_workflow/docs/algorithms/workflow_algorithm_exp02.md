# Rust 类型设计准则：分布式工作流与算法系统

## 目录

- [Rust 类型设计准则：分布式工作流与算法系统](#rust-类型设计准则分布式工作流与算法系统)
  - [目录](#目录)
  - [1. 可观测与可组合工作流](#1-可观测与可组合工作流)
    - [1.1 OpenTelemetry 集成设计](#11-opentelemetry-集成设计)
    - [1.2 指标与日志聚合设计](#12-指标与日志聚合设计)
  - [2. 通用性和分布式系统组合性](#2-通用性和分布式系统组合性)
    - [2.1 分布式工作流协调器](#21-分布式工作流协调器)
    - [2.2 弹性通信模式](#22-弹性通信模式)
  - [3. Docker 集成与拓扑组合](#3-docker-集成与拓扑组合)
    - [3.1 容器化工作流组件](#31-容器化工作流组件)
    - [3.2 复合拓扑管理](#32-复合拓扑管理)
  - [4. 分布式系统控制与恢复](#4-分布式系统控制与恢复)
    - [4.1 故障检测与自愈](#41-故障检测与自愈)
    - [4.2 容错与幂等性](#42-容错与幂等性)
  - [5. 总结：现代分布式系统设计最佳实践](#5-总结现代分布式系统设计最佳实践)
    - [5.1 可观测性与透明度](#51-可观测性与透明度)
    - [5.2 组合性与弹性](#52-组合性与弹性)
    - [5.3 容器集成与拓扑管理](#53-容器集成与拓扑管理)
    - [5.4 故障处理与恢复](#54-故障处理与恢复)
    - [5.5 可持续性与扩展性](#55-可持续性与扩展性)

本文提出的设计准则着重考虑
工作流和算法系统的组合性、可观测性、通用性、可持续性和分布式特性，并考虑与容器化环境的集成。

## 1. 可观测与可组合工作流

### 1.1 OpenTelemetry 集成设计

```rust
// 推荐：可观测性工作流设计
use opentelemetry::{global, trace::{TraceContextExt, Tracer, TracerProvider}};
use opentelemetry::trace::Span;
use std::sync::Arc;

// 可观测工作流基础特征
pub trait ObservableWorkflow {
    type Input;
    type Output;
    type Error;
    
    // 工作流标识符
    fn name(&self) -> &str;
    
    // 执行工作流
    fn execute(&self, input: Self::Input) -> Result<Self::Output, Self::Error>;
}

// 可观测工作流实现 - 添加 OpenTelemetry 跟踪
pub struct TelemetryWorkflow<W: ObservableWorkflow> {
    inner: W,
    tracer: Arc<dyn opentelemetry::trace::Tracer>,
}

impl<W: ObservableWorkflow> TelemetryWorkflow<W> {
    pub fn new(workflow: W) -> Self {
        let tracer = global::tracer_provider().get_tracer(
            "workflow_service",
            Some(env!("CARGO_PKG_VERSION")),
        );
        
        Self {
            inner: workflow,
            tracer: Arc::new(tracer),
        }
    }
}

impl<W: ObservableWorkflow> ObservableWorkflow for TelemetryWorkflow<W> {
    type Input = W::Input;
    type Output = W::Output;
    type Error = W::Error;
    
    fn name(&self) -> &str {
        self.inner.name()
    }
    
    fn execute(&self, input: Self::Input) -> Result<Self::Output, Self::Error> {
        // 创建跟踪 span
        let mut span = self.tracer.start(format!("workflow.{}", self.name()));
        
        // 添加跟踪元数据
        span.set_attribute(opentelemetry::KeyValue::new("workflow.name", self.name().to_string()));
        
        // 记录开始执行
        span.add_event("workflow.started", vec![]);
        
        // 在当前跟踪上下文中执行工作流
        let cx = opentelemetry::Context::current_with_span(span);
        let result = opentelemetry::trace::with_context(cx, || {
            self.inner.execute(input)
        });
        
        // 根据结果记录事件
        match &result {
            Ok(_) => {
                cx.span().add_event("workflow.completed", vec![
                    opentelemetry::KeyValue::new("status", "success"),
                ]);
            }
            Err(e) => {
                cx.span().add_event("workflow.failed", vec![
                    opentelemetry::KeyValue::new("status", "error"),
                    opentelemetry::KeyValue::new("error", format!("{:?}", e)),
                ]);
                cx.span().set_status(opentelemetry::trace::Status::error(format!("{:?}", e)));
            }
        }
        
        // 结束 span 并返回结果
        cx.span().end();
        result
    }
}

// 组合工作流 - 通过装饰器模式添加多种功能
pub struct CompositeWorkflow<W: ObservableWorkflow> {
    stages: Vec<Arc<W>>,
    name: String,
}

impl<W: ObservableWorkflow> CompositeWorkflow<W> {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            stages: Vec::new(),
            name: name.into(),
        }
    }
    
    pub fn add_stage(&mut self, workflow: W) -> &mut Self {
        self.stages.push(Arc::new(workflow));
        self
    }
}

impl<W> ObservableWorkflow for CompositeWorkflow<W>
where
    W: ObservableWorkflow,
    W::Output: Clone + Send + 'static,
    W::Input: Clone + Send + 'static,
    W::Error: Clone + Send + 'static,
{
    type Input = W::Input;
    type Output = Vec<W::Output>;
    type Error = W::Error;
    
    fn name(&self) -> &str {
        &self.name
    }
    
    fn execute(&self, input: Self::Input) -> Result<Self::Output, Self::Error> {
        let tracer = global::tracer_provider().get_tracer(
            "composite_workflow",
            Some(env!("CARGO_PKG_VERSION")),
        );
        
        let mut span = tracer.start(format!("composite.{}", self.name));
        span.set_attribute(opentelemetry::KeyValue::new("stages", self.stages.len() as i64));
        
        let cx = opentelemetry::Context::current_with_span(span);
        
        let mut results = Vec::with_capacity(self.stages.len());
        
        for (i, stage) in self.stages.iter().enumerate() {
            let stage_span = cx.span().tracer().start(format!("stage.{}.{}", self.name, i));
            stage_span.set_attribute(opentelemetry::KeyValue::new("stage.name", stage.name().to_string()));
            stage_span.set_attribute(opentelemetry::KeyValue::new("stage.index", i as i64));
            
            let stage_cx = cx.with_span(stage_span);
            let stage_result = opentelemetry::trace::with_context(stage_cx, || {
                stage.execute(input.clone())
            });
            
            match stage_result {
                Ok(output) => {
                    results.push(output);
                    stage_cx.span().end();
                }
                Err(e) => {
                    stage_cx.span().set_status(opentelemetry::trace::Status::error(format!("{:?}", e)));
                    stage_cx.span().end();
                    cx.span().end();
                    return Err(e);
                }
            }
        }
        
        cx.span().end();
        Ok(results)
    }
}

// 使用具有可观测性的工作流
fn telemetry_workflow_example() {
    // 设置 OpenTelemetry - 在实际应用中通常在程序启动时配置一次
    let tracer = opentelemetry_jaeger::new_pipeline()
        .with_service_name("workflow_service")
        .install_simple()
        .expect("Failed to install OpenTelemetry tracer");
    
    // 定义基本工作流
    struct DataProcessor {
        name: String,
    }
    
    impl ObservableWorkflow for DataProcessor {
        type Input = String;
        type Output = String;
        type Error = String;
        
        fn name(&self) -> &str {
            &self.name
        }
        
        fn execute(&self, input: Self::Input) -> Result<Self::Output, Self::Error> {
            println!("Processing data: {}", input);
            Ok(format!("Processed: {}", input))
        }
    }
    
    // 创建工作流与可观测性包装
    let workflow = DataProcessor { name: "data_processor".into() };
    let observable_workflow = TelemetryWorkflow::new(workflow);
    
    // 执行工作流
    match observable_workflow.execute("sample data".to_string()) {
        Ok(result) => println!("Result: {}", result),
        Err(e) => println!("Error: {}", e),
    }
    
    // 创建组合工作流
    let mut composite = CompositeWorkflow::new("data_pipeline");
    composite
        .add_stage(DataProcessor { name: "validate".into() })
        .add_stage(DataProcessor { name: "transform".into() })
        .add_stage(DataProcessor { name: "enrich".into() });
    
    // 包装组合工作流以添加可观测性
    let observable_composite = TelemetryWorkflow::new(composite);
    
    // 执行组合工作流
    match observable_composite.execute("composite data".to_string()) {
        Ok(results) => println!("Composite results: {:?}", results),
        Err(e) => println!("Composite error: {}", e),
    }
    
    // 关闭 tracer provider
    global::shutdown_tracer_provider();
}
```

**准则**：设计具有内置可观测性的工作流组件，集成标准工具如 OpenTelemetry，实现分布式跟踪和指标收集。

### 1.2 指标与日志聚合设计

```rust
// 推荐：指标与日志聚合
use metrics::{counter, gauge, histogram};
use std::time::Instant;
use tracing::{debug, error, info, span, Level};

// 可指标化特征
pub trait Metered {
    // 获取组件名称 - 用于指标标识
    fn component_name(&self) -> &str;
    
    // 记录计数指标
    fn count_event(&self, name: &str, value: u64) {
        let metric_name = format!("{}.{}", self.component_name(), name);
        counter!(metric_name, value);
    }
    
    // 记录测量值
    fn record_gauge(&self, name: &str, value: f64) {
        let metric_name = format!("{}.{}", self.component_name(), name);
        gauge!(metric_name, value);
    }
    
    // 记录持续时间
    fn record_duration(&self, name: &str, duration: std::time::Duration) {
        let metric_name = format!("{}.{}", self.component_name(), name);
        histogram!(metric_name, duration);
    }
}

// 可指标化工作流基础构建块
pub struct MeteredComponent<T: Metered> {
    inner: T,
}

impl<T: Metered> MeteredComponent<T> {
    pub fn new(component: T) -> Self {
        Self { inner: component }
    }
    
    // 执行并记录指标的方法
    pub fn execute_with_metrics<F, R>(&self, name: &str, f: F) -> R
    where
        F: FnOnce() -> R,
    {
        // 创建跟踪 span
        let span = span!(Level::INFO, "execute", component = %self.inner.component_name(), operation = %name);
        let _guard = span.enter();
        
        info!(operation = %name, "Starting operation");
        
        // 记录计数
        self.inner.count_event(&format!("{}.count", name), 1);
        
        // 记录持续时间
        let start = Instant::now();
        let result = f();
        let duration = start.elapsed();
        
        self.inner.record_duration(&format!("{}.duration", name), duration);
        
        info!(
            operation = %name,
            duration_ms = %duration.as_millis(),
            "Operation completed"
        );
        
        result
    }
}

// 组合式工作流节点，实现 Metered 特征
pub struct WorkflowNode {
    name: String,
    work_fn: Box<dyn Fn(&str) -> Result<String, String>>,
}

impl WorkflowNode {
    pub fn new<F>(name: impl Into<String>, work_fn: F) -> Self
    where
        F: Fn(&str) -> Result<String, String> + 'static,
    {
        Self {
            name: name.into(),
            work_fn: Box::new(work_fn),
        }
    }
    
    pub fn process(&self, input: &str) -> Result<String, String> {
        (self.work_fn)(input)
    }
}

impl Metered for WorkflowNode {
    fn component_name(&self) -> &str {
        &self.name
    }
}

// 使用指标的工作流管道
pub struct MetricsPipeline {
    nodes: Vec<MeteredComponent<WorkflowNode>>,
    name: String,
}

impl MetricsPipeline {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            nodes: Vec::new(),
            name: name.into(),
        }
    }
    
    pub fn add_node(&mut self, node: WorkflowNode) -> &mut Self {
        self.nodes.push(MeteredComponent::new(node));
        self
    }
    
    pub fn process(&self, input: &str) -> Result<String, String> {
        // 创建跟踪 span
        let span = span!(Level::INFO, "pipeline", name = %self.name);
        let _guard = span.enter();
        
        info!(pipeline = %self.name, "Starting pipeline processing");
        
        let start = Instant::now();
        counter!(format!("{}.started", self.name), 1);
        
        let mut current_input = input.to_string();
        
        for (i, node) in self.nodes.iter().enumerate() {
            debug!(stage = %i, node = %node.inner.component_name(), "Processing stage");
            
            match node.execute_with_metrics("process", || node.inner.process(&current_input)) {
                Ok(output) => {
                    current_input = output;
                }
                Err(e) => {
                    error!(
                        stage = %i,
                        node = %node.inner.component_name(),
                        error = %e,
                        "Pipeline processing failed"
                    );
                    counter!(format!("{}.error", self.name), 1);
                    return Err(e);
                }
            }
        }
        
        let duration = start.elapsed();
        histogram!(format!("{}.duration", self.name), duration);
        counter!(format!("{}.completed", self.name), 1);
        
        info!(
            pipeline = %self.name,
            duration_ms = %duration.as_millis(),
            "Pipeline processing completed"
        );
        
        Ok(current_input)
    }
}

// 使用指标和日志的工作流示例
fn metrics_logging_workflow_example() {
    // 设置日志系统 - 在实际应用中通常在程序启动时配置一次
    tracing_subscriber::fmt()
        .with_max_level(Level::DEBUG)
        .init();
    
    // 设置指标系统 - 在实际应用中通常在程序启动时配置一次
    let metrics_recorder = metrics_exporter_prometheus::PrometheusBuilder::new()
        .with_http_listener(([127, 0, 0, 1], 9000))
        .build()
        .expect("Failed to create Prometheus metrics recorder");
    
    metrics::set_boxed_recorder(Box::new(metrics_recorder))
        .expect("Failed to set metrics recorder");
    
    // 创建工作流管道
    let mut pipeline = MetricsPipeline::new("data_processing");
    
    // 添加处理节点
    pipeline
        .add_node(WorkflowNode::new("validator", |input| {
            if input.len() < 5 {
                Err("Input too short".into())
            } else {
                Ok(input.to_string())
            }
        }))
        .add_node(WorkflowNode::new("transformer", |input| {
            Ok(input.to_uppercase())
        }))
        .add_node(WorkflowNode::new("enricher", |input| {
            Ok(format!("{} [enriched]", input))
        }));
    
    // 处理数据并收集指标
    let result = pipeline.process("sample data");
    println!("Pipeline result: {:?}", result);
    
    // 处理另一个数据集
    let error_result = pipeline.process("bad");
    println!("Error result: {:?}", error_result);
    
    println!("Metrics available at http://localhost:9000/metrics");
    std::thread::sleep(std::time::Duration::from_secs(10)); // 允许查看指标
}
```

**准则**：设计支持指标收集和结构化日志记录的组件，提供细粒度的可观测性和问题诊断能力。

## 2. 通用性和分布式系统组合性

### 2.1 分布式工作流协调器

```rust
// 推荐：分布式工作流协调器
use std::collections::HashMap;
use std::future::Future;
use std::pin::Pin;
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::RwLock;
use uuid::Uuid;

// 工作单元状态
#[derive(Debug, Clone, PartialEq)]
pub enum WorkUnitState {
    Pending,
    Running,
    Completed,
    Failed(String),
}

// 工作单元
pub struct WorkUnit<T> {
    id: String,
    state: WorkUnitState,
    result: Option<T>,
    created_at: std::time::Instant,
    updated_at: std::time::Instant,
    retry_count: u32,
    max_retries: u32,
    dependencies: Vec<String>,
}

impl<T> WorkUnit<T> {
    pub fn new(id: impl Into<String>, max_retries: u32) -> Self {
        let now = std::time::Instant::now();
        Self {
            id: id.into(),
            state: WorkUnitState::Pending,
            result: None,
            created_at: now,
            updated_at: now,
            retry_count: 0,
            max_retries,
            dependencies: Vec::new(),
        }
    }
    
    pub fn with_dependency(mut self, dependency_id: impl Into<String>) -> Self {
        self.dependencies.push(dependency_id.into());
        self
    }
    
    pub fn id(&self) -> &str {
        &self.id
    }
    
    pub fn state(&self) -> &WorkUnitState {
        &self.state
    }
    
    pub fn result(&self) -> Option<&T> {
        self.result.as_ref()
    }
    
    pub fn can_retry(&self) -> bool {
        matches!(self.state, WorkUnitState::Failed(_)) && self.retry_count < self.max_retries
    }
    
    fn update_state(&mut self, state: WorkUnitState) {
        self.state = state;
        self.updated_at = std::time::Instant::now();
    }
    
    fn set_result(&mut self, result: T) {
        self.result = Some(result);
    }
    
    fn increment_retry(&mut self) {
        self.retry_count += 1;
    }
}

// 分布式工作流协调器
pub struct DistributedWorkflowCoordinator<T> {
    work_units: Arc<RwLock<HashMap<String, WorkUnit<T>>>>,
    worker_fn: Arc<dyn Fn(String, Vec<T>) -> Pin<Box<dyn Future<Output = Result<T, String>> + Send>> + Send + Sync>,
}

impl<T: Clone + Send + Sync + 'static> DistributedWorkflowCoordinator<T> {
    pub fn new<F, Fut>(worker_fn: F) -> Self
    where
        F: Fn(String, Vec<T>) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = Result<T, String>> + Send + 'static,
    {
        Self {
            work_units: Arc::new(RwLock::new(HashMap::new())),
            worker_fn: Arc::new(move |id, inputs| {
                Box::pin(worker_fn(id, inputs)) as Pin<Box<dyn Future<Output = Result<T, String>> + Send>>
            }),
        }
    }
    
    // 注册工作单元
    pub async fn register_work_unit(&self, work_unit: WorkUnit<T>) -> Result<(), String> {
        let mut units = self.work_units.write().await;
        
        if units.contains_key(work_unit.id()) {
            return Err(format!("Work unit with ID {} already exists", work_unit.id()));
        }
        
        units.insert(work_unit.id().to_string(), work_unit);
        Ok(())
    }
    
    // 获取工作单元状态
    pub async fn get_work_unit_state(&self, id: &str) -> Option<WorkUnitState> {
        let units = self.work_units.read().await;
        units.get(id).map(|unit| unit.state().clone())
    }
    
    // 获取工作单元结果
    pub async fn get_work_unit_result(&self, id: &str) -> Option<T> {
        let units = self.work_units.read().await;
        units.get(id).and_then(|unit| unit.result().cloned())
    }
    
    // 执行工作单元
    pub async fn execute_work_unit(&self, id: &str) -> Result<(), String> {
        // 检查工作单元是否存在
        {
            let units = self.work_units.read().await;
            if !units.contains_key(id) {
                return Err(format!("Work unit with ID {} does not exist", id));
            }
        }
        
        // 检查依赖
        let dependency_results = {
            let units = self.work_units.read().await;
            let unit = units.get(id).unwrap();
            
            let mut results = Vec::with_capacity(unit.dependencies.len());
            for dep_id in &unit.dependencies {
                let dep_unit = match units.get(dep_id) {
                    Some(u) => u,
                    None => return Err(format!("Dependency {} does not exist", dep_id)),
                };
                
                if dep_unit.state() != &WorkUnitState::Completed {
                    return Err(format!("Dependency {} is not completed", dep_id));
                }
                
                if let Some(result) = dep_unit.result() {
                    results.push(result.clone());
                } else {
                    return Err(format!("Dependency {} has no result", dep_id));
                }
            }
            
            results
        };
        
        // 更新状态为正在运行
        {
            let mut units = self.work_units.write().await;
            let unit = units.get_mut(id).unwrap();
            unit.update_state(WorkUnitState::Running);
        }
        
        // 执行工作单元
        let worker_fn = self.worker_fn.clone();
        let result = worker_fn(id.to_string(), dependency_results).await;
        
        // 更新结果
        let mut units = self.work_units.write().await;
        let unit = units.get_mut(id).unwrap();
        
        match result {
            Ok(output) => {
                unit.update_state(WorkUnitState::Completed);
                unit.set_result(output);
                Ok(())
            }
            Err(e) => {
                unit.update_state(WorkUnitState::Failed(e.clone()));
                Err(e)
            }
        }
    }
    
    // 重试失败的工作单元
    pub async fn retry_work_unit(&self, id: &str) -> Result<(), String> {
        let can_retry = {
            let mut units = self.work_units.write().await;
            let unit = match units.get_mut(id) {
                Some(u) => u,
                None => return Err(format!("Work unit with ID {} does not exist", id)),
            };
            
            if !unit.can_retry() {
                return Err(format!("Work unit {} cannot be retried", id));
            }
            
            unit.increment_retry();
            unit.update_state(WorkUnitState::Pending);
            true
        };
        
        if can_retry {
            self.execute_work_unit(id).await
        } else {
            Ok(())
        }
    }
    
    // 执行整个工作流
    pub async fn execute_workflow(&self) -> Result<HashMap<String, T>, HashMap<String, String>> {
        // 获取所有工作单元
        let all_units = {
            let units = self.work_units.read().await;
            units.keys().cloned().collect::<Vec<_>>()
        };
        
        let mut results = HashMap::new();
        let mut errors = HashMap::new();
        
        // 计算执行顺序 - 简单拓扑排序
        let execution_order = self.compute_execution_order().await?;
        
        // 按照顺序执行工作单元
        for id in execution_order {
            match self.execute_work_unit(&id).await {
                Ok(()) => {
                    if let Some(result) = self.get_work_unit_result(&id).await {
                        results.insert(id, result);
                    }
                }
                Err(e) => {
                    errors.insert(id, e);
                }
            }
        }
        
        if errors.is_empty() {
            Ok(results)
        } else {
            Err(errors)
        }
    }
    
    // 计算执行顺序
    async fn compute_execution_order(&self) -> Result<Vec<String>, String> {
        let units = self.work_units.read().await;
        
        // 构建依赖图
        let mut dependencies = HashMap::new();
        let mut reverse_dependencies = HashMap::new();
        
        for (id, unit) in units.iter() {
            dependencies.insert(id.clone(), unit.dependencies.clone());
            
            for dep_id in &unit.dependencies {
                reverse_dependencies
                    .entry(dep_id.clone())
                    .or_insert_with(Vec::new)
                    .push(id.clone());
            }
        }
        
        // 找出没有依赖的节点
        let mut no_dependencies = Vec::new();
        for id in units.keys() {
            if !dependencies.contains_key(id) || dependencies[id].is_empty() {
                no_dependencies.push(id.clone());
            }
        }
        
        // 拓扑排序
        let mut execution_order = Vec::new();
        
        while !no_dependencies.is_empty() {
            let current = no_dependencies.remove(0);
            execution_order.push(current.clone());
            
            if let Some(dependents) = reverse_dependencies.get(&current) {
                for dependent in dependents {
                    let deps = dependencies.get_mut(dependent).unwrap();
                    deps.retain(|d| d != &current);
                    
                    if deps.is_empty() {
                        no_dependencies.push(dependent.clone());
                    }
                }
            }
        }
        
        // 检查是否有循环依赖
        for deps in dependencies.values() {
            if !deps.is_empty() {
                return Err("Circular dependency detected".into());
            }
        }
        
        Ok(execution_order)
    }
}

// 使用分布式工作流协调器
async fn distributed_workflow_example() {
    // 创建工作流协调器
    let coordinator = DistributedWorkflowCoordinator::<String>::new(
        |id, inputs: Vec<String>| async move {
            println!("Executing work unit {}", id);
            println!("Inputs: {:?}", inputs);
            
            // 模拟工作执行
            tokio::time::sleep(Duration::from_millis(500)).await;
            
            if id == "process" && rand::random::<f32>() < 0.3 {
                // 模拟随机失败
                return Err("Random processing failure".into());
            }
            
            Ok(format!("Result of {}: processed {}", id, inputs.join(", ")))
        }
    );
    
    // 注册工作单元
    let fetch = WorkUnit::<String>::new("fetch", 3);
    let validate = WorkUnit::<String>::new("validate", 3).with_dependency("fetch");
    let process = WorkUnit::<String>::new("process", 3).with_dependency("validate");
    let store = WorkUnit::<String>::new("store", 3).with_dependency("process");
    
    coordinator.register_work_unit(fetch).await.unwrap();
    coordinator.register_work_unit(validate).await.unwrap();
    coordinator.register_work_unit(process).await.unwrap();
    coordinator.register_work_unit(store).await.unwrap();
    
    // 执行工作流
    match coordinator.execute_workflow().await {
        Ok(results) => {
            println!("Workflow completed successfully!");
            for (id, result) in results {
                println!("{}: {}", id, result);
            }
        }
        Err(errors) => {
            println!("Workflow failed with errors:");
            for (id, error) in &errors {
                println!("{}: {}", id, error);
                
                // 尝试重试失败的工作单元
                if coordinator.get_work_unit_state(id).await == Some(WorkUnitState::Failed(error.clone())) {
                    println!("Retrying work unit {}", id);
                    if let Err(e) = coordinator.retry_work_unit(id).await {
                        println!("Retry failed: {}", e);
                    } else {
                        println!("Retry successful for {}", id);
                    }
                }
            }
        }
    }
}
```

**准则**：设计支持分布式工作流协调的组件，实现依赖管理、状态追踪和失败重试功能。

### 2.2 弹性通信模式

```rust
// 推荐：弹性通信模式
use async_trait::async_trait;
use backoff::{ExponentialBackoff, backoff::Backoff};
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use std::time::Duration;

// 通信消息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Message {
    id: String,
    payload: Vec<u8>,
    metadata: HashMap<String, String>,
    created_at: chrono::DateTime<chrono::Utc>,
}

impl Message {
    pub fn new(id: impl Into<String>, payload: Vec<u8>) -> Self {
        let mut metadata = HashMap::new();
        metadata.insert("content_type".to_string(), "application/octet-stream".to_string());
        
        Self {
            id: id.into(),
            payload,
            metadata,
            created_at: chrono::Utc::now(),
        }
    }
    
    pub fn with_metadata(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.metadata.insert(key.into(), value.into());
        self
    }
    
    pub fn id(&self) -> &str {
        &self.id
    }
    
    pub fn payload(&self) -> &[u8] {
        &self.payload
    }
    
    pub fn get_metadata(&self, key: &str) -> Option<&String> {
        self.metadata.get(key)
    }
}

// 消息传输接口
#[async_trait]
pub trait MessageTransport: Send + Sync {
    async fn send(&self, message: &Message) -> Result<(), String>;
    async fn receive(&self) -> Result<Option<Message>, String>;
}

// 弹性消息发送器
pub struct ResilientMessageSender {
    transport: Arc<dyn MessageTransport>,
    backoff_config: ExponentialBackoff,
    metrics: Arc<RwLock<HashMap<String, usize>>>,
}

impl ResilientMessageSender {
    pub fn new(transport: Arc<dyn MessageTransport>) -> Self {
        let mut backoff = ExponentialBackoff::default();
        backoff.initial_interval = Duration::from_millis(100);
        backoff.max_interval = Duration::from_secs(30);
        backoff.max_elapsed_time = Some(Duration::from_secs(300)); // 5 minutes
        
        Self {
            transport,
            backoff_config: backoff,
            metrics: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    // 发送消息，带有重试机制
    pub async fn send_with_retry(&self, message: &Message) -> Result<(), String> {
        // 创建退避策略
        let mut backoff = self.backoff_config.clone();
        let mut attempt = 0;
        
        // 添加重试追踪元数据
        let message_with_retry = Message {
            id: message.id.clone(),
            payload: message.payload.clone(),
            metadata: {
                let mut md = message.metadata.clone();
                md.insert("retry_enabled".to_string(), "true".to_string());
                md
            },
            created_at: message.created_at,
        };
        
        loop {
            attempt += 1;
            
            // 添加尝试次数
            {
                let mut metrics = self.metrics.write().await;
                *metrics.entry("send_attempts".to_string()).or_insert(0) += 1;
            }
            
            match self.transport.send(&message_with_retry).await {
                Ok(()) => {
                    // 成功发送
                    {
                        let mut metrics = self.metrics.write().await;
                        *metrics.entry("send_success".to_string()).or_insert(0) += 1;
                    }
                    
                    info!(
                        message_id = %message.id,
                        attempts = %attempt,
                        "Message sent successfully"
                    );
                    
                    return Ok(());
                }
                Err(e) => {
                    // 更新失败指标
                    {
                        let mut metrics = self.metrics.write().await;
                        *metrics.entry("send_failures".to_string()).or_insert(0) += 1;
                    }
                    
                    // 获取下一次重试的延迟
                    let retry_after = match backoff.next_backoff() {
                        Some(duration) => duration,
                        None => {
                            // 已达到最大重试次数
                            error!(
                                message_id = %message.id,
                                attempts = %attempt,
                                error = %e,
                                "Failed to send message after maximum retries"
                            );
                            
                            return Err(format!("Max retries exceeded: {}", e));
                        }
                    };
                    
                    // 记录重试信息
                    warn!(
                        message_id = %message.id,
                        attempt = %attempt,
                        retry_after_ms = %retry_after.as_millis(),
                        error = %e,
                        "Retrying message send after delay"
                    );
                    
                    // 等待退避时间
                    tokio::time::sleep(retry_after).await;
                }
            }
        }
    }
    
    // 接收消息，带有重试机制
    pub async fn receive_with_retry(&self) -> Result<Option<Message>, String> {
        // 创建退避策略
        let mut backoff = self.backoff_config.clone();
        let mut attempt = 0;
        
        loop {
            attempt += 1;
            
            // 添加尝试次数
            {
                let mut metrics = self.metrics.write().await;
                *metrics.entry("receive_attempts".to_string()).or_insert(0) += 1;
            }
            
            match self.transport.receive().await {
                Ok(message) => {
                    // 成功接收
                    {
                        let mut metrics = self.metrics.write().await;
                        *metrics.entry("receive_success".to_string()).or_insert(0) += 1;
                    }
                    
                    if let Some(ref msg) = message {
                        debug!(
                            message_id = %msg.id,
                            attempts = %attempt,
                            "Message received successfully"
                        );
                    }
                    
                    return Ok(message);
                }
                Err(e) => {
                    // 更新失败指标
                    {
                        let mut metrics = self.metrics.write().await;
                        *metrics.entry("receive_failures".to_string()).or_insert(0) += 1;
                    }
                    
                    // 获取下一次重试的延迟
                    let retry_after = match backoff.next_backoff() {
                        Some(duration) => duration,
                        None => {
                            // 已达到最大重试次数
                            error!(
                                attempts = %attempt,
                                error = %e,
                                "Failed to receive message after maximum retries"
                            );
                            
                            return Err(format!("Max retries exceeded: {}", e));
                        }
                    };
                    
                    // 记录重试信息
                    warn!(
                        attempt = %attempt,
                        retry_after_ms = %retry_after.as_millis(),
                        error = %e,
                        "Retrying message receive after delay"
                    );
                    
                    // 等待退避时间
                    tokio::time::sleep(retry_after).await;
                }
            }
        }
    }
    
    // 获取指标
    pub async fn get_metrics(&self) -> HashMap<String, usize> {
        let metrics = self.metrics.read().await;
        metrics.clone()
    }
}

// 简单的网络消息传输实现
struct NetworkTransport {
    endpoint: String,
    client: reqwest::Client,
    receive_queue: Arc<RwLock<Vec<Message>>>,
}

impl NetworkTransport {
    pub fn new(endpoint: impl Into<String>) -> Self {
        Self {
            endpoint: endpoint.into(),
            client: reqwest::Client::new(),
            receive_queue: Arc::new(RwLock::new(Vec::new())),
        }
    }
}

#[async_trait]
impl MessageTransport for NetworkTransport {
    async fn send(&self, message: &Message) -> Result<(), String> {
        // 模拟网络请求
        let serialized = serde_json::to_string(message)
            .map_err(|e| format!("Serialization error: {}", e))?;
        
        // 模拟随机故障
        if rand::random::<f32>() < 0.2 {
            return Err("Simulated network failure".into());
        }
        
        // 模拟发送
        let response = self.client
            .post(&self.endpoint)
            .body(serialized)
            .send()
            .await
            .map_err(|e| format!("Network error: {}", e))?;
        
        if !response.status().is_success() {
            return Err(format!("HTTP error: {}", response.status()));
        }
        
        // 模拟接收队列 - 在实际应用中，这将使用正确的消息队列或发布/订阅系统
        let mut queue = self.receive_queue.write().await;
        queue.push(message.clone());
        
        Ok(())
    }
    
    async fn receive(&self) -> Result<Option<Message>, String> {
        // 模拟随机故障
        if rand::random::<f32>() < 0.1 {
            return Err("Simulated receive failure".into());
        }
        
        // 从队列中获取消息
        let mut queue = self.receive_queue.write().await;
        Ok(queue.pop())
    }
}

// 使用弹性通信模式示例
async fn resilient_communication_example() {
    // 创建传输层
    let transport = Arc::new(NetworkTransport::new("https://example.com/messages"));
    
    // 创建弹性发送器
    let sender = ResilientMessageSender::new(transport.clone());
    
    // 创建消息
    let message = Message::new("msg123", b"Hello, world!".to_vec())
        .with_metadata("priority", "high")
        .with_metadata("sender", "service-a");
    
    // 发送消息
    match sender.send_with_retry(&message).await {
        Ok(()) => println!("Message sent successfully"),
        Err(e) => println!("Failed to send message: {}", e),
    }
    
    // 接收消息
    match sender.receive_with_retry().await {
        Ok(Some(received)) => println!("Received message: {}", received.id()),
        Ok(None) => println!("No messages available"),
        Err(e) => println!("Failed to receive message: {}", e),
    }
    
    // 查看指标
    let metrics = sender.get_metrics().await;
    println!("Communication metrics: {:?}", metrics);
}
```

**准则**：设计具备弹性的通信组件，支持退避重试、故障检测和指标追踪，适用于不可靠的分布式环境。

## 3. Docker 集成与拓扑组合

### 3.1 容器化工作流组件

```rust
// 推荐：容器化工作流组件
use bollard::container::{Config, CreateContainerOptions};
use bollard::Docker;
use bollard::models::*;
use futures_util::stream::StreamExt;
use futures_util::TryStreamExt;
use std::collections::HashMap;

// 容器化工作组件定义
#[derive(Clone)]
pub struct ContainerSpec {
    name: String,
    image: String,
    command: Vec<String>,
    environment: HashMap<String, String>,
    volumes: Vec<String>,
    network: Option<String>,
    memory_limit: Option<i64>,
    cpu_limit: Option<f64>,
    restart_policy: Option<String>,
}

impl ContainerSpec {
    pub fn new(name: impl Into<String>, image: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            image: image.into(),
            command: Vec::new(),
            environment: HashMap::new(),
            volumes: Vec::new(),
            network: None,
            memory_limit: None,
            cpu_limit: None,
            restart_policy: None,
        }
    }
    
    pub fn with_command(mut self, cmd: Vec<impl Into<String>>) -> Self {
        self.command = cmd.into_iter().map(|c| c.into()).collect();
        self
    }
    
    pub fn with_env(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.environment.insert(key.into(), value.into());
        self
    }
    
    pub fn with_volume(mut self, volume: impl Into<String>) -> Self {
        self.volumes.push(volume.into());
        self
    }
    
    pub fn with_network(mut self, network: impl Into<String>) -> Self {
        self.network = Some(network.into());
        self
    }
    
    pub fn with_memory_limit(mut self, limit_mb: i64) -> Self {
        self.memory_limit = Some(limit_mb * 1024 * 1024); // Convert MB to bytes
        self
    }
    
    pub fn with_cpu_limit(mut self, limit: f64) -> Self {
        self.cpu_limit = Some(limit);
        self
    }
    
    pub fn with_restart_policy(mut self, policy: impl Into<String>) -> Self {
        self.restart_policy = Some(policy.into());
        self
    }
}

// 容器化工作流管理器
pub struct ContainerWorkflowManager {
    docker: Docker,
    containers: HashMap<String, String>, // name -> container_id
}

impl ContainerWorkflowManager {
    pub fn new() -> Result<Self, String> {
        let docker = match Docker::connect_with_local_defaults() {
            Ok(docker) => docker,
            Err(e) => return Err(format!("Failed to connect to Docker: {}", e)),
        };
        
        Ok(Self {
            docker,
            containers: HashMap::new(),
        })
    }
    
    // 创建容器
    pub async fn create_container(&mut self, spec: &ContainerSpec) -> Result<String, String> {
        // 准备创建容器的配置
        let env_vars: Vec<String> = spec.environment.iter()
            .map(|(k, v)| format!("{}={}", k, v))
            .collect();
        
        let mut host_config = HostConfig::default();
        
        // 设置资源限制
        if let Some(memory) = spec.memory_limit {
            host_config.memory = Some(memory);
        }
        
        if let Some(cpu) = spec.cpu_limit {
            host_config.nano_cpus = Some((cpu * 1_000_000_000.0) as i64);
        }
        
        // 设置卷挂载
        if !spec.volumes.is_empty() {
            let mounts: Vec<_> = spec.volumes.iter()
                .map(|v| {
                    let parts: Vec<&str> = v.split(':').collect();
                    if parts.len() >= 2 {
                        let mut mount = Mount::default();
                        mount.source = Some(parts[0].to_string());
                        mount.target = Some(parts[1].to_string());
                        mount.type_ = Some("bind".to_string());
                        
                        if parts.len() >= 3 && parts[2] == "ro" {
                            mount.read_only = Some(true);
                        }
                        
                        Some(mount)
                    } else {
                        None
                    }
                })
                .filter_map(|m| m)
                .collect();
            
            host_config.mounts = Some(mounts);
        }
        
        // 设置网络
        if let Some(network) = &spec.network {
            host_config.network_mode = Some(network.clone());
        }
        
        // 设置重启策略
        if let Some(policy) = &spec.restart_policy {
            let mut restart_policy = RestartPolicy::default();
            restart_policy.name = Some(policy.clone());
            host_config.restart_policy = Some(restart_policy);
        }
        
        // 创建容器配置
        let config = Config {
            image: Some(spec.image.clone()),
            cmd: if spec.command.is_empty() { None } else { Some(spec.command.clone()) },
            env: Some(env_vars),
            host_config: Some(host_config),
            ..Default::default()
        };
        
        // 创建容器
        let options = Some(CreateContainerOptions {
            name: spec.name.clone(),
            platform: None,
        });
        
        let response = self.docker.create_container(options, config)
            .await
            .map_err(|e| format!("Failed to create container: {}", e))?;
        
        // 存储容器ID
        let container_id = response.id;
        self.containers.insert(spec.name.clone(), container_id.clone());
        
        Ok(container_id)
    }
    
    // 启动容器
    pub async fn start_container(&self, container_name: &str) -> Result<(), String> {
        let container_id = match self.containers.get(container_name) {
            Some(id) => id,
            None => return Err(format!("Container not found: {}", container_name)),
        };
        
        self.docker.start_container(container_id, None)
            .await
            .map_err(|e| format!("Failed to start container: {}", e))?;
        
        Ok(())
    }
    
    // 停止容器
    pub async fn stop_container(&self, container_name: &str) -> Result<(), String> {
        let container_id = match self.containers.get(container_name) {
            Some(id) => id,
            None => return Err(format!("Container not found: {}", container_name)),
        };
        
        self.docker.stop_container(container_id, None)
            .await
            .map_err(|e| format!("Failed to stop container: {}", e))?;
        
        Ok(())
    }
    
    // 获取容器日志
    pub async fn get_container_logs(&self, container_name: &str) -> Result<Vec<String>, String> {
        let container_id = match self.containers.get(container_name) {
            Some(id) => id,
            None => return Err(format!("Container not found: {}", container_name)),
        };
        
        let logs = self.docker.logs(container_id, None)
            .try_collect::<Vec<_>>()
            .await
            .map_err(|e| format!("Failed to get container logs: {}", e))?;
        
        let log_lines = logs.iter()
            .map(|log| log.to_string())
            .collect();
        
        Ok(log_lines)
    }
    
    // 删除容器
    pub async fn remove_container(&mut self, container_name: &str) -> Result<(), String> {
        let container_id = match self.containers.get(container_name) {
            Some(id) => id.clone(),
            None => return Err(format!("Container not found: {}", container_name)),
        };
        
        self.docker.remove_container(&container_id, None)
            .await
            .map_err(|e| format!("Failed to remove container: {}", e))?;
        
        self.containers.remove(container_name);
        
        Ok(())
    }
}

// 容器化工作流组合器
pub struct ContainerWorkflow {
    manager: ContainerWorkflowManager,
    stages: Vec<ContainerSpec>,
    network: Option<String>,
}

impl ContainerWorkflow {
    pub fn new() -> Result<Self, String> {
        let manager = ContainerWorkflowManager::new()?;
        
        Ok(Self {
            manager,
            stages: Vec::new(),
            network: None,
        })
    }
    
    pub fn with_network(mut self, network: impl Into<String>) -> Self {
        self.network = Some(network.into());
        self
    }
    
    pub fn add_stage(&mut self, mut container: ContainerSpec) -> &mut Self {
        // 如果已设置网络且容器未指定网络，则使用工作流网络
        if container.network.is_none() && self.network.is_some() {
            container.network = self.network.clone();
        }
        
        self.stages.push(container);
        self
    }
    
    pub async fn run(&mut self) -> Result<(), HashMap<String, String>> {
        let mut errors = HashMap::new();
        
        // 创建并启动所有容器
        for (i, spec) in self.stages.iter().enumerate() {
            match self.manager.create_container(spec).await {
                Ok(container_id) => {
                    println!("Created container {} with ID: {}", spec.name, container_id);
                    
                    // 启动容器
                    if let Err(e) = self.manager.start_container(&spec.name).await {
                        errors.insert(spec.name.clone(), e);
                        continue;
                    }
                    
                    println!("Started container {}", spec.name);
                    
                    // 如果不是最后一个容器，则等待一段时间
                    if i < self.stages.len() - 1 {
                        tokio::time::sleep(tokio::time::Duration::from_secs(2)).await;
                    }
                }
                Err(e) => {
                    errors.insert(spec.name.clone(), e);
                }
            }
        }
        
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
    
    pub async fn cleanup(&mut self) -> Result<(), HashMap<String, String>> {
        let mut errors = HashMap::new();
        
        // 停止并删除所有容器，逆序
        for spec in self.stages.iter().rev() {
            if let Err(e) = self.manager.stop_container(&spec.name).await {
                errors.insert(format!("stop:{}", spec.name), e);
                continue;
            }
            
            println!("Stopped container {}", spec.name);
            
            if let Err(e) = self.manager.remove_container(&spec.name).await {
                errors.insert(format!("remove:{}", spec.name), e);
                continue;
            }
            
            println!("Removed container {}", spec.name);
        }
        
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
    
    pub async fn get_all_logs(&self) -> HashMap<String, Result<Vec<String>, String>> {
        let mut logs = HashMap::new();
        
        for spec in &self.stages {
            logs.insert(
                spec.name.clone(),
                self.manager.get_container_logs(&spec.name).await,
            );
        }
        
        logs
    }
}

// 使用容器化工作流示例
async fn containerized_workflow_example() {
    // 创建容器化工作流
    let mut workflow = ContainerWorkflow::new()
        .expect("Failed to create workflow")
        .with_network("my_workflow_network");
    
    // 添加工作流阶段
    workflow
        .add_stage(
            ContainerSpec::new("data-fetcher", "python:3.9-slim")
                .with_command(vec!["python", "-c", "print('Fetching data...'); import time; time.sleep(5); print('Data fetched!')"])
                .with_env("LOG_LEVEL", "DEBUG")
                .with_restart_policy("on-failure")
        )
        .add_stage(
            ContainerSpec::new("data-processor", "python:3.9-slim")
                .with_command(vec!["python", "-c", "print('Processing data...'); import time; time.sleep(3); print('Data processed!')"])
                .with_env("BATCH_SIZE", "100")
                .with_memory_limit(512)
        )
        .add_stage(
            ContainerSpec::new("data-exporter", "python:3.9-slim")
                .with_command(vec!["python", "-c", "print('Exporting results...'); import time; time.sleep(2); print('Results exported!')"])
                .with_volume("/tmp/data:/data")
                .with_cpu_limit(0.5)
        );
    
    // 运行工作流
    match workflow.run().await {
        Ok(()) => {
            println!("Workflow completed successfully");
            
            // 获取所有日志
            let logs = workflow.get_all_logs().await;
            for (container, log_result) in logs {
                match log_result {
                    Ok(log_lines) => {
                        println!("=== Logs for {} ===", container);
                        for line in log_lines {
                            println!("{}", line);
                        }
                        println!("====================");
                    }
                    Err(e) => {
                        println!("Failed to get logs for {}: {}", container, e);
                    }
                }
            }
            
            // 清理资源
            if let Err(errors) = workflow.cleanup().await {
                println!("Cleanup errors: {:?}", errors);
            } else {
                println!("All containers stopped and removed");
            }
        }
        Err(errors) => {
            println!("Workflow failed with errors:");
            for (container, error) in &errors {
                println!("{}: {}", container, error);
            }
            
            // 尝试清理资源
            if let Err(cleanup_errors) = workflow.cleanup().await {
                println!("Cleanup errors: {:?}", cleanup_errors);
            }
        }
    }
}
```

**准则**：设计集成 Docker 容器的工作流组件，支持容器生命周期管理和日志收集，实现模块化和可扩展性。

### 3.2 复合拓扑管理

```rust
// 推荐：复合拓扑管理
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};

// 拓扑节点类型
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum NodeType {
    Container {
        image: String,
        command: Option<Vec<String>>,
        environment: HashMap<String, String>,
        volumes: Vec<String>,
    },
    Service {
        image: String,
        replicas: u32,
        ports: Vec<String>,
        environment: HashMap<String, String>,
    },
    Volume {
        driver: String,
        driver_opts: HashMap<String, String>,
    },
    Network {
        driver: String,
        subnet: Option<String>,
    },
}

// 拓扑节点
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TopologyNode {
    id: String,
    name: String,
    node_type: NodeType,
    depends_on: Vec<String>,
    labels: HashMap<String, String>,
}

impl TopologyNode {
    pub fn new(id: impl Into<String>, name: impl Into<String>, node_type: NodeType) -> Self {
        Self {
            id: id.into(),
            name: name.into(),
            node_type,
            depends_on: Vec::new(),
            labels: HashMap::new(),
        }
    }
    
    pub fn with_dependency(mut self, dependency_id: impl Into<String>) -> Self {
        self.depends_on.push(dependency_id.into());
        self
    }
    
    pub fn with_label(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.labels.insert(key.into(), value.into());
        self
    }
    
    pub fn id(&self) -> &str {
        &self.id
    }
    
    pub fn name(&self) -> &str {
        &self.name
    }
    
    pub fn node_type(&self) -> &NodeType {
        &self.node_type
    }
    
    pub fn dependencies(&self) -> &[String] {
        &self.depends_on
    }
}

// 复合拓扑
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompositeTopology {
    name: String,
    version: String,
    nodes: HashMap<String, TopologyNode>,
}

impl CompositeTopology {
    pub fn new(name: impl Into<String>, version: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            version: version.into(),
            nodes: HashMap::new(),
        }
    }
    
    pub fn add_node(&mut self, node: TopologyNode) -> Result<(), String> {
        let id = node.id().to_string();
        
        if self.nodes.contains_key(&id) {
            return Err(format!("Node with ID {} already exists", id));
        }
        
        // 验证依赖
        for dep_id in node.dependencies() {
            if !self.nodes.contains_key(dep_id) {
                return Err(format!("Dependency {} not found", dep_id));
            }
        }
        
        self.nodes.insert(id, node);
        Ok(())
    }
    
    // 计算部署顺序
    pub fn deployment_order(&self) -> Result<Vec<String>, String> {
        // 使用拓扑排序计算部署顺序
        let mut order = Vec::new();
        let mut visited = HashSet::new();
        let mut temp_visited = HashSet::new();
        
        // 拓扑排序 (DFS)
        fn visit(
            node_id: &str,
            nodes: &HashMap<String, TopologyNode>,
            visited: &mut HashSet<String>,
            temp_visited: &mut HashSet<String>,
            order: &mut Vec<String>,
        ) -> Result<(), String> {
            // 检查是否存在循环依赖
            if temp_visited.contains(node_id) {
                return Err(format!("Circular dependency detected involving node {}", node_id));
            }
            
            // 如果已经访问过，跳过
            if visited.contains(node_id) {
                return Ok(());
            }
            
            // 标记为临时访问
            temp_visited.insert(node_id.to_string());
            
            // 访问所有依赖
            let node = &nodes[node_id];
            for dep_id in node.dependencies() {
                visit(dep_id, nodes, visited, temp_visited, order)?;
            }
            
            // 标记为已访问并添加到顺序中
            temp_visited.remove(node_id);
            visited.insert(node_id.to_string());
            order.push(node_id.to_string());
            
            Ok(())
        }
        
        // 对所有节点执行拓扑排序
        for node_id in self.nodes.keys() {
            if !visited.contains(node_id) {
                visit(
                    node_id,
                    &self.nodes,
                    &mut visited,
                    &mut temp_visited,
                    &mut order,
                )?;
            }
        }
        
        Ok(order)
    }
    
    // 生成 Docker Compose 配置
    pub fn to_docker_compose(&self) -> Result<String, String> {
        // 简化版本，实际实现会更复杂
        let mut compose = String::from("version: '3'\n\n");
        
        // 添加服务
        compose.push_str("services:\n");
        
        for node in self.nodes.values() {
            match &node.node_type {
                NodeType::Container { image, command, environment, volumes } |
                NodeType::Service { image, environment, .. } => {
                    compose.push_str(&format!("  {}:\n", node.name()));
                    compose.push_str(&format!("    image: {}\n", image));
                    
                    if let NodeType::Service { ports, replicas, .. } = &node.node_type {
                        compose.push_str(&format!("    deploy:\n"));
                        compose.push_str(&format!("      replicas: {}\n", replicas));
                        
                        if !ports.is_empty() {
                            compose.push_str("    ports:\n");
                            for port in ports {
                                compose.push_str(&format!("      - {}\n", port));
                            }
                        }
                    }
                    
                    if let Some(cmd) = command {
                        compose.push_str("    command: [");
                        for (i, c) in cmd.iter().enumerate() {
                            if i > 0 {
                                compose.push_str(", ");
                            }
                            compose.push_str(&format!("\"{}\"", c));
                        }
                        compose.push_str("]\n");
                    }
                    
                    if !environment.is_empty() {
                        compose.push_str("    environment:\n");
                        for (k, v) in environment {
                            compose.push_str(&format!("      {}: {}\n", k, v));
                        }
                    }
                    
                    if !volumes.is_empty() {
                        compose.push_str("    volumes:\n");
                        for v in volumes {
                            compose.push_str(&format!("      - {}\n", v));
                        }
                    }
                    
                    if !node.dependencies().is_empty() {
                        compose.push_str("    depends_on:\n");
                        for dep in node.dependencies() {
                            let dep_node = &self.nodes[dep];
                            compose.push_str(&format!("      - {}\n", dep_node.name()));
                        }
                    }
                    
                    if !node.labels.is_empty() {
                        compose.push_str("    labels:\n");
                        for (k, v) in &node.labels {
                            compose.push_str(&format!("      {}: {}\n", k, v));
                        }
                    }
                }
                _ => {} // 其他类型在此简化版本中忽略
            }
        }
        
        // 添加卷
        let has_volumes = self.nodes.values().any(|n| matches!(n.node_type, NodeType::Volume { .. }));
        if has_volumes {
            compose.push_str("\nvolumes:\n");
            for node in self.nodes.values() {
                if let NodeType::Volume { driver, driver_opts } = &node.node_type {
                    compose.push_str(&format!("  {}:\n", node.name()));
                    compose.push_str(&format!("    driver: {}\n", driver));
                    
                    if !driver_opts.is_empty() {
                        compose.push_str("    driver_opts:\n");
                        for (k, v) in driver_opts {
                            compose.push_str(&format!("      {}: {}\n", k, v));
                        }
                    }
                }
            }
        }
        
        // 添加网络
        let has_networks = self.nodes.values().any(|n| matches!(n.node_type, NodeType::Network { .. }));
        if has_networks {
            compose.push_str("\nnetworks:\n");
            for node in self.nodes.values() {
                if let NodeType::Network { driver, subnet } = &node.node_type {
                    compose.push_str(&format!("  {}:\n", node.name()));
                    compose.push_str(&format!("    driver: {}\n", driver));
                    
                    if let Some(subnet_value) = subnet {
                        compose.push_str("    ipam:\n");
                        compose.push_str("      config:\n");
                        compose.push_str(&format!("        - subnet: {}\n", subnet_value));
                    }
                }
            }
        }
        
        Ok(compose)
    }
    
    // 验证拓扑
    pub fn validate(&self) -> Result<(), Vec<String>> {
        let mut errors = Vec::new();
        
        // 检查重复名称
        let mut names = HashSet::new();
        for node in self.nodes.values() {
            if !names.insert(node.name()) {
                errors.push(format!("Duplicate node name: {}", node.name()));
            }
        }
        
        // 检查依赖
        for node in self.nodes.values() {
            for dep_id in node.dependencies() {
                if !self.nodes.contains_key(dep_id) {
                    errors.push(format!(
                        "Node {} depends on non-existent node {}",
                        node.id(), dep_id
                    ));
                }
            }
        }
        
        // 检查循环依赖
        if let Err(e) = self.deployment_order() {
            errors.push(e);
        }
        
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
    
    // 克隆并扩展拓扑
    pub fn extend(&self, other: &CompositeTopology) -> Result<CompositeTopology, String> {
        let mut result = self.clone();
        
        for (id, node) in &other.nodes {
            if result.nodes.contains_key(id) {
                return Err(format!("Node ID conflict: {} already exists", id));
            }
            
            result.nodes.insert(id.clone(), node.clone());
        }
        
        // 验证扩展后的拓扑
        if let Err(e) = result.validate() {
            return Err(format!("Invalid extended topology: {:?}", e));
        }
        
        Ok(result)
    }
}

// 使用复合拓扑示例
fn composite_topology_example() {
    // 创建基础拓扑
    let mut base_topology = CompositeTopology::new("base-system", "1.0");
    
    // 添加网络节点
    let network = TopologyNode::new(
        "app-network",
        "app_network",
        NodeType::Network {
            driver: "bridge".into(),
            subnet: Some("172.28.0.0/16".into()),
        },
    );
    
    base_topology.add_node(network).expect("Failed to add network");
    
    // 添加数据卷节点
    let data_volume = TopologyNode::new(
        "data-volume",
        "data_volume",
        NodeType::Volume {
            driver: "local".into(),
            driver_opts: HashMap::new(),
        },
    );
    
    base_topology.add_node(data_volume).expect("Failed to add volume");
    
    // 添加数据库服务节点
    let db_env = {
        let mut env = HashMap::new();
        env.insert("POSTGRES_USER".into(), "app".into());
        env.insert("POSTGRES_PASSWORD".into(), "password".into());
        env.insert("POSTGRES_DB".into(), "app_db".into());
        env
    };
    
    let db_service = TopologyNode::new(
        "db-service",
        "db",
        NodeType::Service {
            image: "postgres:13".into(),
            replicas: 1,
            ports: vec!["5432:5432".into()],
            environment: db_env,
        },
    )
    .with_dependency("data-volume")
    .with_dependency("app-network")
    .with_label("component", "database");
    
    base_topology.add_node(db_service).expect("Failed to add database service");
    
    // 创建扩展拓扑
    let mut app_topology = CompositeTopology::new("app-system", "1.0");
    
    // 添加应用服务节点
    let app_env = {
        let mut env = HashMap::new();
        env.insert("DB_HOST".into(), "db".into());
        env.insert("DB_USER".into(), "app".into());
        env.insert("DB_PASSWORD".into(), "password".into());
        env.insert("DB_NAME".into(), "app_db".into());
        env
    };
    
    let app_service = TopologyNode::new(
        "app-service",
        "app",
        NodeType::Service {
            image: "my-app:latest".into(),
            replicas: 2,
            ports: vec!["8080:8080".into()],
            environment: app_env,
        },
    )
    .with_dependency("db-service")
    .with_label("component", "application");
    
    app_topology.add_node(app_service).expect("Failed to add app service");
    
    // 合并拓扑
    let combined_topology = base_topology.extend(&app_topology)
        .expect("Failed to extend topology");
    
    // 验证拓扑
    combined_topology.validate().expect("Invalid topology");
    
    // 计算部署顺序
    let deployment_order = combined_topology.deployment_order()
        .expect("Failed to calculate deployment order");
    
    println!("Deployment order:");
    for node_id in &deployment_order {
        let node = &combined_topology.nodes[node_id];
        println!("  {} ({})", node.name(), node_id);
    }
    
    // 生成 Docker Compose 配置
    let compose_config = combined_topology.to_docker_compose()
        .expect("Failed to generate Docker Compose config");
    
    println!("\nDocker Compose Configuration:");
    println!("{}", compose_config);
}
```

**准则**：设计支持复合拓扑和依赖管理的系统，实现模块化部署和自动化配置生成。

## 4. 分布式系统控制与恢复

### 4.1 故障检测与自愈

```rust
// 推荐：故障检测与自愈系统
use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::RwLock;
use tokio::task::JoinHandle;
use tokio::time::sleep;

// 服务健康状态
#[derive(Debug, Clone, PartialEq)]
pub enum HealthStatus {
    Healthy,
    Degraded(String),
    Unhealthy(String),
    Unknown,
}

impl fmt::Display for HealthStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            HealthStatus::Healthy => write!(f, "Healthy"),
            HealthStatus::Degraded(reason) => write!(f, "Degraded: {}", reason),
            HealthStatus::Unhealthy(reason) => write!(f, "Unhealthy: {}", reason),
            HealthStatus::Unknown => write!(f, "Unknown"),
        }
    }
}

// 服务检查接口
#[async_trait::async_trait]
pub trait HealthCheck: Send + Sync {
    // 服务名称
    fn name(&self) -> &str;
    
    // 执行健康检查
    async fn check_health(&self) -> HealthStatus;
    
    // 尝试恢复服务
    async fn attempt_recovery(&self) -> Result<(), String>;
    
    // 服务依赖
    fn dependencies(&self) -> Vec<String> {
        Vec::new()
    }
}

// HTTP 服务健康检查
pub struct HttpHealthCheck {
    name: String,
    endpoint: String,
    client: reqwest::Client,
    timeout: Duration,
    dependencies: Vec<String>,
    recovery_command: Option<String>,
}

impl HttpHealthCheck {
    pub fn new(name: impl Into<String>, endpoint: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            endpoint: endpoint.into(),
            client: reqwest::Client::new(),
            timeout: Duration::from_secs(5),
            dependencies: Vec::new(),
            recovery_command: None,
        }
    }
    
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = timeout;
        self
    }
    
    pub fn with_dependency(mut self, dependency: impl Into<String>) -> Self {
        self.dependencies.push(dependency.into());
        self
    }
    
    pub fn with_recovery_command(mut self, command: impl Into<String>) -> Self {
        self.recovery_command = Some(command.into());
        self
    }
}

#[async_trait::async_trait]
impl HealthCheck for HttpHealthCheck {
    fn name(&self) -> &str {
        &self.name
    }
    
    async fn check_health(&self) -> HealthStatus {
        let request = match self.client
            .get(&self.endpoint)
            .timeout(self.timeout)
            .build() {
                Ok(req) => req,
                Err(e) => return HealthStatus::Unhealthy(format!("Failed to build request: {}", e)),
            };
        
        match self.client.execute(request).await {
            Ok(response) => {
                let status = response.status();
                if status.is_success() {
                    HealthStatus::Healthy
                } else if status.is_server_error() {
                    HealthStatus::Unhealthy(format!("Server error: {}", status))
                } else {
                    HealthStatus::Degraded(format!("Unexpected status: {}", status))
                }
            }
            Err(e) => {
                if e.is_timeout() {
                    HealthStatus::Unhealthy(format!("Request timed out after {:?}", self.timeout))
                } else if e.is_connect() {
                    HealthStatus::Unhealthy(format!("Connection error: {}", e))
                } else {
                    HealthStatus::Unhealthy(format!("Request failed: {}", e))
                }
            }
        }
    }
    
    async fn attempt_recovery(&self) -> Result<(), String> {
        if let Some(command) = &self.recovery_command {
            println!("Attempting recovery for {}: {}", self.name, command);
            
            // 解析命令
            let parts: Vec<&str> = command.split_whitespace().collect();
            if parts.is_empty() {
                return Err("Empty recovery command".into());
            }
            
            // 执行命令
            let output = tokio::process::Command::new(parts[0])
                .args(&parts[1..])
                .output()
                .await
                .map_err(|e| format!("Failed to execute recovery command: {}", e))?;
            
            if output.status.success() {
                Ok(())
            } else {
                let stderr = String::from_utf8_lossy(&output.stderr);
                Err(format!("Recovery command failed: {}", stderr))
            }
        } else {
            Err("No recovery command configured".into())
        }
    }
    
    fn dependencies(&self) -> Vec<String> {
        self.dependencies.clone()
    }
}

// 自定义健康检查
pub struct CustomHealthCheck<F, R>
where
    F: Fn() -> R + Send + Sync,
    R: std::future::Future<Output = HealthStatus> + Send,
{
    name: String,
    check_fn: F,
    recovery_fn: Option<Box<dyn Fn() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<(), String>> + Send>> + Send + Sync>>,
    dependencies: Vec<String>,
}

impl<F, R> CustomHealthCheck<F, R>
where
    F: Fn() -> R + Send + Sync,
    R: std::future::Future<Output = HealthStatus> + Send,
{
    pub fn new(name: impl Into<String>, check_fn: F) -> Self {
        Self {
            name: name.into(),
            check_fn,
            recovery_fn: None,
            dependencies: Vec::new(),
        }
    }
    
    pub fn with_recovery<RF, RR>(mut self, recovery_fn: RF) -> Self
    where
        RF: Fn() -> RR + Send + Sync + 'static,
        RR: std::future::Future<Output = Result<(), String>> + Send + 'static,
    {
        self.recovery_fn = Some(Box::new(move || Box::pin(recovery_fn()) as _));
        self
    }
    
    pub fn with_dependency(mut self, dependency: impl Into<String>) -> Self {
        self.dependencies.push(dependency.into());
        self
    }
}

#[async_trait::async_trait]
impl<F, R> HealthCheck for CustomHealthCheck<F, R>
where
    F: Fn() -> R + Send + Sync,
    R: std::future::Future<Output = HealthStatus> + Send,
{
    fn name(&self) -> &str {
        &self.name
    }
    
    async fn check_health(&self) -> HealthStatus {
        (self.check_fn)().await
    }
    
    async fn attempt_recovery(&self) -> Result<(), String> {
        if let Some(recovery) = &self.recovery_fn {
            recovery().await
        } else {
            Err("No recovery function configured".into())
        }
    }
    
    fn dependencies(&self) -> Vec<String> {
        self.dependencies.clone()
    }
}

// 健康监控系统
pub struct HealthMonitor {
    checks: HashMap<String, Arc<dyn HealthCheck>>,
    status: Arc<RwLock<HashMap<String, (HealthStatus, Instant)>>>,
    check_interval: Duration,
    recovery_attempts: HashMap<String, usize>,
    max_recovery_attempts: usize,
    monitor_handle: Option<JoinHandle<()>>,
}

impl HealthMonitor {
    pub fn new(check_interval: Duration) -> Self {
        Self {
            checks: HashMap::new(),
            status: Arc::new(RwLock::new(HashMap::new())),
            check_interval,
            recovery_attempts: HashMap::new(),
            max_recovery_attempts: 3,
            monitor_handle: None,
        }
    }
    
    pub fn register_check(&mut self, check: impl HealthCheck + 'static) -> Result<(), String> {
        let name = check.name().to_string();
        
        if self.checks.contains_key(&name) {
            return Err(format!("Health check with name {} already registered", name));
        }
        
        self.checks.insert(name.clone(), Arc::new(check));
        self.recovery_attempts.insert(name, 0);
        
        Ok(())
    }
    
    pub fn set_max_recovery_attempts(&mut self, max_attempts: usize) {
        self.max_recovery_attempts = max_attempts;
    }
    
    // 启动健康监控
    pub fn start(&mut self) {
        // 如果已经在运行，则忽略
        if self.monitor_handle.is_some() {
            return;
        }
        
        let checks = self.checks.clone();
        let status = self.status.clone();
        let check_interval = self.check_interval;
        let max_recovery_attempts = self.max_recovery_attempts;
        let mut recovery_attempts = self.recovery_attempts.clone();
        
        // 启动监控任务
        let handle = tokio::spawn(async move {
            loop {
                // 执行所有健康检查
                for (name, check) in &checks {
                    let health = check.check_health().await;
                    
                    // 更新状态
                    {
                        let mut status_map = status.write().await;
                        status_map.insert(name.clone(), (health.clone(), Instant::now()));
                    }
                    
                    // 如果不健康，尝试恢复
                    if matches!(health, HealthStatus::Unhealthy(_)) {
                        let attempts = recovery_attempts.entry(name.clone()).or_insert(0);
                        
                        if *attempts < max_recovery_attempts {
                            *attempts += 1;
                            
                            println!(
                                "Service {} is unhealthy, attempting recovery ({}/{})",
                                name, *attempts, max_recovery_attempts
                            );
                            
                            // 尝试恢复
                            match check.attempt_recovery().await {
                                Ok(()) => {
                                    println!("Recovery attempt for {} succeeded", name);
                                    
                                    // 重新检查健康状态
                                    let new_health = check.check_health().await;
                                    let mut status_map = status.write().await;
                                    status_map.insert(name.clone(), (new_health, Instant::now()));
                                    
                                    // 如果恢复成功，重置恢复计数
                                    if matches!(new_health, HealthStatus::Healthy) {
                                        *attempts = 0;
                                    }
                                }
                                Err(e) => {
                                    println!("Recovery attempt for {} failed: {}", name, e);
                                }
                            }
                        } else {
                            println!(
                                "Service {} remains unhealthy after {} recovery attempts",
                                name, *attempts
                            );
                        }
                    } else if matches!(health, HealthStatus::Healthy) {
                        // 如果健康，重置恢复计数
                        recovery_attempts.insert(name.clone(), 0);
                    }
                }
                
                // 等待下一个检查间隔
                sleep(check_interval).await;
            }
        });
        
        self.monitor_handle = Some(handle);
    }
    
    // 停止健康监控
    pub fn stop(&mut self) {
        if let Some(handle) = self.monitor_handle.take() {
            handle.abort();
        }
    }
    
    // 获取所有服务的健康状态
    pub async fn get_all_status(&self) -> HashMap<String, (HealthStatus, Instant)> {
        let status = self.status.read().await;
        status.clone()
    }
    
    // 获取特定服务的健康状态
    pub async fn get_status(&self, name: &str) -> Option<(HealthStatus, Instant)> {
        let status = self.status.read().await;
        status.get(name).cloned()
    }
    
    // 检查系统整体健康状态
    pub async fn check_system_health(&self) -> HealthStatus {
        let all_status = self.status.read().await;
        
        // 如果没有健康检查，返回未知状态
        if all_status.is_empty() {
            return HealthStatus::Unknown;
        }
        
        // 计算不同状态的服务数量
        let mut unhealthy_count = 0;
        let mut degraded_count = 0;
        let mut unknown_count = 0;
        let mut unhealthy_services = Vec::new();
        
        for (name, (status, _)) in all_status.iter() {
            match status {
                HealthStatus::Unhealthy(_) => {
                    unhealthy_count += 1;
                    unhealthy_services.push(name.clone());
                }
                HealthStatus::Degraded(_) => degraded_count += 1,
                HealthStatus::Unknown => unknown_count += 1,
                _ => {}
            }
        }
        
        // 根据不同状态数量确定系统整体状态
        if unhealthy_count > 0 {
            HealthStatus::Unhealthy(format!("Unhealthy services: {}", unhealthy_services.join(", ")))
        } else if degraded_count > 0 {
            HealthStatus::Degraded(format!("{} services in degraded state", degraded_count))
        } else if unknown_count > 0 {
            HealthStatus::Degraded(format!("{} services in unknown state", unknown_count))
        } else {
            HealthStatus::Healthy
        }
    }
}

// 使用健康监控系统示例
async fn health_monitoring_example() {
    // 创建健康监控系统
    let mut monitor = HealthMonitor::new(Duration::from_secs(30));
    
    // 注册 HTTP 健康检查
    let api_check = HttpHealthCheck::new("api-service", "http://localhost:8080/health")
        .with_timeout(Duration::from_secs(2))
        .with_recovery_command("docker restart api-service");
    
    monitor.register_check(api_check).expect("Failed to register API check");
    
    // 注册数据库健康检查
    let db_check = HttpHealthCheck::new("database", "http://localhost:5432/health")
        .with_dependency("api-service")
        .with_recovery_command("docker restart postgres");
    
    monitor.register_check(db_check).expect("Failed to register DB check");
    
    // 注册自定义健康检查
    let custom_check = CustomHealthCheck::new("custom-service", || async {
        // 模拟自定义健康检查逻辑
        if rand::random::<f32>() < 0.8 {
            HealthStatus::Healthy
        } else {
            HealthStatus::Degraded("Simulated performance issue".into())
        }
    })
    .with_recovery(|| async {
        // 模拟自定义恢复逻辑
        println!("Performing custom recovery action");
        
        // 模拟恢复操作
        tokio::time::sleep(Duration::from_millis(500)).await;
        
        // 模拟恢复结果
        if rand::random::<f32>() < 0.7 {
            Ok(())
        } else {
            Err("Custom recovery failed".into())
        }
    });
    
    monitor.register_check(custom_check).expect("Failed to register custom check");
    
    // 启动健康监控
    monitor.start();
    
    // 模拟运行一段时间
    for i in 0..5 {
        println!("Checking system health (iteration {})", i);
        
        // 获取系统健康状态
        let system_health = monitor.check_system_health().await;
        println!("System health: {}", system_health);
        
        // 获取所有服务健康状态
        let all_status = monitor.get_all_status().await;
        println!("Service health status:");
        
        for (name, (status, last_checked)) in all_status {
            let elapsed = last_checked.elapsed();
            println!(
                "  {}: {} (last checked {} seconds ago)",
                name, status, elapsed.as_secs()
            );
        }
        
        // 等待一段时间
        tokio::time::sleep(Duration::from_secs(5)).await;
    }
    
    // 停止健康监控
    monitor.stop();
}
```

**准则**：设计主动故障检测和自愈系统，支持多种健康检查方式和自动化恢复策略。

### 4.2 容错与幂等性

```rust
// 推荐：容错与幂等性模式
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::hash::Hash;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{Mutex, RwLock};
use tokio::time::{sleep, timeout};
use uuid::Uuid;

// 操作结果缓存 - 用于确保幂等性
#[derive(Clone, Debug)]
struct CachedResult<T> {
    result: T,
    timestamp: Instant,
}

// 幂等操作执行器
pub struct IdempotentExecutor<K, T>
where
    K: Eq + Hash + Clone,
    T: Clone,
{
    results_cache: Arc<RwLock<HashMap<K, CachedResult<T>>>>,
    cache_ttl: Duration,
}

impl<K, T> IdempotentExecutor<K, T>
where
    K: Eq + Hash + Clone,
    T: Clone,
{
    pub fn new(cache_ttl: Duration) -> Self {
        Self {
            results_cache: Arc::new(RwLock::new(HashMap::new())),
            cache_ttl,
        }
    }
    
    // 执行幂等操作
    pub async fn execute<F, Fut>(&self, key: K, operation: F) -> T
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = T>,
    {
        // 首先检查缓存
        if let Some(cached) = self.get_cached_result(&key).await {
            return cached;
        }
        
        // 执行操作
        let result = operation().await;
        
        // 缓存结果
        self.cache_result(key, result.clone()).await;
        
        result
    }
    
    // 从缓存获取结果
    async fn get_cached_result(&self, key: &K) -> Option<T> {
        let cache = self.results_cache.read().await;
        
        if let Some(cached) = cache.get(key) {
            // 检查结果是否过期
            if cached.timestamp.elapsed() < self.cache_ttl {
                return Some(cached.result.clone());
            }
        }
        
        None
    }
    
    // 缓存结果
    async fn cache_result(&self, key: K, result: T) {
        let mut cache = self.results_cache.write().await;
        
        cache.insert(
            key,
            CachedResult {
                result,
                timestamp: Instant::now(),
            },
        );
    }
    
    // 清理过期缓存
    pub async fn cleanup_expired(&self) {
        let mut cache = self.results_cache.write().await;
        
        cache.retain(|_, cached| cached.timestamp.elapsed() < self.cache_ttl);
    }
}

// 断路器状态
#[derive(Debug, Clone, PartialEq)]
enum CircuitState {
    Closed,              // 正常状态，允许请求
    Open {               // 断开状态，阻止请求
        opened_at: Instant,
        reset_timeout: Duration,
    },
    HalfOpen {           // 半开状态，允许有限请求以测试服务恢复
        allowed_requests: usize,
        successful_requests: usize,
        required_successes: usize,
    },
}

// 断路器
pub struct CircuitBreaker {
    name: String,
    state: Arc<RwLock<CircuitState>>,
    failure_threshold: usize,
    reset_timeout: Duration,
    half_open_max_requests: usize,
    recent_failures: Arc<Mutex<Vec<Instant>>>,
    metrics: Arc<RwLock<CircuitBreakerMetrics>>,
}

// 断路器指标
#[derive(Debug, Clone, Default)]
pub struct CircuitBreakerMetrics {
    total_requests: usize,
    successful_requests: usize,
    failed_requests: usize,
    rejected_requests: usize,
    state_transitions: Vec<(Instant, String)>,
}

impl CircuitBreaker {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            state: Arc::new(RwLock::new(CircuitState::Closed)),
            failure_threshold: 5,
            reset_timeout: Duration::from_secs(30),
            half_open_max_requests: 3,
            recent_failures: Arc::new(Mutex::new(Vec::new())),
            metrics: Arc::new(RwLock::new(CircuitBreakerMetrics::default())),
        }
    }
    
    pub fn with_failure_threshold(mut self, threshold: usize) -> Self {
        self.failure_threshold = threshold;
        self
    }
    
    pub fn with_reset_timeout(mut self, timeout: Duration) -> Self {
        self.reset_timeout = timeout;
        self
    }
    
    pub fn with_half_open_max_requests(mut self, max_requests: usize) -> Self {
        self.half_open_max_requests = max_requests;
        self
    }
    
    // 执行受断路器保护的操作
    pub async fn execute<F, T, E>(&self, operation: F) -> Result<T, CircuitBreakerError<E>>
    where
        F: FnOnce() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T, E>> + Send>>,
        E: std::fmt::Debug,
    {
        // 更新指标
        {
            let mut metrics = self.metrics.write().await;
            metrics.total_requests += 1;
        }
        
        // 检查断路器状态
        let can_execute = self.check_can_execute().await;
        
        if !can_execute {
            // 更新指标
            {
                let mut metrics = self.metrics.write().await;
                metrics.rejected_requests += 1;
            }
            
            return Err(CircuitBreakerError::Rejected(format!(
                "Circuit breaker {} is open", self.name
            )));
        }
        
        // 执行操作
        match operation().await {
            Ok(result) => {
                // 记录成功
                self.record_success().await;
                
                // 更新指标
                {
                    let mut metrics = self.metrics.write().await;
                    metrics.successful_requests += 1;
                }
                
                Ok(result)
            }
            Err(error) => {
                // 记录失败
                self.record_failure().await;
                
                // 更新指标
                {
                    let mut metrics = self.metrics.write().await;
                    metrics.failed_requests += 1;
                }
                
                Err(CircuitBreakerError::OperationFailed(error))
            }
        }
    }
    
    // 检查是否可以执行操作
    async fn check_can_execute(&self) -> bool {
        let state = self.state.read().await.clone();
        
        match state {
            CircuitState::Closed => true,
            CircuitState::Open { opened_at, reset_timeout } => {
                // 检查是否应该转换到半开状态
                if opened_at.elapsed() >= reset_timeout {
                    // 转换到半开状态
                    let mut state = self.state.write().await;
                    *state = CircuitState::HalfOpen {
                        allowed_requests: self.half_open_max_requests,
                        successful_requests: 0,
                        required_successes: self.half_open_max_requests,
                    };
                    
                    // 记录状态转换
                    let mut metrics = self.metrics.write().await;
                    metrics.state_transitions.push((Instant::now(), "OPEN -> HALF_OPEN".into()));
                    
                    true
                } else {
                    false
                }
            }
            CircuitState::HalfOpen { allowed_requests, .. } => {
                // 在半开状态下，只允许有限数量的请求
                allowed_requests > 0
            }
        }
    }
    
    // 记录成功操作
    async fn record_success(&self) {
        let mut state = self.state.write().await;
        
        match *state {
            CircuitState::HalfOpen { allowed_requests, successful_requests, required_successes } => {
                // 更新半开状态
                let new_allowed = allowed_requests - 1;
                let new_successful = successful_requests + 1;
                
                if new_successful >= required_successes {
                    // 足够的成功请求，恢复到关闭状态
                    *state = CircuitState::Closed;
                    
                    // 清除失败记录
                    let mut failures = self.recent_failures.lock().await;
                    failures.clear();
                    
                    // 记录状态转换
                    let mut metrics = self.metrics.write().await;
                    metrics.state_transitions.push((Instant::now(), "HALF_OPEN -> CLOSED".into()));
                } else {
                    // 还需要更多成功请求
                    *state = CircuitState::HalfOpen {
                        allowed_requests: new_allowed,
                        successful_requests: new_successful,
                        required_successes,
                    };
                }
            }
            _ => {
                // 在闭合状态下，只需记录成功
            }
        }
    }
    
    // 记录失败操作
    async fn record_failure(&self) {
        // 添加失败记录
        {
            let mut failures = self.recent_failures.lock().await;
            failures.push(Instant::now());
            
            // 只保留最近的失败记录
            while failures.len() > self.failure_threshold {
                failures.remove(0);
            }
            
            // 检查是否达到失败阈值
            if failures.len() >= self.failure_threshold {
                let oldest_failure = failures[0];
                
                // 检查失败是否在短时间内发生
                if oldest_failure.elapsed() <= Duration::from_secs(60) {
                    // 转换到开路状态
                    let mut state = self.state.write().await;
                    
                    // 只有在当前是闭合或半开状态时才转换
                    if *state != CircuitState::Open { opened_at: Instant::now(), reset_timeout: self.reset_timeout } {
                        *state = CircuitState::Open {
                            opened_at: Instant::now(),
                            reset_timeout: self.reset_timeout,
                        };
                        
                        // 记录状态转换
                        let mut metrics = self.metrics.write().await;
                        let transition = match *state {
                            CircuitState::Closed => "CLOSED -> OPEN",
                            CircuitState::HalfOpen { .. } => "HALF_OPEN -> OPEN",
                            _ => "? -> OPEN",
                        };
                        metrics.state_transitions.push((Instant::now(), transition.into()));
                    }
                }
            }
        }
        
        // 处理半开状态下的失败
        let mut state = self.state.write().await;
        if let CircuitState::HalfOpen { .. } = *state {
            // 在半开状态下，任何失败都会导致回到开路状态
            *state = CircuitState::Open {
                opened_at: Instant::now(),
                reset_timeout: self.reset_timeout,
            };
            
            // 记录状态转换
            let mut metrics = self.metrics.write().await;
            metrics.state_transitions.push((Instant::now(), "HALF_OPEN -> OPEN".into()));
        }
    }
    
    // 获取当前状态
    pub async fn get_state(&self) -> CircuitState {
        let state = self.state.read().await;
        state.clone()
    }
    
    // 获取指标
    pub async fn get_metrics(&self) -> CircuitBreakerMetrics {
        let metrics = self.metrics.read().await;
        metrics.clone()
    }
    
    // 手动重置断路器到闭合状态
    pub async fn reset(&self) {
        let mut state = self.state.write().await;
        *state = CircuitState::Closed;
        
        // 清除失败记录
        let mut failures = self.recent_failures.lock().await;
        failures.clear();
        
        // 记录状态转换
        let mut metrics = self.metrics.write().await;
        metrics.state_transitions.push((Instant::now(), "MANUAL RESET -> CLOSED".into()));
    }
}

// 断路器错误
#[derive(Debug)]
pub enum CircuitBreakerError<E> {
    Rejected(String),         // 请求被断路器拒绝
    OperationFailed(E),       // 操作失败，原始错误
}

// 请求ID生成器 - 用于幂等请求跟踪
#[derive(Clone)]
pub struct RequestIdGenerator {
    prefix: String,
}

impl RequestIdGenerator {
    pub fn new(prefix: impl Into<String>) -> Self {
        Self {
            prefix: prefix.into(),
        }
    }
    
    pub fn generate(&self) -> String {
        format!("{}-{}", self.prefix, Uuid::new_v4())
    }
}

// 幂等请求处理器
#[derive(Clone)]
pub struct IdempotentRequest {
    request_id: String,
    timestamp: chrono::DateTime<chrono::Utc>,
}

impl IdempotentRequest {
    pub fn new(request_id: impl Into<String>) -> Self {
        Self {
            request_id: request_id.into(),
            timestamp: chrono::Utc::now(),
        }
    }
    
    pub fn request_id(&self) -> &str {
        &self.request_id
    }
    
    pub fn timestamp(&self) -> chrono::DateTime<chrono::Utc> {
        self.timestamp
    }
}

// 可重试操作
pub struct RetryableOperation<T, E> {
    max_attempts: usize,
    retry_delay: Duration,
    jitter: bool,
    timeout: Option<Duration>,
    operation_name: String,
    _phantom: std::marker::PhantomData<(T, E)>,
}

impl<T, E> RetryableOperation<T, E>
where
    T: Send + 'static,
    E: std::fmt::Debug + Send + 'static,
{
    pub fn new(operation_name: impl Into<String>) -> Self {
        Self {
            max_attempts: 3,
            retry_delay: Duration::from_millis(500),
            jitter: true,
            timeout: None,
            operation_name: operation_name.into(),
            _phantom: std::marker::PhantomData,
        }
    }
    
    pub fn with_max_attempts(mut self, attempts: usize) -> Self {
        self.max_attempts = attempts;
        self
    }
    
    pub fn with_retry_delay(mut self, delay: Duration) -> Self {
        self.retry_delay = delay;
        self
    }
    
    pub fn with_jitter(mut self, enable: bool) -> Self {
        self.jitter = enable;
        self
    }
    
    pub fn with_timeout(mut self, duration: Duration) -> Self {
        self.timeout = Some(duration);
        self
    }
    
    // 执行可重试操作
    pub async fn execute<F, Fut>(&self, operation: F) -> Result<T, RetryError<E>>
    where
        F: Fn() -> Fut + Send + Sync,
        Fut: std::future::Future<Output = Result<T, E>> + Send,
    {
        let mut attempt = 0;
        let mut last_error: Option<E> = None;
        
        while attempt < self.max_attempts {
            attempt += 1;
            
            // 计算当前延迟
            let current_delay = if self.jitter && attempt > 1 {
                let jitter = rand::random::<f64>() * 0.3 + 0.85; // 85% to 115% of base delay
                Duration::from_secs_f64(self.retry_delay.as_secs_f64() * jitter)
            } else {
                self.retry_delay
            };
            
            // 记录尝试信息
            if attempt > 1 {
                println!(
                    "Retrying operation {} (attempt {}/{})",
                    self.operation_name, attempt, self.max_attempts
                );
            }
            
            // 执行操作，可能带有超时
            let operation_result = if let Some(timeout_duration) = self.timeout {
                match timeout(timeout_duration, operation()).await {
                    Ok(result) => result,
                    Err(_) => {
                        println!(
                            "Operation {} timed out after {:?} (attempt {}/{})",
                            self.operation_name, timeout_duration, attempt, self.max_attempts
                        );
                        
                        // 如果超时且已达到最大尝试次数，返回超时错误
                        if attempt >= self.max_attempts {
                            return Err(RetryError::Timeout(format!(
                                "Operation timed out after {} attempts",
                                attempt
                            )));
                        }
                        
                        // 否则继续尝试
                        sleep(current_delay).await;
                        continue;
                    }
                }
            } else {
                operation().await
            };
            
            // 处理操作结果
            match operation_result {
                Ok(result) => {
                    // 操作成功
                    if attempt > 1 {
                        println!(
                            "Operation {} succeeded after {} attempts",
                            self.operation_name, attempt
                        );
                    }
                    
                    return Ok(result);
                }
                Err(error) => {
                    // 操作失败
                    println!(
                        "Operation {} failed (attempt {}/{}): {:?}",
                        self.operation_name, attempt, self.max_attempts, error
                    );
                    
                    last_error = Some(error);
                    
                    // 如果已达到最大尝试次数，返回错误
                    if attempt >= self.max_attempts {
                        break;
                    }
                    
                    // 否则等待后重试
                    sleep(current_delay).await;
                }
            }
        }
        
        // 所有重试都失败
        Err(RetryError::MaxAttemptsExceeded {
            attempts: attempt,
            last_error,
        })
    }
}

// 重试错误
#[derive(Debug)]
pub enum RetryError<E> {
    Timeout(String),
    MaxAttemptsExceeded {
        attempts: usize,
        last_error: Option<E>,
    },
}

// 综合使用容错模式示例
async fn fault_tolerance_example() {
    // 创建幂等执行器
    let idempotent_executor = IdempotentExecutor::<String, String>::new(Duration::from_secs(300));
    
    // 创建断路器
    let circuit_breaker = CircuitBreaker::new("external-api")
        .with_failure_threshold(3)
        .with_reset_timeout(Duration::from_secs(15))
        .with_half_open_max_requests(2);
    
    // 创建请求ID生成器
    let id_generator = RequestIdGenerator::new("api-call");
    
    // 创建可重试操作
    let retryable_op = RetryableOperation::<String, String>::new("fetch-data")
        .with_max_attempts(3)
        .with_retry_delay(Duration::from_millis(200))
        .with_timeout(Duration::from_secs(2));
    
    // 模拟API调用函数
    async fn api_call(id: &str, should_fail: bool) -> Result<String, String> {
        println!("Executing API call with ID: {}", id);
        
        // 模拟处理时间
        sleep(Duration::from_millis(100)).await;
        
        if should_fail {
            Err("API call failed".into())
        } else {
            Ok(format!("Response for {}", id))
        }
    }
    
    // 执行几次操作，演示容错行为
    for i in 0..10 {
        let request_id = id_generator.generate();
        let should_fail = i >= 6 && i <= 8; // 使请求 6-8 失败以触发断路器
        
        println!("\nRequest {}: ID = {}", i, request_id);
        
        // 使用幂等执行器包装操作
        let result = idempotent_executor
            .execute(request_id.clone(), || async {
                // 使用断路器保护操作
                let circuit_result = circuit_breaker
                    .execute(|| Box::pin(async move {
                        // 使用重试逻辑包装操作
                        retryable_op.execute(|| api_call(&request_id, should_fail)).await
                            .map_err(|e| format!("Retry failed: {:?}", e))
                    }))
                    .await;
                
                match circuit_result {
                    Ok(result) => result,
                    Err(CircuitBreakerError::Rejected(reason)) => {
                        format!("Request rejected by circuit breaker: {}", reason)
                    }
                    Err(CircuitBreakerError::OperationFailed(error)) => {
                        format!("Operation failed: {}", error)
                    }
                }
            })
            .await;
        
        println!("Result: {}", result);
        
        if i % 3 == 0 {
            // 打印断路器状态和指标
            let state = circuit_breaker.get_state().await;
            let metrics = circuit_breaker.get_metrics().await;
            
            println!("Circuit Breaker State: {:?}", state);
            println!("Metrics: {} total, {} success, {} failed, {} rejected",
                   metrics.total_requests,
                   metrics.successful_requests,
                   metrics.failed_requests,
                   metrics.rejected_requests);
            
            if !metrics.state_transitions.is_empty() {
                println!("Recent transitions:");
                for (time, transition) in metrics.state_transitions.iter().rev().take(3) {
                    println!("  {} ago: {}", humantime::format_duration(time.elapsed()), transition);
                }
            }
        }
        
        // 稍等一会儿再进行下一次操作
        sleep(Duration::from_millis(500)).await;
    }
    
    // 等待足够长的时间，让断路器重置
    println!("\nWaiting for circuit breaker to reset...");
    sleep(Duration::from_secs(20)).await;
    
    // 尝试一次成功的操作，看断路器是否已重置
    let request_id = id_generator.generate();
    
    let result = circuit_breaker
        .execute(|| Box::pin(async {
            api_call(&request_id, false).await
        }))
        .await;
    
    match result {
        Ok(response) => println!("Circuit reset successful, got response: {}", response),
        Err(e) => println!("Circuit still open or operation failed: {:?}", e),
    }
    
    // 打印最终状态
    let state = circuit_breaker.get_state().await;
    let metrics = circuit_breaker.get_metrics().await;
    
    println!("Final Circuit Breaker State: {:?}", state);
    println!("Final Metrics: {} total, {} success, {} failed, {} rejected",
           metrics.total_requests,
           metrics.successful_requests,
           metrics.failed_requests,
           metrics.rejected_requests);
}
```

**准则**：设计具备容错性和幂等性的组件，确保系统在面临各种故障时能够可靠运行。

## 5. 总结：现代分布式系统设计最佳实践

综合考虑工作流组合、算法设计、可观测性、Docker集成和分布式系统特性，我们可以总结出以下关键设计准则：

### 5.1 可观测性与透明度

1. **嵌入式遥测**：设计组件时，内置支持 OpenTelemetry 等标准可观测性框架，收集跟踪、指标和日志数据。
2. **跨组件跟踪**：在所有组件接口中传递跟踪上下文，确保分布式请求可以端到端跟踪。
3. **健康与指标暴露**：为每个组件提供标准的健康检查和指标端点，便于监控系统集成。
4. **结构化日志**：使用结构化日志记录关键事件，包括请求处理、状态变化和错误情况，提高问题诊断效率。

### 5.2 组合性与弹性

1. **模块化接口**：设计支持组合的接口，通过特征和装饰器模式实现功能叠加，如可观测性、重试逻辑等。
2. **容错模式组合**：集成断路器、重试、超时、幂等性等容错模式，构建多层次防御体系。
3. **自适应行为**：设计能够根据系统状态自动调整行为的组件，如自动扩缩容、自适应批处理、动态超时等。
4. **优雅降级**：为关键功能提供多级降级策略，确保核心服务在部分功能不可用时仍能运行。

### 5.3 容器集成与拓扑管理

1. **拓扑感知**：设计组件时考虑其在容器化环境中的部署拓扑，支持服务发现和动态配置。
2. **Docker生命周期集成**：提供容器生命周期管理接口，支持优雅启动、健康检查和优雅关闭。
3. **拓扑组合**：实现复合拓扑模型，支持不同组件的依赖管理和部署排序。
4. **配置生成**：基于应用需求自动生成 Docker Compose 或 Kubernetes 配置，简化部署流程。

### 5.4 故障处理与恢复

1. **主动故障检测**：实现主动健康检查和自愈机制，快速发现并修复故障。
2. **幂等性保证**：确保所有关键操作都是幂等的，支持安全重试和操作恢复。
3. **分布式协调**：在分布式操作中使用适当的协调机制，如分布式锁、租约、共识协议等。
4. **状态恢复**：设计支持从检查点恢复状态的机制，确保长时间运行的任务可以在失败后继续。

### 5.5 可持续性与扩展性

1. **资源效率**：设计考虑资源使用效率，支持资源限制和自适应工作负载。
2. **纵向与横向扩展**：同时支持提高单实例效率（纵向）和增加实例数量（横向）的扩展策略。
3. **版本兼容性**：设计考虑 API 版本控制和兼容性，支持滚动升级和蓝绿部署。
4. **可测试设计**：构建便于单元测试和集成测试的接口，支持模拟依赖和故障注入。

通过遵循这些准则，
可以构建既有组合性又有弹性的分布式系统，
充分利用容器化和云原生环境，同时确保系统可观测、可管理和可恢复。
