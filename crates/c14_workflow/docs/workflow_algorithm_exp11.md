# Rust 分布式工作流框架深入设计

## 目录

- [Rust 分布式工作流框架深入设计](#rust-分布式工作流框架深入设计)
  - [目录](#目录)
  - [概念设计详解](#概念设计详解)
    - [工作流基础模型](#工作流基础模型)
    - [语义层次协议](#语义层次协议)
    - [自我感知与适应性协议](#自我感知与适应性协议)
  - [数据库设计](#数据库设计)
    - [分布式存储架构](#分布式存储架构)
    - [数据库模式](#数据库模式)
    - [时序数据存储](#时序数据存储)
  - [分布式协议设计](#分布式协议设计)
    - [节点间通信协议](#节点间通信协议)
    - [共识协议](#共识协议)
    - [事件总线协议](#事件总线协议)
  - [前端设计](#前端设计)
    - [前端架构](#前端架构)
    - [Web API 设计](#web-api-设计)
    - [GraphQL API 设计](#graphql-api-设计)
  - [实现示例：工作流引擎核心](#实现示例工作流引擎核心)
  - [实现示例：分布式 Petri 网模型](#实现示例分布式-petri-网模型)
  - [实现示例：分布式自适应机制](#实现示例分布式自适应机制)
  - [实现示例：容错与恢复机制](#实现示例容错与恢复机制)
  - [实现示例：工作流 DSL 与可视化设计器](#实现示例工作流-dsl-与可视化设计器)
  - [实现示例：工作流执行引擎](#实现示例工作流执行引擎)
  - [示例应用：数据处理工作流](#示例应用数据处理工作流)
  - [示例应用：API服务集成](#示例应用api服务集成)
  - [总结与未来发展方向](#总结与未来发展方向)
    - [未来发展方向](#未来发展方向)

## 概念设计详解

### 工作流基础模型

工作流框架采用基于有向图和 Petri 网的混合模型，实现流程控制和数据流的灵活管理。

```rust
// 工作流核心模型
pub mod model {
    use std::collections::HashMap;
    use uuid::Uuid;
    use chrono::{DateTime, Utc};
    use serde::{Serialize, Deserialize};
    
    /// 工作流定义
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct WorkflowDefinition {
        pub id: String,
        pub name: String,
        pub version: String,
        pub nodes: Vec<NodeDefinition>,
        pub edges: Vec<EdgeDefinition>,
        pub variables: HashMap<String, VariableDefinition>,
        pub metadata: HashMap<String, String>,
        pub semantics: Vec<SemanticTag>,
    }
    
    /// 节点定义
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct NodeDefinition {
        pub id: String,
        pub node_type: NodeType,
        pub config: serde_json::Value,
        pub retry_policy: Option<RetryPolicy>,
        pub timeout: Option<std::time::Duration>,
        pub semantics: Vec<SemanticTag>,
    }
    
    /// 节点类型
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub enum NodeType {
        Task { task_type: String },
        SubWorkflow { workflow_ref: String },
        Gateway { gateway_type: GatewayType },
        Event { event_type: EventType },
        Place { initial_tokens: usize },    // Petri网库所
        Transition { condition: Option<String> }, // Petri网变迁
    }
    
    /// 工作流实例
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct WorkflowInstance {
        pub id: String,
        pub definition_id: String,
        pub version: String,
        pub state: WorkflowState,
        pub variables: HashMap<String, RuntimeVariable>,
        pub node_states: HashMap<String, NodeState>,
        pub created_at: DateTime<Utc>,
        pub updated_at: DateTime<Utc>,
        pub parent_instance_id: Option<String>,
        pub trace_context: Option<TraceContext>,
    }
}
```

### 语义层次协议

分层语义协议定义了工作流各层次间的通信与交互方式，使工作流可以在不同抽象级别上组织和执行。

```rust
// 语义层次协议
pub mod semantic_protocol {
    use serde::{Serialize, Deserialize};
    use std::collections::HashMap;
    
    /// 语义标签定义
    #[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
    pub struct SemanticTag {
        pub name: String,
        pub category: String,
        pub properties: HashMap<String, String>,
    }
    
    /// 层次定义
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct LayerDefinition {
        pub id: String,
        pub name: String,
        pub description: String,
        pub parent_layer: Option<String>,
        pub semantics: Vec<SemanticTag>,
    }
    
    /// 层次间通信消息
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct LayerMessage {
        pub source_layer: String,
        pub target_layer: String,
        pub message_type: LayerMessageType,
        pub payload: serde_json::Value,
        pub correlation_id: String,
        pub timestamp: chrono::DateTime<chrono::Utc>,
    }
    
    /// 层次消息类型
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub enum LayerMessageType {
        Command,
        Event,
        Query,
        Response,
        Notification,
    }
    
    /// 语义约束
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct SemanticConstraint {
        pub constraint_type: ConstraintType,
        pub expression: String,
        pub severity: ConstraintSeverity,
    }
    
    /// 约束类型
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub enum ConstraintType {
        Precondition,
        Postcondition,
        Invariant,
        Temporal,
    }
}
```

### 自我感知与适应性协议

自我感知协议确保工作流能够监控和调整自身行为，提高系统的自适应能力。

```rust
// 自我感知协议
pub mod introspection_protocol {
    use serde::{Serialize, Deserialize};
    use std::collections::HashMap;
    use chrono::{DateTime, Utc};
    
    /// 资源使用情况
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct ResourceUsage {
        pub cpu_usage: f64,
        pub memory_usage: usize,
        pub network_rx: usize,
        pub network_tx: usize,
        pub timestamp: DateTime<Utc>,
        pub host_info: HostInfo,
    }
    
    /// 主机信息
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct HostInfo {
        pub hostname: String,
        pub ip_address: String,
        pub os_info: String,
    }
    
    /// 节点健康状态
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct NodeHealth {
        pub node_id: String,
        pub status: HealthStatus,
        pub last_heartbeat: DateTime<Utc>,
        pub metrics: HashMap<String, f64>,
    }
    
    /// 健康状态
    #[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
    pub enum HealthStatus {
        Healthy,
        Degraded,
        Unhealthy,
        Unknown,
    }
    
    /// 适应策略
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct AdaptationPolicy {
        pub policy_id: String,
        pub triggers: Vec<AdaptationTrigger>,
        pub actions: Vec<AdaptationAction>,
        pub cooldown_period: std::time::Duration,
    }
    
    /// 适应触发器
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct AdaptationTrigger {
        pub metric: String,
        pub condition: TriggerCondition,
        pub threshold: f64,
        pub duration: std::time::Duration,
    }
}
```

## 数据库设计

### 分布式存储架构

工作流框架采用多层次存储架构，包括内存缓存、本地嵌入式存储和分布式数据库。

```rust
// 存储层设计
pub mod storage {
    use async_trait::async_trait;
    use serde::{Serialize, Deserialize};
    use thiserror::Error;
    
    /// 存储错误类型
    #[derive(Error, Debug)]
    pub enum StorageError {
        #[error("Item not found: {0}")]
        NotFound(String),
        #[error("Storage connection error: {0}")]
        ConnectionError(String),
        #[error("Serialization error: {0}")]
        SerializationError(String),
        #[error("Concurrent modification error")]
        ConcurrencyError,
        #[error("Storage operation timeout")]
        Timeout,
        #[error("Other storage error: {0}")]
        Other(String),
    }
    
    /// 存储接口
    #[async_trait]
    pub trait Storage: Send + Sync {
        async fn get<T: for<'de> Deserialize<'de> + Send + 'static>(
            &self, 
            key: &str
        ) -> Result<Option<T>, StorageError>;
        
        async fn put<T: Serialize + Send + 'static>(
            &self, 
            key: &str, 
            value: &T
        ) -> Result<(), StorageError>;
        
        async fn delete(&self, key: &str) -> Result<bool, StorageError>;
        
        async fn list_keys(&self, prefix: &str) -> Result<Vec<String>, StorageError>;
    }
    
    /// 分层存储管理器
    pub struct StorageManager {
        memory_cache: MemoryStorage,
        local_storage: Option<LocalStorage>,
        distributed_storage: Box<dyn Storage>,
    }
    
    impl StorageManager {
        pub fn new(
            memory_ttl: std::time::Duration,
            local_path: Option<std::path::PathBuf>,
            distributed: Box<dyn Storage>
        ) -> Self {
            // 构造函数实现
            Self {
                memory_cache: MemoryStorage::new(memory_ttl),
                local_storage: local_path.map(LocalStorage::new),
                distributed_storage: distributed,
            }
        }
        
        // 分层读取方法
        pub async fn get<T: for<'de> Deserialize<'de> + Serialize + Clone + Send + 'static>(
            &self,
            key: &str
        ) -> Result<Option<T>, StorageError> {
            // 首先从内存缓存获取
            if let Some(value) = self.memory_cache.get::<T>(key).await? {
                return Ok(Some(value));
            }
            
            // 然后从本地存储获取
            if let Some(local) = &self.local_storage {
                if let Some(value) = local.get::<T>(key).await? {
                    // 更新内存缓存
                    self.memory_cache.put(key, &value).await?;
                    return Ok(Some(value));
                }
            }
            
            // 最后从分布式存储获取
            if let Some(value) = self.distributed_storage.get::<T>(key).await? {
                // 更新本地缓存
                if let Some(local) = &self.local_storage {
                    local.put(key, &value).await?;
                }
                // 更新内存缓存
                self.memory_cache.put(key, &value).await?;
                return Ok(Some(value));
            }
            
            Ok(None)
        }
    }
}
```

### 数据库模式

```rust
// 数据库模式设计
pub mod database_schema {
    use sea_orm::{entity::prelude::*, Set};
    use chrono::{DateTime, Utc};
    use uuid::Uuid;
    
    // 工作流定义表
    #[derive(Clone, Debug, PartialEq, DeriveEntityModel)]
    #[sea_orm(table_name = "workflow_definitions")]
    pub struct Model {
        #[sea_orm(primary_key, auto_increment = false)]
        pub id: String,
        pub name: String,
        pub version: String,
        pub definition: Json,
        pub created_at: DateTime<Utc>,
        pub updated_at: DateTime<Utc>,
        pub created_by: String,
        pub status: String,
    }
    
    #[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
    pub enum Relation {
        #[sea_orm(has_many = "super::workflow_instance::Entity")]
        WorkflowInstance,
    }
    
    // 工作流实例表
    #[derive(Clone, Debug, PartialEq, DeriveEntityModel)]
    #[sea_orm(table_name = "workflow_instances")]
    pub struct WorkflowInstanceModel {
        #[sea_orm(primary_key, auto_increment = false)]
        pub id: String,
        pub definition_id: String,
        pub version: String,
        pub state: String,
        pub variables: Json,
        pub created_at: DateTime<Utc>,
        pub updated_at: DateTime<Utc>,
        pub parent_instance_id: Option<String>,
        pub trace_id: Option<String>,
    }
    
    // 任务实例表
    #[derive(Clone, Debug, PartialEq, DeriveEntityModel)]
    #[sea_orm(table_name = "task_instances")]
    pub struct TaskInstanceModel {
        #[sea_orm(primary_key, auto_increment = false)]
        pub id: String,
        pub workflow_instance_id: String,
        pub node_id: String,
        pub task_type: String,
        pub state: String,
        pub retries: i32,
        pub scheduled_at: DateTime<Utc>,
        pub started_at: Option<DateTime<Utc>>,
        pub completed_at: Option<DateTime<Utc>>,
        pub result: Option<Json>,
        pub error: Option<String>,
        pub worker_id: Option<String>,
    }
    
    // 工作流事件表
    #[derive(Clone, Debug, PartialEq, DeriveEntityModel)]
    #[sea_orm(table_name = "workflow_events")]
    pub struct WorkflowEventModel {
        #[sea_orm(primary_key, auto_increment = false)]
        pub id: String,
        pub workflow_instance_id: String,
        pub event_type: String,
        pub event_data: Json,
        pub timestamp: DateTime<Utc>,
        pub source_node_id: Option<String>,
        pub correlation_id: Option<String>,
    }
}
```

### 时序数据存储

```rust
// 时序数据存储
pub mod timeseries {
    use influxdb2::Client as InfluxClient;
    use influxdb2::models::DataPoint;
    use async_trait::async_trait;
    use chrono::{DateTime, Utc};
    
    // 时序数据点
    #[derive(Debug, Clone)]
    pub struct TimeseriesDataPoint {
        pub measurement: String,
        pub tags: std::collections::HashMap<String, String>,
        pub fields: std::collections::HashMap<String, Value>,
        pub timestamp: DateTime<Utc>,
    }
    
    // 字段值类型
    #[derive(Debug, Clone)]
    pub enum Value {
        Float(f64),
        Integer(i64),
        UInteger(u64),
        String(String),
        Boolean(bool),
    }
    
    // 时序存储接口
    #[async_trait]
    pub trait TimeseriesStorage: Send + Sync {
        async fn write_points(&self, points: Vec<TimeseriesDataPoint>) -> Result<(), TimeseriesError>;
        async fn query(&self, query: &str) -> Result<Vec<TimeseriesDataPoint>, TimeseriesError>;
    }
    
    // InfluxDB实现
    pub struct InfluxDBStorage {
        client: InfluxClient,
        org: String,
        bucket: String,
    }
    
    #[async_trait]
    impl TimeseriesStorage for InfluxDBStorage {
        async fn write_points(&self, points: Vec<TimeseriesDataPoint>) -> Result<(), TimeseriesError> {
            let data_points: Vec<DataPoint> = points.into_iter()
                .map(|p| {
                    // 将TimeseriesDataPoint转换为InfluxDB DataPoint的实现
                    // ...
                })
                .collect();
            
            self.client.write(&self.bucket, stream::iter(data_points))
                .await
                .map_err(|e| TimeseriesError::WriteError(e.to_string()))
        }
        
        async fn query(&self, query: &str) -> Result<Vec<TimeseriesDataPoint>, TimeseriesError> {
            // 实现查询功能
            // ...
        }
    }
}
```

## 分布式协议设计

### 节点间通信协议

```rust
// 节点间通信协议
pub mod node_protocol {
    use serde::{Serialize, Deserialize};
    use uuid::Uuid;
    use chrono::{DateTime, Utc};
    
    /// 节点消息类型
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub enum NodeMessageType {
        TaskAssignment,
        TaskStatusUpdate,
        HealthCheck,
        CoordinationCommand,
        StateTransfer,
        LeaderElection,
    }
    
    /// 节点消息
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct NodeMessage {
        pub message_id: String,
        pub source_node_id: String,
        pub target_node_id: Option<String>, // None表示广播
        pub message_type: NodeMessageType,
        pub payload: serde_json::Value,
        pub timestamp: DateTime<Utc>,
        pub trace_context: Option<TraceContext>,
        pub priority: MessagePriority,
        pub ttl: Option<i32>,
    }
    
    /// 消息优先级
    #[derive(Clone, Debug, Serialize, Deserialize, PartialEq, PartialOrd)]
    pub enum MessagePriority {
        Low = 0,
        Normal = 1,
        High = 2,
        Critical = 3,
    }
    
    /// 追踪上下文
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct TraceContext {
        pub trace_id: String,
        pub span_id: String,
        pub parent_span_id: Option<String>,
        pub sampled: bool,
        pub baggage: std::collections::HashMap<String, String>,
    }
}
```

### 共识协议

```rust
// 分布式共识协议
pub mod consensus {
    use serde::{Serialize, Deserialize};
    use async_trait::async_trait;
    use tokio::sync::mpsc;
    
    /// Raft消息类型
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub enum RaftMessage {
        VoteRequest(VoteRequest),
        VoteResponse(VoteResponse),
        AppendEntries(AppendEntriesRequest),
        AppendEntriesResponse(AppendEntriesResponse),
        InstallSnapshot(InstallSnapshotRequest),
        InstallSnapshotResponse(InstallSnapshotResponse),
    }
    
    /// 投票请求
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct VoteRequest {
        pub term: u64,
        pub candidate_id: String,
        pub last_log_index: u64,
        pub last_log_term: u64,
    }
    
    /// 投票响应
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct VoteResponse {
        pub term: u64,
        pub vote_granted: bool,
    }
    
    /// 共识状态机
    #[async_trait]
    pub trait StateMachine: Send + Sync {
        async fn apply(&mut self, entry: LogEntry) -> Result<(), StateMachineError>;
        async fn snapshot(&self) -> Result<Vec<u8>, StateMachineError>;
        async fn restore(&mut self, snapshot: Vec<u8>) -> Result<(), StateMachineError>;
    }
    
    /// 工作流共识状态机实现
    pub struct WorkflowStateMachine {
        storage: Box<dyn crate::storage::Storage>,
        latest_applied_index: u64,
    }
    
    #[async_trait]
    impl StateMachine for WorkflowStateMachine {
        async fn apply(&mut self, entry: LogEntry) -> Result<(), StateMachineError> {
            // 应用日志条目到状态机
            match entry.command {
                Command::CreateWorkflow(def) => {
                    self.storage.put(&format!("workflow:{}", def.id), &def).await
                        .map_err(|e| StateMachineError::StorageError(e.to_string()))?;
                },
                Command::UpdateWorkflowState(instance_id, state) => {
                    // 更新工作流实例状态
                    // ...
                },
                // ... 其他命令处理
            }
            
            self.latest_applied_index = entry.index;
            Ok(())
        }
        
        // ... 其他方法实现
    }
}
```

### 事件总线协议

```rust
// 事件总线协议
pub mod event_bus {
    use serde::{Serialize, Deserialize};
    use async_trait::async_trait;
    use futures::Stream;
    use std::pin::Pin;
    
    /// 事件消息
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct EventMessage {
        pub event_id: String,
        pub event_type: String,
        pub source: String,
        pub time: chrono::DateTime<chrono::Utc>,
        pub data: serde_json::Value,
        pub trace_context: Option<TraceContext>,
        pub schema_url: Option<String>,
    }
    
    /// 事件总线接口
    #[async_trait]
    pub trait EventBus: Send + Sync {
        /// 发布事件
        async fn publish(&self, topic: &str, event: EventMessage) -> Result<(), EventBusError>;
        
        /// 订阅事件流
        async fn subscribe(&self, topic: &str) -> Result<
            Pin<Box<dyn Stream<Item = Result<EventMessage, EventBusError>> + Send>>,
            EventBusError
        >;
        
        /// 创建主题（如果需要）
        async fn create_topic(&self, topic: &str) -> Result<(), EventBusError>;
    }
    
    /// NATS实现
    pub struct NatsEventBus {
        client: async_nats::Client,
        jetstream: async_nats::jetstream::Context,
    }
    
    #[async_trait]
    impl EventBus for NatsEventBus {
        async fn publish(&self, topic: &str, event: EventMessage) -> Result<(), EventBusError> {
            let payload = serde_json::to_vec(&event)
                .map_err(|e| EventBusError::SerializationError(e.to_string()))?;
                
            self.jetstream.publish(topic, payload.into())
                .await
                .map_err(|e| EventBusError::PublishError(e.to_string()))?;
                
            Ok(())
        }
        
        // ... 其他方法实现
    }
    
    /// Kafka实现
    pub struct KafkaEventBus {
        producer: rdkafka::producer::FutureProducer,
        consumer_config: rdkafka::config::ClientConfig,
    }
}
```

## 前端设计

### 前端架构

```rust
// 前端架构
pub mod frontend {
    use leptos::*;
    use serde::{Serialize, Deserialize};
    
    /// 应用状态
    #[derive(Clone)]
    pub struct AppState {
        pub workflows: Resource<(), Vec<WorkflowSummary>>,
        pub selected_workflow: RwSignal<Option<String>>,
        pub current_view: RwSignal<ViewType>,
        pub user: RwSignal<Option<User>>,
        pub notifications: RwSignal<Vec<Notification>>,
    }
    
    /// 视图类型
    #[derive(Clone, PartialEq)]
    pub enum ViewType {
        Dashboard,
        WorkflowDesigner,
        WorkflowInstances,
        WorkflowDetails(String),
        Settings,
    }
    
    /// 主组件
    #[component]
    pub fn App() -> impl IntoView {
        // 创建应用状态
        let workflows = create_resource(
            || (),
            |_| async move { fetch_workflows().await.unwrap_or_default() }
        );
        
        let selected_workflow = create_rw_signal(None);
        let current_view = create_rw_signal(ViewType::Dashboard);
        let user = create_rw_signal(None);
        let notifications = create_rw_signal(Vec::new());
        
        let app_state = AppState {
            workflows,
            selected_workflow,
            current_view,
            user,
            notifications,
        };
        
        // 渲染UI
        view! {
            <Router>
                <div class="app-container">
                    <Header app_state=app_state.clone()/>
                    <div class="main-content">
                        <Sidebar app_state=app_state.clone()/>
                        <MainContent app_state=app_state.clone()/>
                    </div>
                    <NotificationPanel notifications=app_state.notifications/>
                </div>
            </Router>
        }
    }
    
    /// 工作流设计器组件
    #[component]
    pub fn WorkflowDesigner(app_state: AppState) -> impl IntoView {
        let nodes = create_rw_signal(Vec::<NodeData>::new());
        let edges = create_rw_signal(Vec::<EdgeData>::new());
        let selected_node = create_rw_signal(None::<String>);
        
        let add_node = move |node_type: NodeType| {
            let new_node = NodeData {
                id: uuid::Uuid::new_v4().to_string(),
                node_type,
                position: Position { x: 100.0, y: 100.0 },
                data: Default::default(),
            };
            
            nodes.update(|n| n.push(new_node));
        };
        
        // 渲染设计器UI
        view! {
            <div class="workflow-designer">
                <div class="toolbar">
                    <button on:click=move |_| add_node(NodeType::Task { task_type: "default".into() })>
                        "Add Task"
                    </button>
                    <button on:click=move |_| add_node(NodeType::Gateway { gateway_type: GatewayType::Parallel })>
                        "Add Gateway"
                    </button>
                    <!-- 其他工具栏按钮 -->
                </div>
                
                <div class="graph-container">
                    <FlowGraph 
                        nodes=nodes
                        edges=edges
                        on_node_selected=move |id| selected_node.set(Some(id))
                    />
                </div>
                
                <div class="properties-panel">
                    <Show
                        when=move || selected_node.get().is_some()
                        fallback=|| view! { <div>"Select a node to edit properties"</div> }
                    >
                        <NodeProperties 
                            node_id=selected_node.get().unwrap()
                            nodes=nodes
                        />
                    </Show>
                </div>
            </div>
        }
    }
    
    /// 工作流监控组件
    #[component]
    pub fn WorkflowMonitoring(app_state: AppState) -> impl IntoView {
        let instance_id = use_params::<WorkflowInstanceParams>().with(|p| p.instance_id.clone());
        
        let instance = create_resource(
            move || instance_id.clone(),
            |id| async move { fetch_workflow_instance(&id).await.ok() }
        );
        
        let metrics = create_resource(
            move || instance_id.clone(),
            |id| async move { fetch_instance_metrics(&id).await.unwrap_or_default() }
        );
        
        let status_class = move || {
            match instance.get() {
                Some(Some(inst)) => match inst.state.as_str() {
                    "RUNNING" => "status-running",
                    "COMPLETED" => "status-completed",
                    "FAILED" => "status-failed",
                    _ => "status-unknown",
                },
                _ => "status-unknown",
            }
        };
        
        // 渲染监控UI
        view! {
            <div class="workflow-monitoring">
                <Suspense fallback=move || view! { <div>"Loading..."</div> }>
                    {move || {
                        instance.get().map(|opt_inst| {
                            match opt_inst {
                                Some(inst) => view! {
                                    <div class="instance-header">
                                        <h2>"Instance: " {&inst.id}</h2>
                                        <div class={"status-badge ".to_string() + &status_class()}>
                                            {&inst.state}
                                        </div>
                                    </div>
                                    
                                    <div class="instance-details">
                                        <div class="detail-card">
                                            <h3>"Timeline"</h3>
                                            <TimelineView instance=inst.clone()/>
                                        </div>
                                        
                                        <div class="detail-card">
                                            <h3>"Metrics"</h3>
                                            <MetricsView metrics=metrics/>
                                        </div>
                                        
                                        <div class="detail-card">
                                            <h3>"Variables"</h3>
                                            <VariablesView variables=inst.variables.clone()/>
                                        </div>
                                    </div>
                                    
                                    <div class="graph-view">
                                        <WorkflowInstanceGraph instance=inst/>
                                    </div>
                                },
                                None => view! { <div>"Instance not found"</div> }
                            }
                        })
                    }}
                </Suspense>
            </div>
        }
    }
}
```

### Web API 设计

```rust
// Web API设计
pub mod web_api {
    use axum::{
        routing::{get, post, put, delete},
        Router, Json, extract::{Path, State, Query},
        response::{IntoResponse, Response},
        http::StatusCode,
    };
    use serde::{Serialize, Deserialize};
    use tower_http::cors::CorsLayer;
    use tower_http::trace::TraceLayer;
    
    /// API应用状态
    pub struct ApiState {
        pub workflow_engine: crate::engine::WorkflowEngine,
        pub auth_service: crate::auth::AuthService,
    }
    
    /// 
# Rust 分布式工作流框架设计（续）

## Web API 设计（续）

```rust
// Web API设计（续）
pub mod web_api {
    // ... 前面内容省略

    /// API路由配置
    pub fn api_routes(state: ApiState) -> Router {
        Router::new()
            // 工作流定义API
            .route("/api/workflows", get(list_workflows))
            .route("/api/workflows", post(create_workflow))
            .route("/api/workflows/:id", get(get_workflow))
            .route("/api/workflows/:id", put(update_workflow))
            .route("/api/workflows/:id", delete(delete_workflow))
            .route("/api/workflows/:id/versions", get(list_workflow_versions))
            .route("/api/workflows/:id/deploy", post(deploy_workflow))
            
            // 工作流实例API
            .route("/api/instances", get(list_workflow_instances))
            .route("/api/instances", post(start_workflow_instance))
            .route("/api/instances/:id", get(get_workflow_instance))
            .route("/api/instances/:id/cancel", post(cancel_workflow_instance))
            .route("/api/instances/:id/retry", post(retry_workflow_instance))
            .route("/api/instances/:id/events", get(list_instance_events))
            
            // 任务API
            .route("/api/tasks", get(list_tasks))
            .route("/api/tasks/:id", get(get_task))
            .route("/api/tasks/:id/complete", post(complete_task))
            .route("/api/tasks/:id/fail", post(fail_task))
            
            // 监控API
            .route("/api/metrics/workflows", get(get_workflow_metrics))
            .route("/api/metrics/instances/:id", get(get_instance_metrics))
            .route("/api/health", get(health_check))
            
            // 权限与用户API
            .route("/api/auth/login", post(login))
            .route("/api/auth/refresh", post(refresh_token))
            .route("/api/users", get(list_users))
            
            .layer(TraceLayer::new_for_http())
            .layer(CorsLayer::permissive())
            .with_state(state)
    }
    
    /// 工作流列表查询参数
    #[derive(Debug, Deserialize)]
    pub struct WorkflowListParams {
        pub page: Option<usize>,
        pub per_page: Option<usize>,
        pub status: Option<String>,
        pub name: Option<String>,
    }
    
    /// 处理获取工作流列表
    async fn list_workflows(
        State(state): State<ApiState>,
        Query(params): Query<WorkflowListParams>,
    ) -> impl IntoResponse {
        let page = params.page.unwrap_or(1);
        let per_page = params.per_page.unwrap_or(20);
        
        match state.workflow_engine.list_workflow_definitions(page, per_page, params.status, params.name).await {
            Ok(workflows) => Json(workflows).into_response(),
            Err(e) => (StatusCode::INTERNAL_SERVER_ERROR, e.to_string()).into_response(),
        }
    }
    
    /// 工作流创建请求
    #[derive(Debug, Deserialize)]
    pub struct CreateWorkflowRequest {
        pub name: String,
        pub description: Option<String>,
        pub definition: serde_json::Value,
    }
    
    /// 处理创建工作流
    async fn create_workflow(
        State(state): State<ApiState>,
        Json(req): Json<CreateWorkflowRequest>,
    ) -> impl IntoResponse {
        match state.workflow_engine.create_workflow_definition(req.name, req.description, req.definition).await {
            Ok(workflow) => (StatusCode::CREATED, Json(workflow)).into_response(),
            Err(e) => (StatusCode::BAD_REQUEST, e.to_string()).into_response(),
        }
    }
    
    // ... 其他API处理函数
}
```

### GraphQL API 设计

```rust
// GraphQL API设计
pub mod graphql_api {
    use async_graphql::{Context, EmptySubscription, Object, Schema, ID, SimpleObject};
    use async_graphql_axum::{GraphQLRequest, GraphQLResponse};
    use axum::{extract::Extension, routing::post, Router};
    use chrono::{DateTime, Utc};
    use serde::{Deserialize, Serialize};
    
    /// GraphQL模式
    pub type ApiSchema = Schema<QueryRoot, MutationRoot, EmptySubscription>;
    
    /// GraphQL查询根
    pub struct QueryRoot;
    
    #[Object]
    impl QueryRoot {
        /// 获取工作流定义
        async fn workflow(&self, ctx: &Context<'_>, id: ID) -> Result<WorkflowType, async_graphql::Error> {
            let engine = ctx.data::<crate::engine::WorkflowEngine>()?;
            let workflow = engine.get_workflow_definition(&id.to_string()).await
                .map_err(|e| async_graphql::Error::new(e.to_string()))?;
                
            Ok(WorkflowType {
                id: ID::from(workflow.id),
                name: workflow.name,
                version: workflow.version,
                created_at: workflow.created_at,
                status: workflow.status,
                // ... 其他字段映射
            })
        }
        
        /// 查询工作流列表
        async fn workflows(
            &self, 
            ctx: &Context<'_>,
            page: Option<i32>,
            per_page: Option<i32>,
            status: Option<String>,
        ) -> Result<WorkflowConnection, async_graphql::Error> {
            let engine = ctx.data::<crate::engine::WorkflowEngine>()?;
            let page = page.unwrap_or(1) as usize;
            let per_page = per_page.unwrap_or(20) as usize;
            
            let result = engine.list_workflow_definitions(page, per_page, status, None).await
                .map_err(|e| async_graphql::Error::new(e.to_string()))?;
                
            let edges = result.items.into_iter()
                .map(|w| WorkflowEdge {
                    cursor: ID::from(w.id.clone()),
                    node: WorkflowType {
                        id: ID::from(w.id),
                        name: w.name,
                        version: w.version,
                        created_at: w.created_at,
                        status: w.status,
                        // ... 其他字段映射
                    }
                })
                .collect();
                
            Ok(WorkflowConnection {
                edges,
                page_info: PageInfo {
                    has_next_page: result.has_more,
                    end_cursor: result.items.last().map(|w| ID::from(w.id.clone())),
                }
            })
        }
        
        /// 获取工作流实例
        async fn workflow_instance(
            &self, 
            ctx: &Context<'_>, 
            id: ID
        ) -> Result<WorkflowInstanceType, async_graphql::Error> {
            let engine = ctx.data::<crate::engine::WorkflowEngine>()?;
            let instance = engine.get_workflow_instance(&id.to_string()).await
                .map_err(|e| async_graphql::Error::new(e.to_string()))?;
                
            Ok(WorkflowInstanceType {
                id: ID::from(instance.id),
                workflow_id: ID::from(instance.definition_id),
                state: instance.state,
                created_at: instance.created_at,
                updated_at: instance.updated_at,
                // ... 其他字段映射
            })
        }
        
        // ... 其他查询
    }
    
    /// GraphQL突变根
    pub struct MutationRoot;
    
    #[Object]
    impl MutationRoot {
        /// 创建工作流
        async fn create_workflow(
            &self,
            ctx: &Context<'_>,
            input: CreateWorkflowInput,
        ) -> Result<CreateWorkflowPayload, async_graphql::Error> {
            let engine = ctx.data::<crate::engine::WorkflowEngine>()?;
            
            let workflow = engine.create_workflow_definition(
                input.name, 
                input.description, 
                input.definition
            ).await.map_err(|e| async_graphql::Error::new(e.to_string()))?;
            
            Ok(CreateWorkflowPayload {
                workflow: WorkflowType {
                    id: ID::from(workflow.id),
                    name: workflow.name,
                    version: workflow.version,
                    created_at: workflow.created_at,
                    status: workflow.status,
                    // ... 其他字段映射
                },
            })
        }
        
        /// 启动工作流实例
        async fn start_workflow_instance(
            &self,
            ctx: &Context<'_>,
            input: StartWorkflowInput,
        ) -> Result<StartWorkflowPayload, async_graphql::Error> {
            let engine = ctx.data::<crate::engine::WorkflowEngine>()?;
            
            let instance = engine.start_workflow_instance(
                &input.workflow_id.to_string(),
                input.variables.unwrap_or_default(),
            ).await.map_err(|e| async_graphql::Error::new(e.to_string()))?;
            
            Ok(StartWorkflowPayload {
                instance: WorkflowInstanceType {
                    id: ID::from(instance.id),
                    workflow_id: ID::from(instance.definition_id),
                    state: instance.state,
                    created_at: instance.created_at,
                    updated_at: instance.updated_at,
                    // ... 其他字段映射
                },
            })
        }
        
        // ... 其他突变
    }
    
    /// 工作流类型
    #[derive(SimpleObject)]
    pub struct WorkflowType {
        pub id: ID,
        pub name: String,
        pub version: String,
        pub created_at: DateTime<Utc>,
        pub status: String,
        // ... 其他字段
    }
    
    /// 工作流实例类型
    #[derive(SimpleObject)]
    pub struct WorkflowInstanceType {
        pub id: ID,
        pub workflow_id: ID,
        pub state: String,
        pub created_at: DateTime<Utc>,
        pub updated_at: DateTime<Utc>,
        // ... 其他字段
    }
    
    // ... 其他GraphQL类型定义
}
```

## 实现示例：工作流引擎核心

```rust
// 工作流引擎核心
pub mod engine {
    use crate::model::{WorkflowDefinition, WorkflowInstance, NodeDefinition, NodeType};
    use crate::storage::StorageManager;
    use crate::execution::Executor;
    use crate::event_bus::EventBus;
    use async_trait::async_trait;
    use tokio::sync::{RwLock, mpsc};
    use std::collections::{HashMap, HashSet};
    use std::sync::Arc;
    use uuid::Uuid;
    use thiserror::Error;
    
    /// 工作流引擎错误
    #[derive(Debug, Error)]
    pub enum WorkflowEngineError {
        #[error("Workflow not found: {0}")]
        WorkflowNotFound(String),
        #[error("Instance not found: {0}")]
        InstanceNotFound(String),
        #[error("Task not found: {0}")]
        TaskNotFound(String),
        #[error("Storage error: {0}")]
        StorageError(String),
        #[error("Validation error: {0}")]
        ValidationError(String),
        #[error("Execution error: {0}")]
        ExecutionError(String),
        #[error("Other error: {0}")]
        Other(String),
    }
    
    /// 工作流引擎
    pub struct WorkflowEngine {
        storage: Arc<StorageManager>,
        event_bus: Arc<dyn EventBus>,
        executors: HashMap<String, Arc<dyn Executor>>,
        active_instances: Arc<RwLock<HashSet<String>>>,
        // 其他引擎组件...
    }
    
    impl WorkflowEngine {
        /// 创建新的工作流引擎
        pub fn new(
            storage: StorageManager,
            event_bus: Arc<dyn EventBus>,
            executors: HashMap<String, Arc<dyn Executor>>,
        ) -> Self {
            Self {
                storage: Arc::new(storage),
                event_bus,
                executors,
                active_instances: Arc::new(RwLock::new(HashSet::new())),
                // 初始化其他组件...
            }
        }
        
        /// 创建工作流定义
        pub async fn create_workflow_definition(
            &self,
            name: String,
            description: Option<String>,
            definition: serde_json::Value,
        ) -> Result<WorkflowDefinition, WorkflowEngineError> {
            // 验证工作流定义
            let parsed_def: WorkflowDefinition = serde_json::from_value(definition.clone())
                .map_err(|e| WorkflowEngineError::ValidationError(format!("Invalid workflow definition: {}", e)))?;
                
            // 验证工作流拓扑结构
            self.validate_workflow_topology(&parsed_def)
                .map_err(|e| WorkflowEngineError::ValidationError(e))?;
                
            // 创建工作流定义对象
            let workflow_def = WorkflowDefinition {
                id: Uuid::new_v4().to_string(),
                name,
                version: "1.0.0".to_string(),
                nodes: parsed_def.nodes,
                edges: parsed_def.edges,
                variables: parsed_def.variables,
                metadata: HashMap::new(),
                semantics: Vec::new(),
            };
            
            // 存储工作流定义
            self.storage.put(&format!("workflow:{}", workflow_def.id), &workflow_def).await
                .map_err(|e| WorkflowEngineError::StorageError(e.to_string()))?;
                
            // 发布工作流创建事件
            let event = crate::event_bus::EventMessage {
                event_id: Uuid::new_v4().to_string(),
                event_type: "workflow.created".to_string(),
                source: "workflow-engine".to_string(),
                time: chrono::Utc::now(),
                data: serde_json::to_value(&workflow_def).unwrap(),
                trace_context: None,
                schema_url: None,
            };
            
            self.event_bus.publish("workflow-events", event).await
                .map_err(|e| WorkflowEngineError::Other(format!("Failed to publish event: {}", e)))?;
                
            Ok(workflow_def)
        }
        
        /// 启动工作流实例
        pub async fn start_workflow_instance(
            &self,
            workflow_id: &str,
            initial_variables: HashMap<String, serde_json::Value>,
        ) -> Result<WorkflowInstance, WorkflowEngineError> {
            // 获取工作流定义
            let workflow_def: WorkflowDefinition = self.storage.get(&format!("workflow:{}", workflow_id)).await
                .map_err(|e| WorkflowEngineError::StorageError(e.to_string()))?
                .ok_or_else(|| WorkflowEngineError::WorkflowNotFound(workflow_id.to_string()))?;
                
            // 创建工作流实例
            let instance_id = Uuid::new_v4().to_string();
            let instance = WorkflowInstance {
                id: instance_id.clone(),
                definition_id: workflow_id.to_string(),
                version: workflow_def.version.clone(),
                state: "CREATED".to_string(),
                variables: initial_variables,
                node_states: HashMap::new(),
                created_at: chrono::Utc::now(),
                updated_at: chrono::Utc::now(),
                parent_instance_id: None,
                trace_context: None,
            };
            
            // 保存实例
            self.storage.put(&format!("instance:{}", instance_id), &instance).await
                .map_err(|e| WorkflowEngineError::StorageError(e.to_string()))?;
                
            // 添加到活动实例集
            self.active_instances.write().await.insert(instance_id.clone());
            
            // 发布实例创建事件
            let event = crate::event_bus::EventMessage {
                event_id: Uuid::new_v4().to_string(),
                event_type: "instance.created".to_string(),
                source: "workflow-engine".to_string(),
                time: chrono::Utc::now(),
                data: serde_json::to_value(&instance).unwrap(),
                trace_context: None,
                schema_url: None,
            };
            
            self.event_bus.publish("instance-events", event).await
                .map_err(|e| WorkflowEngineError::Other(format!("Failed to publish event: {}", e)))?;
                
            // 异步启动工作流执行
            let engine_clone = self.clone();
            tokio::spawn(async move {
                if let Err(e) = engine_clone.execute_workflow_instance(&instance_id).await {
                    eprintln!("Error executing workflow instance {}: {}", instance_id, e);
                    // 处理执行失败
                    engine_clone.handle_instance_failure(&instance_id, &e.to_string()).await;
                }
            });
            
            Ok(instance)
        }
        
        /// 执行工作流实例
        async fn execute_workflow_instance(&self, instance_id: &str) -> Result<(), WorkflowEngineError> {
            // 获取实例信息
            let mut instance: WorkflowInstance = self.storage.get(&format!("instance:{}", instance_id)).await
                .map_err(|e| WorkflowEngineError::StorageError(e.to_string()))?
                .ok_or_else(|| WorkflowEngineError::InstanceNotFound(instance_id.to_string()))?;
                
            // 获取工作流定义
            let workflow_def: WorkflowDefinition = self.storage.get(&format!("workflow:{}", instance.definition_id)).await
                .map_err(|e| WorkflowEngineError::StorageError(e.to_string()))?
                .ok_or_else(|| WorkflowEngineError::WorkflowNotFound(instance.definition_id.clone()))?;
                
            // 更新实例状态为运行中
            instance.state = "RUNNING".to_string();
            instance.updated_at = chrono::Utc::now();
            
            self.storage.put(&format!("instance:{}", instance_id), &instance).await
                .map_err(|e| WorkflowEngineError::StorageError(e.to_string()))?;
                
            // 查找起始节点
            let start_nodes = workflow_def.nodes.iter()
                .filter(|n| match &n.node_type {
                    NodeType::Event { event_type } => event_type == "start",
                    _ => false,
                })
                .collect::<Vec<_>>();
                
            if start_nodes.is_empty() {
                return Err(WorkflowEngineError::ValidationError("No start node found".to_string()));
            }
            
            // 为每个起始节点创建执行任务
            for start_node in start_nodes {
                self.schedule_node_execution(&instance, start_node).await?;
            }
            
            Ok(())
        }
        
        /// 调度节点执行
        async fn schedule_node_execution(
            &self,
            instance: &WorkflowInstance,
            node: &NodeDefinition,
        ) -> Result<(), WorkflowEngineError> {
            // 根据节点类型分配到相应的执行器
            let task_type = match &node.node_type {
                NodeType::Task { task_type } => task_type,
                NodeType::SubWorkflow { .. } => "subworkflow",
                NodeType::Gateway { gateway_type } => match gateway_type {
                    GatewayType::Exclusive => "exclusive-gateway",
                    GatewayType::Parallel => "parallel-gateway",
                    GatewayType::Inclusive => "inclusive-gateway",
                },
                NodeType::Event { event_type } => match event_type.as_str() {
                    "start" => "start-event",
                    "end" => "end-event",
                    _ => "custom-event",
                },
                NodeType::Place { .. } => "place",
                NodeType::Transition { .. } => "transition",
            };
            
            // 查找匹配的执行器
            let executor = self.executors.get(task_type)
                .or_else(|| self.executors.get("default"))
                .ok_or_else(|| WorkflowEngineError::ExecutionError(
                    format!("No executor found for task type: {}", task_type)
                ))?;
                
            // 创建任务上下文
            let context = crate::execution::TaskContext {
                instance_id: instance.id.clone(),
                node_id: node.id.clone(),
                variables: instance.variables.clone(),
                node_config: node.config.clone(),
                // 其他上下文信息...
            };
            
            // 异步执行任务
            let executor_clone = executor.clone();
            let engine_clone = self.clone();
            
            tokio::spawn(async move {
                match executor_clone.execute(context).await {
                    Ok(result) => {
                        // 处理任务执行成功
                        if let Err(e) = engine_clone.handle_node_completion(&instance.id, &node.id, result).await {
                            eprintln!("Error handling node completion: {}", e);
                        }
                    },
                    Err(e) => {
                        // 处理任务执行失败
                        if let Err(e) = engine_clone.handle_node_failure(&instance.id, &node.id, &e.to_string()).await {
                            eprintln!("Error handling node failure: {}", e);
                        }
                    }
                }
            });
            
            Ok(())
        }
        
        // ... 其他引擎方法
    }
    
    // 工作流引擎克隆实现
    impl Clone for WorkflowEngine {
        fn clone(&self) -> Self {
            Self {
                storage: Arc::clone(&self.storage),
                event_bus: Arc::clone(&self.event_bus),
                executors: self.executors.clone(),
                active_instances: Arc::clone(&self.active_instances),
                // 克隆其他组件...
            }
        }
    }
}
```

## 实现示例：分布式 Petri 网模型

```rust
// Petri网工作流实现
pub mod petri {
    use crate::model::{WorkflowDefinition, NodeDefinition, NodeType, EdgeDefinition};
    use std::collections::{HashMap, HashSet};
    use serde::{Serialize, Deserialize};
    use uuid::Uuid;
    use thiserror::Error;
    
    /// Petri网错误
    #[derive(Debug, Error)]
    pub enum PetriNetError {
        #[error("Invalid Petri net structure: {0}")]
        InvalidStructure(String),
        #[error("Execution error: {0}")]
        ExecutionError(String),
        #[error("Deadlock detected")]
        Deadlock,
        #[error("Invalid marking: {0}")]
        InvalidMarking(String),
    }
    
    /// Petri网标记
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct PetriNetMarking {
        pub place_tokens: HashMap<String, usize>,
    }
    
    /// Petri网分析结果
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct PetriNetAnalysis {
        pub is_bounded: bool,
        pub is_safe: bool,
        pub is_deadlock_free: bool,
        pub reachable_markings: Vec<PetriNetMarking>,
        pub terminal_markings: Vec<PetriNetMarking>,
    }
    
    /// Petri网实现
    pub struct PetriNet {
        places: HashMap<String, Place>,
        transitions: HashMap<String, Transition>,
        current_marking: PetriNetMarking,
    }
    
    /// 库所定义
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct Place {
        pub id: String,
        pub name: String,
        pub initial_tokens: usize,
        pub capacity: Option<usize>,
    }
    
    /// 变迁定义
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct Transition {
        pub id: String,
        pub name: String,
        pub guard: Option<String>,
        pub input_arcs: Vec<Arc>,
        pub output_arcs: Vec<Arc>,
    }
    
    /// 弧定义
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct Arc {
        pub source: String,
        pub target: String,
        pub weight: usize,
    }
    
    impl PetriNet {
        /// 从工作流定义创建Petri网
        pub fn from_workflow(workflow: &WorkflowDefinition) -> Result<Self, PetriNetError> {
            let mut places = HashMap::new();
            let mut transitions = HashMap::new();
            
            // 处理节点
            for node in &workflow.nodes {
                match &node.node_type {
                    NodeType::Place { initial_tokens } => {
                        places.insert(node.id.clone(), Place {
                            id: node.id.clone(),
                            name: node.id.clone(),
                            initial_tokens: *initial_tokens,
                            capacity: None,
                        });
                    },
                    NodeType::Transition { condition } => {
                        transitions.insert(node.id.clone(), Transition {
                            id: node.id.clone(),
                            name: node.id.clone(),
                            guard: condition.clone(),
                            input_arcs: Vec::new(),
                            output_arcs: Vec::new(),
                        });
                    },
                    // 将其他节点类型转换为Petri网元素
                    NodeType::Task { .. } => {
                        // 任务节点转换为一个变迁，前后各有一个库所
                        let pre_place_id = format!("{}_pre", node.id);
                        let post_place_id = format!("{}_post", node.id);
                        
                        places.insert(pre_place_id.clone(), Place {
                            id: pre_place_id.clone(),
                            name: format!("Pre-{}", node.id),
                            initial_tokens: 0,
                            capacity: None,
                        });
                        
                        places.insert(post_place_id.clone(), Place {
                            id: post_place_id.clone(),
                            name: format!("Post-{}", node.id),
                            initial_tokens: 0,
                            capacity: None,
                        });
                        
                        transitions.insert(node.id.clone(), Transition {
                            id: node.id.clone(),
                            name: node.id.clone(),
                            guard: None,
                            input_arcs: vec![Arc {
                                source: pre_place_id,
                                target: node.id.clone(),
                                weight: 1,
                            }],
                            output_arcs: vec![Arc {
                                source: node.id.clone(),
                                target: post_place_id,
                                weight: 1,
                            }],
                        });
                    },
                    // ... 处理其他节点类型
                    _ => {}
                }
            }
            
            // 处理边缘
            for edge in &workflow.edges {
                match (
                    workflow.nodes.iter().find(|n| n.id == edge.source),
                    workflow.nodes.iter().find(|n| n.id == edge.target)
                ) {
                    (Some(source), Some(target)) => {
                        match (&source.node_type, &target.node_type) {
                            (NodeType::Place { .. }, NodeType::Transition { .. }) => {
                                // 库所到变迁的弧
                                if let Some(transition) = transitions.get_mut(&target.id) {
                                    transition.input_arcs.push(Arc {
                                        source: source.id.clone(),
                                        target: target.id.clone(),
                                        weight: 1,
                                    });
                                }
                            },
                            (NodeType::Transition { .. }, NodeType::Place { .. }) => {
                                // 变迁到库所的弧
                                if let Some(transition) = transitions.get_mut(&source.id) {
                                    transition.output_arcs.push(Arc {
                                        source: source.id.clone(),
                                        target: target.id.clone(),
                                        weight: 1,
                                    });
                                }
                            },
                            // ... 处理其他情况
                            _ => {}
                        }
                    },
                    _ => return Err(PetriNetError::InvalidStructure(
                        format!("Invalid edge: {} -> {}", edge.source, edge.target)
                    )),
                }
            }
            
            // 创建初始标记
            let mut place_tokens = HashMap::new();
            for (id, place) in &places {
                place_tokens.insert(id.clone(), place.initial_tokens);
            }
            
            Ok(Self {
                places,
                transitions,
                current_marking: PetriNetMarking { place_tokens },
            })
        
# Rust 分布式工作流框架设计（续）

## 实现示例：分布式 Petri 网模型（续）

```rust
// Petri网工作流实现（续）
pub mod petri {
    // ... 前面内容省略

    impl PetriNet {
        // ... 前面内容省略

        /// 检查变迁是否启用
        pub fn is_transition_enabled(&self, transition_id: &str) -> Result<bool, PetriNetError> {
            let transition = self.transitions.get(transition_id)
                .ok_or_else(|| PetriNetError::InvalidStructure(format!("Transition not found: {}", transition_id)))?;
                
            // 检查所有输入库所是否有足够的token
            for arc in &transition.input_arcs {
                let tokens = self.current_marking.place_tokens.get(&arc.source)
                    .ok_or_else(|| PetriNetError::InvalidStructure(format!("Place not found: {}", arc.source)))?;
                    
                if *tokens < arc.weight {
                    return Ok(false);
                }
            }
            
            // 检查所有输出库所是否有足够的容量
            for arc in &transition.output_arcs {
                if let Some(place) = self.places.get(&arc.target) {
                    if let Some(capacity) = place.capacity {
                        let current_tokens = self.current_marking.place_tokens.get(&arc.target).unwrap_or(&0);
                        if *current_tokens + arc.weight > capacity {
                            return Ok(false);
                        }
                    }
                }
            }
            
            // 检查守护条件
            if let Some(guard) = &transition.guard {
                // 在实际实现中，这里需要执行表达式求值
                // 简化版：假设所有非空守护条件都返回true
                return Ok(true);
            }
            
            Ok(true)
        }
        
        /// 执行变迁
        pub fn fire_transition(&mut self, transition_id: &str) -> Result<(), PetriNetError> {
            if !self.is_transition_enabled(transition_id)? {
                return Err(PetriNetError::ExecutionError(format!("Transition not enabled: {}", transition_id)));
            }
            
            let transition = self.transitions.get(transition_id)
                .ok_or_else(|| PetriNetError::InvalidStructure(format!("Transition not found: {}", transition_id)))?;
                
            // 从输入库所移除token
            for arc in &transition.input_arcs {
                if let Some(tokens) = self.current_marking.place_tokens.get_mut(&arc.source) {
                    *tokens -= arc.weight;
                }
            }
            
            // 向输出库所添加token
            for arc in &transition.output_arcs {
                if let Some(tokens) = self.current_marking.place_tokens.get_mut(&arc.target) {
                    *tokens += arc.weight;
                }
            }
            
            Ok(())
        }
        
        /// 分析Petri网性质
        pub fn analyze(&self) -> Result<PetriNetAnalysis, PetriNetError> {
            // 执行可达性分析
            let reachability_result = self.analyze_reachability()?;
            
            // 判断是否有界
            let is_bounded = reachability_result.reachable_markings.len() < 1000; // 简化版：假设可达标记数少于1000就是有界的
            
            // 判断是否安全
            let is_safe = reachability_result.reachable_markings.iter().all(|marking| {
                marking.place_tokens.values().all(|tokens| *tokens <= 1)
            });
            
            // 判断是否无死锁
            let is_deadlock_free = reachability_result.terminal_markings.iter().all(|marking| {
                // 检查是否有期望的终止状态，例如只有终止库所有token
                marking.place_tokens.iter().any(|(place_id, tokens)| {
                    self.places.get(place_id).map(|p| p.name.contains("end") && *tokens > 0).unwrap_or(false)
                })
            });
            
            Ok(PetriNetAnalysis {
                is_bounded,
                is_safe,
                is_deadlock_free,
                reachable_markings: reachability_result.reachable_markings,
                terminal_markings: reachability_result.terminal_markings,
            })
        }
        
        /// 可达性分析
        fn analyze_reachability(&self) -> Result<PetriNetAnalysis, PetriNetError> {
            let mut visited_markings: HashSet<String> = HashSet::new();
            let mut queue: Vec<PetriNetMarking> = Vec::new();
            let mut reachable_markings: Vec<PetriNetMarking> = Vec::new();
            let mut terminal_markings: Vec<PetriNetMarking> = Vec::new();
            
            // 从初始标记开始
            queue.push(self.current_marking.clone());
            
            while let Some(marking) = queue.pop() {
                // 将标记序列化为字符串，用于检测重复
                let marking_str = serde_json::to_string(&marking)
                    .map_err(|e| PetriNetError::ExecutionError(format!("Serialization error: {}", e)))?;
                    
                if visited_markings.contains(&marking_str) {
                    continue;
                }
                
                visited_markings.insert(marking_str);
                reachable_markings.push(marking.clone());
                
                // 检查是否为终止标记（没有启用的变迁）
                let mut has_enabled_transition = false;
                
                // 尝试所有变迁
                for transition_id in self.transitions.keys() {
                    // 创建临时Petri网来尝试变迁
                    let mut temp_net = self.clone();
                    temp_net.current_marking = marking.clone();
                    
                    if temp_net.is_transition_enabled(transition_id)? {
                        has_enabled_transition = true;
                        
                        // 执行变迁
                        temp_net.fire_transition(transition_id)?;
                        
                        // 将新标记加入队列
                        queue.push(temp_net.current_marking.clone());
                    }
                }
                
                if !has_enabled_transition {
                    terminal_markings.push(marking);
                }
                
                // 限制分析规模，防止状态空间爆炸
                if reachable_markings.len() > 10000 {
                    return Err(PetriNetError::ExecutionError("State space too large for analysis".to_string()));
                }
            }
            
            Ok(PetriNetAnalysis {
                is_bounded: true, // 简化版
                is_safe: true,    // 简化版
                is_deadlock_free: !terminal_markings.is_empty(),
                reachable_markings,
                terminal_markings,
            })
        }
        
        /// 动态修改Petri网结构
        pub fn add_place(&mut self, id: String, name: String, initial_tokens: usize) -> Result<(), PetriNetError> {
            if self.places.contains_key(&id) {
                return Err(PetriNetError::InvalidStructure(format!("Place already exists: {}", id)));
            }
            
            self.places.insert(id.clone(), Place {
                id: id.clone(),
                name,
                initial_tokens,
                capacity: None,
            });
            
            self.current_marking.place_tokens.insert(id, initial_tokens);
            
            Ok(())
        }
        
        pub fn add_transition(&mut self, id: String, name: String, guard: Option<String>) -> Result<(), PetriNetError> {
            if self.transitions.contains_key(&id) {
                return Err(PetriNetError::InvalidStructure(format!("Transition already exists: {}", id)));
            }
            
            self.transitions.insert(id.clone(), Transition {
                id,
                name,
                guard,
                input_arcs: Vec::new(),
                output_arcs: Vec::new(),
            });
            
            Ok(())
        }
        
        pub fn add_arc(&mut self, source: String, target: String, weight: usize) -> Result<(), PetriNetError> {
            if self.places.contains_key(&source) && self.transitions.contains_key(&target) {
                // 库所到变迁的弧
                if let Some(transition) = self.transitions.get_mut(&target) {
                    transition.input_arcs.push(Arc {
                        source,
                        target,
                        weight,
                    });
                }
            } else if self.transitions.contains_key(&source) && self.places.contains_key(&target) {
                // 变迁到库所的弧
                if let Some(transition) = self.transitions.get_mut(&source) {
                    transition.output_arcs.push(Arc {
                        source,
                        target,
                        weight,
                    });
                }
            } else {
                return Err(PetriNetError::InvalidStructure(format!(
                    "Invalid arc: {} -> {}. Source and target must be place-transition or transition-place.",
                    source, target
                )));
            }
            
            Ok(())
        }
    }
    
    impl Clone for PetriNet {
        fn clone(&self) -> Self {
            Self {
                places: self.places.clone(),
                transitions: self.transitions.clone(),
                current_marking: self.current_marking.clone(),
            }
        }
    }
}
```

## 实现示例：分布式自适应机制

```rust
// 自适应与资源感知模块
pub mod adaptation {
    use crate::introspection_protocol::{ResourceUsage, NodeHealth, HealthStatus, AdaptationPolicy};
    use async_trait::async_trait;
    use std::collections::HashMap;
    use std::sync::Arc;
    use tokio::sync::RwLock;
    use chrono::{DateTime, Utc, Duration};
    use serde::{Serialize, Deserialize};
    use metrics::{counter, gauge};
    
    /// 资源阈值配置
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct ResourceThresholds {
        pub cpu_high: f64,
        pub cpu_critical: f64,
        pub memory_high: f64,
        pub memory_critical: f64,
        pub latency_high: f64,
        pub latency_critical: f64,
    }
    
    /// 健康状态计算器
    pub struct HealthCalculator {
        thresholds: ResourceThresholds,
    }
    
    impl HealthCalculator {
        pub fn new(thresholds: ResourceThresholds) -> Self {
            Self { thresholds }
        }
        
        pub fn calculate_health(&self, resource: &ResourceUsage) -> HealthStatus {
            // 计算综合健康状态
            if resource.cpu_usage > self.thresholds.cpu_critical || 
               resource.memory_usage as f64 > self.thresholds.memory_critical {
                return HealthStatus::Unhealthy;
            } else if resource.cpu_usage > self.thresholds.cpu_high ||
                      resource.memory_usage as f64 > self.thresholds.memory_high {
                return HealthStatus::Degraded;
            } else {
                return HealthStatus::Healthy;
            }
        }
    }
    
    /// 自适应执行器接口
    #[async_trait]
    pub trait AdaptationExecutor: Send + Sync {
        async fn execute_action(&self, action: &AdaptationAction) -> Result<(), AdaptationError>;
    }
    
    /// 自适应动作
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub enum AdaptationAction {
        ScaleOut { service: String, instances: usize },
        ScaleIn { service: String, instances: usize },
        MigrateWorkflow { workflow_id: String, target_node: String },
        AdjustResourceLimits { service: String, cpu: Option<f64>, memory: Option<usize> },
        ThrottleRequests { service: String, rate: u32 },
        ActivateCircuitBreaker { service: String, recovery_time: u64 },
    }
    
    /// 自适应管理器
    pub struct AdaptationManager {
        policies: Arc<RwLock<Vec<AdaptationPolicy>>>,
        health_calculator: HealthCalculator,
        executors: HashMap<String, Arc<dyn AdaptationExecutor>>,
        last_adaptations: Arc<RwLock<HashMap<String, DateTime<Utc>>>>,
    }
    
    impl AdaptationManager {
        pub fn new(
            health_calculator: HealthCalculator,
            executors: HashMap<String, Arc<dyn AdaptationExecutor>>,
        ) -> Self {
            Self {
                policies: Arc::new(RwLock::new(Vec::new())),
                health_calculator,
                executors,
                last_adaptations: Arc::new(RwLock::new(HashMap::new())),
            }
        }
        
        /// 添加自适应策略
        pub async fn add_policy(&self, policy: AdaptationPolicy) {
            self.policies.write().await.push(policy);
        }
        
        /// 处理资源监控事件
        pub async fn handle_resource_update(&self, node_id: String, resource: ResourceUsage) -> Result<(), AdaptationError> {
            // 计算节点健康状态
            let health_status = self.health_calculator.calculate_health(&resource);
            
            // 记录监控指标
            gauge!("node.cpu.usage", resource.cpu_usage, "node" => node_id.clone());
            gauge!("node.memory.usage", resource.memory_usage as f64, "node" => node_id.clone());
            gauge!("node.network.rx", resource.network_rx as f64, "node" => node_id.clone());
            gauge!("node.network.tx", resource.network_tx as f64, "node" => node_id.clone());
            
            // 创建节点健康信息
            let node_health = NodeHealth {
                node_id: node_id.clone(),
                status: health_status,
                last_heartbeat: Utc::now(),
                metrics: HashMap::from([
                    ("cpu".to_string(), resource.cpu_usage),
                    ("memory".to_string(), resource.memory_usage as f64),
                    ("network_rx".to_string(), resource.network_rx as f64),
                    ("network_tx".to_string(), resource.network_tx as f64),
                ]),
            };
            
            // 检查是否需要触发自适应策略
            self.evaluate_policies(node_health).await?;
            
            Ok(())
        }
        
        /// 评估所有自适应策略
        async fn evaluate_policies(&self, node_health: NodeHealth) -> Result<(), AdaptationError> {
            let policies = self.policies.read().await.clone();
            let mut last_adaptations = self.last_adaptations.write().await;
            
            for policy in policies {
                let mut should_trigger = false;
                
                // 检查所有触发条件
                for trigger in &policy.triggers {
                    if let Some(metric_value) = node_health.metrics.get(&trigger.metric) {
                        let condition_met = match trigger.condition {
                            TriggerCondition::GreaterThan => *metric_value > trigger.threshold,
                            TriggerCondition::LessThan => *metric_value < trigger.threshold,
                            TriggerCondition::Equals => (*metric_value - trigger.threshold).abs() < 0.001,
                        };
                        
                        if condition_met {
                            // 检查冷却期
                            if let Some(last_time) = last_adaptations.get(&policy.policy_id) {
                                if Utc::now() - *last_time < Duration::from_std(policy.cooldown_period).unwrap() {
                                    // 仍在冷却期内
                                    continue;
                                }
                            }
                            
                            should_trigger = true;
                            break;
                        }
                    }
                }
                
                if should_trigger {
                    // 执行自适应动作
                    for action in &policy.actions {
                        match action {
                            AdaptationAction::ScaleOut { service, instances } => {
                                if let Some(executor) = self.executors.get("scale") {
                                    executor.execute_action(action).await?;
                                    
                                    // 记录自适应动作
                                    counter!("adaptation.scale_out", *instances as u64, "service" => service.clone());
                                }
                            },
                            AdaptationAction::ScaleIn { service, instances } => {
                                if let Some(executor) = self.executors.get("scale") {
                                    executor.execute_action(action).await?;
                                    
                                    // 记录自适应动作
                                    counter!("adaptation.scale_in", *instances as u64, "service" => service.clone());
                                }
                            },
                            AdaptationAction::MigrateWorkflow { workflow_id, target_node } => {
                                if let Some(executor) = self.executors.get("migrate") {
                                    executor.execute_action(action).await?;
                                    
                                    // 记录自适应动作
                                    counter!("adaptation.migrate", 1, 
                                        "workflow_id" => workflow_id.clone(), 
                                        "target_node" => target_node.clone()
                                    );
                                }
                            },
                            // ... 处理其他类型的自适应动作
                            _ => {}
                        }
                    }
                    
                    // 更新最后适应时间
                    last_adaptations.insert(policy.policy_id.clone(), Utc::now());
                }
            }
            
            Ok(())
        }
    }
    
    /// 自适应错误
    #[derive(Debug, thiserror::Error)]
    pub enum AdaptationError {
        #[error("Failed to execute adaptation action: {0}")]
        ExecutionError(String),
        #[error("Invalid policy configuration: {0}")]
        ConfigurationError(String),
        #[error("Other error: {0}")]
        Other(String),
    }
    
    /// 触发条件
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub enum TriggerCondition {
        GreaterThan,
        LessThan,
        Equals,
    }
    
    /// Kubernetes自适应执行器实现
    pub struct KubernetesAdaptationExecutor {
        client: k8s_openapi::Client,
        namespace: String,
    }
    
    #[async_trait]
    impl AdaptationExecutor for KubernetesAdaptationExecutor {
        async fn execute_action(&self, action: &AdaptationAction) -> Result<(), AdaptationError> {
            match action {
                AdaptationAction::ScaleOut { service, instances } => {
                    // 实现Kubernetes扩容逻辑
                    tracing::info!(service=%service, instances=%instances, "Scaling out service");
                    
                    // 这里将会调用Kubernetes API进行实际扩容
                    // ...
                    
                    Ok(())
                },
                AdaptationAction::ScaleIn { service, instances } => {
                    // 实现Kubernetes缩容逻辑
                    tracing::info!(service=%service, instances=%instances, "Scaling in service");
                    
                    // 这里将会调用Kubernetes API进行实际缩容
                    // ...
                    
                    Ok(())
                },
                // ... 处理其他适应动作
                _ => Err(AdaptationError::ExecutionError(format!("Unsupported action for Kubernetes executor: {:?}", action))),
            }
        }
    }
}
```

## 实现示例：容错与恢复机制

```rust
// 容错与恢复机制
pub mod recovery {
    use crate::engine::WorkflowEngineError;
    use async_trait::async_trait;
    use backoff::{ExponentialBackoff, backoff::Backoff};
    use std::time::Duration;
    use std::future::Future;
    use std::pin::Pin;
    use tokio::sync::RwLock;
    use std::sync::Arc;
    use std::collections::HashMap;
    use thiserror::Error;
    use serde::{Serialize, Deserialize};
    
    /// 恢复错误
    #[derive(Debug, Error)]
    pub enum RecoveryError {
        #[error("Max retries exceeded: {0}")]
        MaxRetriesExceeded(String),
        #[error("Circuit breaker open: {0}")]
        CircuitBreakerOpen(String),
        #[error("Operation timeout: {0}")]
        Timeout(String),
        #[error("Other error: {0}")]
        Other(String),
    }
    
    /// 断路器状态
    #[derive(Debug, Clone, PartialEq)]
    pub enum CircuitState {
        Closed,
        Open,
        HalfOpen,
    }
    
    /// 断路器
    pub struct CircuitBreaker {
        state: Arc<RwLock<CircuitState>>,
        failure_threshold: u32,
        recovery_time: Duration,
        half_open_success_threshold: u32,
        failure_count: Arc<RwLock<u32>>,
        half_open_success_count: Arc<RwLock<u32>>,
        last_failure_time: Arc<RwLock<Option<std::time::Instant>>>,
    }
    
    impl CircuitBreaker {
        /// 创建新的断路器
        pub fn new(
            failure_threshold: u32,
            recovery_time: Duration,
            half_open_success_threshold: u32,
        ) -> Self {
            Self {
                state: Arc::new(RwLock::new(CircuitState::Closed)),
                failure_threshold,
                recovery_time,
                half_open_success_threshold,
                failure_count: Arc::new(RwLock::new(0)),
                half_open_success_count: Arc::new(RwLock::new(0)),
                last_failure_time: Arc::new(RwLock::new(None)),
            }
        }
        
        /// 执行受断路器保护的操作
        pub async fn execute<F, T, E>(&self, operation: F) -> Result<T, RecoveryError>
        where
            F: FnOnce() -> Pin<Box<dyn Future<Output = Result<T, E>> + Send>> + Send,
            E: std::fmt::Display,
        {
            // 检查当前状态
            let current_state = self.get_state().await;
            
            match current_state {
                CircuitState::Open => {
                    // 检查是否经过了恢复时间
                    let should_transition_to_half_open = {
                        let last_failure = self.last_failure_time.read().await;
                        match *last_failure {
                            Some(time) => time.elapsed() >= self.recovery_time,
                            None => true,
                        }
                    };
                    
                    if should_transition_to_half_open {
                        // 转换为半开状态
                        *self.state.write().await = CircuitState::HalfOpen;
                        *self.half_open_success_count.write().await = 0;
                    } else {
                        return Err(RecoveryError::CircuitBreakerOpen("Circuit breaker is open".to_string()));
                    }
                },
                _ => {},
            }
            
            // 执行操作
            match operation().await {
                Ok(result) => {
                    // 处理成功
                    match *self.state.read().await {
                        CircuitState::HalfOpen => {
                            // 增加半开状态下的成功计数
                            let mut success_count = self.half_open_success_count.write().await;
                            *success_count += 1;
                            
                            if *success_count >= self.half_open_success_threshold {
                                // 转换为关闭状态
                                *self.state.write().await = CircuitState::Closed;
                                *self.failure_count.write().await = 0;
                            }
                        },
                        CircuitState::Closed => {
                            // 重置失败计数
                            *self.failure_count.write().await = 0;
                        },
                        _ => {},
                    }
                    
                    Ok(result)
                },
                Err(e) => {
                    // 处理失败
                    match *self.state.read().await {
                        CircuitState::Closed => {
                            // 增加失败计数
                            let mut count = self.failure_count.write().await;
                            *count += 1;
                            
                            if *count >= self.failure_threshold {
                                // 转换为开路状态
                                *self.state.write().await = CircuitState::Open;
                                *self.last_failure_time.write().await = Some(std::time::Instant::now());
                            }
                        },
                        CircuitState::HalfOpen => {
                            // 半开状态下失败立即转为开路
                            *self.state.write().await = CircuitState::Open;
                            *self.last_failure_time.write().await = Some(std::time::Instant::now());
                        },
                        _ => {},
                    }
                    
                    Err(RecoveryError::Other(e.to_string()))
                }
            }
        }
        
        /// 获取当前断路器状态
        pub async fn get_state(&self) -> CircuitState {
            self.state.read().await.clone()
        }
    }
    
    /// 重试策略
    pub struct RetryPolicy {
        max_retries: usize,
        backoff: ExponentialBackoff,
    }
    
    impl RetryPolicy {
        /// 创建新的重试策略
        pub fn new(max_retries: usize, initial_interval: Duration, max_interval: Duration) -> Self {
            let mut backoff = ExponentialBackoff::default();
            backoff.initial_interval = initial_interval;
            backoff.max_interval = max_interval;
            backoff.multiplier = 2.0;
            backoff.randomization_factor = 0.2;
            backoff.max_elapsed_time = None; // 无最大总时间，使用max_retries控制
            
            Self {
                max_retries,
                backoff,
            }
        }
        
        /// 使用重试策略执行操作
        pub async fn execute<F, T, E>(&self, operation: impl Fn() -> F) -> Result<T, RecoveryError>
        where
            F: Future<Output = Result<T, E>>,
            E: std::fmt::Display,
        {
            let mut backoff = self.backoff.clone();
            let mut attempts = 0;
            
            loop {
                match operation().await {
                    Ok(result) => return Ok(result),
                    Err(e) => {
                        attempts += 1;
                        
                        if attempts >= self.max_retries {
                            return Err(RecoveryError::MaxRetriesExceeded(format!(
                                "Failed after {} attempts: {}", attempts, e
                            )));
                        }
                        
                        // 计算下一次重试的延迟
                        let delay = backoff.next_backoff()
                            .ok_or_else(|| RecoveryError::Other("Backoff exhausted".to_string()))?;
                            
                        tracing::warn!(
                            attempts=%attempts, 
                            retry_delay=?delay,
                            error=%e,
                            "Operation failed, retrying"
                        );
                        
                        // 等待重试
                        tokio::time::sleep(delay).await;
                    }
                }
            }
        }
    }
    
    /// 检查点管理器
    pub struct CheckpointManager {
        storage: Arc<dyn crate::storage::Storage>,
        checkpoint_interval: Duration,
    }
    
    impl CheckpointManager {
        /// 创建新的检查点管理器
        pub fn new(storage: Arc<dyn crate::storage::Storage>, checkpoint_interval: Duration) -> Self {
            Self {
                storage,
                checkpoint_interval,
            }
        }
        
        /// 创建工作流实例检查点
        pub async fn create_checkpoint(
            &self,
            instance_id: &str,
            checkpoint_data: &CheckpointData,
        ) -> Result<String, RecoveryError> {
            let checkpoint_id = format!("checkpoint-{}-{}", instance_id, uuid::Uuid::new_v4());
            
            self.storage.put(&checkpoint_id, checkpoint_data).await
                .map_err(|e| RecoveryError::Other(format!("Failed to create checkpoint: {}", e)))?;
                
            Ok(checkpoint_id)
        }
        
        /// 从检查点恢复
        pub async fn restore_from_checkpoint<T: for<'de> serde::Deserialize<'de>>(
            &self,
            checkpoint_id: &str,
        ) -> Result<T, RecoveryError> {
            self.storage.get::<T>(checkpoint_id).await
                .map_err(|e| RecoveryError::Other(format!("Failed to restore checkpoint: {}", e)))?
                .ok_or_else(|| RecoveryError::Other(format!("Checkpoint not found: {}", checkpoint_id)))
        }
# Rust 分布式工作流框架设计（续）

## 实现示例：容错与恢复机制（续）

```rust
// 容错与恢复机制（续）
pub mod recovery {
    // ... 前面内容省略

    /// 检查点数据
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct CheckpointData {
        pub instance_id: String,
        pub workflow_state: serde_json::Value,
        pub variables: HashMap<String, serde_json::Value>,
        pub node_states: HashMap<String, NodeCheckpointState>,
        pub created_at: chrono::DateTime<chrono::Utc>,
        pub metadata: HashMap<String, String>,
    }
    
    /// 节点检查点状态
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct NodeCheckpointState {
        pub node_id: String,
        pub state: String,
        pub data: Option<serde_json::Value>,
        pub retry_count: u32,
    }
    
    /// 定期检查点创建任务
    pub async fn start_periodic_checkpointing(
        checkpoint_manager: Arc<CheckpointManager>,
        engine: Arc<crate::engine::WorkflowEngine>,
        interval: Duration,
    ) -> tokio::task::JoinHandle<()> {
        tokio::spawn(async move {
            let mut interval_timer = tokio::time::interval(interval);
            
            loop {
                interval_timer.tick().await;
                
                // 获取所有活动实例
                match engine.list_active_instances().await {
                    Ok(instances) => {
                        for instance_id in instances {
                            if let Err(e) = checkpoint_instance(
                                Arc::clone(&checkpoint_manager),
                                Arc::clone(&engine),
                                &instance_id
                            ).await {
                                tracing::error!(
                                    instance_id=%instance_id,
                                    error=%e,
                                    "Failed to create checkpoint for instance"
                                );
                            }
                        }
                    },
                    Err(e) => {
                        tracing::error!(error=%e, "Failed to list active instances for checkpointing");
                    }
                }
            }
        })
    }
    
    /// 为单个实例创建检查点
    async fn checkpoint_instance(
        checkpoint_manager: Arc<CheckpointManager>,
        engine: Arc<crate::engine::WorkflowEngine>,
        instance_id: &str,
    ) -> Result<String, RecoveryError> {
        // 获取实例详情
        let instance = engine.get_workflow_instance(instance_id).await
            .map_err(|e| RecoveryError::Other(format!("Failed to get instance: {}", e)))?;
            
        // 创建检查点数据
        let checkpoint_data = CheckpointData {
            instance_id: instance_id.to_string(),
            workflow_state: serde_json::to_value(&instance.state)
                .map_err(|e| RecoveryError::Other(format!("Failed to serialize state: {}", e)))?,
            variables: instance.variables.clone(),
            node_states: instance.node_states.iter()
                .map(|(node_id, state)| {
                    (node_id.clone(), NodeCheckpointState {
                        node_id: node_id.clone(),
                        state: state.state.clone(),
                        data: Some(state.data.clone()),
                        retry_count: state.retries,
                    })
                })
                .collect(),
            created_at: chrono::Utc::now(),
            metadata: HashMap::new(),
        };
        
        // 保存检查点
        checkpoint_manager.create_checkpoint(instance_id, &checkpoint_data).await
    }
    
    /// 故障检测器
    pub struct FailureDetector {
        heartbeat_timeout: Duration,
        last_heartbeats: Arc<RwLock<HashMap<String, std::time::Instant>>>,
        node_statuses: Arc<RwLock<HashMap<String, NodeStatus>>>,
    }
    
    /// 节点状态
    #[derive(Clone, Debug, PartialEq)]
    pub enum NodeStatus {
        Healthy,
        Suspected,
        Failed,
    }
    
    impl FailureDetector {
        /// 创建新的故障检测器
        pub fn new(heartbeat_timeout: Duration) -> Self {
            Self {
                heartbeat_timeout,
                last_heartbeats: Arc::new(RwLock::new(HashMap::new())),
                node_statuses: Arc::new(RwLock::new(HashMap::new())),
            }
        }
        
        /// 处理节点心跳
        pub async fn handle_heartbeat(&self, node_id: &str) {
            let mut heartbeats = self.last_heartbeats.write().await;
            heartbeats.insert(node_id.to_string(), std::time::Instant::now());
            
            // 更新节点状态
            let mut statuses = self.node_statuses.write().await;
            statuses.insert(node_id.to_string(), NodeStatus::Healthy);
        }
        
        /// 启动故障检测任务
        pub fn start_detection_task(self: Arc<Self>, check_interval: Duration) -> tokio::task::JoinHandle<()> {
            tokio::spawn(async move {
                let mut interval = tokio::time::interval(check_interval);
                
                loop {
                    interval.tick().await;
                    
                    let now = std::time::Instant::now();
                    let heartbeats = self.last_heartbeats.read().await.clone();
                    let mut statuses = self.node_statuses.write().await;
                    
                    for (node_id, last_time) in heartbeats.iter() {
                        let elapsed = now.duration_since(*last_time);
                        
                        if elapsed > self.heartbeat_timeout {
                            // 节点可能故障
                            let current_status = statuses.get(node_id).cloned().unwrap_or(NodeStatus::Healthy);
                            
                            match current_status {
                                NodeStatus::Healthy => {
                                    // 首次超时，标记为可疑
                                    statuses.insert(node_id.clone(), NodeStatus::Suspected);
                                    tracing::warn!(node_id=%node_id, "Node suspected as failed due to missed heartbeats");
                                },
                                NodeStatus::Suspected => {
                                    // 连续超时，标记为故障
                                    statuses.insert(node_id.clone(), NodeStatus::Failed);
                                    tracing::error!(node_id=%node_id, "Node marked as failed");
                                    
                                    // 触发故障处理
                                    // 这里可以发布节点故障事件
                                },
                                NodeStatus::Failed => {
                                    // 已经是故障状态，不做变化
                                }
                            }
                        }
                    }
                }
            })
        }
        
        /// 获取节点状态
        pub async fn get_node_status(&self, node_id: &str) -> NodeStatus {
            self.node_statuses.read().await
                .get(node_id)
                .cloned()
                .unwrap_or(NodeStatus::Healthy)
        }
        
        /// 获取所有故障节点
        pub async fn get_failed_nodes(&self) -> Vec<String> {
            self.node_statuses.read().await
                .iter()
                .filter_map(|(node_id, status)| {
                    if *status == NodeStatus::Failed {
                        Some(node_id.clone())
                    } else {
                        None
                    }
                })
                .collect()
        }
    }
    
    /// 故障恢复协调器
    pub struct FailureRecoveryCoordinator {
        checkpoint_manager: Arc<CheckpointManager>,
        engine: Arc<crate::engine::WorkflowEngine>,
        failure_detector: Arc<FailureDetector>,
    }
    
    impl FailureRecoveryCoordinator {
        /// 创建新的故障恢复协调器
        pub fn new(
            checkpoint_manager: Arc<CheckpointManager>,
            engine: Arc<crate::engine::WorkflowEngine>,
            failure_detector: Arc<FailureDetector>,
        ) -> Self {
            Self {
                checkpoint_manager,
                engine,
                failure_detector,
            }
        }
        
        /// 启动恢复协调任务
        pub fn start_recovery_task(self: Arc<Self>, check_interval: Duration) -> tokio::task::JoinHandle<()> {
            tokio::spawn(async move {
                let mut interval = tokio::time::interval(check_interval);
                
                loop {
                    interval.tick().await;
                    
                    // 获取故障节点
                    let failed_nodes = self.failure_detector.get_failed_nodes().await;
                    
                    for node_id in failed_nodes {
                        // 查找故障节点上运行的实例
                        match self.engine.find_instances_by_node(&node_id).await {
                            Ok(instances) => {
                                for instance_id in instances {
                                    // 尝试恢复实例
                                    if let Err(e) = self.recover_instance(&instance_id).await {
                                        tracing::error!(
                                            instance_id=%instance_id,
                                            node_id=%node_id,
                                            error=%e,
                                            "Failed to recover instance from failed node"
                                        );
                                    }
                                }
                            },
                            Err(e) => {
                                tracing::error!(
                                    node_id=%node_id,
                                    error=%e,
                                    "Failed to find instances on failed node"
                                );
                            }
                        }
                    }
                }
            })
        }
        
        /// 恢复单个实例
        async fn recover_instance(&self, instance_id: &str) -> Result<(), RecoveryError> {
            tracing::info!(instance_id=%instance_id, "Starting instance recovery");
            
            // 查找最新检查点
            let checkpoints = self.engine.list_instance_checkpoints(instance_id).await
                .map_err(|e| RecoveryError::Other(format!("Failed to list checkpoints: {}", e)))?;
                
            if checkpoints.is_empty() {
                return Err(RecoveryError::Other(format!("No checkpoints found for instance {}", instance_id)));
            }
            
            // 找到最新的检查点
            let latest_checkpoint = checkpoints.into_iter()
                .max_by_key(|c| c.created_at)
                .unwrap();
                
            // 从检查点恢复实例
            let checkpoint_data: CheckpointData = self.checkpoint_manager
                .restore_from_checkpoint(&latest_checkpoint.id).await?;
                
            // 创建恢复后的实例状态
            let recovered_instance = crate::model::WorkflowInstance {
                id: instance_id.to_string(),
                definition_id: self.engine.get_instance_definition_id(instance_id).await
                    .map_err(|e| RecoveryError::Other(format!("Failed to get definition ID: {}", e)))?,
                version: latest_checkpoint.metadata.get("version")
                    .cloned()
                    .unwrap_or_else(|| "1.0.0".to_string()),
                state: "RECOVERING".to_string(),
                variables: checkpoint_data.variables,
                node_states: checkpoint_data.node_states.into_iter()
                    .map(|(node_id, checkpoint_state)| {
                        (node_id, crate::model::NodeState {
                            node_id: checkpoint_state.node_id,
                            state: checkpoint_state.state,
                            data: checkpoint_state.data.unwrap_or(serde_json::Value::Null),
                            retries: checkpoint_state.retry_count,
                            last_updated: chrono::Utc::now(),
                        })
                    })
                    .collect(),
                created_at: chrono::DateTime::parse_from_rfc3339(
                    latest_checkpoint.metadata.get("created_at").unwrap_or(&chrono::Utc::now().to_rfc3339())
                ).unwrap_or(chrono::Utc::now()).into(),
                updated_at: chrono::Utc::now(),
                parent_instance_id: None, // 可能需要从检查点恢复
                trace_context: None, // 可能需要从检查点恢复
            };
            
            // 保存恢复的实例
            self.engine.save_recovered_instance(&recovered_instance).await
                .map_err(|e| RecoveryError::Other(format!("Failed to save recovered instance: {}", e)))?;
                
            // 重启实例执行
            self.engine.resume_instance(instance_id).await
                .map_err(|e| RecoveryError::Other(format!("Failed to resume instance: {}", e)))?;
                
            tracing::info!(instance_id=%instance_id, "Instance recovery completed successfully");
            
            Ok(())
        }
    }
}
```

## 实现示例：工作流 DSL 与可视化设计器

```rust
// 工作流DSL与可视化设计器
pub mod dsl {
    use crate::model::{WorkflowDefinition, NodeDefinition, EdgeDefinition, NodeType, GatewayType};
    use serde::{Serialize, Deserialize};
    use std::collections::HashMap;
    use thiserror::Error;
    
    /// DSL错误
    #[derive(Debug, Error)]
    pub enum DslError {
        #[error("Parse error: {0}")]
        ParseError(String),
        #[error("Validation error: {0}")]
        ValidationError(String),
        #[error("Compilation error: {0}")]
        CompilationError(String),
    }
    
    /// YAML DSL定义
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct WorkflowDsl {
        pub name: String,
        pub version: Option<String>,
        pub description: Option<String>,
        pub variables: Option<HashMap<String, VariableDsl>>,
        pub nodes: Vec<NodeDsl>,
        pub flows: Vec<FlowDsl>,
        pub semantics: Option<Vec<SemanticTagDsl>>,
    }
    
    /// 变量DSL
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct VariableDsl {
        pub default: Option<serde_json::Value>,
        pub description: Option<String>,
        #[serde(rename = "type")]
        pub type_name: String,
    }
    
    /// 节点DSL
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct NodeDsl {
        pub id: String,
        pub name: Option<String>,
        #[serde(rename = "type")]
        pub node_type: String,
        pub config: Option<serde_json::Value>,
        pub retry: Option<RetryDsl>,
        pub timeout: Option<String>,
        pub semantics: Option<Vec<SemanticTagDsl>>,
    }
    
    /// 流程DSL
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct FlowDsl {
        pub from: String,
        pub to: String,
        pub condition: Option<String>,
    }
    
    /// 重试DSL
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct RetryDsl {
        pub max_attempts: u32,
        pub interval: String,
        pub backoff_factor: Option<f64>,
    }
    
    /// 语义标签DSL
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct SemanticTagDsl {
        pub name: String,
        pub category: String,
        pub properties: Option<HashMap<String, String>>,
    }
    
    /// DSL解析器
    pub struct DslParser;
    
    impl DslParser {
        /// 从YAML解析工作流DSL
        pub fn parse_yaml(yaml: &str) -> Result<WorkflowDsl, DslError> {
            serde_yaml::from_str(yaml)
                .map_err(|e| DslError::ParseError(format!("Failed to parse YAML: {}", e)))
        }
        
        /// 将DSL编译为工作流定义
        pub fn compile(dsl: &WorkflowDsl) -> Result<WorkflowDefinition, DslError> {
            // 创建唯一ID
            let id = uuid::Uuid::new_v4().to_string();
            
            // 解析节点
            let nodes = Self::compile_nodes(&dsl.nodes)?;
            
            // 解析边
            let edges = Self::compile_flows(&dsl.flows)?;
            
            // 解析变量
            let variables = match &dsl.variables {
                Some(vars) => vars.iter()
                    .map(|(key, var)| {
                        let var_def = crate::model::VariableDefinition {
                            name: key.clone(),
                            var_type: var.type_name.clone(),
                            default_value: var.default.clone(),
                            description: var.description.clone(),
                        };
                        (key.clone(), var_def)
                    })
                    .collect(),
                None => HashMap::new(),
            };
            
            // 解析语义标签
            let semantics = match &dsl.semantics {
                Some(tags) => tags.iter()
                    .map(|tag| crate::model::SemanticTag {
                        name: tag.name.clone(),
                        category: tag.category.clone(),
                        properties: tag.properties.clone().unwrap_or_default(),
                    })
                    .collect(),
                None => Vec::new(),
            };
            
            // 创建工作流定义
            let workflow = WorkflowDefinition {
                id,
                name: dsl.name.clone(),
                version: dsl.version.clone().unwrap_or_else(|| "1.0.0".to_string()),
                nodes,
                edges,
                variables,
                metadata: HashMap::new(),
                semantics,
            };
            
            // 验证工作流定义
            Self::validate_workflow(&workflow)?;
            
            Ok(workflow)
        }
        
        /// 编译节点定义
        fn compile_nodes(nodes_dsl: &[NodeDsl]) -> Result<Vec<NodeDefinition>, DslError> {
            let mut nodes = Vec::new();
            
            for node_dsl in nodes_dsl {
                let node_type = match node_dsl.node_type.as_str() {
                    "task" => {
                        let task_type = node_dsl.config.as_ref()
                            .and_then(|c| c.get("task_type"))
                            .and_then(|v| v.as_str())
                            .ok_or_else(|| DslError::ValidationError(format!(
                                "Task node {} must specify a task_type", node_dsl.id
                            )))?
                            .to_string();
                            
                        NodeType::Task { task_type }
                    },
                    "subworkflow" => {
                        let workflow_ref = node_dsl.config.as_ref()
                            .and_then(|c| c.get("workflow_ref"))
                            .and_then(|v| v.as_str())
                            .ok_or_else(|| DslError::ValidationError(format!(
                                "SubWorkflow node {} must specify a workflow_ref", node_dsl.id
                            )))?
                            .to_string();
                            
                        NodeType::SubWorkflow { workflow_ref }
                    },
                    "gateway" => {
                        let gateway_type_str = node_dsl.config.as_ref()
                            .and_then(|c| c.get("gateway_type"))
                            .and_then(|v| v.as_str())
                            .ok_or_else(|| DslError::ValidationError(format!(
                                "Gateway node {} must specify a gateway_type", node_dsl.id
                            )))?;
                            
                        let gateway_type = match gateway_type_str {
                            "exclusive" => GatewayType::Exclusive,
                            "parallel" => GatewayType::Parallel,
                            "inclusive" => GatewayType::Inclusive,
                            _ => return Err(DslError::ValidationError(format!(
                                "Invalid gateway type: {}", gateway_type_str
                            ))),
                        };
                        
                        NodeType::Gateway { gateway_type }
                    },
                    "event" => {
                        let event_type = node_dsl.config.as_ref()
                            .and_then(|c| c.get("event_type"))
                            .and_then(|v| v.as_str())
                            .ok_or_else(|| DslError::ValidationError(format!(
                                "Event node {} must specify an event_type", node_dsl.id
                            )))?
                            .to_string();
                            
                        NodeType::Event { event_type }
                    },
                    "place" => {
                        let initial_tokens = node_dsl.config.as_ref()
                            .and_then(|c| c.get("initial_tokens"))
                            .and_then(|v| v.as_u64())
                            .unwrap_or(0) as usize;
                            
                        NodeType::Place { initial_tokens }
                    },
                    "transition" => {
                        let condition = node_dsl.config.as_ref()
                            .and_then(|c| c.get("condition"))
                            .and_then(|v| v.as_str())
                            .map(|s| s.to_string());
                            
                        NodeType::Transition { condition }
                    },
                    _ => return Err(DslError::ValidationError(format!(
                        "Invalid node type: {}", node_dsl.node_type
                    ))),
                };
                
                // 解析超时
                let timeout = if let Some(timeout_str) = &node_dsl.timeout {
                    Some(parse_duration::parse(timeout_str)
                        .map_err(|e| DslError::ValidationError(format!(
                            "Invalid timeout format for node {}: {}", node_dsl.id, e
                        )))?)
                } else {
                    None
                };
                
                // 解析重试策略
                let retry_policy = if let Some(retry_dsl) = &node_dsl.retry {
                    let interval = parse_duration::parse(&retry_dsl.interval)
                        .map_err(|e| DslError::ValidationError(format!(
                            "Invalid retry interval format for node {}: {}", node_dsl.id, e
                        )))?;
                        
                    Some(crate::model::RetryPolicy {
                        max_attempts: retry_dsl.max_attempts,
                        interval,
                        backoff_factor: retry_dsl.backoff_factor.unwrap_or(1.0),
                    })
                } else {
                    None
                };
                
                // 解析语义标签
                let semantics = match &node_dsl.semantics {
                    Some(tags) => tags.iter()
                        .map(|tag| crate::model::SemanticTag {
                            name: tag.name.clone(),
                            category: tag.category.clone(),
                            properties: tag.properties.clone().unwrap_or_default(),
                        })
                        .collect(),
                    None => Vec::new(),
                };
                
                // 创建节点定义
                let node = NodeDefinition {
                    id: node_dsl.id.clone(),
                    node_type,
                    config: node_dsl.config.clone().unwrap_or(serde_json::Value::Object(serde_json::Map::new())),
                    retry_policy,
                    timeout,
                    semantics,
                };
                
                nodes.push(node);
            }
            
            Ok(nodes)
        }
        
        /// 编译流程定义
        fn compile_flows(flows_dsl: &[FlowDsl]) -> Result<Vec<EdgeDefinition>, DslError> {
            flows_dsl.iter()
                .map(|flow| {
                    Ok(EdgeDefinition {
                        id: format!("{}-to-{}", flow.from, flow.to),
                        source: flow.from.clone(),
                        target: flow.to.clone(),
                        condition: flow.condition.clone(),
                    })
                })
                .collect()
        }
        
        /// 验证工作流定义
        fn validate_workflow(workflow: &WorkflowDefinition) -> Result<(), DslError> {
            // 检查是否存在起始节点
            let has_start = workflow.nodes.iter().any(|n| match &n.node_type {
                NodeType::Event { event_type } => event_type == "start",
                _ => false,
            });
            
            if !has_start {
                return Err(DslError::ValidationError("Workflow must have at least one start event".to_string()));
            }
            
            // 检查是否存在终止节点
            let has_end = workflow.nodes.iter().any(|n| match &n.node_type {
                NodeType::Event { event_type } => event_type == "end",
                _ => false,
            });
            
            if !has_end {
                return Err(DslError::ValidationError("Workflow must have at least one end event".to_string()));
            }
            
            // 检查节点ID唯一性
            let mut node_ids = std::collections::HashSet::new();
            for node in &workflow.nodes {
                if !node_ids.insert(&node.id) {
                    return Err(DslError::ValidationError(format!("Duplicate node ID: {}", node.id)));
                }
            }
            
            // 检查边引用的节点是否存在
            for edge in &workflow.edges {
                if !workflow.nodes.iter().any(|n| n.id == edge.source) {
                    return Err(DslError::ValidationError(format!("Edge references non-existent source node: {}", edge.source)));
                }
                
                if !workflow.nodes.iter().any(|n| n.id == edge.target) {
                    return Err(DslError::ValidationError(format!("Edge references non-existent target node: {}", edge.target)));
                }
            }
            
            // 检查是否存在孤立节点
            for node in &workflow.nodes {
                let is_connected = workflow.edges.iter().any(|e| e.source == node.id || e.target == node.id);
                
                if !is_connected {
                    // 允许起始和终止事件不连接
                    let is_special = match &node.node_type {
                        NodeType::Event { event_type } => event_type == "start" || event_type == "end",
                        _ => false,
                    };
                    
                    if !is_special {
                        return Err(DslError::ValidationError(format!("Isolated node: {}", node.id)));
                    }
                }
            }
            
            Ok(())
        }
    }
    
    /// DSL生成器
    pub struct DslGenerator;
    
    impl DslGenerator {
        /// 将工作流定义转换为DSL
        pub fn generate(workflow: &WorkflowDefinition) -> WorkflowDsl {
            // 转换节点
            let nodes = workflow.nodes.iter()
                .map(|node| Self::node_to_dsl(node))
                .collect();
                
            // 转换流程
            let flows = workflow.edges.iter()
                .map(|edge| FlowDsl {
                    from: edge.source.clone(),
                    to: edge.target.clone(),
                    condition: edge.condition.clone(),
                })
                .collect();
                
            // 转换变量
            let variables = if !workflow.variables.is_empty() {
                Some(workflow.variables.iter()
                    .map(|(key, var)| {
                        (key.clone(), VariableDsl {
                            default: var.default_value.clone(),
                            description: var.description.clone(),
                            type_name: var.var_type.clone(),
                        })
                    })
                    .collect())
            } else {
                None
            };
            
            // 转换语义标签
            let semantics = if !workflow.semantics.is_empty() {
                Some(workflow.semantics.iter()
                    .map(|tag| SemanticTagDsl {
                        name: tag.name.clone(),
                        category: tag.category.clone(),
                        properties: Some(tag.properties.clone()),
                    })
                    .collect())
            } else {
                None
            };
            
            WorkflowDsl {
                name: workflow.name.clone(),
                version: Some(workflow.version.clone()),
                description: workflow.metadata.get("description").cloned(),
                variables,
                nodes,
                flows,
                semantics,
            }
        }
        
        /// 将节点定义转换为DSL
        fn node_to_dsl(node: &NodeDefinition) -> NodeDsl {
            let (node_type, config) = match &node.node_type {
                NodeType::Task { task_type } => {
                    let mut config = serde_json::Map::new();
                    config.insert("task_type".to_string(), serde_json::Value::String(task_type.clone()));
                    ("task".to_string(), Some(serde_json::Value::Object(config)))
                },
                NodeType::SubWorkflow { workflow_ref } => {
                    let mut config = serde_json::Map::new();
                    config.insert("workflow_ref".to_string(), serde_json::Value::String(workflow_ref.clone()));
                    ("subworkflow".to_string(), Some(serde_json::Value::Object(config)))
                },
                NodeType::Gateway { gateway_type } => {
                    let mut config =
# Rust 分布式工作流框架设计（续）

## 实现示例：工作流 DSL 与可视化设计器（续）

```rust
// 工作流DSL与可视化设计器（续）
pub mod dsl {
    // ... 前面内容省略

    impl DslGenerator {
        // ... 前面内容省略

        /// 将节点定义转换为DSL（续）
        fn node_to_dsl(node: &NodeDefinition) -> NodeDsl {
            let (node_type, config) = match &node.node_type {
                // ... 前面内容省略
                NodeType::Gateway { gateway_type } => {
                    let mut config = serde_json::Map::new();
                    let gateway_type_str = match gateway_type {
                        GatewayType::Exclusive => "exclusive",
                        GatewayType::Parallel => "parallel",
                        GatewayType::Inclusive => "inclusive",
                    };
                    config.insert("gateway_type".to_string(), serde_json::Value::String(gateway_type_str.to_string()));
                    ("gateway".to_string(), Some(serde_json::Value::Object(config)))
                },
                NodeType::Event { event_type } => {
                    let mut config = serde_json::Map::new();
                    config.insert("event_type".to_string(), serde_json::Value::String(event_type.clone()));
                    ("event".to_string(), Some(serde_json::Value::Object(config)))
                },
                NodeType::Place { initial_tokens } => {
                    let mut config = serde_json::Map::new();
                    config.insert("initial_tokens".to_string(), serde_json::Value::Number((*initial_tokens).into()));
                    ("place".to_string(), Some(serde_json::Value::Object(config)))
                },
                NodeType::Transition { condition } => {
                    let mut config = serde_json::Map::new();
                    if let Some(cond) = condition {
                        config.insert("condition".to_string(), serde_json::Value::String(cond.clone()));
                    }
                    ("transition".to_string(), Some(serde_json::Value::Object(config)))
                },
            };
            
            // 转换重试策略
            let retry = node.retry_policy.as_ref().map(|policy| {
                RetryDsl {
                    max_attempts: policy.max_attempts,
                    interval: format!("{}s", policy.interval.as_secs()),
                    backoff_factor: Some(policy.backoff_factor),
                }
            });
            
            // 转换超时
            let timeout = node.timeout.as_ref().map(|timeout| {
                format!("{}s", timeout.as_secs())
            });
            
            // 转换语义标签
            let semantics = if !node.semantics.is_empty() {
                Some(node.semantics.iter()
                    .map(|tag| SemanticTagDsl {
                        name: tag.name.clone(),
                        category: tag.category.clone(),
                        properties: Some(tag.properties.clone()),
                    })
                    .collect())
            } else {
                None
            };
            
            NodeDsl {
                id: node.id.clone(),
                name: node.config.get("name").and_then(|v| v.as_str()).map(|s| s.to_string()),
                node_type,
                config,
                retry,
                timeout,
                semantics,
            }
        }
        
        /// 生成DSL的YAML表示
        pub fn to_yaml(dsl: &WorkflowDsl) -> Result<String, DslError> {
            serde_yaml::to_string(dsl)
                .map_err(|e| DslError::CompilationError(format!("Failed to generate YAML: {}", e)))
        }
    }
    
    /// 可视化设计器Web组件
    #[cfg(feature = "web")]
    pub mod designer {
        use leptos::*;
        use super::*;
        use crate::model::{WorkflowDefinition, NodeDefinition, EdgeDefinition};
        use web_sys::{MouseEvent, DragEvent};
        
        /// 设计器状态
        #[derive(Clone)]
        pub struct DesignerState {
            pub workflow: RwSignal<WorkflowDefinition>,
            pub selected_node: RwSignal<Option<String>>,
            pub selected_edge: RwSignal<Option<String>>,
            pub dragging: RwSignal<Option<DragInfo>>,
            pub canvas_scale: RwSignal<f64>,
            pub canvas_offset: RwSignal<(f64, f64)>,
            pub show_properties_panel: RwSignal<bool>,
        }
        
        /// 拖拽信息
        #[derive(Clone)]
        pub struct DragInfo {
            pub node_id: String,
            pub start_x: f64,
            pub start_y: f64,
            pub current_x: f64,
            pub current_y: f64,
        }
        
        /// 节点位置
        #[derive(Clone, Copy, Debug)]
        pub struct NodePosition {
            pub x: f64,
            pub y: f64,
        }
        
        /// 工作流设计器组件
        #[component]
        pub fn WorkflowDesigner(
            workflow_id: Option<String>,
            on_save: Callback<WorkflowDefinition>,
        ) -> impl IntoView {
            // 初始化新工作流或加载现有工作流
            let workflow = create_rw_signal(match workflow_id {
                Some(id) => {
                    // 在实际应用中，这里会从API获取现有工作流
                    // 这里使用简化的示例
                    WorkflowDefinition {
                        id,
                        name: "Sample Workflow".to_string(),
                        version: "1.0.0".to_string(),
                        nodes: vec![],
                        edges: vec![],
                        variables: std::collections::HashMap::new(),
                        metadata: std::collections::HashMap::new(),
                        semantics: vec![],
                    }
                },
                None => {
                    // 创建新工作流
                    WorkflowDefinition {
                        id: uuid::Uuid::new_v4().to_string(),
                        name: "New Workflow".to_string(),
                        version: "1.0.0".to_string(),
                        nodes: vec![],
                        edges: vec![],
                        variables: std::collections::HashMap::new(),
                        metadata: std::collections::HashMap::new(),
                        semantics: vec![],
                    }
                }
            });
            
            // 初始化设计器状态
            let state = DesignerState {
                workflow,
                selected_node: create_rw_signal(None),
                selected_edge: create_rw_signal(None),
                dragging: create_rw_signal(None),
                canvas_scale: create_rw_signal(1.0),
                canvas_offset: create_rw_signal((0.0, 0.0)),
                show_properties_panel: create_rw_signal(true),
            };
            
            // 节点拖拽开始处理器
            let on_node_drag_start = move |node_id: String, event: DragEvent| {
                let offset = state.canvas_offset.get();
                let scale = state.canvas_scale.get();
                
                let canvas_rect = event.current_target()
                    .and_then(|t| t.dyn_into::<web_sys::Element>().ok())
                    .map(|e| e.get_bounding_client_rect());
                
                if let Some(rect) = canvas_rect {
                    let x = (event.client_x() as f64 - rect.left()) / scale - offset.0;
                    let y = (event.client_y() as f64 - rect.top()) / scale - offset.1;
                    
                    state.dragging.set(Some(DragInfo {
                        node_id,
                        start_x: x,
                        start_y: y,
                        current_x: x,
                        current_y: y,
                    }));
                }
            };
            
            // 节点拖拽处理器
            let on_node_drag = move |event: DragEvent| {
                if let Some(drag_info) = state.dragging.get() {
                    let offset = state.canvas_offset.get();
                    let scale = state.canvas_scale.get();
                    
                    let canvas_rect = event.current_target()
                        .and_then(|t| t.dyn_into::<web_sys::Element>().ok())
                        .map(|e| e.get_bounding_client_rect());
                    
                    if let Some(rect) = canvas_rect {
                        let x = (event.client_x() as f64 - rect.left()) / scale - offset.0;
                        let y = (event.client_y() as f64 - rect.top()) / scale - offset.1;
                        
                        state.dragging.set(Some(DragInfo {
                            node_id: drag_info.node_id,
                            start_x: drag_info.start_x,
                            start_y: drag_info.start_y,
                            current_x: x,
                            current_y: y,
                        }));
                    }
                }
            };
            
            // 节点拖拽结束处理器
            let on_node_drag_end = move |event: DragEvent| {
                if let Some(drag_info) = state.dragging.get() {
                    let offset = state.canvas_offset.get();
                    let scale = state.canvas_scale.get();
                    
                    let canvas_rect = event.current_target()
                        .and_then(|t| t.dyn_into::<web_sys::Element>().ok())
                        .map(|e| e.get_bounding_client_rect());
                    
                    if let Some(rect) = canvas_rect {
                        let x = (event.client_x() as f64 - rect.left()) / scale - offset.0;
                        let y = (event.client_y() as f64 - rect.top()) / scale - offset.1;
                        
                        // 更新节点位置
                        state.workflow.update(|wf| {
                            if let Some(node) = wf.nodes.iter_mut().find(|n| n.id == drag_info.node_id) {
                                let mut config = node.config.clone();
                                
                                // 确保config是一个对象
                                if !config.is_object() {
                                    config = serde_json::Value::Object(serde_json::Map::new());
                                }
                                
                                // 更新位置
                                if let Some(obj) = config.as_object_mut() {
                                    obj.insert("x".to_string(), serde_json::Value::Number((x as f64).into()));
                                    obj.insert("y".to_string(), serde_json::Value::Number((y as f64).into()));
                                }
                                
                                node.config = config;
                            }
                        });
                        
                        state.dragging.set(None);
                    }
                }
            };
            
            // 添加节点处理器
            let add_node = move |node_type: NodeType| {
                let node_id = uuid::Uuid::new_v4().to_string();
                
                // 默认位置
                let mut config = serde_json::Map::new();
                config.insert("x".to_string(), serde_json::Value::Number((100.0).into()));
                config.insert("y".to_string(), serde_json::Value::Number((100.0).into()));
                
                let node = NodeDefinition {
                    id: node_id.clone(),
                    node_type,
                    config: serde_json::Value::Object(config),
                    retry_policy: None,
                    timeout: None,
                    semantics: vec![],
                };
                
                state.workflow.update(|wf| {
                    wf.nodes.push(node);
                });
                
                state.selected_node.set(Some(node_id));
            };
            
            // 添加连接处理器
            let add_connection = move |from_id: String, to_id: String| {
                let edge_id = format!("{}-to-{}", from_id, to_id);
                
                // 检查是否已有相同连接
                let already_exists = state.workflow.with(|wf| {
                    wf.edges.iter().any(|e| e.source == from_id && e.target == to_id)
                });
                
                if !already_exists {
                    let edge = EdgeDefinition {
                        id: edge_id.clone(),
                        source: from_id,
                        target: to_id,
                        condition: None,
                    };
                    
                    state.workflow.update(|wf| {
                        wf.edges.push(edge);
                    });
                    
                    state.selected_edge.set(Some(edge_id));
                }
            };
            
            // 删除节点处理器
            let delete_node = move |node_id: String| {
                state.workflow.update(|wf| {
                    // 删除节点
                    wf.nodes.retain(|n| n.id != node_id);
                    
                    // 删除相关连接
                    wf.edges.retain(|e| e.source != node_id && e.target != node_id);
                });
                
                if state.selected_node.get().as_deref() == Some(&node_id) {
                    state.selected_node.set(None);
                }
            };
            
            // 删除连接处理器
            let delete_edge = move |edge_id: String| {
                state.workflow.update(|wf| {
                    wf.edges.retain(|e| e.id != edge_id);
                });
                
                if state.selected_edge.get().as_deref() == Some(&edge_id) {
                    state.selected_edge.set(None);
                }
            };
            
            // 保存工作流处理器
            let save_workflow = move |_| {
                on_save.call(state.workflow.get());
            };
            
            view! {
                <div class="workflow-designer">
                    <div class="toolbar">
                        <div class="node-palette">
                            <h3>"添加节点"</h3>
                            <button on:click=move |_| add_node(NodeType::Task { task_type: "default".to_string() })>
                                "任务"
                            </button>
                            <button on:click=move |_| add_node(NodeType::Gateway { gateway_type: GatewayType::Exclusive })>
                                "排他网关"
                            </button>
                            <button on:click=move |_| add_node(NodeType::Gateway { gateway_type: GatewayType::Parallel })>
                                "并行网关"
                            </button>
                            <button on:click=move |_| add_node(NodeType::Event { event_type: "start".to_string() })>
                                "开始事件"
                            </button>
                            <button on:click=move |_| add_node(NodeType::Event { event_type: "end".to_string() })>
                                "结束事件"
                            </button>
                        </div>
                        <div class="actions">
                            <button on:click=save_workflow>"保存工作流"</button>
                        </div>
                    </div>
                    
                    <div class="canvas-container"
                        on:dragover=|e| e.prevent_default() 
                        on:drop=on_node_drag_end>
                        
                        <Canvas
                            state=state.clone()
                            on_node_drag_start=on_node_drag_start
                            on_node_drag=on_node_drag
                            on_node_drag_end=on_node_drag_end
                            on_node_select=move |id| state.selected_node.set(Some(id))
                            on_edge_select=move |id| state.selected_edge.set(Some(id))
                            on_canvas_click=move |_| {
                                state.selected_node.set(None);
                                state.selected_edge.set(None);
                            }
                        />
                    </div>
                    
                    <Show
                        when=move || state.show_properties_panel.get()
                        fallback=|| view! { <div></div> }
                    >
                        <div class="properties-panel">
                            <button class="close-panel" on:click=move |_| state.show_properties_panel.set(false)>
                                "×"
                            </button>
                            
                            <h3>"属性"</h3>
                            
                            <Show
                                when=move || state.selected_node.get().is_some()
                                fallback=|| {
                                    view! {
                                        <Show
                                            when=move || state.selected_edge.get().is_some()
                                            fallback=|| view! { <div>"选择一个节点或连接查看属性"</div> }
                                        >
                                            <EdgeProperties 
                                                edge_id=state.selected_edge.get().unwrap()
                                                workflow=state.workflow
                                                on_delete=delete_edge
                                            />
                                        </Show>
                                    }
                                }
                            >
                                <NodeProperties 
                                    node_id=state.selected_node.get().unwrap()
                                    workflow=state.workflow
                                    on_delete=delete_node
                                />
                            </Show>
                        </div>
                    </Show>
                </div>
            }
        }
        
        /// 画布组件
        #[component]
        fn Canvas(
            state: DesignerState,
            on_node_drag_start: Callback<(String, DragEvent)>,
            on_node_drag: Callback<DragEvent>,
            on_node_drag_end: Callback<DragEvent>,
            on_node_select: Callback<String>,
            on_edge_select: Callback<String>,
            on_canvas_click: Callback<MouseEvent>,
        ) -> impl IntoView {
            let nodes = create_memo(move |_| {
                state.workflow.get().nodes.iter()
                    .map(|node| {
                        let config = node.config.clone();
                        let x = config.get("x").and_then(|v| v.as_f64()).unwrap_or(0.0);
                        let y = config.get("y").and_then(|v| v.as_f64()).unwrap_or(0.0);
                        
                        (node.clone(), NodePosition { x, y })
                    })
                    .collect::<Vec<_>>()
            });
            
            let edges = create_memo(move |_| {
                state.workflow.get().edges.clone()
            });
            
            let render_nodes = move || {
                nodes.get().into_iter().map(|(node, pos)| {
                    let node_id = node.id.clone();
                    let is_selected = state.selected_node.get().as_deref() == Some(&node_id);
                    
                    let node_type_class = match &node.node_type {
                        NodeType::Task { .. } => "node-task",
                        NodeType::Gateway { gateway_type } => match gateway_type {
                            GatewayType::Exclusive => "node-gateway-exclusive",
                            GatewayType::Parallel => "node-gateway-parallel",
                            GatewayType::Inclusive => "node-gateway-inclusive",
                        },
                        NodeType::Event { event_type } => match event_type.as_str() {
                            "start" => "node-event-start",
                            "end" => "node-event-end",
                            _ => "node-event",
                        },
                        NodeType::SubWorkflow { .. } => "node-subworkflow",
                        NodeType::Place { .. } => "node-place",
                        NodeType::Transition { .. } => "node-transition",
                    };
                    
                    let node_label = match &node.node_type {
                        NodeType::Task { task_type } => task_type.clone(),
                        NodeType::Gateway { gateway_type } => match gateway_type {
                            GatewayType::Exclusive => "Exclusive".to_string(),
                            GatewayType::Parallel => "Parallel".to_string(),
                            GatewayType::Inclusive => "Inclusive".to_string(),
                        },
                        NodeType::Event { event_type } => match event_type.as_str() {
                            "start" => "Start".to_string(),
                            "end" => "End".to_string(),
                            _ => event_type.clone(),
                        },
                        NodeType::SubWorkflow { workflow_ref } => format!("SubWF: {}", workflow_ref),
                        NodeType::Place { .. } => "Place".to_string(),
                        NodeType::Transition { .. } => "Transition".to_string(),
                    };
                    
                    let offset = state.canvas_offset.get();
                    let scale = state.canvas_scale.get();
                    
                    let x = (pos.x + offset.0) * scale;
                    let y = (pos.y + offset.1) * scale;
                    
                    let dragging = state.dragging.get()
                        .filter(|d| d.node_id == node_id)
                        .map(|d| (d.current_x, d.current_y));
                        
                    let actual_x = if let Some((drag_x, _)) = dragging { drag_x } else { pos.x };
                    let actual_y = if let Some((_, drag_y)) = dragging { drag_y } else { pos.y };
                    
                    let node_style = format!(
                        "left: {}px; top: {}px; transform: translate(-50%, -50%);",
                        (actual_x + offset.0) * scale, (actual_y + offset.1) * scale
                    );
                    
                    let this_node_id = node_id.clone();
                    
                    view! {
                        <div
                            class=format!("workflow-node {} {}", node_type_class, if is_selected { "selected" } else { "" })
                            style=node_style
                            draggable="true"
                            on:dragstart=move |e| on_node_drag_start.call((this_node_id.clone(), e))
                            on:click=move |e| {
                                e.stop_propagation();
                                on_node_select.call(this_node_id.clone());
                            }
                            data-node-id=node_id
                        >
                            <div class="node-label">{node_label}</div>
                        </div>
                    }
                }).collect_view()
            };
            
            let render_edges = move || {
                let node_positions = nodes.get().into_iter()
                    .map(|(node, pos)| (node.id, pos))
                    .collect::<HashMap<String, NodePosition>>();
                    
                edges.get().into_iter().map(|edge| {
                    let edge_id = edge.id.clone();
                    let is_selected = state.selected_edge.get().as_deref() == Some(&edge_id);
                    
                    let source_pos = node_positions.get(&edge.source).cloned().unwrap_or(NodePosition { x: 0.0, y: 0.0 });
                    let target_pos = node_positions.get(&edge.target).cloned().unwrap_or(NodePosition { x: 0.0, y: 0.0 });
                    
                    let offset = state.canvas_offset.get();
                    let scale = state.canvas_scale.get();
                    
                    let x1 = (source_pos.x + offset.0) * scale;
                    let y1 = (source_pos.y + offset.1) * scale;
                    let x2 = (target_pos.x + offset.0) * scale;
                    let y2 = (target_pos.y + offset.1) * scale;
                    
                    // 计算控制点，创建曲线
                    let dx = x2 - x1;
                    let dy = y2 - y1;
                    let control_x = x1 + dx * 0.5;
                    let control_y = y1 + dy * 0.5;
                    
                    let path = format!(
                        "M {} {} Q {} {} {} {}",
                        x1, y1, control_x, control_y, x2, y2
                    );
                    
                    let this_edge_id = edge_id.clone();
                    
                    view! {
                        <g
                            class=format!("workflow-edge {}", if is_selected { "selected" } else { "" })
                            on:click=move |e| {
                                e.stop_propagation();
                                on_edge_select.call(this_edge_id.clone());
                            }
                            data-edge-id=edge_id
                        >
                            <path 
                                d=path 
                                fill="none" 
                                stroke="black" 
                                stroke-width="2"
                            />
                            <polygon 
                                points="0,0 -10,5 -10,-5" 
                                fill="black"
                                transform=format!(
                                    "translate({},{}) rotate({})",
                                    x2, y2, (dy.atan2(dx) * 180.0 / std::f64::consts::PI)
                                )
                            />
                        </g>
                    }
                }).collect_view()
            };
            
            view! {
                <div class="canvas" on:click=move |e| on_canvas_click.call(e)>
                    <svg width="100%" height="100%">
                        {render_edges}
                    </svg>
                    {render_nodes}
                </div>
            }
        }
        
        /// 节点属性组件
        #[component]
        fn NodeProperties(
            node_id: String,
            workflow: RwSignal<WorkflowDefinition>,
            on_delete: Callback<String>,
        ) -> impl IntoView {
            let node = create_memo(move |_| {
                workflow.get().nodes.iter()
                    .find(|n| n.id == node_id)
                    .cloned()
            });
            
            let node_name = create_rw_signal(node.get().and_then(|n| n.config.get("name").and_then(|v| v.as_str()).map(|s| s.to_string())).unwrap_or_default());
            
            let update_node_name = move |_| {
                let name = node_name.get();
                workflow.update(|wf| {
                    if let Some(node) = wf.nodes.iter_mut().find(|n| n.id == node_id) {
                        let mut config = node.config.clone();
                        
                        // 确保config是一个对象
                        if !config.is_object() {
                            config = serde_json::Value::Object(serde_json::Map::new());
                        }
                        
                        if let Some(obj) = config.as_object_mut() {
                            obj.insert("name".to_string(), serde_json::Value::String(name));
                        }
                        
                        node.config = config;
                    }
                });
            };
            
            let handle_delete = move |_| {
                on_delete.call(node_id.clone());
            };
            
            view! {
                <div class="node-properties">
                    <h4>"节点属性"</h4>
                    
                    <Show
                        when=move || node.get().is_some()
                        fallback=|| view! { <div>"节点不存在"</div> }
                    >
                        <div class="property-group">
                            <label>"节点ID:"</label>
                            <input type="text" readonly value=node_id/>
                        </div>
                        
                        <div class="property-group">
                            <label>"节点名称:"</label>
                            <input 
                                type="text" 
                                prop:value=move || node_name.get()
                                on:input=move |e| {
                                    if let Some(input) = event_target_value(&e) {
                                        node_name.set(input);
                                    }
                                }
                                on:blur=update_node_name
                            />
                        </div>
                        
                        <div class="property-group">
                            <label>"节点类型:"</label>
                            <input 
                                type="text" 
                                readonly 
                                value=move || match &node.get().unwrap().node_type {
                                    NodeType::Task { task_type } => format!("任务 ({})", task_type),
                                    NodeType::Gateway { gateway_type } => match gateway_type {
                                        GatewayType::Exclusive => "排他网关".to_string(),
                                        GatewayType::Parallel => "并行网关".to_string(),
                                        GatewayType::Inclusive => "包容网关".to_string(),
                                    },
                                    NodeType::Event { event_type } => match event_type.as_str() {
                                        "start" => "开始事件".to_string(),
                                        "end" => "结束事件".to_string(),
                                        _ => format!("事件 ({})", event_type),
                                    },
                                    NodeType::SubWorkflow { workflow_ref } => format!("子工作流 ({})", workflow_ref),
                                    NodeType::Place { .. } => "库所".to_string(),
                                    NodeType::Transition { .. } => "变迁".to_string(),
                                }
                            />
                        </div>
                        
                        
# Rust 分布式工作流框架设计（续）

## 实现示例：工作流 DSL 与可视化设计器（续）

```rust
// 工作流DSL与可视化设计器（续）
pub mod dsl {
    // ... 前面内容省略

    #[cfg(feature = "web")]
    pub mod designer {
        // ... 前面内容省略

        /// 节点属性组件（续）
        #[component]
        fn NodeProperties(
            // ... 前面内容省略
        ) -> impl IntoView {
            // ... 前面内容省略
            
            view! {
                <div class="node-properties">
                    // ... 前面内容省略
                    
                    <Show
                        when=move || node.get().is_some()
                        fallback=|| view! { <div>"节点不存在"</div> }
                    >
                        // ... 前面内容省略
                        
                        {move || {
                            // 根据节点类型渲染特定属性编辑器
                            match &node.get().unwrap().node_type {
                                NodeType::Task { task_type } => {
                                    let task_type_signal = create_rw_signal(task_type.clone());
                                    
                                    let update_task_type = move |_| {
                                        let new_type = task_type_signal.get();
                                        workflow.update(|wf| {
                                            if let Some(node) = wf.nodes.iter_mut().find(|n| n.id == node_id) {
                                                if let NodeType::Task { .. } = &node.node_type {
                                                    node.node_type = NodeType::Task { task_type: new_type.clone() };
                                                }
                                            }
                                        });
                                    };
                                    
                                    view! {
                                        <div class="property-group">
                                            <label>"任务类型:"</label>
                                            <input 
                                                type="text" 
                                                prop:value=move || task_type_signal.get()
                                                on:input=move |e| {
                                                    if let Some(input) = event_target_value(&e) {
                                                        task_type_signal.set(input);
                                                    }
                                                }
                                                on:blur=update_task_type
                                            />
                                        </div>
                                        
                                        <TaskPropertiesEditor 
                                            node_id=node_id.clone()
                                            workflow=workflow
                                        />
                                    }.into_view()
                                },
                                NodeType::Gateway { gateway_type } => {
                                    let gateway_options = vec![
                                        ("exclusive", "排他网关"),
                                        ("parallel", "并行网关"),
                                        ("inclusive", "包容网关"),
                                    ];
                                    
                                    let current_type = match gateway_type {
                                        GatewayType::Exclusive => "exclusive",
                                        GatewayType::Parallel => "parallel",
                                        GatewayType::Inclusive => "inclusive",
                                    };
                                    
                                    let gateway_type_signal = create_rw_signal(current_type.to_string());
                                    
                                    let update_gateway_type = move |_| {
                                        let new_type = gateway_type_signal.get();
                                        workflow.update(|wf| {
                                            if let Some(node) = wf.nodes.iter_mut().find(|n| n.id == node_id) {
                                                let gateway_type = match new_type.as_str() {
                                                    "exclusive" => GatewayType::Exclusive,
                                                    "parallel" => GatewayType::Parallel,
                                                    "inclusive" => GatewayType::Inclusive,
                                                    _ => GatewayType::Exclusive,
                                                };
                                                
                                                if let NodeType::Gateway { .. } = &node.node_type {
                                                    node.node_type = NodeType::Gateway { gateway_type };
                                                }
                                            }
                                        });
                                    };
                                    
                                    view! {
                                        <div class="property-group">
                                            <label>"网关类型:"</label>
                                            <select 
                                                on:change=move |e| {
                                                    if let Some(value) = event_target_value(&e) {
                                                        gateway_type_signal.set(value);
                                                        update_gateway_type(());
                                                    }
                                                }
                                            >
                                                {gateway_options.iter().map(|(value, label)| {
                                                    view! {
                                                        <option 
                                                            value=value 
                                                            selected=current_type == *value
                                                        >
                                                            {label}
                                                        </option>
                                                    }
                                                }).collect_view()}
                                            </select>
                                        </div>
                                    }.into_view()
                                },
                                NodeType::Event { event_type } => {
                                    let event_type_signal = create_rw_signal(event_type.clone());
                                    
                                    let update_event_type = move |_| {
                                        let new_type = event_type_signal.get();
                                        workflow.update(|wf| {
                                            if let Some(node) = wf.nodes.iter_mut().find(|n| n.id == node_id) {
                                                if let NodeType::Event { .. } = &node.node_type {
                                                    node.node_type = NodeType::Event { event_type: new_type.clone() };
                                                }
                                            }
                                        });
                                    };
                                    
                                    view! {
                                        <div class="property-group">
                                            <label>"事件类型:"</label>
                                            <select 
                                                on:change=move |e| {
                                                    if let Some(value) = event_target_value(&e) {
                                                        event_type_signal.set(value);
                                                        update_event_type(());
                                                    }
                                                }
                                            >
                                                <option value="start" selected=event_type == "start">"开始"</option>
                                                <option value="end" selected=event_type == "end">"结束"</option>
                                                <option value="timer" selected=event_type == "timer">"定时器"</option>
                                                <option value="message" selected=event_type == "message">"消息"</option>
                                                <option value="error" selected=event_type == "error">"错误"</option>
                                            </select>
                                        </div>
                                    }.into_view()
                                },
                                // ... 其他节点类型的专用编辑器
                                _ => view! { <div></div> }.into_view()
                            }
                        }}
                        
                        <div class="property-group">
                            <h5>"超时设置"</h5>
                            <div class="timeout-editor">
                                <input 
                                    type="checkbox" 
                                    id="enable-timeout"
                                    checked=move || node.get().unwrap().timeout.is_some()
                                    on:change=move |e| {
                                        let checked = event_target_checked(&e);
                                        workflow.update(|wf| {
                                            if let Some(node) = wf.nodes.iter_mut().find(|n| n.id == node_id) {
                                                if checked {
                                                    node.timeout = Some(std::time::Duration::from_secs(60)); // 默认1分钟
                                                } else {
                                                    node.timeout = None;
                                                }
                                            }
                                        });
                                    }
                                />
                                <label for="enable-timeout">"启用超时"</label>
                                
                                <Show
                                    when=move || node.get().unwrap().timeout.is_some()
                                >
                                    {move || {
                                        let timeout_secs = create_rw_signal(
                                            node.get().unwrap().timeout.map(|t| t.as_secs()).unwrap_or(60).to_string()
                                        );
                                        
                                        let update_timeout = move |_| {
                                            if let Ok(secs) = timeout_secs.get().parse::<u64>() {
                                                workflow.update(|wf| {
                                                    if let Some(node) = wf.nodes.iter_mut().find(|n| n.id == node_id) {
                                                        node.timeout = Some(std::time::Duration::from_secs(secs));
                                                    }
                                                });
                                            }
                                        };
                                        
                                        view! {
                                            <div class="timeout-duration">
                                                <input 
                                                    type="number" 
                                                    min="1"
                                                    prop:value=move || timeout_secs.get()
                                                    on:input=move |e| {
                                                        if let Some(input) = event_target_value(&e) {
                                                            timeout_secs.set(input);
                                                        }
                                                    }
                                                    on:blur=update_timeout
                                                />
                                                <span>"秒"</span>
                                            </div>
                                        }
                                    }}
                                </Show>
                            </div>
                        </div>
                        
                        <div class="property-group">
                            <h5>"重试策略"</h5>
                            <div class="retry-editor">
                                <input 
                                    type="checkbox" 
                                    id="enable-retry"
                                    checked=move || node.get().unwrap().retry_policy.is_some()
                                    on:change=move |e| {
                                        let checked = event_target_checked(&e);
                                        workflow.update(|wf| {
                                            if let Some(node) = wf.nodes.iter_mut().find(|n| n.id == node_id) {
                                                if checked {
                                                    // 默认重试策略
                                                    node.retry_policy = Some(crate::model::RetryPolicy {
                                                        max_attempts: 3,
                                                        interval: std::time::Duration::from_secs(5),
                                                        backoff_factor: 2.0,
                                                    });
                                                } else {
                                                    node.retry_policy = None;
                                                }
                                            }
                                        });
                                    }
                                />
                                <label for="enable-retry">"启用重试"</label>
                                
                                <Show
                                    when=move || node.get().unwrap().retry_policy.is_some()
                                >
                                    {move || {
                                        let retry_policy = node.get().unwrap().retry_policy.clone().unwrap();
                                        
                                        let max_attempts = create_rw_signal(retry_policy.max_attempts.to_string());
                                        let interval_secs = create_rw_signal((retry_policy.interval.as_secs()).to_string());
                                        let backoff_factor = create_rw_signal(retry_policy.backoff_factor.to_string());
                                        
                                        let update_retry_policy = move |_| {
                                            let max = max_attempts.get().parse::<u32>().unwrap_or(3);
                                            let interval = interval_secs.get().parse::<u64>().unwrap_or(5);
                                            let factor = backoff_factor.get().parse::<f64>().unwrap_or(2.0);
                                            
                                            workflow.update(|wf| {
                                                if let Some(node) = wf.nodes.iter_mut().find(|n| n.id == node_id) {
                                                    node.retry_policy = Some(crate::model::RetryPolicy {
                                                        max_attempts: max,
                                                        interval: std::time::Duration::from_secs(interval),
                                                        backoff_factor: factor,
                                                    });
                                                }
                                            });
                                        };
                                        
                                        view! {
                                            <div class="retry-settings">
                                                <div class="form-group">
                                                    <label>"最大尝试次数:"</label>
                                                    <input 
                                                        type="number" 
                                                        min="1"
                                                        prop:value=move || max_attempts.get()
                                                        on:input=move |e| {
                                                            if let Some(input) = event_target_value(&e) {
                                                                max_attempts.set(input);
                                                            }
                                                        }
                                                        on:blur=update_retry_policy.clone()
                                                    />
                                                </div>
                                                
                                                <div class="form-group">
                                                    <label>"初始间隔(秒):"</label>
                                                    <input 
                                                        type="number" 
                                                        min="1"
                                                        prop:value=move || interval_secs.get()
                                                        on:input=move |e| {
                                                            if let Some(input) = event_target_value(&e) {
                                                                interval_secs.set(input);
                                                            }
                                                        }
                                                        on:blur=update_retry_policy.clone()
                                                    />
                                                </div>
                                                
                                                <div class="form-group">
                                                    <label>"退避因子:"</label>
                                                    <input 
                                                        type="number" 
                                                        min="1"
                                                        step="0.1"
                                                        prop:value=move || backoff_factor.get()
                                                        on:input=move |e| {
                                                            if let Some(input) = event_target_value(&e) {
                                                                backoff_factor.set(input);
                                                            }
                                                        }
                                                        on:blur=update_retry_policy
                                                    />
                                                </div>
                                            </div>
                                        }
                                    }}
                                </Show>
                            </div>
                        </div>
                        
                        <div class="action-buttons">
                            <button class="delete-button" on:click=handle_delete>
                                "删除节点"
                            </button>
                        </div>
                    </Show>
                </div>
            }
        }
        
        /// 任务属性编辑器组件
        #[component]
        fn TaskPropertiesEditor(
            node_id: String,
            workflow: RwSignal<WorkflowDefinition>,
        ) -> impl IntoView {
            // 获取节点配置
            let node_config = create_memo(move |_| {
                workflow.get().nodes.iter()
                    .find(|n| n.id == node_id)
                    .map(|n| n.config.clone())
                    .unwrap_or_else(|| serde_json::Value::Object(serde_json::Map::new()))
            });
            
            // 创建表单字段信号
            let input_vars = create_rw_signal(
                node_config.get().get("input_vars")
                    .and_then(|v| v.as_array())
                    .map(|arr| arr.iter().filter_map(|v| v.as_str().map(|s| s.to_string())).collect::<Vec<_>>())
                    .unwrap_or_default()
            );
            
            let output_vars = create_rw_signal(
                node_config.get().get("output_vars")
                    .and_then(|v| v.as_array())
                    .map(|arr| arr.iter().filter_map(|v| v.as_str().map(|s| s.to_string())).collect::<Vec<_>>())
                    .unwrap_or_default()
            );
            
            let task_handler = create_rw_signal(
                node_config.get().get("handler")
                    .and_then(|v| v.as_str())
                    .unwrap_or("")
                    .to_string()
            );
            
            // 更新配置方法
            let update_config = move || {
                workflow.update(|wf| {
                    if let Some(node) = wf.nodes.iter_mut().find(|n| n.id == node_id) {
                        let mut config = node.config.clone();
                        
                        // 确保config是一个对象
                        if !config.is_object() {
                            config = serde_json::Value::Object(serde_json::Map::new());
                        }
                        
                        if let Some(obj) = config.as_object_mut() {
                            // 更新输入变量
                            let input_array = input_vars.get().iter()
                                .map(|s| serde_json::Value::String(s.clone()))
                                .collect::<Vec<_>>();
                            obj.insert("input_vars".to_string(), serde_json::Value::Array(input_array));
                            
                            // 更新输出变量
                            let output_array = output_vars.get().iter()
                                .map(|s| serde_json::Value::String(s.clone()))
                                .collect::<Vec<_>>();
                            obj.insert("output_vars".to_string(), serde_json::Value::Array(output_array));
                            
                            // 更新处理器
                            obj.insert("handler".to_string(), serde_json::Value::String(task_handler.get()));
                        }
                        
                        node.config = config;
                    }
                });
            };
            
            // 添加变量处理方法
            let add_input_var = move |_| {
                input_vars.update(|vars| vars.push("".to_string()));
            };
            
            let add_output_var = move |_| {
                output_vars.update(|vars| vars.push("".to_string()));
            };
            
            // 删除变量处理方法
            let remove_input_var = move |index: usize| {
                input_vars.update(|vars| {
                    vars.remove(index);
                });
                update_config();
            };
            
            let remove_output_var = move |index: usize| {
                output_vars.update(|vars| {
                    vars.remove(index);
                });
                update_config();
            };
            
            view! {
                <div class="task-properties">
                    <div class="property-group">
                        <label>"处理器:"</label>
                        <input 
                            type="text" 
                            prop:value=move || task_handler.get()
                            on:input=move |e| {
                                if let Some(input) = event_target_value(&e) {
                                    task_handler.set(input);
                                }
                            }
                            on:blur=move |_| update_config()
                        />
                        <span class="hint">"任务处理函数的标识符"</span>
                    </div>
                    
                    <div class="property-group">
                        <label>"输入变量:"</label>
                        <div class="var-list">
                            <For
                                each=move || input_vars.get()
                                key=|(_i, _)| uuid::Uuid::new_v4().to_string()
                                let:item
                            >
                                {move |(index, var)| {
                                    let var_signal = create_rw_signal(var);
                                    
                                    let update_var = move |_| {
                                        input_vars.update(|vars| {
                                            vars[index] = var_signal.get();
                                        });
                                        update_config();
                                    };
                                    
                                    view! {
                                        <div class="var-item">
                                            <input 
                                                type="text" 
                                                prop:value=move || var_signal.get()
                                                on:input=move |e| {
                                                    if let Some(input) = event_target_value(&e) {
                                                        var_signal.set(input);
                                                    }
                                                }
                                                on:blur=update_var
                                            />
                                            <button 
                                                class="remove-var" 
                                                on:click=move |_| remove_input_var(index)
                                            >
                                                "×"
                                            </button>
                                        </div>
                                    }
                                }}
                            </For>
                            
                            <button class="add-var" on:click=add_input_var>
                                "+ 添加输入变量"
                            </button>
                        </div>
                    </div>
                    
                    <div class="property-group">
                        <label>"输出变量:"</label>
                        <div class="var-list">
                            <For
                                each=move || output_vars.get()
                                key=|(_i, _)| uuid::Uuid::new_v4().to_string()
                                let:item
                            >
                                {move |(index, var)| {
                                    let var_signal = create_rw_signal(var);
                                    
                                    let update_var = move |_| {
                                        output_vars.update(|vars| {
                                            vars[index] = var_signal.get();
                                        });
                                        update_config();
                                    };
                                    
                                    view! {
                                        <div class="var-item">
                                            <input 
                                                type="text" 
                                                prop:value=move || var_signal.get()
                                                on:input=move |e| {
                                                    if let Some(input) = event_target_value(&e) {
                                                        var_signal.set(input);
                                                    }
                                                }
                                                on:blur=update_var
                                            />
                                            <button 
                                                class="remove-var" 
                                                on:click=move |_| remove_output_var(index)
                                            >
                                                "×"
                                            </button>
                                        </div>
                                    }
                                }}
                            </For>
                            
                            <button class="add-var" on:click=add_output_var>
                                "+ 添加输出变量"
                            </button>
                        </div>
                    </div>
                </div>
            }
        }
        
        /// 边属性组件
        #[component]
        fn EdgeProperties(
            edge_id: String,
            workflow: RwSignal<WorkflowDefinition>,
            on_delete: Callback<String>,
        ) -> impl IntoView {
            let edge = create_memo(move |_| {
                workflow.get().edges.iter()
                    .find(|e| e.id == edge_id)
                    .cloned()
            });
            
            let condition = create_rw_signal(edge.get().and_then(|e| e.condition.clone()).unwrap_or_default());
            
            let update_condition = move |_| {
                let cond = condition.get();
                workflow.update(|wf| {
                    if let Some(edge) = wf.edges.iter_mut().find(|e| e.id == edge_id) {
                        if cond.trim().is_empty() {
                            edge.condition = None;
                        } else {
                            edge.condition = Some(cond);
                        }
                    }
                });
            };
            
            let handle_delete = move |_| {
                on_delete.call(edge_id.clone());
            };
            
            view! {
                <div class="edge-properties">
                    <h4>"连接属性"</h4>
                    
                    <Show
                        when=move || edge.get().is_some()
                        fallback=|| view! { <div>"连接不存在"</div> }
                    >
                        <div class="property-group">
                            <label>"连接ID:"</label>
                            <input type="text" readonly value=edge_id/>
                        </div>
                        
                        <div class="property-group">
                            <label>"源节点:"</label>
                            <input 
                                type="text" 
                                readonly 
                                value=move || edge.get().map(|e| e.source).unwrap_or_default()
                            />
                        </div>
                        
                        <div class="property-group">
                            <label>"目标节点:"</label>
                            <input 
                                type="text" 
                                readonly 
                                value=move || edge.get().map(|e| e.target).unwrap_or_default()
                            />
                        </div>
                        
                        <div class="property-group">
                            <label>"条件表达式:"</label>
                            <textarea 
                                prop:value=move || condition.get()
                                on:input=move |e| {
                                    if let Some(input) = event_target_value(&e) {
                                        condition.set(input);
                                    }
                                }
                                on:blur=update_condition
                                placeholder="输入条件表达式，留空表示无条件"
                            ></textarea>
                            <span class="hint">"可以使用JavaScript表达式，访问工作流变量"</span>
                        </div>
                        
                        <div class="action-buttons">
                            <button class="delete-button" on:click=handle_delete>
                                "删除连接"
                            </button>
                        </div>
                    </Show>
                </div>
            }
        }
    }
}
```

## 实现示例：工作流执行引擎

```rust
// 工作流执行引擎
pub mod execution {
    use crate::model::{WorkflowDefinition, WorkflowInstance, NodeDefinition, NodeType, GatewayType};
    use crate::storage::StorageManager;
    use crate::event_bus::EventBus;
    use async_trait::async_trait;
    use tokio::sync::{mpsc, oneshot, RwLock};
    use std::collections::{HashMap, HashSet, VecDeque};
    use std::sync::Arc;
    use std::time::Duration;
    use serde::{Serialize, Deserialize};
    use thiserror::Error;
    use uuid::Uuid;
    use tracing::{info, warn, error, debug, instrument, Span, trace};
    
    /// 任务上下文
    #[derive(Clone, Debug)]
    pub struct TaskContext {
        pub instance_id: String,
        pub node_id: String,
        pub variables: HashMap<String, serde_json::Value>,
        pub node_config: serde_json::Value,
        pub retry_count: u32,
        pub correlation_id: String,
        pub trace_context: Option<TraceContext>,
    }
    
    /// 任务结果
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct TaskResult {
        pub output: HashMap<String, serde_json::Value>,
        pub status: TaskStatus,
        pub message: Option<String>,
    }
    
    /// 任务状态
    #[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
    pub enum TaskStatus {
        Completed,
        Failed(String),
        Suspended(String),
    }
    
    /// 执行错误
    #[derive(Debug, Error)]
    pub enum ExecutionError {
        #[error("Task execution failed: {0}")]
        TaskFailed(String),
        #[error("Task timeout")]
        Timeout,
        #[error("Workflow definition not found: {0}")]
        WorkflowNotFound(String),
        #[error("Node not found: {0}")]
        NodeNotFound(String),
        #[error("Storage error: {0}")]
        StorageError(String),
        #[error("Validation error: {0}")]
        ValidationError(String),
        #[error("Concurrency error: {0}")]
        ConcurrencyError(String),
        #[error("Other error: {0}")]
        Other(String),
    }
    
    /// 追踪上下文
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct TraceContext {
        pub trace_id: String,
        pub span_id: String,
        pub parent_span_id: Option<String>,
    }
    
    /// 任务执行器接口
    #[async_trait]
    pub trait Executor: Send + Sync {
        async fn execute(&self, context: TaskContext) -> Result<TaskResult, ExecutionError>;
        fn get_task_types(&self) -> Vec<String>;
        fn get_stats(&self) -> ExecutorStats;
    }
    
    /// 执行器统计
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct ExecutorStats {
        pub tasks_completed: u64,
        pub tasks_failed: u64,
        pub tasks_in_progress: u64,
        pub avg_execution_time_ms: f64,
    }
    
    /// 工作流执行引擎
    pub struct WorkflowExecutionEngine {
        storage: Arc<StorageManager>,
        event_bus: Arc<dyn EventBus>,
        executors: HashMap<String, Arc<dyn Executor>>,
        active_instances: Arc<RwLock<HashMap<String, InstanceExecutionState>>>,
        task_queue: mpsc::Sender<QueuedTask>,
        worker_count: usize,
    }
    
    /// 实例执行状态
    struct InstanceExecutionState {
        instance_id: String,
        pending_nodes:
# Rust 分布式工作流框架设计（续）

## 实现示例：工作流执行引擎（续）

```rust
// 工作流执行引擎（续）
pub mod execution {
    // ... 前面内容省略

    /// 实例执行状态
    struct InstanceExecutionState {
        instance_id: String,
        pending_nodes: HashSet<String>,
        running_nodes: HashSet<String>,
        completed_nodes: HashSet<String>,
        variables: HashMap<String, serde_json::Value>,
        created_at: chrono::DateTime<chrono::Utc>,
        updated_at: chrono::DateTime<chrono::Utc>,
        cancellation_token: Option<oneshot::Sender<()>>,
    }
    
    /// 排队任务
    struct QueuedTask {
        instance_id: String,
        node_id: String,
        context: TaskContext,
        result_sender: oneshot::Sender<Result<TaskResult, ExecutionError>>,
    }
    
    impl WorkflowExecutionEngine {
        /// 创建新的工作流执行引擎
        pub fn new(
            storage: Arc<StorageManager>,
            event_bus: Arc<dyn EventBus>,
            executors: HashMap<String, Arc<dyn Executor>>,
            worker_count: usize,
        ) -> Self {
            let (tx, rx) = mpsc::channel::<QueuedTask>(1000);
            
            let engine = Self {
                storage,
                event_bus,
                executors,
                active_instances: Arc::new(RwLock::new(HashMap::new())),
                task_queue: tx,
                worker_count,
            };
            
            // 启动任务执行工作器
            engine.start_workers(rx);
            
            engine
        }
        
        /// 启动任务执行工作器
        fn start_workers(&self, rx: mpsc::Receiver<QueuedTask>) {
            let rx = Arc::new(tokio::sync::Mutex::new(rx));
            let executors = self.executors.clone();
            
            for i in 0..self.worker_count {
                let worker_rx = Arc::clone(&rx);
                let worker_executors = executors.clone();
                
                tokio::spawn(async move {
                    let worker_id = format!("worker-{}", i);
                    info!(worker_id = %worker_id, "Starting task worker");
                    
                    loop {
                        // 获取下一个任务
                        let task = {
                            let mut rx_guard = worker_rx.lock().await;
                            match rx_guard.recv().await {
                                Some(task) => task,
                                None => {
                                    // 通道已关闭
                                    break;
                                }
                            }
                        };
                        
                        // 处理任务
                        let task_type = match get_node_task_type(&task.context.node_config) {
                            Some(task_type) => task_type,
                            None => {
                                error!(
                                    instance_id = %task.instance_id,
                                    node_id = %task.node_id,
                                    "Failed to determine task type"
                                );
                                
                                let _ = task.result_sender.send(Err(ExecutionError::ValidationError(
                                    "Failed to determine task type".to_string()
                                )));
                                
                                continue;
                            }
                        };
                        
                        // 查找合适的执行器
                        let executor = match find_executor_for_task(&worker_executors, &task_type) {
                            Some(executor) => executor,
                            None => {
                                error!(
                                    instance_id = %task.instance_id,
                                    node_id = %task.node_id,
                                    task_type = %task_type,
                                    "No executor found for task type"
                                );
                                
                                let _ = task.result_sender.send(Err(ExecutionError::ValidationError(
                                    format!("No executor found for task type: {}", task_type)
                                )));
                                
                                continue;
                            }
                        };
                        
                        // 执行任务
                        info!(
                            worker_id = %worker_id,
                            instance_id = %task.instance_id,
                            node_id = %task.node_id,
                            task_type = %task_type,
                            "Executing task"
                        );
                        
                        let start_time = std::time::Instant::now();
                        let result = executor.execute(task.context).await;
                        let duration = start_time.elapsed();
                        
                        match &result {
                            Ok(task_result) => {
                                info!(
                                    worker_id = %worker_id,
                                    instance_id = %task.instance_id,
                                    node_id = %task.node_id,
                                    duration_ms = %duration.as_millis(),
                                    status = ?task_result.status,
                                    "Task completed"
                                );
                            },
                            Err(e) => {
                                error!(
                                    worker_id = %worker_id,
                                    instance_id = %task.instance_id,
                                    node_id = %task.node_id,
                                    duration_ms = %duration.as_millis(),
                                    error = %e,
                                    "Task failed"
                                );
                            }
                        }
                        
                        // 返回结果
                        let _ = task.result_sender.send(result);
                    }
                    
                    info!(worker_id = %worker_id, "Task worker stopped");
                });
            }
        }
        
        /// 启动工作流实例
        #[instrument(skip(self), fields(workflow_id = %workflow_id, instance_id))]
        pub async fn start_workflow(
            &self,
            workflow_id: &str,
            initial_variables: HashMap<String, serde_json::Value>,
        ) -> Result<WorkflowInstance, ExecutionError> {
            // 生成实例ID
            let instance_id = Uuid::new_v4().to_string();
            Span::current().record("instance_id", &instance_id);
            
            info!(workflow_id = %workflow_id, "Starting workflow instance");
            
            // 获取工作流定义
            let workflow_def: WorkflowDefinition = self.storage.get(&format!("workflow:{}", workflow_id)).await
                .map_err(|e| ExecutionError::StorageError(e.to_string()))?
                .ok_or_else(|| ExecutionError::WorkflowNotFound(workflow_id.to_string()))?;
                
            // 创建工作流实例
            let instance = WorkflowInstance {
                id: instance_id.clone(),
                definition_id: workflow_id.to_string(),
                version: workflow_def.version.clone(),
                state: "RUNNING".to_string(),
                variables: initial_variables.clone(),
                node_states: HashMap::new(),
                created_at: chrono::Utc::now(),
                updated_at: chrono::Utc::now(),
                parent_instance_id: None,
                trace_context: None,
            };
            
            // 保存实例
            self.storage.put(&format!("instance:{}", instance_id), &instance).await
                .map_err(|e| ExecutionError::StorageError(e.to_string()))?;
                
            // 发布实例创建事件
            let event = crate::event_bus::EventMessage {
                event_id: Uuid::new_v4().to_string(),
                event_type: "workflow.instance.created".to_string(),
                source: "workflow-engine".to_string(),
                time: chrono::Utc::now(),
                data: serde_json::to_value(&instance).unwrap(),
                trace_context: None,
                schema_url: None,
            };
            
            self.event_bus.publish("workflow-events", event).await
                .map_err(|e| ExecutionError::Other(format!("Failed to publish event: {}", e)))?;
                
            // 初始化实例执行状态
            let state = InstanceExecutionState {
                instance_id: instance_id.clone(),
                pending_nodes: HashSet::new(),
                running_nodes: HashSet::new(),
                completed_nodes: HashSet::new(),
                variables: initial_variables,
                created_at: chrono::Utc::now(),
                updated_at: chrono::Utc::now(),
                cancellation_token: None,
            };
            
            self.active_instances.write().await.insert(instance_id.clone(), state);
            
            // 查找起始节点
            let start_nodes = workflow_def.nodes.iter()
                .filter(|n| match &n.node_type {
                    NodeType::Event { event_type } => event_type == "start",
                    _ => false,
                })
                .collect::<Vec<_>>();
                
            if start_nodes.is_empty() {
                return Err(ExecutionError::ValidationError("No start node found".to_string()));
            }
            
            // 开始执行工作流
            for start_node in start_nodes {
                self.schedule_node(&instance, start_node).await?;
            }
            
            Ok(instance)
        }
        
        /// 调度节点执行
        #[instrument(skip(self, instance, node), fields(instance_id = %instance.id, node_id = %node.id))]
        async fn schedule_node(
            &self,
            instance: &WorkflowInstance,
            node: &NodeDefinition,
        ) -> Result<(), ExecutionError> {
            let instance_id = instance.id.clone();
            let node_id = node.id.clone();
            
            // 更新实例状态
            {
                let mut instances = self.active_instances.write().await;
                if let Some(state) = instances.get_mut(&instance_id) {
                    state.pending_nodes.insert(node_id.clone());
                    state.updated_at = chrono::Utc::now();
                } else {
                    // 实例不在活动列表中，可能已完成或被取消
                    return Err(ExecutionError::ValidationError(format!(
                        "Instance {} not active", instance_id
                    )));
                }
            }
            
            // 创建任务上下文
            let context = TaskContext {
                instance_id: instance_id.clone(),
                node_id: node_id.clone(),
                variables: instance.variables.clone(),
                node_config: node.config.clone(),
                retry_count: 0,
                correlation_id: Uuid::new_v4().to_string(),
                trace_context: instance.trace_context.clone(),
            };
            
            // 发布节点调度事件
            let event = crate::event_bus::EventMessage {
                event_id: Uuid::new_v4().to_string(),
                event_type: "workflow.node.scheduled".to_string(),
                source: "workflow-engine".to_string(),
                time: chrono::Utc::now(),
                data: serde_json::json!({
                    "instance_id": instance_id,
                    "node_id": node_id,
                    "node_type": format!("{:?}", node.node_type),
                }),
                trace_context: instance.trace_context.clone(),
                schema_url: None,
            };
            
            self.event_bus.publish("workflow-events", event).await
                .map_err(|e| ExecutionError::Other(format!("Failed to publish event: {}", e)))?;
                
            // 基于节点类型执行不同的逻辑
            match &node.node_type {
                NodeType::Task { .. } => {
                    self.execute_task_node(instance, node, context).await?;
                },
                NodeType::Gateway { gateway_type } => {
                    self.execute_gateway_node(instance, node, *gateway_type, context).await?;
                },
                NodeType::Event { event_type } => {
                    if event_type == "start" {
                        // 开始事件，直接完成并继续执行
                        self.complete_node(instance, node, TaskResult {
                            output: HashMap::new(),
                            status: TaskStatus::Completed,
                            message: None,
                        }).await?;
                    } else if event_type == "end" {
                        // 结束事件，完成节点并检查是否所有节点都已完成
                        self.complete_node(instance, node, TaskResult {
                            output: HashMap::new(),
                            status: TaskStatus::Completed,
                            message: None,
                        }).await?;
                        
                        self.check_workflow_completion(&instance_id).await?;
                    } else {
                        // 其他类型的事件，需要特定执行器处理
                        self.execute_task_node(instance, node, context).await?;
                    }
                },
                NodeType::SubWorkflow { workflow_ref } => {
                    self.execute_subworkflow_node(instance, node, workflow_ref, context).await?;
                },
                NodeType::Place { initial_tokens } => {
                    // Petri网库所节点，根据token数量决定是否激活
                    if *initial_tokens > 0 {
                        self.complete_node(instance, node, TaskResult {
                            output: HashMap::new(),
                            status: TaskStatus::Completed,
                            message: None,
                        }).await?;
                    } else {
                        // 等待token
                        debug!(
                            instance_id = %instance_id,
                            node_id = %node_id,
                            "Place waiting for tokens"
                        );
                    }
                },
                NodeType::Transition { condition } => {
                    // Petri网变迁节点
                    let can_fire = if let Some(cond) = condition {
                        self.evaluate_condition(cond, &instance.variables)?
                    } else {
                        true
                    };
                    
                    if can_fire {
                        self.complete_node(instance, node, TaskResult {
                            output: HashMap::new(),
                            status: TaskStatus::Completed,
                            message: None,
                        }).await?;
                    } else {
                        debug!(
                            instance_id = %instance_id,
                            node_id = %node_id,
                            "Transition condition not met"
                        );
                        
                        // 更新节点状态为挂起
                        self.suspend_node(instance, node, "Condition not met").await?;
                    }
                },
            }
            
            Ok(())
        }
        
        /// 执行任务节点
        #[instrument(skip(self, instance, node, context), fields(instance_id = %instance.id, node_id = %node.id))]
        async fn execute_task_node(
            &self,
            instance: &WorkflowInstance,
            node: &NodeDefinition,
            context: TaskContext,
        ) -> Result<(), ExecutionError> {
            let instance_id = instance.id.clone();
            let node_id = node.id.clone();
            
            // 更新节点状态为运行中
            {
                let mut instances = self.active_instances.write().await;
                if let Some(state) = instances.get_mut(&instance_id) {
                    state.pending_nodes.remove(&node_id);
                    state.running_nodes.insert(node_id.clone());
                    state.updated_at = chrono::Utc::now();
                }
            }
            
            // 创建结果接收通道
            let (result_tx, result_rx) = oneshot::channel();
            
            // 将任务加入队列
            let queued_task = QueuedTask {
                instance_id: instance_id.clone(),
                node_id: node_id.clone(),
                context,
                result_sender: result_tx,
            };
            
            // 发送任务到队列
            if let Err(e) = self.task_queue.send(queued_task).await {
                error!(
                    instance_id = %instance_id,
                    node_id = %node_id,
                    error = %e,
                    "Failed to queue task"
                );
                
                return Err(ExecutionError::Other(format!("Failed to queue task: {}", e)));
            }
            
            // 处理任务超时
            let timeout_duration = node.timeout.unwrap_or(Duration::from_secs(3600)); // 默认1小时
            
            // 在单独的任务中等待结果
            let self_clone = self.clone();
            let instance_clone = instance.clone();
            let node_clone = node.clone();
            
            tokio::spawn(async move {
                match tokio::time::timeout(timeout_duration, result_rx).await {
                    Ok(result) => {
                        match result {
                            Ok(task_result) => {
                                match task_result {
                                    Ok(result) => {
                                        // 任务成功完成
                                        if let Err(e) = self_clone.complete_node(&instance_clone, &node_clone, result).await {
                                            error!(
                                                instance_id = %instance_id,
                                                node_id = %node_id,
                                                error = %e,
                                                "Failed to complete node"
                                            );
                                        }
                                    },
                                    Err(e) => {
                                        error!(
                                            instance_id = %instance_id,
                                            node_id = %node_id,
                                            error = %e,
                                            "Task execution failed"
                                        );
                                        
                                        // 处理任务失败
                                        if let Err(e) = self_clone.fail_node(&instance_clone, &node_clone, e.to_string()).await {
                                            error!(
                                                instance_id = %instance_id,
                                                node_id = %node_id,
                                                error = %e,
                                                "Failed to mark node as failed"
                                            );
                                        }
                                    }
                                }
                            },
                            Err(_) => {
                                // 结果通道关闭
                                error!(
                                    instance_id = %instance_id,
                                    node_id = %node_id,
                                    "Task result channel closed"
                                );
                                
                                if let Err(e) = self_clone.fail_node(&instance_clone, &node_clone, "Task result channel closed".to_string()).await {
                                    error!(
                                        instance_id = %instance_id,
                                        node_id = %node_id,
                                        error = %e,
                                        "Failed to mark node as failed"
                                    );
                                }
                            }
                        }
                    },
                    Err(_) => {
                        // 任务超时
                        error!(
                            instance_id = %instance_id,
                            node_id = %node_id,
                            timeout = ?timeout_duration,
                            "Task execution timed out"
                        );
                        
                        if let Err(e) = self_clone.fail_node(&instance_clone, &node_clone, "Task execution timed out".to_string()).await {
                            error!(
                                instance_id = %instance_id,
                                node_id = %node_id,
                                error = %e,
                                "Failed to mark node as failed"
                            );
                        }
                    }
                }
            });
            
            Ok(())
        }
        
        /// 执行网关节点
        #[instrument(skip(self, instance, node, context), fields(instance_id = %instance.id, node_id = %node.id))]
        async fn execute_gateway_node(
            &self,
            instance: &WorkflowInstance,
            node: &NodeDefinition,
            gateway_type: GatewayType,
            context: TaskContext,
        ) -> Result<(), ExecutionError> {
            let instance_id = instance.id.clone();
            let node_id = node.id.clone();
            
            // 获取工作流定义
            let workflow_def: WorkflowDefinition = self.storage.get(&format!("workflow:{}", instance.definition_id)).await
                .map_err(|e| ExecutionError::StorageError(e.to_string()))?
                .ok_or_else(|| ExecutionError::WorkflowNotFound(instance.definition_id.clone()))?;
                
            // 查找出边
            let outgoing_edges = workflow_def.edges.iter()
                .filter(|e| e.source == node_id)
                .collect::<Vec<_>>();
                
            match gateway_type {
                GatewayType::Exclusive => {
                    // 排他网关：评估每个条件，执行第一个满足的
                    let mut executed = false;
                    
                    for edge in outgoing_edges {
                        if let Some(condition) = &edge.condition {
                            // 评估条件
                            if self.evaluate_condition(condition, &context.variables)? {
                                // 找到目标节点
                                if let Some(target_node) = workflow_def.nodes.iter().find(|n| n.id == edge.target) {
                                    // 调度目标节点
                                    self.schedule_node(instance, target_node).await?;
                                    executed = true;
                                    break;
                                }
                            }
                        } else {
                            // 没有条件的边是默认路径
                            if let Some(target_node) = workflow_def.nodes.iter().find(|n| n.id == edge.target) {
                                self.schedule_node(instance, target_node).await?;
                                executed = true;
                                break;
                            }
                        }
                    }
                    
                    if !executed && !outgoing_edges.is_empty() {
                        // 如果没有满足条件的路径，使用最后一个作为默认
                        if let Some(last_edge) = outgoing_edges.last() {
                            if let Some(target_node) = workflow_def.nodes.iter().find(|n| n.id == last_edge.target) {
                                self.schedule_node(instance, target_node).await?;
                                executed = true;
                            }
                        }
                    }
                    
                    if !executed {
                        warn!(
                            instance_id = %instance_id,
                            node_id = %node_id,
                            "Exclusive gateway has no outgoing paths"
                        );
                    }
                },
                GatewayType::Parallel => {
                    // 并行网关：执行所有出边
                    for edge in outgoing_edges {
                        if let Some(target_node) = workflow_def.nodes.iter().find(|n| n.id == edge.target) {
                            self.schedule_node(instance, target_node).await?;
                        }
                    }
                },
                GatewayType::Inclusive => {
                    // 包容网关：执行所有满足条件的出边
                    let mut executed = false;
                    
                    for edge in outgoing_edges {
                        let should_execute = if let Some(condition) = &edge.condition {
                            self.evaluate_condition(condition, &context.variables)?
                        } else {
                            true // 没有条件的边总是执行
                        };
                        
                        if should_execute {
                            if let Some(target_node) = workflow_def.nodes.iter().find(|n| n.id == edge.target) {
                                self.schedule_node(instance, target_node).await?;
                                executed = true;
                            }
                        }
                    }
                    
                    if !executed {
                        warn!(
                            instance_id = %instance_id,
                            node_id = %node_id,
                            "Inclusive gateway has no active outgoing paths"
                        );
                    }
                },
            }
            
            // 完成网关节点
            self.complete_node(instance, node, TaskResult {
                output: HashMap::new(),
                status: TaskStatus::Completed,
                message: None,
            }).await?;
            
            Ok(())
        }
        
        /// 执行子工作流节点
        #[instrument(skip(self, instance, node, context), fields(instance_id = %instance.id, node_id = %node.id))]
        async fn execute_subworkflow_node(
            &self,
            instance: &WorkflowInstance,
            node: &NodeDefinition,
            workflow_ref: &str,
            context: TaskContext,
        ) -> Result<(), ExecutionError> {
            let instance_id = instance.id.clone();
            let node_id = node.id.clone();
            
            info!(
                parent_instance_id = %instance_id,
                node_id = %node_id,
                sub_workflow_id = %workflow_ref,
                "Starting sub-workflow"
            );
            
            // 创建子工作流的初始变量
            let mut sub_variables = context.variables.clone();
            
            // 添加父工作流信息
            sub_variables.insert("parent_instance_id".to_string(), serde_json::Value::String(instance_id.clone()));
            sub_variables.insert("parent_node_id".to_string(), serde_json::Value::String(node_id.clone()));
            
            // 启动子工作流
            let sub_instance = self.start_workflow(workflow_ref, sub_variables).await?;
            
            // 更新节点状态
            {
                let mut instances = self.active_instances.write().await;
                if let Some(state) = instances.get_mut(&instance_id) {
                    state.pending_nodes.remove(&node_id);
                    state.running_nodes.insert(node_id.clone());
                    state.updated_at = chrono::Utc::now();
                }
            }
            
            // 将子工作流ID保存到父节点状态
            let node_state = crate::model::NodeState {
                node_id: node_id.clone(),
                state: "RUNNING".to_string(),
                data: serde_json::json!({ "sub_workflow_instance_id": sub_instance.id }),
                retries: 0,
                last_updated: chrono::Utc::now(),
            };
            
            // 更新实例节点状态
            let mut instance_clone = instance.clone();
            instance_clone.node_states.insert(node_id.clone(), node_state);
            instance_clone.updated_at = chrono::Utc::now();
            
            self.storage.put(&format!("instance:{}", instance_id), &instance_clone).await
                .map_err(|e| ExecutionError::StorageError(e.to_string()))?;
                
            Ok(())
        }
        
        /// 完成节点执行
        #[instrument(skip(self, instance, node, result), fields(instance_id = %instance.id, node_id = %node.id))]
        async fn complete_node(
            &self,
            instance: &WorkflowInstance,
            node: &NodeDefinition,
            result: TaskResult,
        ) -> Result<(), ExecutionError> {
            let instance_id = instance.id.clone();
            let node_id = node.id.clone();
            
            info!(
                instance_id = %instance_id,
                node_id = %node_id,
                "Node completed"
            );
            
            // 更新实例状态
            let mut instance_clone = instance.clone();
            
            // 更新节点状态
            let node_state = crate::model::NodeState {
                node_id: node_id.clone(),
                state: "COMPLETED".to_string(),
                data: serde_json::to_value(&result).unwrap_or(serde_json::Value::Null),
                retries: 0,
                last_updated: chrono::Utc::now(),
            };
            
            instance_clone.node_states.insert(node_id.clone(), node_state);
            
            // 更新变量
            for (key, value) in result.output {
                instance_clone.variables.insert(key, value);
            }
            
            instance_clone.updated_at = chrono::Utc::now();
            
            // 保存实例
            self.storage.put(&format!("instance:{}", instance_id), &instance_clone).await
                .map_err(|e| ExecutionError::StorageError(e.to_string()))?;
                
            // 更新内部状态
            {
                let mut instances = self.active_instances.write().await;
                if let Some(state) = instances.get_mut(&instance_id) {
                    state.running_nodes.remove(&node_id);
                    state.completed_nodes.insert(node_id.clone());
                    
                    // 更新变量
                    for (key, value) in &result.output {
                        state.variables.insert(key.clone(), value.clone());
                    }
                    
                    state.updated_at = chrono::Utc::now();
                }
            }
            
            // 发布节点完成事件
            let event = crate::event_bus::EventMessage {
                event_id: Uuid::new_v4().to_string(),
                event_type: "workflow.node.completed".to_string(),
                source: "workflow-engine".to_string(),
                time: chrono::Utc::now(),
                data: serde_json::json!({
                    "instance_id": instance_id,
                    "node_id": node_id,
                    "node_type": format!("{:?}", node.node_type),
                }),
                trace_context: instance.trace_context.clone(),
                schema_url: None,
            };
            
            self.event_bus.publish("workflow-events", event).await
                .map_err(|e| ExecutionError::Other(format!("Failed to publish event: {}", e)))?;
                
            // 获取工作流定义，查找后续节点
            let workflow_def: WorkflowDefinition = self.storage.get(&format!("workflow:{}", instance.definition_id)).await
                
# Rust 分布式工作流框架设计（续）

## 实现示例：工作流执行引擎（续）

```rust
// 工作流执行引擎（续）
pub mod execution {
    // ... 前面内容省略

    impl WorkflowExecutionEngine {
        // ... 前面内容省略

        /// 完成节点执行（续）
        #[instrument(skip(self, instance, node, result), fields(instance_id = %instance.id, node_id = %node.id))]
        async fn complete_node(
            &self,
            instance: &WorkflowInstance,
            node: &NodeDefinition,
            result: TaskResult,
        ) -> Result<(), ExecutionError> {
            // ... 前面内容省略
            
            // 获取工作流定义，查找后续节点
            let workflow_def: WorkflowDefinition = self.storage.get(&format!("workflow:{}", instance.definition_id)).await
                .map_err(|e| ExecutionError::StorageError(e.to_string()))?
                .ok_or_else(|| ExecutionError::WorkflowNotFound(instance.definition_id.clone()))?;
                
            // 查找出边
            let outgoing_edges = workflow_def.edges.iter()
                .filter(|e| e.source == node_id)
                .collect::<Vec<_>>();
                
            // 如果是普通节点（非网关），执行所有出边
            if !matches!(&node.node_type, NodeType::Gateway { .. }) {
                for edge in outgoing_edges {
                    let should_follow = if let Some(condition) = &edge.condition {
                        self.evaluate_condition(condition, &instance_clone.variables)?
                    } else {
                        true
                    };
                    
                    if should_follow {
                        if let Some(target_node) = workflow_def.nodes.iter().find(|n| n.id == edge.target) {
                            self.schedule_node(&instance_clone, target_node).await?;
                        }
                    }
                }
            }
            
            // 检查工作流是否完成
            self.check_workflow_completion(&instance_id).await?;
            
            Ok(())
        }
        
        /// 节点执行失败
        #[instrument(skip(self, instance, node), fields(instance_id = %instance.id, node_id = %node.id))]
        async fn fail_node(
            &self,
            instance: &WorkflowInstance,
            node: &NodeDefinition,
            error_message: String,
        ) -> Result<(), ExecutionError> {
            let instance_id = instance.id.clone();
            let node_id = node.id.clone();
            
            error!(
                instance_id = %instance_id,
                node_id = %node_id,
                error = %error_message,
                "Node execution failed"
            );
            
            // 检查是否有重试策略
            if let Some(retry_policy) = &node.retry_policy {
                // 获取当前重试次数
                let current_retries = instance.node_states.get(&node_id)
                    .map(|state| state.retries)
                    .unwrap_or(0);
                    
                if current_retries < retry_policy.max_attempts {
                    // 还有重试机会，更新重试次数并安排重试
                    let next_retry = current_retries + 1;
                    
                    info!(
                        instance_id = %instance_id,
                        node_id = %node_id,
                        attempt = %next_retry,
                        max_attempts = %retry_policy.max_attempts,
                        "Scheduling node retry"
                    );
                    
                    // 计算重试延迟
                    let delay = Duration::from_secs(
                        (retry_policy.interval.as_secs() as f64 * retry_policy.backoff_factor.powi(next_retry as i32)) as u64
                    );
                    
                    // 更新节点状态
                    let mut instance_clone = instance.clone();
                    
                    let node_state = crate::model::NodeState {
                        node_id: node_id.clone(),
                        state: "RETRYING".to_string(),
                        data: serde_json::json!({
                            "error": error_message,
                            "retry_count": next_retry,
                            "next_retry_at": (chrono::Utc::now() + chrono::Duration::from_std(delay).unwrap()).to_rfc3339(),
                        }),
                        retries: next_retry,
                        last_updated: chrono::Utc::now(),
                    };
                    
                    instance_clone.node_states.insert(node_id.clone(), node_state);
                    instance_clone.updated_at = chrono::Utc::now();
                    
                    // 保存实例
                    self.storage.put(&format!("instance:{}", instance_id), &instance_clone).await
                        .map_err(|e| ExecutionError::StorageError(e.to_string()))?;
                        
                    // 更新内部状态
                    {
                        let mut instances = self.active_instances.write().await;
                        if let Some(state) = instances.get_mut(&instance_id) {
                            state.running_nodes.remove(&node_id);
                            state.pending_nodes.insert(node_id.clone());
                            state.updated_at = chrono::Utc::now();
                        }
                    }
                    
                    // 发布节点重试事件
                    let event = crate::event_bus::EventMessage {
                        event_id: Uuid::new_v4().to_string(),
                        event_type: "workflow.node.retrying".to_string(),
                        source: "workflow-engine".to_string(),
                        time: chrono::Utc::now(),
                        data: serde_json::json!({
                            "instance_id": instance_id,
                            "node_id": node_id,
                            "error": error_message,
                            "retry_count": next_retry,
                            "max_attempts": retry_policy.max_attempts,
                            "delay_seconds": delay.as_secs(),
                        }),
                        trace_context: instance.trace_context.clone(),
                        schema_url: None,
                    };
                    
                    self.event_bus.publish("workflow-events", event).await
                        .map_err(|e| ExecutionError::Other(format!("Failed to publish event: {}", e)))?;
                        
                    // 安排延迟重试
                    let self_clone = self.clone();
                    let node_clone = node.clone();
                    let instance_clone = instance_clone.clone();
                    
                    tokio::spawn(async move {
                        tokio::time::sleep(delay).await;
                        
                        info!(
                            instance_id = %instance_id,
                            node_id = %node_id,
                            attempt = %next_retry,
                            "Executing node retry"
                        );
                        
                        if let Err(e) = self_clone.schedule_node(&instance_clone, &node_clone).await {
                            error!(
                                instance_id = %instance_id,
                                node_id = %node_id,
                                error = %e,
                                "Failed to schedule node retry"
                            );
                        }
                    });
                    
                    return Ok(());
                }
            }
            
            // 没有重试策略或者已经超过最大重试次数，标记节点为失败
            
            // 更新节点状态
            let mut instance_clone = instance.clone();
            
            let node_state = crate::model::NodeState {
                node_id: node_id.clone(),
                state: "FAILED".to_string(),
                data: serde_json::json!({ "error": error_message }),
                retries: instance.node_states.get(&node_id).map(|s| s.retries).unwrap_or(0),
                last_updated: chrono::Utc::now(),
            };
            
            instance_clone.node_states.insert(node_id.clone(), node_state);
            
            // 检查是否设置工作流整体失败
            // 默认情况下，任何节点失败都会导致工作流失败，除非节点配置了特殊处理
            let fail_workflow = node.config.get("fail_workflow_on_error")
                .and_then(|v| v.as_bool())
                .unwrap_or(true);
                
            if fail_workflow {
                instance_clone.state = "FAILED".to_string();
            }
            
            instance_clone.updated_at = chrono::Utc::now();
            
            // 保存实例
            self.storage.put(&format!("instance:{}", instance_id), &instance_clone).await
                .map_err(|e| ExecutionError::StorageError(e.to_string()))?;
                
            // 更新内部状态
            {
                let mut instances = self.active_instances.write().await;
                if let Some(state) = instances.get_mut(&instance_id) {
                    state.running_nodes.remove(&node_id);
                    state.updated_at = chrono::Utc::now();
                    
                    if fail_workflow {
                        // 清理活动节点
                        state.pending_nodes.clear();
                        state.running_nodes.clear();
                        
                        // 取消所有进行中的任务
                        if let Some(cancel_tx) = state.cancellation_token.take() {
                            let _ = cancel_tx.send(());
                        }
                    }
                }
            }
            
            // 发布节点失败事件
            let event = crate::event_bus::EventMessage {
                event_id: Uuid::new_v4().to_string(),
                event_type: "workflow.node.failed".to_string(),
                source: "workflow-engine".to_string(),
                time: chrono::Utc::now(),
                data: serde_json::json!({
                    "instance_id": instance_id,
                    "node_id": node_id,
                    "error": error_message,
                    "fail_workflow": fail_workflow,
                }),
                trace_context: instance.trace_context.clone(),
                schema_url: None,
            };
            
            self.event_bus.publish("workflow-events", event).await
                .map_err(|e| ExecutionError::Other(format!("Failed to publish event: {}", e)))?;
                
            // 如果工作流失败，发布工作流失败事件
            if fail_workflow {
                let workflow_event = crate::event_bus::EventMessage {
                    event_id: Uuid::new_v4().to_string(),
                    event_type: "workflow.instance.failed".to_string(),
                    source: "workflow-engine".to_string(),
                    time: chrono::Utc::now(),
                    data: serde_json::json!({
                        "instance_id": instance_id,
                        "failed_node_id": node_id,
                        "error": error_message,
                    }),
                    trace_context: instance.trace_context.clone(),
                    schema_url: None,
                };
                
                self.event_bus.publish("workflow-events", workflow_event).await
                    .map_err(|e| ExecutionError::Other(format!("Failed to publish event: {}", e)))?;
                    
                // 如果是子工作流，通知父工作流
                if let Some(parent_id) = &instance.parent_instance_id {
                    self.handle_subworkflow_failure(parent_id, &instance_id, &node_id, &error_message).await?;
                }
            } else {
                // 如果节点失败不导致工作流失败，查找错误处理路径
                let workflow_def: WorkflowDefinition = self.storage.get(&format!("workflow:{}", instance.definition_id)).await
                    .map_err(|e| ExecutionError::StorageError(e.to_string()))?
                    .ok_or_else(|| ExecutionError::WorkflowNotFound(instance.definition_id.clone()))?;
                    
                // 查找标记为错误处理的出边
                let error_edges = workflow_def.edges.iter()
                    .filter(|e| e.source == node_id && e.condition.as_ref().map_or(false, |c| c.contains("error")))
                    .collect::<Vec<_>>();
                    
                for edge in error_edges {
                    if let Some(target_node) = workflow_def.nodes.iter().find(|n| n.id == edge.target) {
                        self.schedule_node(&instance_clone, target_node).await?;
                    }
                }
            }
            
            Ok(())
        }
        
        /// 挂起节点
        #[instrument(skip(self, instance, node), fields(instance_id = %instance.id, node_id = %node.id))]
        async fn suspend_node(
            &self,
            instance: &WorkflowInstance,
            node: &NodeDefinition,
            reason: &str,
        ) -> Result<(), ExecutionError> {
            let instance_id = instance.id.clone();
            let node_id = node.id.clone();
            
            info!(
                instance_id = %instance_id,
                node_id = %node_id,
                reason = %reason,
                "Suspending node"
            );
            
            // 更新节点状态
            let mut instance_clone = instance.clone();
            
            let node_state = crate::model::NodeState {
                node_id: node_id.clone(),
                state: "SUSPENDED".to_string(),
                data: serde_json::json!({ "reason": reason }),
                retries: instance.node_states.get(&node_id).map(|s| s.retries).unwrap_or(0),
                last_updated: chrono::Utc::now(),
            };
            
            instance_clone.node_states.insert(node_id.clone(), node_state);
            instance_clone.updated_at = chrono::Utc::now();
            
            // 保存实例
            self.storage.put(&format!("instance:{}", instance_id), &instance_clone).await
                .map_err(|e| ExecutionError::StorageError(e.to_string()))?;
                
            // 更新内部状态
            {
                let mut instances = self.active_instances.write().await;
                if let Some(state) = instances.get_mut(&instance_id) {
                    state.running_nodes.remove(&node_id);
                    state.pending_nodes.remove(&node_id);
                    state.updated_at = chrono::Utc::now();
                }
            }
            
            // 发布节点挂起事件
            let event = crate::event_bus::EventMessage {
                event_id: Uuid::new_v4().to_string(),
                event_type: "workflow.node.suspended".to_string(),
                source: "workflow-engine".to_string(),
                time: chrono::Utc::now(),
                data: serde_json::json!({
                    "instance_id": instance_id,
                    "node_id": node_id,
                    "reason": reason,
                }),
                trace_context: instance.trace_context.clone(),
                schema_url: None,
            };
            
            self.event_bus.publish("workflow-events", event).await
                .map_err(|e| ExecutionError::Other(format!("Failed to publish event: {}", e)))?;
                
            Ok(())
        }
        
        /// 处理子工作流失败
        #[instrument(skip(self, parent_instance_id, sub_instance_id), fields(parent_id = %parent_instance_id))]
        async fn handle_subworkflow_failure(
            &self,
            parent_instance_id: &str,
            sub_instance_id: &str,
            failed_node_id: &str,
            error_message: &str,
        ) -> Result<(), ExecutionError> {
            info!(
                parent_instance_id = %parent_instance_id,
                sub_instance_id = %sub_instance_id,
                "Handling subworkflow failure"
            );
            
            // 获取父工作流实例
            let parent_instance: WorkflowInstance = self.storage.get(&format!("instance:{}", parent_instance_id)).await
                .map_err(|e| ExecutionError::StorageError(e.to_string()))?
                .ok_or_else(|| ExecutionError::ValidationError(format!(
                    "Parent instance {} not found", parent_instance_id
                )))?;
                
            // 查找引用子工作流的节点
            let subworkflow_node = parent_instance.node_states.iter()
                .find(|(_, state)| {
                    state.data.get("sub_workflow_instance_id")
                        .and_then(|v| v.as_str())
                        .map_or(false, |id| id == sub_instance_id)
                })
                .map(|(node_id, _)| node_id);
                
            if let Some(node_id) = subworkflow_node {
                // 获取节点定义
                let workflow_def: WorkflowDefinition = self.storage.get(&format!("workflow:{}", parent_instance.definition_id)).await
                    .map_err(|e| ExecutionError::StorageError(e.to_string()))?
                    .ok_or_else(|| ExecutionError::WorkflowNotFound(parent_instance.definition_id.clone()))?;
                    
                let node = workflow_def.nodes.iter()
                    .find(|n| n.id == *node_id)
                    .ok_or_else(|| ExecutionError::NodeNotFound(node_id.clone()))?;
                    
                // 标记子工作流节点为失败
                let error = format!("Sub-workflow failed: {}. Node: {}. Error: {}", 
                    sub_instance_id, failed_node_id, error_message);
                    
                self.fail_node(&parent_instance, node, error).await?;
            } else {
                warn!(
                    parent_instance_id = %parent_instance_id,
                    sub_instance_id = %sub_instance_id,
                    "Could not find node referencing sub-workflow"
                );
            }
            
            Ok(())
        }
        
        /// 检查工作流是否完成
        #[instrument(skip(self), fields(instance_id = %instance_id))]
        async fn check_workflow_completion(&self, instance_id: &str) -> Result<bool, ExecutionError> {
            // 检查是否还有待执行或执行中的节点
            let is_completed = {
                let instances = self.active_instances.read().await;
                if let Some(state) = instances.get(instance_id) {
                    state.pending_nodes.is_empty() && state.running_nodes.is_empty()
                } else {
                    false
                }
            };
            
            if is_completed {
                info!(instance_id = %instance_id, "Workflow instance completed");
                
                // 获取实例
                let mut instance: WorkflowInstance = self.storage.get(&format!("instance:{}", instance_id)).await
                    .map_err(|e| ExecutionError::StorageError(e.to_string()))?
                    .ok_or_else(|| ExecutionError::ValidationError(format!(
                        "Instance {} not found", instance_id
                    )))?;
                    
                // 如果实例状态不是失败，设为完成
                if instance.state != "FAILED" {
                    instance.state = "COMPLETED".to_string();
                    instance.updated_at = chrono::Utc::now();
                    
                    // 保存实例
                    self.storage.put(&format!("instance:{}", instance_id), &instance).await
                        .map_err(|e| ExecutionError::StorageError(e.to_string()))?;
                        
                    // 发布工作流完成事件
                    let event = crate::event_bus::EventMessage {
                        event_id: Uuid::new_v4().to_string(),
                        event_type: "workflow.instance.completed".to_string(),
                        source: "workflow-engine".to_string(),
                        time: chrono::Utc::now(),
                        data: serde_json::json!({
                            "instance_id": instance_id,
                            "definition_id": instance.definition_id,
                        }),
                        trace_context: instance.trace_context.clone(),
                        schema_url: None,
                    };
                    
                    self.event_bus.publish("workflow-events", event).await
                        .map_err(|e| ExecutionError::Other(format!("Failed to publish event: {}", e)))?;
                        
                    // 如果是子工作流，通知父工作流
                    if let Some(parent_id) = &instance.parent_instance_id {
                        self.handle_subworkflow_completion(parent_id, instance_id).await?;
                    }
                }
                
                // 从活动实例中移除
                self.active_instances.write().await.remove(instance_id);
                
                Ok(true)
            } else {
                Ok(false)
            }
        }
        
        /// 处理子工作流完成
        #[instrument(skip(self, parent_instance_id, sub_instance_id), fields(parent_id = %parent_instance_id))]
        async fn handle_subworkflow_completion(
            &self,
            parent_instance_id: &str,
            sub_instance_id: &str,
        ) -> Result<(), ExecutionError> {
            info!(
                parent_instance_id = %parent_instance_id,
                sub_instance_id = %sub_instance_id,
                "Handling subworkflow completion"
            );
            
            // 获取父工作流实例
            let parent_instance: WorkflowInstance = self.storage.get(&format!("instance:{}", parent_instance_id)).await
                .map_err(|e| ExecutionError::StorageError(e.to_string()))?
                .ok_or_else(|| ExecutionError::ValidationError(format!(
                    "Parent instance {} not found", parent_instance_id
                )))?;
                
            // 获取子工作流实例
            let sub_instance: WorkflowInstance = self.storage.get(&format!("instance:{}", sub_instance_id)).await
                .map_err(|e| ExecutionError::StorageError(e.to_string()))?
                .ok_or_else(|| ExecutionError::ValidationError(format!(
                    "Sub instance {} not found", sub_instance_id
                )))?;
                
            // 查找引用子工作流的节点
            let subworkflow_node = parent_instance.node_states.iter()
                .find(|(_, state)| {
                    state.data.get("sub_workflow_instance_id")
                        .and_then(|v| v.as_str())
                        .map_or(false, |id| id == sub_instance_id)
                })
                .map(|(node_id, _)| node_id);
                
            if let Some(node_id) = subworkflow_node {
                // 获取节点定义
                let workflow_def: WorkflowDefinition = self.storage.get(&format!("workflow:{}", parent_instance.definition_id)).await
                    .map_err(|e| ExecutionError::StorageError(e.to_string()))?
                    .ok_or_else(|| ExecutionError::WorkflowNotFound(parent_instance.definition_id.clone()))?;
                    
                let node = workflow_def.nodes.iter()
                    .find(|n| n.id == *node_id)
                    .ok_or_else(|| ExecutionError::NodeNotFound(node_id.clone()))?;
                    
                // 构建子工作流输出
                let sub_output = sub_instance.variables.into_iter()
                    .filter(|(key, _)| key.starts_with("output_"))
                    .map(|(key, value)| {
                        let output_key = key.trim_start_matches("output_").to_string();
                        (output_key, value)
                    })
                    .collect();
                    
                // 完成子工作流节点
                self.complete_node(&parent_instance, node, TaskResult {
                    output: sub_output,
                    status: TaskStatus::Completed,
                    message: None,
                }).await?;
            } else {
                warn!(
                    parent_instance_id = %parent_instance_id,
                    sub_instance_id = %sub_instance_id,
                    "Could not find node referencing sub-workflow"
                );
            }
            
            Ok(())
        }
        
        /// 评估条件表达式
        fn evaluate_condition(
            &self,
            condition: &str,
            variables: &HashMap<String, serde_json::Value>,
        ) -> Result<bool, ExecutionError> {
            // 简化版本：仅支持基本表达式
            // 在实际实现中，应使用表达式引擎如 rhai, deno_core 等
            
            // 测试一些简单条件
            if condition == "true" {
                return Ok(true);
            } else if condition == "false" {
                return Ok(false);
            }
            
            // 检查变量比较
            // 格式: ${varName} == "value" 或 ${varName} > 10
            let re = regex::Regex::new(r"\$\{([^}]+)\}\s*([=><]=?|!=)\s*(.+)").unwrap();
            
            if let Some(captures) = re.captures(condition) {
                let var_name = captures.get(1).unwrap().as_str();
                let operator = captures.get(2).unwrap().as_str();
                let value_str = captures.get(3).unwrap().as_str();
                
                if let Some(var_value) = variables.get(var_name) {
                    match operator {
                        "==" => {
                            // 处理字符串
                            if value_str.starts_with('"') && value_str.ends_with('"') {
                                let str_value = &value_str[1..value_str.len()-1];
                                if let Some(var_str) = var_value.as_str() {
                                    return Ok(var_str == str_value);
                                }
                            } 
                            // 处理数字
                            else if let Ok(num_value) = value_str.parse::<f64>() {
                                if let Some(var_num) = var_value.as_f64() {
                                    return Ok((var_num - num_value).abs() < 0.000001);
                                }
                            }
                            // 处理布尔值
                            else if value_str == "true" || value_str == "false" {
                                if let Some(var_bool) = var_value.as_bool() {
                                    return Ok(var_bool == (value_str == "true"));
                                }
                            }
                        },
                        "!=" => {
                            // 处理字符串
                            if value_str.starts_with('"') && value_str.ends_with('"') {
                                let str_value = &value_str[1..value_str.len()-1];
                                if let Some(var_str) = var_value.as_str() {
                                    return Ok(var_str != str_value);
                                }
                            } 
                            // 处理数字
                            else if let Ok(num_value) = value_str.parse::<f64>() {
                                if let Some(var_num) = var_value.as_f64() {
                                    return Ok((var_num - num_value).abs() >= 0.000001);
                                }
                            }
                            // 处理布尔值
                            else if value_str == "true" || value_str == "false" {
                                if let Some(var_bool) = var_value.as_bool() {
                                    return Ok(var_bool != (value_str == "true"));
                                }
                            }
                        },
                        ">" => {
                            if let Ok(num_value) = value_str.parse::<f64>() {
                                if let Some(var_num) = var_value.as_f64() {
                                    return Ok(var_num > num_value);
                                }
                            }
                        },
                        ">=" => {
                            if let Ok(num_value) = value_str.parse::<f64>() {
                                if let Some(var_num) = var_value.as_f64() {
                                    return Ok(var_num >= num_value);
                                }
                            }
                        },
                        "<" => {
                            if let Ok(num_value) = value_str.parse::<f64>() {
                                if let Some(var_num) = var_value.as_f64() {
                                    return Ok(var_num < num_value);
                                }
                            }
                        },
                        "<=" => {
                            if let Ok(num_value) = value_str.parse::<f64>() {
                                if let Some(var_num) = var_value.as_f64() {
                                    return Ok(var_num <= num_value);
                                }
                            }
                        },
                        _ => {}
                    }
                }
            }
            
            // 默认返回false
            warn!(condition = %condition, "Could not evaluate condition expression");
            Ok(false)
        }
        
        /// 取消工作流实例
        #[instrument(skip(self), fields(instance_id = %instance_id))]
        pub async fn cancel_workflow(&self, instance_id: &str) -> Result<(), ExecutionError> {
            info!(instance_id = %instance_id, "Cancelling workflow instance");
            
            // 获取实例
            let mut instance: WorkflowInstance = self.storage.get(&format!("instance:{}", instance_id)).await
                .map_err(|e| Execution
# Rust 分布式工作流框架设计（续）

## 实现示例：工作流执行引擎（续）

```rust
// 工作流执行引擎（续）
pub mod execution {
    // ... 前面内容省略

    impl WorkflowExecutionEngine {
        // ... 前面内容省略

        /// 取消工作流实例（续）
        #[instrument(skip(self), fields(instance_id = %instance_id))]
        pub async fn cancel_workflow(&self, instance_id: &str) -> Result<(), ExecutionError> {
            // ... 前面内容省略
            
            // 获取实例
            let mut instance: WorkflowInstance = self.storage.get(&format!("instance:{}", instance_id)).await
                .map_err(|e| ExecutionError::StorageError(e.to_string()))?
                .ok_or_else(|| ExecutionError::ValidationError(format!(
                    "Instance {} not found", instance_id
                )))?;
                
            // 检查是否已完成或失败
            if instance.state == "COMPLETED" || instance.state == "FAILED" || instance.state == "CANCELLED" {
                return Err(ExecutionError::ValidationError(format!(
                    "Cannot cancel instance {} in state {}", instance_id, instance.state
                )));
            }
            
            // 更新实例状态
            instance.state = "CANCELLED".to_string();
            instance.updated_at = chrono::Utc::now();
            
            // 保存实例
            self.storage.put(&format!("instance:{}", instance_id), &instance).await
                .map_err(|e| ExecutionError::StorageError(e.to_string()))?;
                
            // 取消活动节点
            {
                let mut instances = self.active_instances.write().await;
                if let Some(state) = instances.get_mut(instance_id) {
                    // 清理活动节点列表
                    state.pending_nodes.clear();
                    state.running_nodes.clear();
                    
                    // 发送取消信号
                    if let Some(cancel_tx) = state.cancellation_token.take() {
                        let _ = cancel_tx.send(());
                    }
                    
                    // 从活动实例列表中移除
                    instances.remove(instance_id);
                }
            }
            
            // 发布工作流取消事件
            let event = crate::event_bus::EventMessage {
                event_id: Uuid::new_v4().to_string(),
                event_type: "workflow.instance.cancelled".to_string(),
                source: "workflow-engine".to_string(),
                time: chrono::Utc::now(),
                data: serde_json::json!({
                    "instance_id": instance_id,
                    "definition_id": instance.definition_id,
                }),
                trace_context: instance.trace_context.clone(),
                schema_url: None,
            };
            
            self.event_bus.publish("workflow-events", event).await
                .map_err(|e| ExecutionError::Other(format!("Failed to publish event: {}", e)))?;
                
            // 如果是子工作流，通知父工作流
            if let Some(parent_id) = &instance.parent_instance_id {
                self.handle_subworkflow_cancellation(parent_id, instance_id).await?;
            }
            
            Ok(())
        }
        
        /// 处理子工作流取消
        #[instrument(skip(self, parent_instance_id, sub_instance_id), fields(parent_id = %parent_instance_id))]
        async fn handle_subworkflow_cancellation(
            &self,
            parent_instance_id: &str,
            sub_instance_id: &str,
        ) -> Result<(), ExecutionError> {
            info!(
                parent_instance_id = %parent_instance_id,
                sub_instance_id = %sub_instance_id,
                "Handling subworkflow cancellation"
            );
            
            // 获取父工作流实例
            let parent_instance: WorkflowInstance = self.storage.get(&format!("instance:{}", parent_instance_id)).await
                .map_err(|e| ExecutionError::StorageError(e.to_string()))?
                .ok_or_else(|| ExecutionError::ValidationError(format!(
                    "Parent instance {} not found", parent_instance_id
                )))?;
                
            // 查找引用子工作流的节点
            let subworkflow_node = parent_instance.node_states.iter()
                .find(|(_, state)| {
                    state.data.get("sub_workflow_instance_id")
                        .and_then(|v| v.as_str())
                        .map_or(false, |id| id == sub_instance_id)
                })
                .map(|(node_id, _)| node_id);
                
            if let Some(node_id) = subworkflow_node {
                // 获取节点定义
                let workflow_def: WorkflowDefinition = self.storage.get(&format!("workflow:{}", parent_instance.definition_id)).await
                    .map_err(|e| ExecutionError::StorageError(e.to_string()))?
                    .ok_or_else(|| ExecutionError::WorkflowNotFound(parent_instance.definition_id.clone()))?;
                    
                let node = workflow_def.nodes.iter()
                    .find(|n| n.id == *node_id)
                    .ok_or_else(|| ExecutionError::NodeNotFound(node_id.clone()))?;
                    
                // 根据配置决定是否取消父工作流
                let cancel_parent = node.config.get("cancel_parent_on_cancel")
                    .and_then(|v| v.as_bool())
                    .unwrap_or(false);
                    
                if cancel_parent {
                    // 取消父工作流
                    self.cancel_workflow(parent_instance_id).await?;
                } else {
                    // 将子工作流节点标记为取消
                    let mut parent_instance_clone = parent_instance.clone();
                    
                    let node_state = crate::model::NodeState {
                        node_id: node_id.clone(),
                        state: "CANCELLED".to_string(),
                        data: serde_json::json!({
                            "sub_workflow_instance_id": sub_instance_id,
                            "sub_workflow_cancelled": true,
                        }),
                        retries: parent_instance.node_states.get(node_id).map(|s| s.retries).unwrap_or(0),
                        last_updated: chrono::Utc::now(),
                    };
                    
                    parent_instance_clone.node_states.insert(node_id.clone(), node_state);
                    parent_instance_clone.updated_at = chrono::Utc::now();
                    
                    // 保存父实例
                    self.storage.put(&format!("instance:{}", parent_instance_id), &parent_instance_clone).await
                        .map_err(|e| ExecutionError::StorageError(e.to_string()))?;
                        
                    // 更新内部状态
                    {
                        let mut instances = self.active_instances.write().await;
                        if let Some(state) = instances.get_mut(parent_instance_id) {
                            state.running_nodes.remove(node_id);
                            state.updated_at = chrono::Utc::now();
                        }
                    }
                    
                    // 获取工作流定义，查找取消处理路径
                    let workflow_def: WorkflowDefinition = self.storage.get(&format!("workflow:{}", parent_instance.definition_id)).await
                        .map_err(|e| ExecutionError::StorageError(e.to_string()))?
                        .ok_or_else(|| ExecutionError::WorkflowNotFound(parent_instance.definition_id.clone()))?;
                        
                    // 查找标记为取消处理的出边
                    let cancel_edges = workflow_def.edges.iter()
                        .filter(|e| e.source == *node_id && e.condition.as_ref().map_or(false, |c| c.contains("cancel")))
                        .collect::<Vec<_>>();
                        
                    for edge in cancel_edges {
                        if let Some(target_node) = workflow_def.nodes.iter().find(|n| n.id == edge.target) {
                            self.schedule_node(&parent_instance_clone, target_node).await?;
                        }
                    }
                }
            } else {
                warn!(
                    parent_instance_id = %parent_instance_id,
                    sub_instance_id = %sub_instance_id,
                    "Could not find node referencing sub-workflow"
                );
            }
            
            Ok(())
        }
        
        /// 恢复工作流实例
        #[instrument(skip(self), fields(instance_id = %instance_id))]
        pub async fn resume_workflow(&self, instance_id: &str) -> Result<(), ExecutionError> {
            info!(instance_id = %instance_id, "Resuming workflow instance");
            
            // 获取实例
            let instance: WorkflowInstance = self.storage.get(&format!("instance:{}", instance_id)).await
                .map_err(|e| ExecutionError::StorageError(e.to_string()))?
                .ok_or_else(|| ExecutionError::ValidationError(format!(
                    "Instance {} not found", instance_id
                )))?;
                
            // 检查状态是否允许恢复
            if instance.state != "SUSPENDED" && instance.state != "RECOVERING" {
                return Err(ExecutionError::ValidationError(format!(
                    "Cannot resume instance {} in state {}", instance_id, instance.state
                )));
            }
            
            // 获取工作流定义
            let workflow_def: WorkflowDefinition = self.storage.get(&format!("workflow:{}", instance.definition_id)).await
                .map_err(|e| ExecutionError::StorageError(e.to_string()))?
                .ok_or_else(|| ExecutionError::WorkflowNotFound(instance.definition_id.clone()))?;
                
            // 更新实例状态
            let mut instance_clone = instance.clone();
            instance_clone.state = "RUNNING".to_string();
            instance_clone.updated_at = chrono::Utc::now();
            
            // 保存实例
            self.storage.put(&format!("instance:{}", instance_id), &instance_clone).await
                .map_err(|e| ExecutionError::StorageError(e.to_string()))?;
                
            // 初始化执行状态
            let (cancel_tx, cancel_rx) = oneshot::channel();
            
            let state = InstanceExecutionState {
                instance_id: instance_id.to_string(),
                pending_nodes: HashSet::new(),
                running_nodes: HashSet::new(),
                completed_nodes: instance.node_states.iter()
                    .filter(|(_, state)| state.state == "COMPLETED")
                    .map(|(id, _)| id.clone())
                    .collect(),
                variables: instance.variables.clone(),
                created_at: instance.created_at,
                updated_at: chrono::Utc::now(),
                cancellation_token: Some(cancel_tx),
            };
            
            // 添加到活动实例
            self.active_instances.write().await.insert(instance_id.to_string(), state);
            
            // 查找需要恢复的节点
            let suspended_nodes = instance.node_states.iter()
                .filter(|(_, state)| state.state == "SUSPENDED")
                .map(|(id, _)| id)
                .collect::<Vec<_>>();
                
            let failed_nodes = instance.node_states.iter()
                .filter(|(_, state)| state.state == "FAILED")
                .map(|(id, _)| id)
                .collect::<Vec<_>>();
                
            // 恢复挂起的节点
            for node_id in suspended_nodes {
                if let Some(node) = workflow_def.nodes.iter().find(|n| n.id == *node_id) {
                    self.schedule_node(&instance_clone, node).await?;
                }
            }
            
            // 恢复失败的节点
            for node_id in failed_nodes {
                if let Some(node) = workflow_def.nodes.iter().find(|n| n.id == *node_id) {
                    self.schedule_node(&instance_clone, node).await?;
                }
            }
            
            // 如果没有待恢复的节点，尝试查找未完成的路径
            if suspended_nodes.is_empty() && failed_nodes.is_empty() {
                // 查找所有已完成节点的出边
                let completed_nodes = instance.node_states.iter()
                    .filter(|(_, state)| state.state == "COMPLETED")
                    .map(|(id, _)| id)
                    .collect::<HashSet<_>>();
                    
                let possible_next_edges = workflow_def.edges.iter()
                    .filter(|e| completed_nodes.contains(&e.source))
                    .collect::<Vec<_>>();
                    
                // 检查每个边的目标节点是否已经完成
                for edge in possible_next_edges {
                    if !completed_nodes.contains(&edge.target) {
                        // 找到未完成的路径
                        if let Some(target_node) = workflow_def.nodes.iter().find(|n| n.id == edge.target) {
                            self.schedule_node(&instance_clone, target_node).await?;
                        }
                    }
                }
            }
            
            // 发布工作流恢复事件
            let event = crate::event_bus::EventMessage {
                event_id: Uuid::new_v4().to_string(),
                event_type: "workflow.instance.resumed".to_string(),
                source: "workflow-engine".to_string(),
                time: chrono::Utc::now(),
                data: serde_json::json!({
                    "instance_id": instance_id,
                    "definition_id": instance.definition_id,
                }),
                trace_context: instance.trace_context.clone(),
                schema_url: None,
            };
            
            self.event_bus.publish("workflow-events", event).await
                .map_err(|e| ExecutionError::Other(format!("Failed to publish event: {}", e)))?;
                
            Ok(())
        }
        
        /// 获取工作流实例
        pub async fn get_workflow_instance(&self, instance_id: &str) -> Result<WorkflowInstance, ExecutionError> {
            self.storage.get(&format!("instance:{}", instance_id)).await
                .map_err(|e| ExecutionError::StorageError(e.to_string()))?
                .ok_or_else(|| ExecutionError::ValidationError(format!(
                    "Instance {} not found", instance_id
                )))
        }
        
        /// 列出活动实例
        pub async fn list_active_instances(&self) -> Result<Vec<String>, ExecutionError> {
            let instances = self.active_instances.read().await;
            Ok(instances.keys().cloned().collect())
        }
        
        /// 根据节点查找实例
        pub async fn find_instances_by_node(&self, node_id: &str) -> Result<Vec<String>, ExecutionError> {
            // 简化实现：遍历所有活动实例查找
            let instances = self.active_instances.read().await;
            let mut result = Vec::new();
            
            for (instance_id, state) in instances.iter() {
                if state.running_nodes.contains(node_id) || state.pending_nodes.contains(node_id) {
                    result.push(instance_id.clone());
                }
            }
            
            Ok(result)
        }
        
        /// 获取实例的定义ID
        pub async fn get_instance_definition_id(&self, instance_id: &str) -> Result<String, ExecutionError> {
            let instance: WorkflowInstance = self.storage.get(&format!("instance:{}", instance_id)).await
                .map_err(|e| ExecutionError::StorageError(e.to_string()))?
                .ok_or_else(|| ExecutionError::ValidationError(format!(
                    "Instance {} not found", instance_id
                )))?;
                
            Ok(instance.definition_id)
        }
        
        /// 列出实例检查点
        pub async fn list_instance_checkpoints(&self, instance_id: &str) -> Result<Vec<CheckpointInfo>, ExecutionError> {
            // 从存储中查询检查点
            let prefix = format!("checkpoint:{}:", instance_id);
            let keys = self.storage.list_keys(&prefix).await
                .map_err(|e| ExecutionError::StorageError(e.to_string()))?;
                
            let mut checkpoints = Vec::new();
            
            for key in keys {
                let checkpoint_info: CheckpointInfo = self.storage.get(&key).await
                    .map_err(|e| ExecutionError::StorageError(e.to_string()))?
                    .ok_or_else(|| ExecutionError::ValidationError(format!(
                        "Checkpoint {} not found", key
                    )))?;
                    
                checkpoints.push(checkpoint_info);
            }
            
            // 按创建时间排序
            checkpoints.sort_by(|a, b| b.created_at.cmp(&a.created_at));
            
            Ok(checkpoints)
        }
        
        /// 保存恢复的实例
        pub async fn save_recovered_instance(&self, instance: &WorkflowInstance) -> Result<(), ExecutionError> {
            let instance_id = instance.id.clone();
            
            // 更新存储
            self.storage.put(&format!("instance:{}", instance_id), instance).await
                .map_err(|e| ExecutionError::StorageError(e.to_string()))?;
                
            // 发布实例恢复事件
            let event = crate::event_bus::EventMessage {
                event_id: Uuid::new_v4().to_string(),
                event_type: "workflow.instance.recovered".to_string(),
                source: "workflow-engine".to_string(),
                time: chrono::Utc::now(),
                data: serde_json::json!({
                    "instance_id": instance_id,
                    "definition_id": instance.definition_id,
                }),
                trace_context: instance.trace_context.clone(),
                schema_url: None,
            };
            
            self.event_bus.publish("workflow-events", event).await
                .map_err(|e| ExecutionError::Other(format!("Failed to publish event: {}", e)))?;
                
            Ok(())
        }
    }
    
    /// 执行引擎克隆实现
    impl Clone for WorkflowExecutionEngine {
        fn clone(&self) -> Self {
            Self {
                storage: Arc::clone(&self.storage),
                event_bus: Arc::clone(&self.event_bus),
                executors: self.executors.clone(),
                active_instances: Arc::clone(&self.active_instances),
                task_queue: self.task_queue.clone(),
                worker_count: self.worker_count,
            }
        }
    }
    
    /// 检查点信息
    #[derive(Clone, Debug, Serialize, Deserialize)]
    pub struct CheckpointInfo {
        pub id: String,
        pub instance_id: String,
        pub created_at: chrono::DateTime<chrono::Utc>,
        pub metadata: HashMap<String, String>,
    }
    
    /// 辅助函数：获取节点任务类型
    fn get_node_task_type(node_config: &serde_json::Value) -> Option<String> {
        node_config.get("task_type")
            .and_then(|v| v.as_str())
            .map(|s| s.to_string())
    }
    
    /// 辅助函数：查找合适的执行器
    fn find_executor_for_task(executors: &HashMap<String, Arc<dyn Executor>>, task_type: &str) -> Option<Arc<dyn Executor>> {
        // 直接匹配任务类型
        if let Some(executor) = executors.get(task_type) {
            return Some(Arc::clone(executor));
        }
        
        // 查找支持此任务类型的执行器
        for (_, executor) in executors {
            if executor.get_task_types().contains(&task_type.to_string()) {
                return Some(Arc::clone(executor));
            }
        }
        
        // 使用默认执行器
        executors.get("default").cloned()
    }
    
    /// 通用任务执行器实现
    pub struct GenericTaskExecutor {
        task_handlers: Arc<RwLock<HashMap<String, Box<dyn TaskHandler>>>>,
        stats: Arc<RwLock<ExecutorStats>>,
    }
    
    /// 任务处理器特性
    #[async_trait]
    pub trait TaskHandler: Send + Sync {
        async fn handle(&self, context: TaskContext) -> Result<TaskResult, ExecutionError>;
    }
    
    impl GenericTaskExecutor {
        /// 创建新的任务执行器
        pub fn new() -> Self {
            Self {
                task_handlers: Arc::new(RwLock::new(HashMap::new())),
                stats: Arc::new(RwLock::new(ExecutorStats {
                    tasks_completed: 0,
                    tasks_failed: 0,
                    tasks_in_progress: 0,
                    avg_execution_time_ms: 0.0,
                })),
            }
        }
        
        /// 注册任务处理器
        pub async fn register_handler<H>(&self, task_type: &str, handler: H)
        where
            H: TaskHandler + 'static,
        {
            self.task_handlers.write().await.insert(task_type.to_string(), Box::new(handler));
        }
    }
    
    #[async_trait]
    impl Executor for GenericTaskExecutor {
        async fn execute(&self, context: TaskContext) -> Result<TaskResult, ExecutionError> {
            let task_type = get_node_task_type(&context.node_config)
                .ok_or_else(|| ExecutionError::ValidationError("No task_type specified".to_string()))?;
                
            // 更新统计信息
            {
                let mut stats = self.stats.write().await;
                stats.tasks_in_progress += 1;
            }
            
            let start_time = std::time::Instant::now();
            
            // 查找处理器
            let handler = {
                let handlers = self.task_handlers.read().await;
                handlers.get(&task_type)
                    .cloned()
                    .ok_or_else(|| ExecutionError::ValidationError(format!("No handler found for task type: {}", task_type)))?
            };
            
            // 执行任务
            let result = handler.handle(context).await;
            
            // 更新统计信息
            let duration_ms = start_time.elapsed().as_millis() as f64;
            {
                let mut stats = self.stats.write().await;
                stats.tasks_in_progress -= 1;
                
                match &result {
                    Ok(_) => {
                        stats.tasks_completed += 1;
                    },
                    Err(_) => {
                        stats.tasks_failed += 1;
                    }
                }
                
                // 更新平均执行时间
                let total_tasks = stats.tasks_completed + stats.tasks_failed;
                if total_tasks > 1 {
                    stats.avg_execution_time_ms = (stats.avg_execution_time_ms * (total_tasks - 1) as f64 + duration_ms) / total_tasks as f64;
                } else {
                    stats.avg_execution_time_ms = duration_ms;
                }
            }
            
            result
        }
        
        fn get_task_types(&self) -> Vec<String> {
            tokio::task::block_in_place(|| {
                let runtime = tokio::runtime::Handle::current();
                runtime.block_on(async {
                    self.task_handlers.read().await.keys().cloned().collect()
                })
            })
        }
        
        fn get_stats(&self) -> ExecutorStats {
            tokio::task::block_in_place(|| {
                let runtime = tokio::runtime::Handle::current();
                runtime.block_on(async {
                    self.stats.read().await.clone()
                })
            })
        }
    }
}
```

## 示例应用：数据处理工作流

以下是一个完整的数据处理工作流示例，展示如何使用我们的框架构建一个实际应用：

```rust
// 数据处理工作流示例
use crate::model::{WorkflowDefinition, NodeDefinition, NodeType, EdgeDefinition, GatewayType};
use crate::execution::{TaskContext, TaskResult, TaskStatus, ExecutionError, TaskHandler};
use crate::storage::StorageManager;
use crate::event_bus::EventBus;
use crate::execution::{WorkflowExecutionEngine, GenericTaskExecutor, Executor};
use async_trait::async_trait;
use std::collections::HashMap;
use std::sync::Arc;
use serde::{Serialize, Deserialize};
use tracing::{info, warn, error};

/// 数据提取处理器
struct DataExtractHandler {
    db_client: Arc<DbClient>,
}

#[async_trait]
impl TaskHandler for DataExtractHandler {
    async fn handle(&self, context: TaskContext) -> Result<TaskResult, ExecutionError> {
        info!(
            instance_id = %context.instance_id,
            node_id = %context.node_id,
            "Executing data extraction"
        );
        
        // 获取查询参数
        let query = context.node_config.get("query")
            .and_then(|v| v.as_str())
            .ok_or_else(|| ExecutionError::ValidationError("No query specified".to_string()))?;
            
        let data_source = context.node_config.get("data_source")
            .and_then(|v| v.as_str())
            .ok_or_else(|| ExecutionError::ValidationError("No data_source specified".to_string()))?;
            
        info!(
            query = %query,
            data_source = %data_source,
            "Extracting data"
        );
        
        // 执行数据库查询
        let result = self.db_client.query(data_source, query).await
            .map_err(|e| ExecutionError::TaskFailed(format!("Database query failed: {}", e)))?;
            
        // 构建输出
        let mut output = HashMap::new();
        output.insert("data".to_string(), serde_json::to_value(&result).unwrap());
        output.insert("record_count".to_string(), serde_json::json!(result.len()));
        
        info!(
            instance_id = %context.instance_id,
            node_id = %context.node_id,
            record_count = %result.len(),
            "Data extraction completed"
        );
        
        Ok(TaskResult {
            output,
            status: TaskStatus::Completed,
            message: Some(format!("Extracted {} records", result.len())),
        })
    }
}

/// 数据转换处理器
struct DataTransformHandler;

#[async_trait]
impl TaskHandler for DataTransformHandler {
    async fn handle(&self, context: TaskContext) -> Result<TaskResult, ExecutionError> {
        info!(
            instance_id = %context.instance_id,
            node_id = %context.node_id,
            "Executing data transformation"
        );
        
        // 获取输入数据
        let data = context.variables.get("data")
            .ok_or_else(|| ExecutionError::ValidationError("No input data found".to_string()))?;
            
        let records: Vec<Record> = serde_json::from_value(data.clone())
            .map_err(|e| ExecutionError::ValidationError(format!("Invalid input data: {}", e)))?;
            
        // 获取转换规则
        let transform_rules = context.node_config.get("transform_rules")
            .and_then(|v| v.as_array())
            .ok_or_else(|| ExecutionError::ValidationError("No transform_rules specified".to_string()))?;
            
        // 执行转换
        let mut transformed_records = Vec::new();
        
        for record in records {
            let mut transformed_record = record.clone();
            
            for rule in transform_rules {
                let field = rule.get("field").and_then(|v| v.as_str());
                let action = rule.get("action").and_then(|v| v.as_str());
                
                if let (Some(field), Some(action)) = (field, action) {
                    match action {
                        "uppercase" => {
                            if let Some(value) = transformed_record.fields.get_mut(field) {
                                if let serde_json::Value::String(s) = value {
                                    *s = s.to_uppercase();
                                }
                            }
                        },
                        "lowercase" => {
                            if let Some(value) = transformed_record.fields.get_mut(field) {
                                if let serde_json::Value::String(s) = value {
                                    *s = s.to_lowercase();
                                }
                            }
                        },
                        "multiply" => {
                            if let Some(factor) = rule.get("factor").and_then(|v| v.as_f64()) {
                                if let Some(value) = transformed_record.fields.get_mut(field) {
                                    if let serde_json::Value::Number(n) = value {
                                        if let Some(num) = n.as_f64() {
                                            *value = serde
# Rust 分布式工作流框架设计（续）

## 示例应用：数据处理工作流（续）

```rust
// 数据处理工作流示例（续）
use crate::model::{WorkflowDefinition, NodeDefinition, NodeType, EdgeDefinition, GatewayType};
use crate::execution::{TaskContext, TaskResult, TaskStatus, ExecutionError, TaskHandler};
use crate::storage::StorageManager;
use crate::event_bus::EventBus;
use crate::execution::{WorkflowExecutionEngine, GenericTaskExecutor, Executor};
use async_trait::async_trait;
use std::collections::HashMap;
use std::sync::Arc;
use serde::{Serialize, Deserialize};
use tracing::{info, warn, error};

// ... 前面内容省略

/// 数据转换处理器（续）
#[async_trait]
impl TaskHandler for DataTransformHandler {
    async fn handle(&self, context: TaskContext) -> Result<TaskResult, ExecutionError> {
        // ... 前面内容省略

        // 执行转换
        let mut transformed_records = Vec::new();
        
        for record in records {
            let mut transformed_record = record.clone();
            
            for rule in transform_rules {
                let field = rule.get("field").and_then(|v| v.as_str());
                let action = rule.get("action").and_then(|v| v.as_str());
                
                if let (Some(field), Some(action)) = (field, action) {
                    match action {
                        // ... 前面内容省略
                        "multiply" => {
                            if let Some(factor) = rule.get("factor").and_then(|v| v.as_f64()) {
                                if let Some(value) = transformed_record.fields.get_mut(field) {
                                    if let serde_json::Value::Number(n) = value {
                                        if let Some(num) = n.as_f64() {
                                            *value = serde_json::json!(num * factor);
                                        }
                                    }
                                }
                            }
                        },
                        "divide" => {
                            if let Some(divisor) = rule.get("divisor").and_then(|v| v.as_f64()) {
                                if divisor == 0.0 {
                                    warn!(field = %field, "Cannot divide by zero");
                                    continue;
                                }
                                
                                if let Some(value) = transformed_record.fields.get_mut(field) {
                                    if let serde_json::Value::Number(n) = value {
                                        if let Some(num) = n.as_f64() {
                                            *value = serde_json::json!(num / divisor);
                                        }
                                    }
                                }
                            }
                        },
                        "trim" => {
                            if let Some(value) = transformed_record.fields.get_mut(field) {
                                if let serde_json::Value::String(s) = value {
                                    *s = s.trim().to_string();
                                }
                            }
                        },
                        "replace" => {
                            if let (Some(pattern), Some(replacement)) = (
                                rule.get("pattern").and_then(|v| v.as_str()),
                                rule.get("replacement").and_then(|v| v.as_str())
                            ) {
                                if let Some(value) = transformed_record.fields.get_mut(field) {
                                    if let serde_json::Value::String(s) = value {
                                        *s = s.replace(pattern, replacement);
                                    }
                                }
                            }
                        },
                        _ => {
                            warn!(action = %action, "Unknown transform action");
                        }
                    }
                }
            }
            
            transformed_records.push(transformed_record);
        }
        
        // 构建输出
        let mut output = HashMap::new();
        output.insert("transformed_data".to_string(), serde_json::to_value(&transformed_records).unwrap());
        output.insert("record_count".to_string(), serde_json::json!(transformed_records.len()));
        
        info!(
            instance_id = %context.instance_id,
            node_id = %context.node_id,
            record_count = %transformed_records.len(),
            "Data transformation completed"
        );
        
        Ok(TaskResult {
            output,
            status: TaskStatus::Completed,
            message: Some(format!("Transformed {} records", transformed_records.len())),
        })
    }
}

/// 数据验证处理器
struct DataValidationHandler;

#[async_trait]
impl TaskHandler for DataValidationHandler {
    async fn handle(&self, context: TaskContext) -> Result<TaskResult, ExecutionError> {
        info!(
            instance_id = %context.instance_id,
            node_id = %context.node_id,
            "Executing data validation"
        );
        
        // 获取输入数据
        let data = context.variables.get("transformed_data")
            .ok_or_else(|| ExecutionError::ValidationError("No transformed data found".to_string()))?;
            
        let records: Vec<Record> = serde_json::from_value(data.clone())
            .map_err(|e| ExecutionError::ValidationError(format!("Invalid input data: {}", e)))?;
            
        // 获取验证规则
        let validation_rules = context.node_config.get("validation_rules")
            .and_then(|v| v.as_array())
            .ok_or_else(|| ExecutionError::ValidationError("No validation_rules specified".to_string()))?;
            
        // 执行验证
        let mut valid_records = Vec::new();
        let mut invalid_records = Vec::new();
        let mut validation_errors = Vec::new();
        
        for (index, record) in records.into_iter().enumerate() {
            let mut record_valid = true;
            let mut record_errors = Vec::new();
            
            for rule in validation_rules {
                let field = rule.get("field").and_then(|v| v.as_str());
                let rule_type = rule.get("type").and_then(|v| v.as_str());
                
                if let (Some(field), Some(rule_type)) = (field, rule_type) {
                    if let Some(value) = record.fields.get(field) {
                        let valid = match rule_type {
                            "required" => {
                                !value.is_null() && (value != &serde_json::Value::String("".to_string()))
                            },
                            "number" => {
                                value.is_number()
                            },
                            "integer" => {
                                value.is_number() && value.as_f64().map_or(false, |n| n.fract() == 0.0)
                            },
                            "string" => {
                                value.is_string()
                            },
                            "email" => {
                                value.as_str().map_or(false, |s| {
                                    // 简单的电子邮件验证
                                    s.contains('@') && s.contains('.')
                                })
                            },
                            "min" => {
                                if let Some(min_value) = rule.get("min_value").and_then(|v| v.as_f64()) {
                                    value.as_f64().map_or(false, |n| n >= min_value)
                                } else {
                                    true
                                }
                            },
                            "max" => {
                                if let Some(max_value) = rule.get("max_value").and_then(|v| v.as_f64()) {
                                    value.as_f64().map_or(false, |n| n <= max_value)
                                } else {
                                    true
                                }
                            },
                            "regex" => {
                                if let Some(pattern) = rule.get("pattern").and_then(|v| v.as_str()) {
                                    let re = regex::Regex::new(pattern).unwrap();
                                    value.as_str().map_or(false, |s| re.is_match(s))
                                } else {
                                    true
                                }
                            },
                            _ => {
                                warn!(rule_type = %rule_type, "Unknown validation rule type");
                                true
                            }
                        };
                        
                        if !valid {
                            record_valid = false;
                            let error_message = rule.get("error_message")
                                .and_then(|v| v.as_str())
                                .unwrap_or(&format!("Field '{}' failed '{}' validation", field, rule_type))
                                .to_string();
                                
                            record_errors.push(ValidationError {
                                record_index: index,
                                field: field.to_string(),
                                rule_type: rule_type.to_string(),
                                message: error_message,
                            });
                        }
                    } else if rule_type == "required" {
                        // 如果字段不存在，但规则是required，则验证失败
                        record_valid = false;
                        let error_message = rule.get("error_message")
                            .and_then(|v| v.as_str())
                            .unwrap_or(&format!("Required field '{}' is missing", field))
                            .to_string();
                            
                        record_errors.push(ValidationError {
                            record_index: index,
                            field: field.to_string(),
                            rule_type: rule_type.to_string(),
                            message: error_message,
                        });
                    }
                }
            }
            
            if record_valid {
                valid_records.push(record);
            } else {
                invalid_records.push(record);
                validation_errors.extend(record_errors);
            }
        }
        
        // 构建输出
        let mut output = HashMap::new();
        output.insert("valid_data".to_string(), serde_json::to_value(&valid_records).unwrap());
        output.insert("invalid_data".to_string(), serde_json::to_value(&invalid_records).unwrap());
        output.insert("validation_errors".to_string(), serde_json::to_value(&validation_errors).unwrap());
        output.insert("valid_count".to_string(), serde_json::json!(valid_records.len()));
        output.insert("invalid_count".to_string(), serde_json::json!(invalid_records.len()));
        output.insert("is_valid".to_string(), serde_json::json!(invalid_records.is_empty()));
        
        info!(
            instance_id = %context.instance_id,
            node_id = %context.node_id,
            valid_count = %valid_records.len(),
            invalid_count = %invalid_records.len(),
            "Data validation completed"
        );
        
        Ok(TaskResult {
            output,
            status: TaskStatus::Completed,
            message: Some(format!(
                "Validated {} records. {} valid, {} invalid", 
                valid_records.len() + invalid_records.len(),
                valid_records.len(),
                invalid_records.len()
            )),
        })
    }
}

/// 数据加载处理器
struct DataLoadHandler {
    db_client: Arc<DbClient>,
}

#[async_trait]
impl TaskHandler for DataLoadHandler {
    async fn handle(&self, context: TaskContext) -> Result<TaskResult, ExecutionError> {
        info!(
            instance_id = %context.instance_id,
            node_id = %context.node_id,
            "Executing data loading"
        );
        
        // 获取目标配置
        let target_table = context.node_config.get("target_table")
            .and_then(|v| v.as_str())
            .ok_or_else(|| ExecutionError::ValidationError("No target_table specified".to_string()))?;
            
        let target_db = context.node_config.get("target_db")
            .and_then(|v| v.as_str())
            .ok_or_else(|| ExecutionError::ValidationError("No target_db specified".to_string()))?;
            
        // 获取有效数据
        let data = context.variables.get("valid_data")
            .ok_or_else(|| ExecutionError::ValidationError("No valid data found".to_string()))?;
            
        let records: Vec<Record> = serde_json::from_value(data.clone())
            .map_err(|e| ExecutionError::ValidationError(format!("Invalid input data: {}", e)))?;
            
        if records.is_empty() {
            info!(
                instance_id = %context.instance_id,
                node_id = %context.node_id,
                "No valid records to load"
            );
            
            return Ok(TaskResult {
                output: HashMap::from([
                    ("loaded_count".to_string(), serde_json::json!(0)),
                ]),
                status: TaskStatus::Completed,
                message: Some("No records to load".to_string()),
            });
        }
        
        // 执行数据加载
        info!(
            target_db = %target_db,
            target_table = %target_table,
            record_count = %records.len(),
            "Loading data"
        );
        
        let result = self.db_client.insert_batch(target_db, target_table, &records).await
            .map_err(|e| ExecutionError::TaskFailed(format!("Database insert failed: {}", e)))?;
            
        // 构建输出
        let mut output = HashMap::new();
        output.insert("loaded_count".to_string(), serde_json::json!(result.inserted_count));
        
        info!(
            instance_id = %context.instance_id,
            node_id = %context.node_id,
            loaded_count = %result.inserted_count,
            "Data loading completed"
        );
        
        Ok(TaskResult {
            output,
            status: TaskStatus::Completed,
            message: Some(format!("Loaded {} records", result.inserted_count)),
        })
    }
}

/// 错误处理器
struct ErrorHandlerTask;

#[async_trait]
impl TaskHandler for ErrorHandlerTask {
    async fn handle(&self, context: TaskContext) -> Result<TaskResult, ExecutionError> {
        info!(
            instance_id = %context.instance_id,
            node_id = %context.node_id,
            "Executing error handling"
        );
        
        // 获取错误数据
        let data = context.variables.get("invalid_data")
            .ok_or_else(|| ExecutionError::ValidationError("No invalid data found".to_string()))?;
            
        let records: Vec<Record> = serde_json::from_value(data.clone())
            .map_err(|e| ExecutionError::ValidationError(format!("Invalid error data: {}", e)))?;
            
        let errors = context.variables.get("validation_errors")
            .ok_or_else(|| ExecutionError::ValidationError("No validation errors found".to_string()))?;
            
        let validation_errors: Vec<ValidationError> = serde_json::from_value(errors.clone())
            .map_err(|e| ExecutionError::ValidationError(format!("Invalid validation errors: {}", e)))?;
            
        // 获取错误处理配置
        let error_log_path = context.node_config.get("error_log_path")
            .and_then(|v| v.as_str())
            .unwrap_or("./errors.log");
            
        let notify_email = context.node_config.get("notify_email")
            .and_then(|v| v.as_str());
            
        // 记录错误
        info!(
            instance_id = %context.instance_id,
            error_count = %validation_errors.len(),
            error_log_path = %error_log_path,
            "Logging validation errors"
        );
        
        // 在实际应用中，这里会写入文件或数据库
        // 简化示例中，我们只打印日志
        for error in &validation_errors {
            error!(
                record_index = %error.record_index,
                field = %error.field,
                rule = %error.rule_type,
                message = %error.message,
                "Validation error"
            );
        }
        
        // 如果配置了邮件通知，发送通知
        if let Some(email) = notify_email {
            info!(
                email = %email,
                error_count = %validation_errors.len(),
                "Sending error notification email"
            );
            
            // 模拟发送邮件
            tokio::time::sleep(std::time::Duration::from_millis(100)).await;
        }
        
        // 构建输出
        let mut output = HashMap::new();
        output.insert("error_count".to_string(), serde_json::json!(validation_errors.len()));
        output.insert("error_log_path".to_string(), serde_json::json!(error_log_path));
        
        Ok(TaskResult {
            output,
            status: TaskStatus::Completed,
            message: Some(format!("Processed {} validation errors", validation_errors.len())),
        })
    }
}

/// 数据记录结构
#[derive(Clone, Debug, Serialize, Deserialize)]
struct Record {
    id: String,
    fields: HashMap<String, serde_json::Value>,
}

/// 验证错误结构
#[derive(Clone, Debug, Serialize, Deserialize)]
struct ValidationError {
    record_index: usize,
    field: String,
    rule_type: String,
    message: String,
}

/// 数据库客户端（模拟）
struct DbClient;

/// 插入结果
#[derive(Clone, Debug)]
struct InsertResult {
    inserted_count: usize,
}

impl DbClient {
    /// 创建新的数据库客户端
    pub fn new() -> Self {
        Self {}
    }
    
    /// 执行查询
    pub async fn query(&self, data_source: &str, query: &str) -> Result<Vec<Record>, String> {
        // 模拟查询延迟
        tokio::time::sleep(std::time::Duration::from_millis(500)).await;
        
        // 生成模拟数据
        let mut records = Vec::new();
        
        for i in 1..20 {
            let mut fields = HashMap::new();
            fields.insert("name".to_string(), serde_json::json!(format!("User {}", i)));
            fields.insert("email".to_string(), serde_json::json!(format!("user{}@example.com", i)));
            fields.insert("age".to_string(), serde_json::json!(20 + (i % 50)));
            fields.insert("score".to_string(), serde_json::json!(75.5 + (i as f64 * 0.5)));
            
            if i % 5 == 0 {
                // 添加一些无效数据，用于测试验证
                fields.insert("email".to_string(), serde_json::json!("invalid-email"));
            }
            
            if i % 7 == 0 {
                // 添加一些无效年龄
                fields.insert("age".to_string(), serde_json::json!(-5));
            }
            
            records.push(Record {
                id: format!("REC-{}", i),
                fields,
            });
        }
        
        Ok(records)
    }
    
    /// 批量插入数据
    pub async fn insert_batch(&self, target_db: &str, target_table: &str, records: &[Record]) -> Result<InsertResult, String> {
        // 模拟插入延迟
        tokio::time::sleep(std::time::Duration::from_millis(records.len() as u64 * 50)).await;
        
        // 简单返回插入结果
        Ok(InsertResult {
            inserted_count: records.len(),
        })
    }
}

/// 创建数据处理工作流
fn create_data_processing_workflow() -> WorkflowDefinition {
    // 创建节点
    let mut nodes = Vec::new();
    
    // 开始事件
    nodes.push(NodeDefinition {
        id: "start".to_string(),
        node_type: NodeType::Event { event_type: "start".to_string() },
        config: serde_json::json!({
            "name": "开始",
            "x": 100,
            "y": 200,
        }),
        retry_policy: None,
        timeout: None,
        semantics: vec![],
    });
    
    // 数据提取节点
    nodes.push(NodeDefinition {
        id: "extract".to_string(),
        node_type: NodeType::Task { task_type: "data_extract".to_string() },
        config: serde_json::json!({
            "name": "数据提取",
            "x": 250,
            "y": 200,
            "data_source": "customers_db",
            "query": "SELECT * FROM customers WHERE status = 'active'",
        }),
        retry_policy: Some(crate::model::RetryPolicy {
            max_attempts: 3,
            interval: std::time::Duration::from_secs(10),
            backoff_factor: 2.0,
        }),
        timeout: Some(std::time::Duration::from_secs(60)),
        semantics: vec![],
    });
    
    // 数据转换节点
    nodes.push(NodeDefinition {
        id: "transform".to_string(),
        node_type: NodeType::Task { task_type: "data_transform".to_string() },
        config: serde_json::json!({
            "name": "数据转换",
            "x": 400,
            "y": 200,
            "transform_rules": [
                { "field": "name", "action": "uppercase" },
                { "field": "score", "action": "multiply", "factor": 1.1 },
            ],
        }),
        retry_policy: Some(crate::model::RetryPolicy {
            max_attempts: 2,
            interval: std::time::Duration::from_secs(5),
            backoff_factor: 2.0,
        }),
        timeout: Some(std::time::Duration::from_secs(30)),
        semantics: vec![],
    });
    
    // 数据验证节点
    nodes.push(NodeDefinition {
        id: "validate".to_string(),
        node_type: NodeType::Task { task_type: "data_validate".to_string() },
        config: serde_json::json!({
            "name": "数据验证",
            "x": 550,
            "y": 200,
            "validation_rules": [
                { 
                    "field": "email", 
                    "type": "email", 
                    "error_message": "Invalid email format" 
                },
                { 
                    "field": "age", 
                    "type": "min", 
                    "min_value": 0, 
                    "error_message": "Age must be positive" 
                },
                { 
                    "field": "score", 
                    "type": "number", 
                    "error_message": "Score must be a number" 
                },
            ],
        }),
        retry_policy: None,
        timeout: Some(std::time::Duration::from_secs(30)),
        semantics: vec![],
    });
    
    // 验证网关
    nodes.push(NodeDefinition {
        id: "validation_gateway".to_string(),
        node_type: NodeType::Gateway { gateway_type: GatewayType::Exclusive },
        config: serde_json::json!({
            "name": "验证网关",
            "x": 700,
            "y": 200,
        }),
        retry_policy: None,
        timeout: None,
        semantics: vec![],
    });
    
    // 数据加载节点
    nodes.push(NodeDefinition {
        id: "load".to_string(),
        node_type: NodeType::Task { task_type: "data_load".to_string() },
        config: serde_json::json!({
            "name": "数据加载",
            "x": 850,
            "y": 150,
            "target_db": "analytics_db",
            "target_table": "processed_customers",
        }),
        retry_policy: Some(crate::model::RetryPolicy {
            max_attempts: 3,
            interval: std::time::Duration::from_secs(10),
            backoff_factor: 1.5,
        }),
        timeout: Some(std::time::Duration::from_secs(60)),
        semantics: vec![],
    });
    
    // 错误处理节点
    nodes.push(NodeDefinition {
        id: "error_handler".to_string(),
        node_type: NodeType::Task { task_type: "error_handler".to_string() },
        config: serde_json::json!({
            "name": "错误处理",
            "x": 850,
            "y": 250,
            "error_log_path": "/var/log/workflow/validation_errors.log",
            "notify_email": "admin@example.com",
        }),
        retry_policy: None,
        timeout: Some(std::time::Duration::from_secs(30)),
        semantics: vec![],
    });
    
    // 处理结束节点
    nodes.push(NodeDefinition {
        id: "end_processed".to_string(),
        node_type: NodeType::Event { event_type: "end".to_string() },
        config: serde_json::json!({
            "name": "处理完成",
            "x": 1000,
            "y": 150,
        }),
        retry_policy: None,
        timeout: None,
        semantics: vec![],
    });
    
    // 错误结束节点
    nodes.push(NodeDefinition {
        id: "end_error".to_string(),
        node_type: NodeType::Event { event_type: "end".to_string() },
        config: serde_json::json!({
            "name": "处理错误",
            "x": 1000,
            "y": 250,
        }),
        retry_policy: None,
        timeout: None,
        semantics: vec![],
    });
    
    // 创建边
    let edges = vec![
        EdgeDefinition {
            id: "start-to-extract".to_string(),
            source: "start".to_string(),
            target: "extract".to_string(),
            condition: None,
        },
        EdgeDefinition {
            id: "extract-to-transform".to_string(),
            source: "extract".to_string(),
            target: "transform".to_string(),
            condition: None,
        },
        EdgeDefinition {
            id: "transform-to-validate".to_string(),
            source: "transform".to_string(),
            target: "validate".to_string(),
            condition: None,
        },
        EdgeDefinition {
            id: "validate-to-gateway".to_string(),
            source: "validate".to_string(),
            target: "validation_gateway".to_string(),
            condition: None,
        },
        EdgeDefinition {
            id: "gateway-to-load".to_string(),
            source: "validation_gateway".to_string(),
            target: "load".to_string(),
            condition: Some("${is_valid} == true".to_string()),
        },
        EdgeDefinition {
            id: "gateway-to-error".to_string(),
            source: "validation_gateway".to_string(),
            target: "error_handler".to_string(),
            condition: Some("${is_valid} == false".to_string()),
        },
        EdgeDefinition {
            id: "load-to-end".to_string(),
            source: "load".to_string(),
            target: "end_processed".to_string(),
            condition: None,
        },
        EdgeDefinition {
            id: "error-to-end".to_string(),
            source: "error_handler".to_string(),
            target: "end_error".to_string(),
            condition: None,
        },
    ];
    
    // 创建工作流定义
    WorkflowDefinition {
        id: uuid::Uuid::new_v4().to_string(),
        name: "数据处理工作流".to_string(),
        version: "1.0.0".to_string(),
        nodes,
        edges,
        variables: HashMap::new(),
        metadata: HashMap::from([
            ("description".to_string(), "从数据源提取、转换、验证和加载数据的ETL工作流".to_string()),
            ("author".to_string(), "系统管理员".to_string()),
            ("created_at".to_string(), chrono::Utc::now().to_rfc3339()),
        ]),
        semantics: vec![],
    }
}

/// 主函数
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt::init();
    
    // 创建存储管理器
    let storage = StorageManager::new(
        std::time::Duration::from_secs(60),
        Some(std::path::PathBuf::from("./workflow_data")),
        Box::new(crate::storage::MemoryStorage::new(std::time::Duration::from_secs(3600))),
    );
    
    // 创建事件总线
    let event_bus = Arc::new(crate::event_bus::NatsEventBus::new("localhost:4222").await?);
    
    // 创建数据库客户端
    let db_client = Arc::new(DbClient::new());
    
    // 创建任务执行器
    let mut executor = GenericTaskExecutor::new();
    
    // 注册任务处理器
    executor.register_handler("data_extract", DataExtractHandler {
        db_client: Arc::clone(&db_client),
    }).await;
    
    executor.register_handler("data_transform", DataTransformHandler).await;
    executor.register_handler("data_validate", DataValidationHandler).await;
    
    executor.register_handler("data_load", DataLoadHandler {
        db_client: Arc::
# Rust 分布式工作流框架设计（续）

## 示例应用：数据处理工作流（续）

```rust
// 数据处理工作流示例（续）
use crate::model::{WorkflowDefinition, NodeDefinition, NodeType, EdgeDefinition, GatewayType};
use crate::execution::{TaskContext, TaskResult, TaskStatus, ExecutionError, TaskHandler};
use crate::storage::StorageManager;
use crate::event_bus::EventBus;
use crate::execution::{WorkflowExecutionEngine, GenericTaskExecutor, Executor};
use async_trait::async_trait;
use std::collections::HashMap;
use std::sync::Arc;
use serde::{Serialize, Deserialize};
use tracing::{info, warn, error};

/// 主函数（续）
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // ... 前面内容省略
    
    // 注册任务处理器（续）
    executor.register_handler("data_load", DataLoadHandler {
        db_client: Arc::clone(&db_client),
    }).await;
    
    executor.register_handler("error_handler", ErrorHandlerTask).await;
    
    // 创建执行器映射
    let executors = HashMap::from([
        ("default".to_string(), Arc::new(executor) as Arc<dyn Executor>),
    ]);
    
    // 创建工作流执行引擎
    let engine = WorkflowExecutionEngine::new(
        Arc::new(storage.clone()),
        Arc::clone(&event_bus) as Arc<dyn EventBus>,
        executors,
        8, // 工作线程数
    );
    
    // 创建工作流定义
    let workflow_def = create_data_processing_workflow();
    
    // 保存工作流定义
    storage.put(&format!("workflow:{}", workflow_def.id), &workflow_def).await?;
    
    info!(
        workflow_id = %workflow_def.id,
        workflow_name = %workflow_def.name,
        "工作流定义已保存"
    );
    
    // 创建初始变量
    let initial_variables = HashMap::new();
    
    // 执行工作流
    info!(
        workflow_id = %workflow_def.id,
        "启动工作流实例"
    );
    
    let instance = engine.start_workflow(&workflow_def.id, initial_variables).await?;
    
    info!(
        instance_id = %instance.id,
        workflow_id = %workflow_def.id,
        "工作流实例已启动"
    );
    
    // 等待工作流完成
    loop {
        tokio::time::sleep(std::time::Duration::from_secs(1)).await;
        
        let instance = engine.get_workflow_instance(&instance.id).await?;
        
        if instance.state == "COMPLETED" || instance.state == "FAILED" || instance.state == "CANCELLED" {
            info!(
                instance_id = %instance.id,
                state = %instance.state,
                "工作流实例已结束"
            );
            
            // 打印结果
            for (key, value) in &instance.variables {
                if key == "validation_errors" || key == "transformed_data" || key == "data" {
                    // 跳过大数据
                    info!(
                        key = %key,
                        size = %value.to_string().len(),
                        "大数据变量已省略"
                    );
                } else {
                    info!(
                        key = %key,
                        value = %value,
                        "工作流变量"
                    );
                }
            }
            
            break;
        }
        
        info!(
            instance_id = %instance.id,
            state = %instance.state,
            "工作流实例正在运行"
        );
    }
    
    Ok(())
}
```

## 示例应用：API服务集成

以下是一个基于我们的工作流框架实现的REST API服务，可以通过Web界面管理和执行工作流：

```rust
// API服务示例
use crate::model::{WorkflowDefinition, NodeDefinition, NodeType, EdgeDefinition};
use crate::storage::StorageManager;
use crate::event_bus::EventBus;
use crate::execution::WorkflowExecutionEngine;
use crate::dsl::{DslParser, WorkflowDsl};
use axum::{
    routing::{get, post},
    Router, Json, extract::{State, Path, Query},
    response::{IntoResponse, Response},
    http::StatusCode,
};
use tower_http::cors::CorsLayer;
use tower_http::trace::TraceLayer;
use serde::{Serialize, Deserialize};
use std::collections::HashMap;
use std::sync::Arc;
use tracing::{info, warn, error};

/// API状态
struct ApiState {
    engine: Arc<WorkflowExecutionEngine>,
    storage: Arc<StorageManager>,
}

/// 工作流列表响应
#[derive(Serialize)]
struct WorkflowListResponse {
    workflows: Vec<WorkflowSummary>,
    total: usize,
    page: usize,
    per_page: usize,
}

/// 工作流摘要
#[derive(Serialize)]
struct WorkflowSummary {
    id: String,
    name: String,
    version: String,
    description: Option<String>,
    created_at: String,
    node_count: usize,
    edge_count: usize,
}

/// 工作流实例列表响应
#[derive(Serialize)]
struct InstanceListResponse {
    instances: Vec<InstanceSummary>,
    total: usize,
    page: usize,
    per_page: usize,
}

/// 实例摘要
#[derive(Serialize)]
struct InstanceSummary {
    id: String,
    workflow_id: String,
    workflow_name: String,
    state: String,
    created_at: String,
    updated_at: String,
    node_count: usize,
    completed_node_count: usize,
}

/// 工作流创建请求
#[derive(Deserialize)]
struct CreateWorkflowRequest {
    name: String,
    description: Option<String>,
    yaml_definition: String,
}

/// 工作流创建响应
#[derive(Serialize)]
struct CreateWorkflowResponse {
    id: String,
    name: String,
    version: String,
}

/// 启动工作流请求
#[derive(Deserialize)]
struct StartWorkflowRequest {
    workflow_id: String,
    variables: Option<HashMap<String, serde_json::Value>>,
}

/// 启动工作流响应
#[derive(Serialize)]
struct StartWorkflowResponse {
    instance_id: String,
    workflow_id: String,
    state: String,
}

/// 操作响应
#[derive(Serialize)]
struct ActionResponse {
    success: bool,
    message: String,
}

/// 查询参数
#[derive(Deserialize)]
struct PaginationParams {
    page: Option<usize>,
    per_page: Option<usize>,
}

/// 列出工作流
async fn list_workflows(
    State(state): State<Arc<ApiState>>,
    Query(params): Query<PaginationParams>,
) -> impl IntoResponse {
    let page = params.page.unwrap_or(1);
    let per_page = params.per_page.unwrap_or(10);
    
    // 列出工作流键
    let result = state.storage.list_keys("workflow:").await;
    
    match result {
        Ok(keys) => {
            // 计算分页
            let total = keys.len();
            let start = (page - 1) * per_page;
            let end = std::cmp::min(start + per_page, total);
            
            let paginated_keys = if start < total {
                keys[start..end].to_vec()
            } else {
                Vec::new()
            };
            
            // 获取工作流定义
            let mut workflows = Vec::new();
            
            for key in paginated_keys {
                if let Ok(Some(workflow)) = state.storage.get::<WorkflowDefinition>(&key).await {
                    let description = workflow.metadata.get("description").cloned();
                    let created_at = workflow.metadata.get("created_at")
                        .cloned()
                        .unwrap_or_else(|| chrono::Utc::now().to_rfc3339());
                        
                    workflows.push(WorkflowSummary {
                        id: workflow.id,
                        name: workflow.name,
                        version: workflow.version,
                        description,
                        created_at,
                        node_count: workflow.nodes.len(),
                        edge_count: workflow.edges.len(),
                    });
                }
            }
            
            // 返回响应
            let response = WorkflowListResponse {
                workflows,
                total,
                page,
                per_page,
            };
            
            Json(response).into_response()
        },
        Err(e) => {
            (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({
                    "error": format!("Failed to list workflows: {}", e)
                }))
            ).into_response()
        }
    }
}

/// 获取工作流定义
async fn get_workflow(
    State(state): State<Arc<ApiState>>,
    Path(workflow_id): Path<String>,
) -> impl IntoResponse {
    match state.storage.get::<WorkflowDefinition>(&format!("workflow:{}", workflow_id)).await {
        Ok(Some(workflow)) => {
            Json(workflow).into_response()
        },
        Ok(None) => {
            (
                StatusCode::NOT_FOUND,
                Json(serde_json::json!({
                    "error": format!("Workflow not found: {}", workflow_id)
                }))
            ).into_response()
        },
        Err(e) => {
            (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({
                    "error": format!("Failed to get workflow: {}", e)
                }))
            ).into_response()
        }
    }
}

/// 创建工作流
async fn create_workflow(
    State(state): State<Arc<ApiState>>,
    Json(req): Json<CreateWorkflowRequest>,
) -> impl IntoResponse {
    // 解析YAML定义
    let dsl_result = DslParser::parse_yaml(&req.yaml_definition);
    
    match dsl_result {
        Ok(dsl) => {
            // 编译为工作流定义
            match DslParser::compile(&dsl) {
                Ok(mut workflow) => {
                    // 更新名称和元数据
                    workflow.name = req.name;
                    
                    if let Some(description) = req.description {
                        workflow.metadata.insert("description".to_string(), description);
                    }
                    
                    workflow.metadata.insert("created_at".to_string(), chrono::Utc::now().to_rfc3339());
                    
                    // 保存工作流定义
                    match state.storage.put(&format!("workflow:{}", workflow.id), &workflow).await {
                        Ok(_) => {
                            // 返回成功响应
                            let response = CreateWorkflowResponse {
                                id: workflow.id,
                                name: workflow.name,
                                version: workflow.version,
                            };
                            
                            (StatusCode::CREATED, Json(response)).into_response()
                        },
                        Err(e) => {
                            (
                                StatusCode::INTERNAL_SERVER_ERROR,
                                Json(serde_json::json!({
                                    "error": format!("Failed to save workflow: {}", e)
                                }))
                            ).into_response()
                        }
                    }
                },
                Err(e) => {
                    (
                        StatusCode::BAD_REQUEST,
                        Json(serde_json::json!({
                            "error": format!("Failed to compile workflow: {}", e)
                        }))
                    ).into_response()
                }
            }
        },
        Err(e) => {
            (
                StatusCode::BAD_REQUEST,
                Json(serde_json::json!({
                    "error": format!("Failed to parse YAML: {}", e)
                }))
            ).into_response()
        }
    }
}

/// 删除工作流
async fn delete_workflow(
    State(state): State<Arc<ApiState>>,
    Path(workflow_id): Path<String>,
) -> impl IntoResponse {
    // 检查是否存在
    match state.storage.get::<WorkflowDefinition>(&format!("workflow:{}", workflow_id)).await {
        Ok(Some(_)) => {
            // 删除工作流定义
            match state.storage.delete(&format!("workflow:{}", workflow_id)).await {
                Ok(true) => {
                    // 返回成功响应
                    Json(ActionResponse {
                        success: true,
                        message: format!("Workflow {} deleted", workflow_id),
                    }).into_response()
                },
                Ok(false) => {
                    (
                        StatusCode::NOT_FOUND,
                        Json(serde_json::json!({
                            "error": format!("Workflow not found: {}", workflow_id)
                        }))
                    ).into_response()
                },
                Err(e) => {
                    (
                        StatusCode::INTERNAL_SERVER_ERROR,
                        Json(serde_json::json!({
                            "error": format!("Failed to delete workflow: {}", e)
                        }))
                    ).into_response()
                }
            }
        },
        Ok(None) => {
            (
                StatusCode::NOT_FOUND,
                Json(serde_json::json!({
                    "error": format!("Workflow not found: {}", workflow_id)
                }))
            ).into_response()
        },
        Err(e) => {
            (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({
                    "error": format!("Failed to check workflow: {}", e)
                }))
            ).into_response()
        }
    }
}

/// 列出工作流实例
async fn list_instances(
    State(state): State<Arc<ApiState>>,
    Query(params): Query<PaginationParams>,
) -> impl IntoResponse {
    let page = params.page.unwrap_or(1);
    let per_page = params.per_page.unwrap_or(10);
    
    // 列出实例键
    let result = state.storage.list_keys("instance:").await;
    
    match result {
        Ok(keys) => {
            // 计算分页
            let total = keys.len();
            let start = (page - 1) * per_page;
            let end = std::cmp::min(start + per_page, total);
            
            let paginated_keys = if start < total {
                keys[start..end].to_vec()
            } else {
                Vec::new()
            };
            
            // 获取实例
            let mut instances = Vec::new();
            
            for key in paginated_keys {
                if let Ok(Some(instance)) = state.storage.get::<crate::model::WorkflowInstance>(&key).await {
                    // 获取工作流名称
                    let workflow_name = if let Ok(Some(workflow)) = state.storage.get::<WorkflowDefinition>(&format!("workflow:{}", instance.definition_id)).await {
                        workflow.name
                    } else {
                        "Unknown".to_string()
                    };
                    
                    // 计算节点完成数
                    let completed_node_count = instance.node_states.values()
                        .filter(|s| s.state == "COMPLETED")
                        .count();
                        
                    instances.push(InstanceSummary {
                        id: instance.id,
                        workflow_id: instance.definition_id,
                        workflow_name,
                        state: instance.state,
                        created_at: instance.created_at.to_rfc3339(),
                        updated_at: instance.updated_at.to_rfc3339(),
                        node_count: instance.node_states.len(),
                        completed_node_count,
                    });
                }
            }
            
            // 返回响应
            let response = InstanceListResponse {
                instances,
                total,
                page,
                per_page,
            };
            
            Json(response).into_response()
        },
        Err(e) => {
            (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({
                    "error": format!("Failed to list instances: {}", e)
                }))
            ).into_response()
        }
    }
}

/// 获取工作流实例
async fn get_instance(
    State(state): State<Arc<ApiState>>,
    Path(instance_id): Path<String>,
) -> impl IntoResponse {
    match state.engine.get_workflow_instance(&instance_id).await {
        Ok(instance) => {
            Json(instance).into_response()
        },
        Err(e) => {
            (
                StatusCode::NOT_FOUND,
                Json(serde_json::json!({
                    "error": format!("Instance not found: {}", e)
                }))
            ).into_response()
        }
    }
}

/// 启动工作流实例
async fn start_workflow(
    State(state): State<Arc<ApiState>>,
    Json(req): Json<StartWorkflowRequest>,
) -> impl IntoResponse {
    // 获取初始变量
    let variables = req.variables.unwrap_or_default();
    
    // 启动工作流实例
    match state.engine.start_workflow(&req.workflow_id, variables).await {
        Ok(instance) => {
            // 返回成功响应
            let response = StartWorkflowResponse {
                instance_id: instance.id,
                workflow_id: instance.definition_id,
                state: instance.state,
            };
            
            (StatusCode::CREATED, Json(response)).into_response()
        },
        Err(e) => {
            (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({
                    "error": format!("Failed to start workflow: {}", e)
                }))
            ).into_response()
        }
    }
}

/// 取消工作流实例
async fn cancel_instance(
    State(state): State<Arc<ApiState>>,
    Path(instance_id): Path<String>,
) -> impl IntoResponse {
    match state.engine.cancel_workflow(&instance_id).await {
        Ok(_) => {
            // 返回成功响应
            Json(ActionResponse {
                success: true,
                message: format!("Instance {} cancelled", instance_id),
            }).into_response()
        },
        Err(e) => {
            (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({
                    "error": format!("Failed to cancel instance: {}", e)
                }))
            ).into_response()
        }
    }
}

/// 恢复工作流实例
async fn resume_instance(
    State(state): State<Arc<ApiState>>,
    Path(instance_id): Path<String>,
) -> impl IntoResponse {
    match state.engine.resume_workflow(&instance_id).await {
        Ok(_) => {
            // 返回成功响应
            Json(ActionResponse {
                success: true,
                message: format!("Instance {} resumed", instance_id),
            }).into_response()
        },
        Err(e) => {
            (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({
                    "error": format!("Failed to resume instance: {}", e)
                }))
            ).into_response()
        }
    }
}

/// 健康检查
async fn health_check() -> impl IntoResponse {
    Json(serde_json::json!({
        "status": "ok",
        "version": env!("CARGO_PKG_VERSION"),
        "timestamp": chrono::Utc::now().to_rfc3339(),
    }))
}

/// 创建API路由
fn create_api_routes(state: Arc<ApiState>) -> Router {
    Router::new()
        // 工作流定义API
        .route("/api/workflows", get(list_workflows))
        .route("/api/workflows", post(create_workflow))
        .route("/api/workflows/:id", get(get_workflow))
        .route("/api/workflows/:id", delete(delete_workflow))
        
        // 工作流实例API
        .route("/api/instances", get(list_instances))
        .route("/api/instances", post(start_workflow))
        .route("/api/instances/:id", get(get_instance))
        .route("/api/instances/:id/cancel", post(cancel_instance))
        .route("/api/instances/:id/resume", post(resume_instance))
        
        // 健康检查
        .route("/api/health", get(health_check))
        
        // 中间件
        .layer(TraceLayer::new_for_http())
        .layer(CorsLayer::permissive())
        .with_state(state)
}

/// 启动API服务
pub async fn start_api_server(
    engine: Arc<WorkflowExecutionEngine>,
    storage: Arc<StorageManager>,
    bind_address: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    // 创建API状态
    let state = Arc::new(ApiState {
        engine,
        storage,
    });
    
    // 创建路由
    let app = create_api_routes(state);
    
    // 解析地址
    let addr = bind_address.parse()?;
    
    // 启动服务器
    info!("API server listening on {}", bind_address);
    axum::Server::bind(&addr)
        .serve(app.into_make_service())
        .await?;
        
    Ok(())
}
```

## 总结与未来发展方向

通过上述设计与实现，我们构建了一个功能完善、高度可扩展的分布式工作流框架，该框架充分利用了Rust的类型系统和性能优势，实现了以下核心特性：

1. **语义层次化工作流模型**：支持工作流的分层组织和语义化标记，便于理解和管理复杂工作流。

2. **自我感知与适应性**：通过资源监控和行为追踪，实现工作流的自我感知和动态调整。

3. **多种执行模式**：同时支持同步、异步、并发和并行执行模式，满足不同场景需求。

4. **基于 Petri 网的动态拓扑**：使用 Petri 网模型实现工作流的动态拓扑结构，支持复杂的流程控制。

5. **全面的容错与恢复机制**：通过断路器、重试策略和检查点等机制，实现系统的高可用性和容错性。

6. **完善的监控与追踪**：集成现代可观测性工具，实现工作流全过程的监控和追踪。

7. **友好的前端界面与API**：提供直观的Web界面和RESTful API，简化工作流的管理和操作。

### 未来发展方向

1. **强化分布式协调**：进一步增强分布式环境下的一致性保障和故障恢复能力。

2. **AI辅助工作流设计**：集成机器学习模型，实现智能化的工作流推荐和优化。

3. **跨语言执行支持**：扩展任务执行能力，支持多种编程语言编写的任务。

4. **增强WebAssembly集成**：利用WebAssembly实现更安全、更高效的工作流执行环境。

5. **增强云原生能力**：深度集成Kubernetes和云服务商API，提供更强大的云原生部署和管理能力。

6. **工作流数据分析**：增加数据分析组件，提供工作流执行的历史分析和性能优化建议。

7. **事件驱动架构集成**：增强与事件驱动架构的集成，支持更丰富的事件触发模式和复杂事件处理。

这个设计充分展示了Rust在建构高性能、类型安全的分布式系统方面的优势，同时也体现了先进的工作流管理理念和最佳实践。通过这个框架，开发者可以构建出高度可靠、可维护和可扩展的分布式工作流应用。
