# 分布式工作流执行引擎设计方案

## 目录

- [分布式工作流执行引擎设计方案](#分布式工作流执行引擎设计方案)
  - [目录](#目录)
  - [思维导图-text](#思维导图-text)
  - [1. 总体架构](#1-总体架构)
    - [1.1 架构概览](#11-架构概览)
    - [1.2 核心组件](#12-核心组件)
    - [1.3 设计原则](#13-设计原则)
  - [2. 工作流定义模型](#2-工作流定义模型)
    - [2.1 工作流定义结构](#21-工作流定义结构)
    - [2.2 步骤类型](#22-步骤类型)
    - [2.3 转换和条件](#23-转换和条件)
    - [2.4 事件处理器](#24-事件处理器)
  - [3. 分布式事件总线](#3-分布式事件总线)
    - [3.1 事件模型](#31-事件模型)
    - [3.2 多种消息队列集成](#32-多种消息队列集成)
    - [3.3 工作流间编排](#33-工作流间编排)
    - [3.4 事件订阅与处理](#34-事件订阅与处理)
  - [4. 任务调度与执行](#4-任务调度与执行)
    - [4.1 任务模型](#41-任务模型)
    - [4.2 调度策略](#42-调度策略)
    - [4.3 分布式任务协调](#43-分布式任务协调)
    - [4.4 弹性与自动扩展](#44-弹性与自动扩展)
  - [5. 状态管理与持久化](#5-状态管理与持久化)
    - [5.1 事务性工作流执行](#51-事务性工作流执行)
    - [5.2 分布式锁](#52-分布式锁)
    - [5.3 状态一致性保证](#53-状态一致性保证)
    - [5.4 存储策略](#54-存储策略)
  - [6. 故障恢复机制](#6-故障恢复机制)
    - [6.1 失败检测](#61-失败检测)
    - [6.2 补偿策略](#62-补偿策略)
    - [6.3 节点故障恢复](#63-节点故障恢复)
    - [6.4 事务补偿](#64-事务补偿)
  - [7. 可视化与监控](#7-可视化与监控)
    - [7.1 实时可视化架构](#71-实时可视化架构)
    - [7.2 D3.js集成](#72-d3js集成)
    - [7.3 指标采集与展示](#73-指标采集与展示)
    - [7.4 警报机制](#74-警报机制)
  - [8. API与集成方案](#8-api与集成方案)
    - [8.1 RESTful API](#81-restful-api)
    - [8.2 WebSocket接口](#82-websocket接口)
    - [8.3 SDK集成](#83-sdk集成)
    - [8.4 第三方系统集成](#84-第三方系统集成)
  - [9. 安全与访问控制](#9-安全与访问控制)
    - [9.1 身份验证](#91-身份验证)
    - [9.2 授权模型](#92-授权模型)
    - [9.3 数据加密](#93-数据加密)
    - [9.4 审计跟踪](#94-审计跟踪)
  - [10. 形式化验证与证明](#10-形式化验证与证明)
    - [10.1 工作流属性验证](#101-工作流属性验证)
    - [10.2 死锁检测](#102-死锁检测)
    - [10.3 Petri网模型](#103-petri网模型)
    - [10.4 时间和资源约束验证](#104-时间和资源约束验证)
  - [11. 部署与运维](#11-部署与运维)
    - [11.1 容器化部署](#111-容器化部署)
    - [11.2 Kubernetes集成](#112-kubernetes集成)
    - [11.3 配置管理](#113-配置管理)
    - [11.4 升级策略](#114-升级策略)
  - [12. 性能优化](#12-性能优化)
    - [12.1 并行执行优化](#121-并行执行优化)
    - [12.2 缓存策略](#122-缓存策略)
    - [12.3 批处理优化](#123-批处理优化)
    - [12.4 异步计算优化](#124-异步计算优化)
  - [13. 可观测性设计](#13-可观测性设计)
    - [13.1 分布式追踪](#131-分布式追踪)
    - [13.3 指标收集](#133-指标收集)
  - [14. 系统集成设计](#14-系统集成设计)
    - [14.1 REST API接口](#141-rest-api接口)
    - [14.2 WebSocket接口](#142-websocket接口)
    - [14.3 命令行接口](#143-命令行接口)
  - [15. 部署与扩展设计](#15-部署与扩展设计)
    - [15.1 容器化部署](#151-容器化部署)
    - [15.2 Kubernetes部署](#152-kubernetes部署)
    - [15.3 扩展与高可用设计](#153-扩展与高可用设计)
  - [16. 总结与展望](#16-总结与展望)
    - [16.1 系统整体架构回顾](#161-系统整体架构回顾)
    - [16.2 主要特性与优势](#162-主要特性与优势)
    - [16.3 未来发展方向](#163-未来发展方向)

## 思维导图-text

```text
分布式工作流执行引擎
├── 总体架构
│   ├── 微服务组件式设计
│   ├── 事件驱动架构
│   └── 多层次扩展性
├── 工作流定义模型
│   ├── 声明式工作流定义
│   ├── 多种步骤类型支持
│   ├── 条件转换与并行控制
│   └── 人机交互集成点
├── 分布式事件总线
│   ├── 多消息队列适配器
│   │   ├── Kafka
│   │   ├── NATS
│   │   ├── RabbitMQ
│   │   └── MQTT
│   ├── 事件持久化与重放
│   ├── 工作流间事件依赖
│   └── 跨节点事件路由
├── 任务调度与执行
│   ├── 分布式任务队列
│   ├── 优先级调度
│   ├── 资源感知调度
│   └── 负载均衡策略
├── 状态管理与持久化
│   ├── 分布式事务支持
│   ├── 乐观与悲观锁机制
│   ├── 状态机模型
│   └── 多存储引擎适配
├── 故障恢复机制
│   ├── 节点故障检测
│   ├── 任务重试策略
│   ├── 补偿事务
│   └── 一致性恢复点
├── 可视化与监控
│   ├── WebSocket实时数据流
│   ├── D3.js交互式可视化
│   ├── 自定义视图与布局
│   └── 历史回放功能
├── API与集成
│   ├── RESTful API
│   ├── WebSocket接口
│   ├── 语言SDK
│   └── 第三方系统连接器
├── 安全与访问控制
│   ├── 基于角色的访问控制
│   ├── 数据加密与脱敏
│   ├── 审计日志
│   └── 合规性支持
├── 形式化验证与证明
│   ├── Petri网模型分析
│   ├── 时态逻辑属性检验
│   ├── 资源约束分析
│   └── 可达性与终止性证明
├── 部署与运维
│   ├── 容器化部署
│   ├── Kubernetes原生支持
│   ├── 滚动更新策略
│   └── 自动伸缩配置
└── 性能优化
    ├── 并行执行管道
    ├── 多级缓存策略
    ├── 批处理与合并
    └── 资源隔离机制
```

## 1. 总体架构

### 1.1 架构概览

分布式工作流执行引擎采用微服务架构，以事件驱动模式构建，确保高可扩展性和弹性。核心架构分为以下几个层次：

1. **接入层**：提供RESTful API、WebSocket、SDK接口
2. **协调层**：负责工作流管理、任务调度和资源分配
3. **执行层**：执行各类工作流任务
4. **存储层**：持久化工作流定义和执行状态
5. **消息层**：基于多种消息队列的事件总线
6. **监控层**：提供可视化、监控和告警功能

![架构图]

### 1.2 核心组件

1. **工作流管理器**：处理工作流定义注册、版本控制和生命周期管理
2. **任务调度器**：分配任务到执行节点，处理优先级和负载均衡
3. **分布式事件总线**：提供多种消息队列适配，支持事件路由和过滤
4. **状态管理器**：维护工作流和任务状态，处理分布式锁和一致性
5. **执行引擎**：运行各类任务，包括活动、决策、并行和人工任务
6. **可视化引擎**：提供实时工作流状态可视化和监控
7. **形式验证器**：验证工作流模型的正确性和属性合规性

### 1.3 设计原则

1. **事件驱动**：系统各组件通过事件进行松耦合通信
2. **状态不可变**：工作流状态变更通过追加事件而非直接修改
3. **确定性**：相同输入和事件序列产生相同结果
4. **弹性恢复**：从任何崩溃点恢复而不丢失状态
5. **可扩展性**：各组件可独立水平扩展
6. **多租户**：支持多组织隔离
7. **插件化**：核心框架加插件架构，易于扩展

## 2. 工作流定义模型

### 2.1 工作流定义结构

```rust
pub struct WorkflowDefinition {
    pub id: String,
    pub name: String,
    pub version: String,
    pub description: Option<String>,
    pub input_schema: Option<JsonSchema>,
    pub output_schema: Option<JsonSchema>,
    pub steps: Vec<WorkflowStep>,
    pub transitions: Vec<Transition>,
    pub event_handlers: Vec<EventHandler>,
    pub human_intervention_points: Vec<HumanInterventionPoint>,
    pub default_error_policy: ErrorPolicy,
    pub timeout: Option<Timeout>,
    pub tags: HashMap<String, String>,
    pub metadata: HashMap<String, String>,
}
```

工作流定义采用声明式结构，明确分离步骤定义和流程控制（转换）。支持JSON Schema验证输入输出，增强类型安全性。

### 2.2 步骤类型

1. **活动步骤**：执行特定业务逻辑
2. **决策步骤**：基于条件选择路径
3. **并行步骤**：并行执行多个分支
4. **等待步骤**：等待外部事件
5. **计时器步骤**：延迟执行
6. **人工步骤**：需要人工干预
7. **子工作流步骤**：嵌套其他工作流
8. **脚本步骤**：执行自定义脚本
9. **服务调用步骤**：调用外部服务API

每种步骤类型都有特定的属性和行为模式，确保表达力和灵活性。

### 2.3 转换和条件

工作流使用显式转换定义控制流，支持条件转换、错误转换和默认转换：

```rust
pub struct Transition {
    pub id: String,
    pub from: String,  // 源步骤ID
    pub to: String,    // 目标步骤ID
    pub condition: String,  // 条件表达式
    pub priority: u32,  // 条件优先级
    pub metadata: HashMap<String, String>,
}
```

条件表达式支持：

- JSONPath查询
- 数学和逻辑运算
- 函数调用
- 上下文变量访问

### 2.4 事件处理器

工作流可以定义事件处理器，响应内部或外部事件：

```rust
pub struct EventHandler {
    pub id: String,
    pub event_type: String,  // 事件类型
    pub condition: Option<String>,  // 可选过滤条件
    pub actions: Vec<EventAction>,  // 触发的动作
    pub timeout: Option<Timeout>,
}

pub enum EventAction {
    StartWorkflow { workflow_id: String, input_mapping: Option<HashMap<String, String>> },
    SignalWorkflow { execution_id: String, signal_name: String, data: Option<serde_json::Value> },
    TriggerStep { step_id: String },
    CancelWorkflow { execution_id: String },
    PauseWorkflow { execution_id: String },
    ResumeWorkflow { execution_id: String },
    Custom { action_type: String, parameters: HashMap<String, serde_json::Value> },
}
```

这允许工作流对系统内外的事件做出响应，实现松耦合的事件驱动架构。

## 3. 分布式事件总线

### 3.1 事件模型

事件采用统一格式，确保一致处理：

```rust
pub struct Event {
    pub id: String,
    pub event_type: String,
    pub source: String,
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub correlation_id: Option<String>,
    pub causation_id: Option<String>,
    pub data: Option<serde_json::Value>,
    pub metadata: HashMap<String, String>,
    pub target_node: Option<String>,
}
```

事件类型包括：

- 系统事件（节点启动/关闭）
- 工作流事件（工作流创建/完成/失败）
- 步骤事件（步骤开始/完成/失败）
- 任务事件（任务创建/调度/完成）
- 用户事件（人工任务操作）
- 外部事件（集成系统触发）

### 3.2 多种消息队列集成

事件总线设计为适配器模式，支持多种消息队列：

```rust
pub trait MessageBroker: Send + Sync {
    fn publish(&self, topic: &str, event: &Event) -> Result<(), BrokerError>;
    fn subscribe(&self, topic: &str, handler: Box<dyn Fn(Event) -> BoxFuture<'static, ()> + Send + Sync>) -> Result<SubscriptionHandle, BrokerError>;
    fn unsubscribe(&self, handle: SubscriptionHandle) -> Result<(), BrokerError>;
}

pub struct KafkaBroker { /* ... */ }
pub struct NatsBroker { /* ... */ }
pub struct RabbitMQBroker { /* ... */ }
pub struct MqttBroker { /* ... */ }
pub struct RedisPubSubBroker { /* ... */ }
```

实现特定适配器，处理每种消息队列的特性：

**Kafka适配器**：

- 使用消费者组实现负载均衡
- 利用分区实现顺序保证
- 提供持久化和重放能力

**NATS适配器**：

- 利用JetStream持久化
- 使用NATS主题通配符实现灵活订阅
- 低延迟消息传递

**MQTT适配器**：

- 支持QoS级别
- 利用主题层次结构
- 适用于资源受限环境

统一的消息队列抽象使系统可以根据需求选择最合适的消息技术。

### 3.3 工作流间编排

事件总线提供工作流间编排能力：

```rust
pub async fn create_workflow_dependency(
    &self,
    trigger_workflow_id: &str,
    trigger_condition: Option<String>,
    target_workflow_id: &str,
    input_mapping: Option<HashMap<String, String>>,
) -> Result<DependencyId, WorkflowError>
```

这允许基于事件创建工作流依赖链：

1. 当触发工作流满足指定条件时发出事件
2. 事件总线路由事件到对应订阅者
3. 目标工作流接收事件并启动

支持的依赖关系：

- 完成后依赖：工作流A完成后触发工作流B
- 条件依赖：工作流A在特定条件下触发工作流B
- 事件依赖：工作流A发出特定事件触发工作流B
- 错误依赖：工作流A失败时触发工作流B

### 3.4 事件订阅与处理

事件总线提供丰富的事件订阅能力：

```rust
pub async fn subscribe<F>(
    &self, 
    event_pattern: &str, 
    callback: F
) -> Result<SubscriptionId, EventBusError>
where F: Fn(Event) -> BoxFuture<'static, ()> + Send + Sync + 'static
```

支持：

- 精确匹配：`workflow.completed.workflow-123`
- 通配符：`workflow.*.workflow-123`
- 过滤条件：`step.completed.#[$.metadata.retry_count > 3]`
- 聚合：多个事件模式组合

事件处理可以是同步或异步的，支持重试策略和死信处理。

## 4. 任务调度与执行

### 4.1 任务模型

任务表示工作流步骤的具体执行单元：

```rust
pub struct Task {
    pub id: String,
    pub execution_id: String,
    pub workflow_id: String,
    pub parent_id: Option<String>,
    pub step_id: Option<String>,
    pub task_type: TaskType,
    pub state: TaskState,
    pub priority: Priority,
    pub workflow: Option<Arc<WorkflowDefinition>>,
    pub input: Option<serde_json::Value>,
    pub result: Option<serde_json::Value>,
    pub version: u64,
    pub created_at: chrono::DateTime<chrono::Utc>,
    pub scheduled_at: Option<chrono::DateTime<chrono::Utc>>,
    pub started_at: Option<chrono::DateTime<chrono::Utc>>,
    pub completed_at: Option<chrono::DateTime<chrono::Utc>>,
    pub last_heartbeat_at: Option<chrono::DateTime<chrono::Utc>>,
    pub assigned_node: Option<String>,
    pub retry_count: u32,
    pub cancellation_requested: bool,
    pub pause_requested: bool,
    pub resume_requested: bool,
}
```

任务生命周期状态：

1. **Pending**：等待调度
2. **Scheduled**：已调度待执行
3. **Running**：正在执行
4. **Completed**：成功完成
5. **Failed**：执行失败
6. **Canceled**：已取消
7. **WaitingForEvent**：等待事件
8. **WaitingForTimer**：等待计时器
9. **WaitingForHumanIntervention**：等待人工处理

### 4.2 调度策略

工作流调度器支持多种策略：

1. **优先级调度**：基于任务优先级分配资源
2. **公平调度**：确保所有工作流获得公平资源分配
3. **资源感知调度**：考虑节点负载和资源容量
4. **亲和性调度**：相关任务分配到同一节点提高局部性
5. **截止时间调度**：基于任务截止时间优先级
6. **批处理调度**：合并相似任务减少开销

```rust
pub trait SchedulingStrategy: Send + Sync {
    fn select_tasks(&self, available_tasks: &[Task], node_capacity: &NodeCapacity) -> Vec<Task>;
    fn calculate_priority(&self, task: &Task) -> u32;
}
```

不同策略可以组合使用，适应不同工作负载特性。

### 4.3 分布式任务协调

分布式任务协调包括：

1. **任务分配**：将任务分配给合适的执行节点
2. **心跳监控**：检测执行节点活跃状态
3. **任务重新平衡**：在节点加入/离开时重新分配任务
4. **任务接管**：从失败节点接管任务

```rust
pub struct TaskCoordinator {
    node_manager: Arc<NodeManager>,
    task_queue: Arc<TaskQueue>,
    lock_manager: Arc<LockManager>,
    event_bus: Arc<dyn MessageBroker>,
}
```

协调器确保任务在分布式环境中的可靠执行，处理节点故障和负载变化。

### 4.4 弹性与自动扩展

系统支持工作负载变化下的弹性扩展：

1. **节点自动发现**：新节点自动加入集群
2. **容量规划**：基于历史和当前负载预测资源需求
3. **自动扩缩容**：根据队列积压和资源利用率触发扩缩容
4. **热点检测**：识别和处理负载不均衡

```rust
pub struct CapacityPlanner {
    metrics_collector: Arc<MetricsCollector>,
    node_manager: Arc<NodeManager>,
    config: CapacityPlannerConfig,
}

impl CapacityPlanner {
    pub async fn analyze_and_plan(&self) -> Vec<ScalingAction> {
        // 分析当前负载
        // 预测未来需求
        // 生成扩缩容计划
    }
}
```

与Kubernetes集成，实现基于自定义指标的自动伸缩。

## 5. 状态管理与持久化

### 5.1 事务性工作流执行

工作流执行需要事务保证：

1. **原子性**：步骤要么完全执行，要么完全不执行
2. **一致性**：执行前后工作流状态保持一致
3. **隔离性**：并发工作流执行互不干扰
4. **持久性**：完成的步骤结果永久保存

实现方法：

- 事件溯源模式
- 补偿事务
- 两阶段提交（必要时）

```rust
pub struct TransactionManager {
    storage: Arc<dyn WorkflowStorage>,
    lock_manager: Arc<LockManager>,
}

impl TransactionManager {
    pub async fn execute_in_transaction<F, T>(&self, execution_id: &str, operation: F) -> Result<T, TransactionError>
    where F: FnOnce() -> BoxFuture<'static, Result<T, WorkflowError>> + Send + 'static
    {
        // 获取分布式锁
        // 读取当前状态
        // 执行操作
        // 验证状态一致性
        // 提交或回滚
    }
}
```

### 5.2 分布式锁

分布式锁确保多节点协调：

```rust
pub struct LockManager {
    redis_client: Option<redis::Client>,
    etcd_client: Option<etcd_client::Client>,
    zookeeper_client: Option<zookeeper::ZooKeeper>,
    lock_type: LockType,
}

impl LockManager {
    pub async fn acquire_lock(&self, resource_id: &str, owner: &str, ttl_seconds: u64) -> Result<Lock, LockError> {
        // 根据配置的锁类型获取分布式锁
    }
    
    pub async fn release_lock(&self, lock: &Lock) -> Result<(), LockError> {
        // 释放锁
    }
    
    pub async fn refresh_lock(&self, lock: &Lock) -> Result<Lock, LockError> {
        // 刷新锁TTL
    }
}
```

支持多种锁实现：

- Redis锁（SETNX + TTL）
- Etcd锁（lease机制）
- ZooKeeper锁（临时节点）
- 数据库锁（SELECT FOR UPDATE）

### 5.3 状态一致性保证

通过多种机制确保状态一致性：

1. **版本控制**：乐观并发控制
2. **检查点**：定期保存一致性快照
3. **事件日志**：维护所有状态变更的日志
4. **幂等操作**：相同操作重复执行产生相同结果

```rust
pub struct StateManager {
    storage: Arc<dyn WorkflowStorage>,
    event_bus: Arc<dyn MessageBroker>,
    lock_manager: Arc<LockManager>,
}

impl StateManager {
    pub async fn update_task_state(&self, task: &Task, new_state: TaskState) -> Result<Task, StateError> {
        // 获取锁
        // 检查版本
        // 应用状态变更
        // 发布事件
        // 更新存储
    }
}
```

### 5.4 存储策略

系统支持多种存储策略与引擎：

1. **关系型数据库**：PostgreSQL, MySQL
2. **文档数据库**：MongoDB
3. **键值存储**：Redis
4. **分布式存储**：Cassandra, DynamoDB
5. **对象存储**：S3兼容存储

```rust
pub trait WorkflowStorage: Send + Sync {
    async fn save_workflow_definition(&self, definition: &WorkflowDefinition) -> Result<(), StorageError>;
    async fn get_workflow_definition(&self, workflow_id: &str) -> Result<WorkflowDefinition, StorageError>;
    async fn save_task(&self, task: &Task) -> Result<(), StorageError>;
    async fn get_task(&self, task_id: &str) -> Result<Task, StorageError>;
    async fn update_task(&self, task: &Task) -> Result<(), StorageError>;
    async fn get_tasks_by_state(&self, states: &[TaskState], limit: usize) -> Result<Vec<Task>, StorageError>;
    // 其他存储方法...
}
```

存储适配器处理不同数据库的特性，并封装查询逻辑。

## 6. 故障恢复机制

### 6.1 失败检测

系统实现多层次失败检测：

1. **任务级检测**：心跳超时、错误返回
2. **节点级检测**：心跳检测、网络诊断
3. **系统级检测**：关联错误分析、异常模式识别

```rust
pub struct FailureDetector {
    node_manager: Arc<NodeManager>,
    event_bus: Arc<dyn MessageBroker>,
    task_queue: Arc<TaskQueue>,
    config: FailureDetectorConfig,
}

impl FailureDetector {
    pub async fn start(&self) {
        // 启动周期性检测
        loop {
            self.detect_node_failures().await;
            self.detect_task_failures().await;
            tokio::time::sleep(self.config.check_interval).await;
        }
    }
    
    async fn detect_node_failures(&self) {
        // 检查所有节点心跳
        // 标记可疑节点
        // 执行节点健康检查
        // 处理确认的节点故障
    }
    
    async fn detect_task_failures(&self) {
        // 检查长时间运行的任务
        // 验证心跳是否超时
        // 标记失败任务
    }
}
```

### 6.2 补偿策略

任务失败时的补偿策略：

1. **重试策略**：指数退避、有界重试
2. **备选路径**：备用执行路径
3. **补偿操作**：执行相反操作撤销效果
4. **手动干预**：人工解决复杂失败

```rust
pub enum CompensationStrategy {
    Retry { 
        max_attempts: u32, 
        backoff_coefficient: f64,
        initial_interval_ms: u64,
        max_interval_ms: u64
    },
    AlternativePath { 
        step_id: String 
    },
    CompensatingAction {
        action_type: String,
        parameters: HashMap<String, serde_json::Value>
    },
    HumanIntervention {
        intervention_point_id: String
    },
    FailWorkflow,
    ContinueWorkflow
}
```

补偿策略可以定义在工作流、步骤或活动级别，形成层次化错误处理：

```rust
impl WorkflowDefinition {
    pub fn get_compensation_strategy(&self, step_id: &str, error_type: &str) -> CompensationStrategy {
        // 先检查步骤特定错误类型的策略
        // 然后检查步骤默认策略
        // 最后回退到工作流默认策略
    }
}
```

### 6.3 节点故障恢复

处理执行节点故障的机制：

1. **检测**：通过心跳超时、连接失败检测节点故障
2. **任务接管**：重新分配失败节点的任务
3. **状态恢复**：从最后已知状态恢复
4. **幂等性保证**：确保重复执行不产生副作用

```rust
pub struct NodeFailureHandler {
    node_manager: Arc<NodeManager>,
    task_queue: Arc<TaskQueue>,
    event_bus: Arc<dyn MessageBroker>,
    lock_manager: Arc<LockManager>,
}

impl NodeFailureHandler {
    pub async fn handle_node_failure(&self, node_id: &str) -> Result<(), WorkflowError> {
        // 获取节点锁，防止竞争条件
        let lock = self.lock_manager.acquire_lock(&format!("node:{}", node_id), "failure_handler", 60).await?;
        
        // 检索节点上运行的任务
        let node_tasks = self.task_queue.get_tasks_by_node(node_id).await?;
        
        // 对每个任务进行处理
        for task in node_tasks {
            match task.state {
                TaskState::Running => {
                    // 将运行中任务重置为待处理
                    let mut updated_task = task.clone();
                    updated_task.state = TaskState::Pending;
                    updated_task.assigned_node = None;
                    
                    // 增加版本号，确保并发控制
                    updated_task.version += 1;
                    
                    // 更新任务并发布事件
                    self.task_queue.update_task(&updated_task).await?;
                    
                    let event = TaskRecoveredEvent {
                        task_id: task.id.clone(),
                        execution_id: task.execution_id.clone(),
                        workflow_id: task.workflow_id.clone(),
                        failed_node_id: node_id.to_string(),
                        timestamp: chrono::Utc::now(),
                    };
                    
                    self.event_bus.publish("task.recovered", &event).await?;
                },
                TaskState::Scheduled => {
                    // 类似处理，将已调度任务重置
                },
                _ => {
                    // 其他状态的任务不需要特殊处理
                }
            }
        }
        
        // 将节点标记为不可用
        self.node_manager.mark_node_unavailable(node_id).await?;
        
        // 释放节点锁
        self.lock_manager.release_lock(&lock).await?;
        
        Ok(())
    }
}
```

### 6.4 事务补偿

对于需要保持一致性的跨系统操作，实现分布式事务与补偿：

```rust
pub struct CompensationManager {
    storage: Arc<dyn WorkflowStorage>,
    event_bus: Arc<dyn MessageBroker>,
}

impl CompensationManager {
    pub async fn register_compensation_action(
        &self, 
        execution_id: &str, 
        step_id: &str, 
        compensation_action: CompensationAction
    ) -> Result<(), WorkflowError> {
        // 记录补偿动作，用于失败恢复
        self.storage.save_compensation_action(execution_id, step_id, &compensation_action).await?;
        Ok(())
    }
    
    pub async fn execute_compensation(
        &self, 
        execution_id: &str, 
        from_step_id: &str
    ) -> Result<(), WorkflowError> {
        // 获取需要补偿的步骤列表（逆序）
        let steps = self.storage.get_completed_steps_after(execution_id, from_step_id).await?;
        
        // 按照相反顺序执行补偿动作
        for step in steps.iter().rev() {
            if let Some(compensation_action) = self.storage.get_compensation_action(execution_id, &step.id).await? {
                // 执行补偿动作
                self.execute_action(&compensation_action).await?;
                
                // 更新补偿状态
                self.storage.mark_step_compensated(execution_id, &step.id).await?;
            }
        }
        
        // 发布补偿完成事件
        let event = WorkflowCompensatedEvent {
            execution_id: execution_id.to_string(),
            from_step_id: from_step_id.to_string(),
            timestamp: chrono::Utc::now(),
        };
        
        self.event_bus.publish("workflow.compensated", &event).await?;
        
        Ok(())
    }
    
    async fn execute_action(&self, action: &CompensationAction) -> Result<(), WorkflowError> {
        match action {
            CompensationAction::ServiceCall { url, method, headers, body } => {
                // 执行HTTP调用
            },
            CompensationAction::DatabaseRevert { query, parameters } => {
                // 执行数据库操作
            },
            CompensationAction::MessagePublish { topic, message } => {
                // 发布消息
            },
            CompensationAction::Custom { action_type, parameters } => {
                // 执行自定义补偿逻辑
            }
        }
    }
}
```

支持的补偿模式：

- **向前恢复**：继续执行直到成功
- **向后恢复**：撤销已完成步骤的效果
- **混合模式**：部分补偿后继续

## 7. 可视化与监控

### 7.1 实时可视化架构

实时可视化架构基于以下组件：

1. **WebSocket服务器**：推送实时状态更新
2. **可视化引擎**：生成工作流视图
3. **事件处理器**：订阅工作流状态变更
4. **指标收集器**：收集性能和状态指标

```rust
pub struct VisualizationServer {
    visualization_engine: Arc<VisualizationEngine>,
    event_bus: Arc<dyn MessageBroker>,
    active_connections: Arc<RwLock<HashMap<String, Vec<mpsc::UnboundedSender<Result<warp::ws::Message, warp::Error>>>>>>,
}

impl VisualizationServer {
    pub fn new(visualization_engine: Arc<VisualizationEngine>, event_bus: Arc<dyn MessageBroker>) -> Self {
        let server = Self {
            visualization_engine,
            event_bus,
            active_connections: Arc::new(RwLock::new(HashMap::new())),
        };
        
        // 启动事件监听器，订阅相关事件并推送更新
        tokio::spawn(server.start_event_listener());
        
        server
    }
    
    async fn start_event_listener(&self) {
        let connections = self.active_connections.clone();
        let vis_engine = self.visualization_engine.clone();
        
        // 订阅工作流状态变更事件
        self.event_bus.subscribe("workflow.*", move |event| {
            let conns = connections.clone();
            let vis = vis_engine.clone();
            
            Box::pin(async move {
                // 从事件中提取工作流ID和执行ID
                let workflow_id = event.metadata.get("workflow_id").cloned();
                let execution_id = event.metadata.get("execution_id").cloned();
                
                if let (Some(wf_id), Some(exec_id)) = (workflow_id, execution_id) {
                    // 构建可视化更新
                    let update = VisualizationUpdate {
                        event_type: event.event_type.clone(),
                        workflow_id: wf_id.clone(),
                        execution_id: exec_id.clone(),
                        timestamp: event.timestamp.to_rfc3339(),
                        data: event.data.clone(),
                    };
                    
                    // 尝试获取更详细的视图
                    let view_update = match vis.generate_incremental_view(&wf_id, &exec_id, &event).await {
                        Ok(view) => serde_json::to_string(&view).unwrap_or_else(|_| 
                            serde_json::to_string(&update).unwrap_or_default()),
                        Err(_) => serde_json::to_string(&update).unwrap_or_default(),
                    };
                    
                    // 推送到所有连接
                    let mut connections = conns.write().await;
                    
                    // 处理工作流和执行ID连接
                    for connection_key in [wf_id.clone(), format!("{}:{}", wf_id, exec_id)] {
                        if let Some(senders) = connections.get_mut(&connection_key) {
                            senders.retain(|sender| {
                                sender.send(Ok(warp::ws::Message::text(view_update.clone()))).is_ok()
                            });
                        }
                    }
                }
            })
        }).await.unwrap();
        
        // 订阅步骤状态变更事件
        self.event_bus.subscribe("step.*", /* 类似的处理逻辑 */).await.unwrap();
        
        // 订阅任务状态变更事件
        self.event_bus.subscribe("task.*", /* 类似的处理逻辑 */).await.unwrap();
    }
    
    pub fn ws_routes(&self) -> impl Filter<Extract = impl warp::Reply, Error = warp::Rejection> + Clone {
        let connections = self.active_connections.clone();
        let vis_engine = self.visualization_engine.clone();
        
        // 为工作流定义创建WebSocket路由
        let workflow_route = warp::path!("ws" / "workflow" / String)
            .and(warp::ws())
            .map(move |workflow_id: String, ws: warp::ws::Ws| {
                let connections = connections.clone();
                let vis_engine = vis_engine.clone();
                
                ws.on_upgrade(move |websocket| async move {
                    Self::handle_workflow_connection(websocket, workflow_id, connections, vis_engine).await;
                })
            });
            
        // 为工作流执行创建WebSocket路由
        let execution_route = warp::path!("ws" / "execution" / String / String)
            .and(warp::ws())
            .map(move |workflow_id: String, execution_id: String, ws: warp::ws::Ws| {
                let connections = connections.clone();
                let vis_engine = vis_engine.clone();
                
                ws.on_upgrade(move |websocket| async move {
                    Self::handle_execution_connection(websocket, workflow_id, execution_id, connections, vis_engine).await;
                })
            });
            
        workflow_route.or(execution_route)
    }
    
    async fn handle_workflow_connection(
        websocket: warp::ws::WebSocket,
        workflow_id: String,
        connections: Arc<RwLock<HashMap<String, Vec<mpsc::UnboundedSender<Result<warp::ws::Message, warp::Error>>>>>>,
        vis_engine: Arc<VisualizationEngine>
    ) {
        // 处理单个工作流的WebSocket连接
        // 拆分发送和接收
        // 注册连接到活动连接中
        // 发送初始视图
        // 处理客户端消息
    }
    
    async fn handle_execution_connection(
        websocket: warp::ws::WebSocket,
        workflow_id: String,
        execution_id: String,
        connections: Arc<RwLock<HashMap<String, Vec<mpsc::UnboundedSender<Result<warp::ws::Message, warp::Error>>>>>>,
        vis_engine: Arc<VisualizationEngine>
    ) {
        // 类似上面，但专注于特定执行实例
    }
}
```

### 7.2 D3.js集成

系统提供了与D3.js无缝集成的客户端库：

```javascript
// 工作流可视化D3.js集成
class WorkflowVisualizer {
    constructor(options) {
        this.containerId = options.containerId;
        this.workflowId = options.workflowId;
        this.executionId = options.executionId;
        this.serverUrl = options.serverUrl || window.location.origin;
        this.layoutType = options.layoutType || 'dagre'; // 'dagre', 'force', 'tree'
        this.theme = options.theme || 'light';
        
        // D3可视化状态
        this.svg = null;
        this.mainGroup = null;
        this.nodeElements = null;
        this.linkElements = null;
        this.simulation = null;
        
        // 数据模型
        this.nodes = [];
        this.links = [];
        this.nodeMap = new Map();
        
        // 初始化
        this.initializeVisualization();
        this.connectWebSocket();
    }
    
    initializeVisualization() {
        const container = d3.select(`#${this.containerId}`);
        
        // 清空容器
        container.html('');
        
        // 创建SVG
        this.svg = container.append('svg')
            .attr('width', '100%')
            .attr('height', '800px')
            .attr('class', `workflow-visualization ${this.theme}`);
            
        // 添加缩放和平移支持
        const zoom = d3.zoom()
            .scaleExtent([0.1, 4])
            .on('zoom', (event) => {
                this.mainGroup.attr('transform', event.transform);
            });
            
        this.svg.call(zoom);
        
        // 创建主要图形组
        this.mainGroup = this.svg.append('g');
        
        // 添加标记定义（箭头等）
        const defs = this.svg.append('defs');
        
        defs.append('marker')
            .attr('id', 'arrowhead')
            .attr('viewBox', '0 -5 10 10')
            .attr('refX', 20)
            .attr('refY', 0)
            .attr('orient', 'auto')
            .attr('markerWidth', 10)
            .attr('markerHeight', 10)
            .append('path')
            .attr('d', 'M0,-5L10,0L0,5')
            .attr('class', 'arrow');
            
        // 添加图例
        this.createLegend();
    }
    
    connectWebSocket() {
        const wsUrl = this.serverUrl.replace(/^http/, 'ws');
        const wsEndpoint = this.executionId 
            ? `${wsUrl}/ws/execution/${this.workflowId}/${this.executionId}`
            : `${wsUrl}/ws/workflow/${this.workflowId}`;
            
        this.ws = new WebSocket(wsEndpoint);
        
        this.ws.onopen = () => {
            console.log('WebSocket连接已建立');
            
            // 请求完整视图数据
            this.ws.send(JSON.stringify({
                request_type: 'get_full_view',
                include_metrics: true,
                include_history: true
            }));
        };
        
        this.ws.onmessage = (event) => {
            const data = JSON.parse(event.data);
            
            if (data.view_type) {
                // 完整视图更新
                this.handleFullViewUpdate(data);
            } else {
                // 增量更新
                this.handleIncrementalUpdate(data);
            }
        };
        
        this.ws.onerror = (error) => {
            console.error('WebSocket错误:', error);
        };
        
        this.ws.onclose = () => {
            console.log('WebSocket连接已关闭');
            // 5秒后尝试重新连接
            setTimeout(() => this.connectWebSocket(), 5000);
        };
    }
    
    handleFullViewUpdate(viewData) {
        // 处理完整视图更新
        this.buildGraphData(viewData);
        this.renderGraph();
    }
    
    handleIncrementalUpdate(updateData) {
        // 处理增量更新
        if (updateData.node_updates) {
            this.updateNodes(updateData.node_updates);
        }
        
        if (updateData.link_updates) {
            this.updateLinks(updateData.link_updates);
        }
    }
    
    buildGraphData(viewData) {
        // 从视图数据构建图形数据
        this.nodes = [];
        this.links = [];
        this.nodeMap.clear();
        
        if (viewData.definition) {
            // 从工作流定义构建节点
            viewData.definition.steps.forEach(step => {
                const node = {
                    id: step.id,
                    name: step.name || step.id,
                    type: step.step_type,
                    state: viewData.node_states[step.id] || 'not_started',
                    data: step
                };
                
                this.nodes.push(node);
                this.nodeMap.set(node.id, node);
            });
            
            // 从工作流定义构建连接
            viewData.definition.transitions.forEach(transition => {
                // 确保源节点和目标节点存在
                if (this.nodeMap.has(transition.from) && this.nodeMap.has(transition.to)) {
                    const link = {
                        id: `${transition.from}-${transition.to}`,
                        source: transition.from,
                        target: transition.to,
                        condition: transition.condition,
                        data: transition
                    };
                    
                    this.links.push(link);
                }
            });
        }
    }
    
    renderGraph() {
        // 根据所选布局渲染图形
        switch (this.layoutType) {
            case 'dagre':
                this.renderDagreLayout();
                break;
            case 'force':
                this.renderForceLayout();
                break;
            case 'tree':
                this.renderTreeLayout();
                break;
            default:
                this.renderDagreLayout();
        }
    }
    
    renderDagreLayout() {
        // 使用dagre布局算法
        const g = new dagre.graphlib.Graph();
        g.setGraph({ rankdir: 'LR', align: 'UL', nodesep: 50, edgesep: 15, ranksep: 75 });
        g.setDefaultEdgeLabel(() => ({}));
        
        // 添加节点
        this.nodes.forEach(node => {
            g.setNode(node.id, { width: 120, height: 50, label: node.name });
        });
        
        // 添加边
        this.links.forEach(link => {
            g.setEdge(link.source, link.target);
        });
        
        // 计算布局
        dagre.layout(g);
        
        // 更新节点位置
        this.nodes.forEach(node => {
            const dagreNode = g.node(node.id);
            node.x = dagreNode.x;
            node.y = dagreNode.y;
        });
        
        // 渲染图形
        this.renderGraphElements();
    }
    
    renderForceLayout() {
        // 使用D3力导向布局
        const simulation = d3.forceSimulation(this.nodes)
            .force('link', d3.forceLink(this.links).id(d => d.id).distance(150))
            .force('charge', d3.forceManyBody().strength(-500))
            .force('center', d3.forceCenter(
                this.svg.node().clientWidth / 2, 
                this.svg.node().clientHeight / 2
            ))
            .on('tick', () => this.updatePositions());
            
        this.simulation = simulation;
        
        // 渲染图形
        this.renderGraphElements();
    }
    
    renderTreeLayout() {
        // 使用D3树形布局
        // 首先找出根节点
        const rootId = this.findRootNode();
        if (!rootId) return;
        
        // 构建层次结构
        const hierarchy = this.buildHierarchy(rootId);
        
        // 创建树形布局
        const treeLayout = d3.tree()
            .size([this.svg.node().clientHeight * 0.9, this.svg.node().clientWidth * 0.9])
            .nodeSize([50, 120]);
            
        // 计算布局
        const rootNode = d3.hierarchy(hierarchy);
        const treeNodes = treeLayout(rootNode);
        
        // 更新节点位置
        treeNodes.descendants().forEach(d => {
            const node = this.nodeMap.get(d.data.id);
            if (node) {
                node.x = d.y;  // 交换x和y，使树水平
                node.y = d.x;
            }
        });
        
        // 渲染图形
        this.renderGraphElements();
    }
    
    renderGraphElements() {
        // 清除现有元素
        this.mainGroup.selectAll('*').remove();
        
        // 创建连接线组
        const linksGroup = this.mainGroup.append('g').attr('class', 'links');
        
        // 创建链接线
        this.linkElements = linksGroup.selectAll('.link')
            .data(this.links, d => d.id)
            .enter()
            .append('path')
            .attr('class', d => `link ${d.data ? d.data.condition : ''}`)
            .attr('marker-end', 'url(#arrowhead)')
            .on('mouseover', (event, d) => this.showLinkTooltip(event, d))
            .on('mouseout', () => this.hideTooltip());
            
        // 更新连接线位置
        this.updateLinkPaths();
        
        // 创建节点组
        const nodesGroup = this.mainGroup.append('g').attr('class', 'nodes');
        
        // 创建节点
        this.nodeElements = nodesGroup.selectAll('.node')
            .data(this.nodes, d => d.id)
            .enter()
            .append('g')
            .attr('class', d => `node ${d.type} ${d.state}`)
            .attr('transform', d => `translate(${d.x},${d.y})`)
            .call(d3.drag()
                .on('start', this.dragStarted.bind(this))
                .on('drag', this.dragged.bind(this))
                .on('end', this.dragEnded.bind(this))
            )
            .on('click', (event, d) => this.onNodeClick(event, d))
            .on('mouseover', (event, d) => this.showNodeTooltip(event, d))
            .on('mouseout', () => this.hideTooltip());
            
        // 添加节点背景
        this.nodeElements.append('rect')
            .attr('rx', 5)
            .attr('ry', 5)
            .attr('width', 120)
            .attr('height', 50)
            .attr('x', -60)
            .attr('y', -25);
            
        // 添加节点图标
        this.nodeElements.append('text')
            .attr('class', 'icon')
            .attr('x', -40)
            .attr('y', 5)
            .text(d => this.getNodeIcon(d.type));
            
        // 添加节点名称
        this.nodeElements.append('text')
            .attr('class', 'name')
            .attr('x', -25)
            .attr('y', 5)
            .text(d => this.truncateText(d.name, 12));
            
        // 添加状态指示器
        this.nodeElements.append('circle')
            .attr('class', 'status')
            .attr('cx', 45)
            .attr('cy', -15)
            .attr('r', 5);
    }
    
    updatePositions() {
        // 更新节点和连接线位置
        this.nodeElements.attr('transform', d => `translate(${d.x},${d.y})`);
        this.updateLinkPaths();
    }
    
    updateLinkPaths() {
        // 更新连接线路径
        this.linkElements.attr('d', d => {
            const sourceNode = this.nodeMap.get(d.source.id || d.source);
            const targetNode = this.nodeMap.get(d.target.id || d.target);
            
            if (!sourceNode || !targetNode) return '';
            
            // 使用贝塞尔曲线连接节点
            const sourceX = sourceNode.x;
            const sourceY = sourceNode.y;
            const targetX = targetNode.x;
            const targetY = targetNode.y;
            
            // 计算控制点
            const dx = targetX - sourceX;
            const dy = targetY - sourceY;
            const controlX = sourceX + dx * 0.5;
            const controlY = sourceY + dy * 0.5;
            
            return `M${sourceX},${sourceY} Q${controlX},${controlY} ${targetX},${targetY}`;
        });
    }
    
    updateNodes(nodeUpdates) {
        // 应用节点更新
        nodeUpdates.forEach(update => {
            const node = this.nodeMap.get(update.id);
            if (node) {
                // 更新节点状态
                node.state = update.state;
                
                // 更新节点样式
                d3.select(`.node[data-id="${update.id}"]`)
                    .attr('class', `node ${node.type} ${node.state}`);
                    
                // 如果有动画需要
                if (update.state === 'running') {
                    this.animateNode(update.id);
                }
            }
        });
    }
    
    // 更多方法：拖拽处理、点击处理、工具提示、动画等
}
```

关键客户端库功能：

1. **多种布局**：支持DAG、力导向、树形等布局
2. **主题定制**：支持多种可视化主题
3. **交互功能**：缩放、平移、点击、拖拽
4. **实时更新**：增量更新减少网络开销
5. **动态过滤**：选择特定视图和细节级别
6. **响应式设计**：适应不同屏幕尺寸

### 7.3 指标采集与展示

系统提供全面的指标采集和展示：

```rust
pub struct MetricsCollector {
    prometheus_registry: prometheus::Registry,
    metrics_cache: Arc<RwLock<HashMap<String, HashMap<String, f64>>>>,
    event_bus: Arc<dyn MessageBroker>,
    storage: Arc<dyn WorkflowStorage>,
}

impl MetricsCollector {
    pub fn new(event_bus: Arc<dyn MessageBroker>, storage: Arc<dyn WorkflowStorage>) -> Self {
        let registry = prometheus::Registry::new();
        
        // 注册各种指标
        // 工作流指标
        let workflow_executions = prometheus::IntCounterVec::new(
            prometheus::opts!("workflow_executions_total", "工作流执行总数"),
            &["workflow_id", "status"]
        ).unwrap();
        
        let workflow_duration = prometheus::HistogramVec::new(
            prometheus::HistogramOpts::new("workflow_duration_seconds", "工作流执行时间")
                .buckets(vec![0.1, 0.5, 1.0, 5.0, 10.0, 30.0, 60.0, 120.0, 300.0, 600.0]),
            &["workflow_id"]
        ).unwrap();
        
        // 步骤指标
        let step_executions = prometheus::IntCounterVec::new(
            prometheus::opts!("step_executions_total", "步骤执行总数"),
            &["workflow_id", "step_id", "status"]
        ).unwrap();
        
        let step_duration = prometheus::HistogramVec::new(
            prometheus::HistogramOpts::new("
# 分布式工作流执行引擎设计方案（续）

## 7. 可视化与监控（续）

### 7.3 指标采集与展示（续）

```rust
        let step_duration = prometheus::HistogramVec::new(
            prometheus::HistogramOpts::new("step_duration_seconds", "步骤执行时间")
                .buckets(vec![0.01, 0.05, 0.1, 0.5, 1.0, 5.0, 10.0, 30.0, 60.0]),
            &["workflow_id", "step_id", "step_type"]
        ).unwrap();
        
        // 任务指标
        let task_queue_size = prometheus::IntGaugeVec::new(
            prometheus::opts!("task_queue_size", "任务队列大小"),
            &["state", "priority"]
        ).unwrap();
        
        let task_processing_time = prometheus::HistogramVec::new(
            prometheus::HistogramOpts::new("task_processing_time_seconds", "任务处理时间")
                .buckets(vec![0.001, 0.005, 0.01, 0.05, 0.1, 0.5, 1.0, 5.0]),
            &["task_type"]
        ).unwrap();
        
        // 节点指标
        let node_tasks = prometheus::IntGaugeVec::new(
            prometheus::opts!("node_active_tasks", "节点活跃任务数"),
            &["node_id"]
        ).unwrap();
        
        let node_cpu_usage = prometheus::GaugeVec::new(
            prometheus::opts!("node_cpu_usage", "节点CPU使用率"),
            &["node_id"]
        ).unwrap();
        
        let node_memory_usage = prometheus::GaugeVec::new(
            prometheus::opts!("node_memory_usage", "节点内存使用率"),
            &["node_id"]
        ).unwrap();
        
        // 事件总线指标
        let events_published = prometheus::IntCounterVec::new(
            prometheus::opts!("events_published_total", "已发布事件总数"),
            &["event_type"]
        ).unwrap();
        
        let event_processing_time = prometheus::HistogramVec::new(
            prometheus::HistogramOpts::new("event_processing_time_seconds", "事件处理时间")
                .buckets(vec![0.001, 0.005, 0.01, 0.05, 0.1, 0.5]),
            &["event_type"]
        ).unwrap();
        
        // 注册所有指标
        registry.register(Box::new(workflow_executions.clone())).unwrap();
        registry.register(Box::new(workflow_duration.clone())).unwrap();
        registry.register(Box::new(step_executions.clone())).unwrap();
        registry.register(Box::new(step_duration.clone())).unwrap();
        registry.register(Box::new(task_queue_size.clone())).unwrap();
        registry.register(Box::new(task_processing_time.clone())).unwrap();
        registry.register(Box::new(node_tasks.clone())).unwrap();
        registry.register(Box::new(node_cpu_usage.clone())).unwrap();
        registry.register(Box::new(node_memory_usage.clone())).unwrap();
        registry.register(Box::new(events_published.clone())).unwrap();
        registry.register(Box::new(event_processing_time.clone())).unwrap();
        
        let collector = Self {
            prometheus_registry: registry,
            metrics_cache: Arc::new(RwLock::new(HashMap::new())),
            event_bus,
            storage,
        };
        
        // 启动指标收集
        tokio::spawn(collector.clone().start_metrics_collection());
        
        collector
    }
    
    async fn start_metrics_collection(&self) {
        // 订阅相关事件以更新指标
        self.event_bus.subscribe("workflow.started", {
            let workflow_executions = self.workflow_executions.clone();
            
            Box::new(move |event| {
                let workflow_id = event.metadata.get("workflow_id").cloned().unwrap_or_default();
                workflow_executions.with_label_values(&[&workflow_id, "started"]).inc();
                Box::pin(async {})
            })
        }).await.unwrap();
        
        self.event_bus.subscribe("workflow.completed", {
            let workflow_executions = self.workflow_executions.clone();
            let workflow_duration = self.workflow_duration.clone();
            
            Box::new(move |event| {
                let workflow_id = event.metadata.get("workflow_id").cloned().unwrap_or_default();
                let duration = event.metadata.get("duration_ms")
                    .and_then(|d| d.parse::<f64>().ok())
                    .unwrap_or(0.0) / 1000.0;  // 转换为秒
                    
                workflow_executions.with_label_values(&[&workflow_id, "completed"]).inc();
                workflow_duration.with_label_values(&[&workflow_id]).observe(duration);
                
                Box::pin(async {})
            })
        }).await.unwrap();
        
        // 类似地订阅其他事件
        // ...
        
        // 定期收集系统状态指标
        loop {
            self.collect_system_metrics().await;
            tokio::time::sleep(tokio::time::Duration::from_secs(15)).await;
        }
    }
    
    async fn collect_system_metrics(&self) {
        // 收集任务队列指标
        let queue_metrics = self.storage.get_task_queue_metrics().await.unwrap_or_default();
        for (state, counts) in queue_metrics {
            for (priority, count) in counts {
                self.task_queue_size.with_label_values(&[&state, &priority]).set(count as i64);
            }
        }
        
        // 收集节点指标
        let node_metrics = self.storage.get_node_metrics().await.unwrap_or_default();
        for (node_id, metrics) in node_metrics {
            if let Some(active_tasks) = metrics.get("active_tasks") {
                self.node_tasks.with_label_values(&[&node_id]).set(*active_tasks as i64);
            }
            
            if let Some(cpu_usage) = metrics.get("cpu_usage") {
                self.node_cpu_usage.with_label_values(&[&node_id]).set(*cpu_usage);
            }
            
            if let Some(memory_usage) = metrics.get("memory_usage") {
                self.node_memory_usage.with_label_values(&[&node_id]).set(*memory_usage);
            }
        }
    }
    
    // 提供Prometheus指标端点的处理函数
    pub fn metrics_handler(&self) -> impl Filter<Extract = impl warp::Reply, Error = warp::Rejection> + Clone {
        warp::path!("metrics")
            .and(warp::get())
            .map(move || {
                let metric_families = self.prometheus_registry.gather();
                let encoder = prometheus::TextEncoder::new();
                let mut buffer = Vec::new();
                encoder.encode(&metric_families, &mut buffer).unwrap();
                
                warp::http::Response::builder()
                    .header("Content-Type", "text/plain")
                    .body(String::from_utf8(buffer).unwrap())
            })
    }
    
    // 获取指定工作流的指标
    pub async fn get_workflow_metrics(&self, workflow_id: &str) -> Result<HashMap<String, serde_json::Value>, WorkflowError> {
        let mut metrics = HashMap::new();
        
        // 收集执行次数
        let execution_count = self.storage.count_workflow_executions(workflow_id).await?;
        metrics.insert("execution_count".to_string(), json!(execution_count));
        
        // 收集平均执行时间
        let avg_duration = self.storage.get_workflow_avg_duration(workflow_id).await?;
        metrics.insert("avg_duration_ms".to_string(), json!(avg_duration));
        
        // 收集成功率
        let success_rate = self.storage.get_workflow_success_rate(workflow_id).await?;
        metrics.insert("success_rate".to_string(), json!(success_rate));
        
        // 收集步骤指标
        let step_metrics = self.storage.get_workflow_step_metrics(workflow_id).await?;
        metrics.insert("steps".to_string(), json!(step_metrics));
        
        // 收集最近执行
        let recent_executions = self.storage.get_recent_workflow_executions(workflow_id, 10).await?;
        metrics.insert("recent_executions".to_string(), json!(recent_executions));
        
        Ok(metrics)
    }
    
    // 获取指定执行实例的指标
    pub async fn get_execution_metrics(&self, execution_id: &str) -> Result<HashMap<String, serde_json::Value>, WorkflowError> {
        // 类似上面，但针对特定执行实例
        // ...
        
        Ok(HashMap::new()) // 简化返回
    }
    
    // 获取系统指标
    pub async fn get_system_metrics(&self) -> Result<HashMap<String, serde_json::Value>, WorkflowError> {
        // 获取系统级指标
        // ...
        
        Ok(HashMap::new()) // 简化返回
    }
}
```

指标数据可通过以下方式访问：

1. **Prometheus集成**：暴露标准Prometheus端点
2. **Grafana仪表板**：预配置的Grafana仪表板
3. **API访问**：直接通过API获取指标
4. **WebSocket推送**：实时指标更新

### 7.4 警报机制

基于收集的指标，系统提供自动告警功能：

```rust
pub struct AlertManager {
    metrics_collector: Arc<MetricsCollector>,
    event_bus: Arc<dyn MessageBroker>,
    storage: Arc<dyn WorkflowStorage>,
    alert_configs: Arc<RwLock<HashMap<String, AlertConfig>>>,
}

pub struct AlertConfig {
    pub id: String,
    pub name: String,
    pub condition: String,
    pub severity: AlertSeverity,
    pub channels: Vec<AlertChannel>,
    pub cooldown_minutes: u32,
    pub description_template: String,
}

pub enum AlertSeverity {
    Info,
    Warning,
    Error,
    Critical,
}

pub enum AlertChannel {
    Email { recipients: Vec<String> },
    Slack { webhook_url: String },
    WebHook { url: String, headers: HashMap<String, String> },
    PagerDuty { routing_key: String },
}

impl AlertManager {
    pub fn new(
        metrics_collector: Arc<MetricsCollector>,
        event_bus: Arc<dyn MessageBroker>,
        storage: Arc<dyn WorkflowStorage>
    ) -> Self {
        let manager = Self {
            metrics_collector,
            event_bus,
            storage,
            alert_configs: Arc::new(RwLock::new(HashMap::new())),
        };
        
        // 启动告警检查循环
        tokio::spawn(manager.clone().start_alert_check_loop());
        
        manager
    }
    
    async fn start_alert_check_loop(&self) {
        loop {
            self.check_alerts().await;
            tokio::time::sleep(tokio::time::Duration::from_secs(60)).await;
        }
    }
    
    async fn check_alerts(&self) {
        let configs = {
            let configs_guard = self.alert_configs.read().await;
            configs_guard.clone()
        };
        
        for (alert_id, config) in configs {
            if let Err(e) = self.check_alert(&config).await {
                log::error!("检查告警失败 {}: {}", alert_id, e);
            }
        }
    }
    
    async fn check_alert(&self, config: &AlertConfig) -> Result<(), WorkflowError> {
        // 评估告警条件
        let condition_met = self.evaluate_condition(&config.condition).await?;
        
        if condition_met {
            // 检查冷却期
            let last_alert = self.storage.get_last_alert(&config.id).await?;
            let now = chrono::Utc::now();
            
            let can_alert = match last_alert {
                Some(alert) => {
                    let cooldown = chrono::Duration::minutes(config.cooldown_minutes as i64);
                    now - alert.triggered_at > cooldown
                },
                None => true,
            };
            
            if can_alert {
                // 生成告警
                let alert = Alert {
                    id: format!("alert-{}", uuid::Uuid::new_v4()),
                    config_id: config.id.clone(),
                    name: config.name.clone(),
                    description: self.render_alert_description(config).await?,
                    severity: config.severity.clone(),
                    triggered_at: now,
                    resolved_at: None,
                };
                
                // 保存告警
                self.storage.save_alert(&alert).await?;
                
                // 发送告警
                self.send_alert(&alert, &config.channels).await?;
                
                // 发布告警事件
                let event = AlertTriggeredEvent {
                    alert_id: alert.id.clone(),
                    alert_name: alert.name.clone(),
                    severity: format!("{:?}", alert.severity),
                    description: alert.description.clone(),
                    timestamp: alert.triggered_at,
                };
                
                self.event_bus.publish("alert.triggered", &event).await?;
            }
        } else {
            // 检查是否需要解决告警
            let active_alerts = self.storage.get_active_alerts_by_config(&config.id).await?;
            
            for alert in active_alerts {
                // 更新告警为已解决
                let mut updated_alert = alert.clone();
                updated_alert.resolved_at = Some(chrono::Utc::now());
                
                // 保存更新
                self.storage.update_alert(&updated_alert).await?;
                
                // 发布告警解决事件
                let event = AlertResolvedEvent {
                    alert_id: alert.id.clone(),
                    alert_name: alert.name.clone(),
                    resolution_time: updated_alert.resolved_at.unwrap(),
                    timestamp: chrono::Utc::now(),
                };
                
                self.event_bus.publish("alert.resolved", &event).await?;
            }
        }
        
        Ok(())
    }
    
    async fn evaluate_condition(&self, condition: &str) -> Result<bool, WorkflowError> {
        // 使用表达式评估引擎解析和评估条件
        // 这里简化实现
        Ok(false)
    }
    
    async fn render_alert_description(&self, config: &AlertConfig) -> Result<String, WorkflowError> {
        // 使用模板引擎渲染告警描述
        // 这里简化实现
        Ok(config.description_template.clone())
    }
    
    async fn send_alert(&self, alert: &Alert, channels: &[AlertChannel]) -> Result<(), WorkflowError> {
        for channel in channels {
            match channel {
                AlertChannel::Email { recipients } => {
                    self.send_email_alert(alert, recipients).await?;
                },
                AlertChannel::Slack { webhook_url } => {
                    self.send_slack_alert(alert, webhook_url).await?;
                },
                AlertChannel::WebHook { url, headers } => {
                    self.send_webhook_alert(alert, url, headers).await?;
                },
                AlertChannel::PagerDuty { routing_key } => {
                    self.send_pagerduty_alert(alert, routing_key).await?;
                },
            }
        }
        
        Ok(())
    }
    
    // 具体发送方法实现
    async fn send_email_alert(&self, alert: &Alert, recipients: &[String]) -> Result<(), WorkflowError> {
        // 发送电子邮件
        // ...
        Ok(())
    }
    
    async fn send_slack_alert(&self, alert: &Alert, webhook_url: &str) -> Result<(), WorkflowError> {
        // 发送Slack消息
        // ...
        Ok(())
    }
    
    async fn send_webhook_alert(&self, alert: &Alert, url: &str, headers: &HashMap<String, String>) -> Result<(), WorkflowError> {
        // 调用webhook
        // ...
        Ok(())
    }
    
    async fn send_pagerduty_alert(&self, alert: &Alert, routing_key: &str) -> Result<(), WorkflowError> {
        // 触发PagerDuty事件
        // ...
        Ok(())
    }
    
    // 添加新的告警配置
    pub async fn add_alert_config(&self, config: AlertConfig) -> Result<(), WorkflowError> {
        let mut configs = self.alert_configs.write().await;
        configs.insert(config.id.clone(), config);
        Ok(())
    }
    
    // 删除告警配置
    pub async fn remove_alert_config(&self, config_id: &str) -> Result<(), WorkflowError> {
        let mut configs = self.alert_configs.write().await;
        configs.remove(config_id);
        Ok(())
    }
}
```

告警系统支持：

- **条件告警**：基于指标和事件的条件触发
- **多渠道通知**：电子邮件、Slack、Webhook、PagerDuty等
- **自动解决**：条件不再满足时自动解决告警
- **告警历史**：维护告警历史记录
- **冷却期**：防止告警风暴
- **模板描述**：动态生成告警内容

## 8. API与集成方案

### 8.1 RESTful API

系统提供全面的RESTful API，支持所有工作流管理操作：

```rust
pub struct ApiServer {
    workflow_service: Arc<WorkflowService>,
    visualization_engine: Arc<VisualizationEngine>,
    metrics_collector: Arc<MetricsCollector>,
    alert_manager: Arc<AlertManager>,
    port: u16,
}

impl ApiServer {
    pub fn new(
        workflow_service: Arc<WorkflowService>,
        visualization_engine: Arc<VisualizationEngine>,
        metrics_collector: Arc<MetricsCollector>,
        alert_manager: Arc<AlertManager>,
        port: u16
    ) -> Self {
        Self {
            workflow_service,
            visualization_engine,
            metrics_collector,
            alert_manager,
            port,
        }
    }
    
    pub async fn start(&self) -> Result<(), WorkflowError> {
        // 构建API路由
        let api_routes = self.build_api_routes();
        
        // 添加CORS支持
        let cors = warp::cors()
            .allow_any_origin()
            .allow_methods(vec!["GET", "POST", "PUT", "DELETE", "PATCH"])
            .allow_headers(vec!["Content-Type", "Authorization"]);
            
        let routes = api_routes.with(cors);
        
        // 启动服务器
        log::info!("启动API服务器在端口 {}", self.port);
        warp::serve(routes).run(([0, 0, 0, 0], self.port)).await;
        
        Ok(())
    }
    
    fn build_api_routes(&self) -> impl Filter<Extract = impl warp::Reply, Error = warp::Rejection> + Clone {
        let workflow_service = self.workflow_service.clone();
        let vis_engine = self.visualization_engine.clone();
        let metrics_collector = self.metrics_collector.clone();
        let alert_manager = self.alert_manager.clone();
        
        // 健康检查路由
        let health_route = warp::path!("health")
            .and(warp::get())
            .map(|| warp::reply::json(&json!({"status": "ok", "version": env!("CARGO_PKG_VERSION")})));
            
        // 指标路由
        let metrics_route = self.metrics_collector.metrics_handler();
        
        // 工作流定义路由
        let workflow_routes = self.build_workflow_routes(workflow_service.clone());
        
        // 工作流执行路由
        let execution_routes = self.build_execution_routes(workflow_service.clone());
        
        // 可视化路由
        let visualization_routes = self.build_visualization_routes(vis_engine);
        
        // 指标API路由
        let metrics_api_routes = self.build_metrics_api_routes(metrics_collector);
        
        // 告警路由
        let alert_routes = self.build_alert_routes(alert_manager);
        
        // 组合所有路由
        health_route
            .or(metrics_route)
            .or(workflow_routes)
            .or(execution_routes)
            .or(visualization_routes)
            .or(metrics_api_routes)
            .or(alert_routes)
            .recover(Self::handle_rejection)
    }
    
    fn build_workflow_routes(&self, service: Arc<WorkflowService>) -> impl Filter<Extract = impl warp::Reply, Error = warp::Rejection> + Clone {
        // 获取所有工作流
        let list_workflows = warp::path!("workflows")
            .and(warp::get())
            .and(warp::query::<HashMap<String, String>>())
            .and(with_service(service.clone()))
            .and_then(Self::handle_list_workflows);
            
        // 创建工作流
        let create_workflow = warp::path!("workflows")
            .and(warp::post())
            .and(warp::body::json())
            .and(with_service(service.clone()))
            .and_then(Self::handle_create_workflow);
            
        // 获取工作流
        let get_workflow = warp::path!("workflows" / String)
            .and(warp::get())
            .and(with_service(service.clone()))
            .and_then(Self::handle_get_workflow);
            
        // 更新工作流
        let update_workflow = warp::path!("workflows" / String)
            .and(warp::put())
            .and(warp::body::json())
            .and(with_service(service.clone()))
            .and_then(Self::handle_update_workflow);
            
        // 删除工作流
        let delete_workflow = warp::path!("workflows" / String)
            .and(warp::delete())
            .and(with_service(service.clone()))
            .and_then(Self::handle_delete_workflow);
            
        // 验证工作流
        let validate_workflow = warp::path!("workflows" / "validate")
            .and(warp::post())
            .and(warp::body::json())
            .and(with_service(service.clone()))
            .and_then(Self::handle_validate_workflow);
            
        list_workflows
            .or(create_workflow)
            .or(get_workflow)
            .or(update_workflow)
            .or(delete_workflow)
            .or(validate_workflow)
    }
    
    fn build_execution_routes(&self, service: Arc<WorkflowService>) -> impl Filter<Extract = impl warp::Reply, Error = warp::Rejection> + Clone {
        // 启动工作流
        let start_workflow = warp::path!("workflows" / "start")
            .and(warp::post())
            .and(warp::body::json())
            .and(with_service(service.clone()))
            .and_then(Self::handle_start_workflow);
            
        // 获取执行历史
        let get_execution_history = warp::path!("workflows" / "executions" / String / "history")
            .and(warp::get())
            .and(with_service(service.clone()))
            .and_then(Self::handle_get_execution_history);
            
        // 获取执行状态
        let get_execution_status = warp::path!("workflows" / "executions" / String)
            .and(warp::get())
            .and(with_service(service.clone()))
            .and_then(Self::handle_get_execution_status);
            
        // 控制工作流执行
        let control_execution = warp::path!("workflows" / "executions" / String / "control")
            .and(warp::post())
            .and(warp::body::json())
            .and(with_service(service.clone()))
            .and_then(Self::handle_control_execution);
            
        // 发送事件
        let send_event = warp::path!("events")
            .and(warp::post())
            .and(warp::body::json())
            .and(with_service(service.clone()))
            .and_then(Self::handle_send_event);
            
        // 人工任务路由
        let human_task_routes = self.build_human_task_routes(service);
        
        start_workflow
            .or(get_execution_history)
            .or(get_execution_status)
            .or(control_execution)
            .or(send_event)
            .or(human_task_routes)
    }
    
    // 更多路由构建方法
    // ...
    
    // API处理方法
    async fn handle_list_workflows(
        query: HashMap<String, String>,
        service: Arc<WorkflowService>
    ) -> Result<impl warp::Reply, warp::Rejection> {
        // 处理参数
        let limit = query.get("limit").and_then(|v| v.parse::<usize>().ok()).unwrap_or(100);
        let offset = query.get("offset").and_then(|v| v.parse::<usize>().ok()).unwrap_or(0);
        let tag = query.get("tag").cloned();
        
        // 调用服务
        match service.list_workflows(limit, offset, tag).await {
            Ok(workflows) => Ok(warp::reply::with_status(
                warp::reply::json(&workflows),
                warp::http::StatusCode::OK,
            )),
            Err(e) => Err(warp::reject::custom(ApiError::from(e))),
        }
    }
    
    // 更多API处理方法
    // ...
    
    // 错误处理
    async fn handle_rejection(err: warp::Rejection) -> Result<impl warp::Reply, warp::Rejection> {
        if let Some(api_error) = err.find::<ApiError>() {
            let status = match api_error.code {
                "not_found" => warp::http::StatusCode::NOT_FOUND,
                "bad_request" => warp::http::StatusCode::BAD_REQUEST,
                "conflict" => warp::http::StatusCode::CONFLICT,
                "unauthorized" => warp::http::StatusCode::UNAUTHORIZED,
                "forbidden" => warp::http::StatusCode::FORBIDDEN,
                _ => warp::http::StatusCode::INTERNAL_SERVER_ERROR,
            };
            
            let json = warp::reply::json(&api_error);
            Ok(warp::reply::with_status(json, status))
        } else if let Some(e) = err.find::<warp::filters::body::BodyDeserializeError>() {
            let error = ApiError {
                code: "bad_request".to_string(),
                message: format!("无效的请求体: {}", e),
                details: None,
            };
            
            Ok(warp::reply::with_status(
                warp::reply::json(&error),
                warp::http::StatusCode::BAD_REQUEST,
            ))
        } else {
            // 其他未处理的错误
            let error = ApiError {
                code: "internal_error".to_string(),
                message: "内部服务器错误".to_string(),
                details: None,
            };
            
            Ok(warp::reply::with_status(
                warp::reply::json(&error),
                warp::http::StatusCode::INTERNAL_SERVER_ERROR,
            ))
        }
    }
}
```

RESTful API设计原则：

- **资源导向**：API围绕核心资源设计
- **标准HTTP方法**：使用GET、POST、PUT、DELETE等
- **标准状态码**：使用适当的HTTP状态码
- **统一错误格式**：一致的错误响应结构
- **版本控制**：支持API版本演进
- **分页与过滤**：支持大型集合的分页和过滤
- **HATEOAS**：提供资源之间的关系链接

### 8.2 WebSocket接口

WebSocket接口提供实时通信能力：

```rust
pub struct WebSocketServer {
    event_bus: Arc<dyn MessageBroker>,
    workflow_service: Arc<WorkflowService>,
    active_connections: Arc<RwLock<HashMap<String, Vec<mpsc::UnboundedSender<Result<warp::ws::Message, warp::Error>>>>>>,
}

impl WebSocketServer {
    pub fn new(event_bus: Arc<dyn MessageBroker>, workflow_service: Arc<WorkflowService>) -> Self {
        Self {
            event_bus,
            workflow_service,
            active_connections: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    pub fn routes(&self) -> impl Filter<Extract = impl warp::Reply, Error = warp::Rejection> + Clone {
        let connections = self.active_connections.clone();
        let event_bus = self.event_bus.clone();
# 分布式工作流执行引擎设计方案（续）

## 8. API与集成方案（续）

### 8.2 WebSocket接口（续）

```rust
    pub fn routes(&self) -> impl Filter<Extract = impl warp::Reply, Error = warp::Rejection> + Clone {
        let connections = self.active_connections.clone();
        let event_bus = self.event_bus.clone();
        let workflow_service = self.workflow_service.clone();
        
        // 工作流执行事件WebSocket
        let execution_ws = warp::path!("ws" / "executions" / String)
            .and(warp::ws())
            .and(with_connections(connections.clone()))
            .and(with_event_bus(event_bus.clone()))
            .and(with_service(workflow_service.clone()))
            .map(|execution_id: String, ws: warp::ws::Ws, connections, event_bus, service| {
                ws.on_upgrade(move |websocket| {
                    Self::handle_execution_connection(websocket, execution_id, connections, event_bus, service)
                })
            });
            
        // 工作流定义事件WebSocket
        let workflow_ws = warp::path!("ws" / "workflows" / String)
            .and(warp::ws())
            .and(with_connections(connections.clone()))
            .and(with_event_bus(event_bus.clone()))
            .map(|workflow_id: String, ws: warp::ws::Ws, connections, event_bus| {
                ws.on_upgrade(move |websocket| {
                    Self::handle_workflow_connection(websocket, workflow_id, connections, event_bus)
                })
            });
            
        // 全局事件WebSocket
        let events_ws = warp::path!("ws" / "events")
            .and(warp::ws())
            .and(with_connections(connections.clone()))
            .and(with_event_bus(event_bus.clone()))
            .map(|ws: warp::ws::Ws, connections, event_bus| {
                ws.on_upgrade(move |websocket| {
                    Self::handle_events_connection(websocket, connections, event_bus)
                })
            });
            
        execution_ws.or(workflow_ws).or(events_ws)
    }
    
    async fn handle_execution_connection(
        websocket: warp::ws::WebSocket,
        execution_id: String,
        connections: Arc<RwLock<HashMap<String, Vec<mpsc::UnboundedSender<Result<warp::ws::Message, warp::Error>>>>>>,
        event_bus: Arc<dyn MessageBroker>,
        service: Arc<WorkflowService>
    ) {
        // 拆分WebSocket为发送和接收部分
        let (mut ws_sender, mut ws_receiver) = websocket.split();
        
        // 创建通道以便从多个任务发送消息到单个WebSocket
        let (tx, rx) = mpsc::unbounded_channel();
        
        // 将消息从通道转发到WebSocket
        tokio::task::spawn(rx.forward(ws_sender).map(|result| {
            if let Err(e) = result {
                log::error!("WebSocket发送错误: {}", e);
            }
        }));
        
        // 注册连接
        {
            let mut conns = connections.write().await;
            let conn_list = conns.entry(format!("execution:{}", execution_id)).or_insert_with(Vec::new);
            conn_list.push(tx.clone());
        }
        
        // 发送初始执行状态
        match service.get_workflow_status(&execution_id).await {
            Ok(status) => {
                if let Ok(json) = serde_json::to_string(&status) {
                    let _ = tx.send(Ok(warp::ws::Message::text(json)));
                }
            },
            Err(e) => {
                log::error!("获取执行状态失败: {}", e);
                let _ = tx.send(Ok(warp::ws::Message::text(format!("{{\"error\": \"{}\"}}", e))));
            }
        }
        
        // 订阅执行相关事件
        let subscription_id = event_bus.subscribe(&format!("execution.{}.#", execution_id), {
            let tx = tx.clone();
            
            Box::new(move |event| {
                let tx = tx.clone();
                
                Box::pin(async move {
                    if let Ok(json) = serde_json::to_string(&event) {
                        let _ = tx.send(Ok(warp::ws::Message::text(json)));
                    }
                })
            })
        }).await.unwrap();
        
        // 处理来自客户端的消息
        while let Some(result) = ws_receiver.next().await {
            match result {
                Ok(msg) => {
                    // 处理客户端消息
                    if let Ok(text) = msg.to_str() {
                        if let Ok(command) = serde_json::from_str::<ClientCommand>(text) {
                            match command.command_type.as_str() {
                                "cancel" => {
                                    let _ = service.cancel_workflow(&execution_id, command.reason).await;
                                },
                                "pause" => {
                                    let _ = service.pause_workflow(&execution_id, command.reason).await;
                                },
                                "resume" => {
                                    let _ = service.resume_workflow(&execution_id, command.reason).await;
                                },
                                "send_event" => {
                                    if let Some(event_data) = command.data {
                                        let _ = service.send_event(
                                            command.event_type.as_deref().unwrap_or("custom"),
                                            event_data,
                                            &execution_id,
                                            command.source
                                        ).await;
                                    }
                                },
                                _ => {
                                    let _ = tx.send(Ok(warp::ws::Message::text(
                                        format!("{{\"error\": \"未知命令: {}\"}}", command.command_type)
                                    )));
                                }
                            }
                        }
                    }
                },
                Err(e) => {
                    log::error!("WebSocket接收错误: {}", e);
                    break;
                }
            }
        }
        
        // 清理: 取消订阅和移除连接
        event_bus.unsubscribe(subscription_id).await.unwrap();
        
        {
            let mut conns = connections.write().await;
            if let Some(conn_list) = conns.get_mut(&format!("execution:{}", execution_id)) {
                conn_list.retain(|x| !std::ptr::eq(&*x, &tx));
                if conn_list.is_empty() {
                    conns.remove(&format!("execution:{}", execution_id));
                }
            }
        }
    }
    
    // 其他WebSocket处理函数...
}

// 用于在Warp过滤器之间传递数据的辅助函数
fn with_connections(
    connections: Arc<RwLock<HashMap<String, Vec<mpsc::UnboundedSender<Result<warp::ws::Message, warp::Error>>>>>>
) -> impl Filter<Extract = (Arc<RwLock<HashMap<String, Vec<mpsc::UnboundedSender<Result<warp::ws::Message, warp::Error>>>>>>,), Error = std::convert::Infallible> + Clone {
    warp::any().map(move || connections.clone())
}

fn with_event_bus(
    event_bus: Arc<dyn MessageBroker>
) -> impl Filter<Extract = (Arc<dyn MessageBroker>,), Error = std::convert::Infallible> + Clone {
    warp::any().map(move || event_bus.clone())
}

fn with_service(
    service: Arc<WorkflowService>
) -> impl Filter<Extract = (Arc<WorkflowService>,), Error = std::convert::Infallible> + Clone {
    warp::any().map(move || service.clone())
}

// 客户端命令模型
#[derive(Debug, Deserialize)]
struct ClientCommand {
    command_type: String,
    execution_id: Option<String>,
    event_type: Option<String>,
    data: Option<serde_json::Value>,
    reason: Option<String>,
    source: Option<String>,
}
```

WebSocket接口提供以下功能：

1. **实时事件订阅**：接收工作流事件的实时更新
2. **命令发送**：通过WebSocket发送控制命令
3. **状态同步**：自动发送初始状态和增量更新
4. **可视化支持**：提供前端可视化所需的实时数据

### 8.3 SDK集成

为简化客户端集成，系统提供多语言SDK：

```rust
// Rust SDK实现示例
pub struct WorkflowClient {
    base_url: String,
    http_client: reqwest::Client,
    ws_client: Option<WebSocketClient>,
    auth_token: Option<String>,
}

impl WorkflowClient {
    pub fn new(base_url: &str) -> Self {
        Self {
            base_url: base_url.to_string(),
            http_client: reqwest::Client::new(),
            ws_client: None,
            auth_token: None,
        }
    }
    
    pub fn with_auth_token(mut self, token: &str) -> Self {
        self.auth_token = Some(token.to_string());
        self
    }
    
    pub async fn list_workflows(&self, limit: Option<usize>, offset: Option<usize>, tag: Option<&str>) -> Result<Vec<WorkflowSummary>, ClientError> {
        let mut url = format!("{}/workflows", self.base_url);
        let mut query_params = Vec::new();
        
        if let Some(limit) = limit {
            query_params.push(format!("limit={}", limit));
        }
        
        if let Some(offset) = offset {
            query_params.push(format!("offset={}", offset));
        }
        
        if let Some(tag) = tag {
            query_params.push(format!("tag={}", tag));
        }
        
        if !query_params.is_empty() {
            url = format!("{}?{}", url, query_params.join("&"));
        }
        
        let mut request = self.http_client.get(&url);
        
        if let Some(token) = &self.auth_token {
            request = request.header("Authorization", format!("Bearer {}", token));
        }
        
        let response = request.send().await?;
        
        if response.status().is_success() {
            let workflows = response.json::<Vec<WorkflowSummary>>().await?;
            Ok(workflows)
        } else {
            let error = response.json::<ApiError>().await?;
            Err(ClientError::ApiError(error))
        }
    }
    
    pub async fn get_workflow(&self, workflow_id: &str) -> Result<WorkflowDefinition, ClientError> {
        let url = format!("{}/workflows/{}", self.base_url, workflow_id);
        
        let mut request = self.http_client.get(&url);
        
        if let Some(token) = &self.auth_token {
            request = request.header("Authorization", format!("Bearer {}", token));
        }
        
        let response = request.send().await?;
        
        if response.status().is_success() {
            let workflow = response.json::<WorkflowDefinition>().await?;
            Ok(workflow)
        } else {
            let error = response.json::<ApiError>().await?;
            Err(ClientError::ApiError(error))
        }
    }
    
    pub async fn create_workflow(&self, definition: &WorkflowDefinition) -> Result<WorkflowCreatedResponse, ClientError> {
        let url = format!("{}/workflows", self.base_url);
        
        let mut request = self.http_client.post(&url)
            .json(definition);
        
        if let Some(token) = &self.auth_token {
            request = request.header("Authorization", format!("Bearer {}", token));
        }
        
        let response = request.send().await?;
        
        if response.status().is_success() {
            let result = response.json::<WorkflowCreatedResponse>().await?;
            Ok(result)
        } else {
            let error = response.json::<ApiError>().await?;
            Err(ClientError::ApiError(error))
        }
    }
    
    pub async fn start_workflow(&self, request: &StartWorkflowRequest) -> Result<WorkflowStartedResponse, ClientError> {
        let url = format!("{}/workflows/start", self.base_url);
        
        let mut req = self.http_client.post(&url)
            .json(request);
        
        if let Some(token) = &self.auth_token {
            req = req.header("Authorization", format!("Bearer {}", token));
        }
        
        let response = req.send().await?;
        
        if response.status().is_success() {
            let result = response.json::<WorkflowStartedResponse>().await?;
            Ok(result)
        } else {
            let error = response.json::<ApiError>().await?;
            Err(ClientError::ApiError(error))
        }
    }
    
    // 更多API方法...
    
    // WebSocket集成
    pub async fn connect_to_execution(&self, execution_id: &str, handler: Box<dyn Fn(ExecutionEvent) + Send + Sync>) -> Result<WebSocketConnection, ClientError> {
        let ws_url = self.base_url.replace("http", "ws");
        let ws_endpoint = format!("{}/ws/executions/{}", ws_url, execution_id);
        
        let mut request = http::Request::builder()
            .uri(ws_endpoint)
            .header("Upgrade", "websocket")
            .header("Connection", "Upgrade");
            
        if let Some(token) = &self.auth_token {
            request = request.header("Authorization", format!("Bearer {}", token));
        }
        
        // 使用tokio-tungstenite创建WebSocket连接
        // 简化实现，省略具体WebSocket连接代码
        
        Ok(WebSocketConnection { 
            id: execution_id.to_string(),
            // ... 其他字段
        })
    }
}

// 其他语言SDK类似，如JavaScript SDK示例
/*
class WorkflowClient {
    constructor(baseUrl, options = {}) {
        this.baseUrl = baseUrl;
        this.token = options.token;
        this.connections = new Map();
    }
    
    // API方法
    async listWorkflows(options = {}) {
        const queryParams = new URLSearchParams();
        if (options.limit) queryParams.append('limit', options.limit);
        if (options.offset) queryParams.append('offset', options.offset);
        if (options.tag) queryParams.append('tag', options.tag);
        
        const url = `${this.baseUrl}/workflows?${queryParams.toString()}`;
        
        const response = await fetch(url, {
            headers: this._getHeaders()
        });
        
        if (response.ok) {
            return await response.json();
        } else {
            const error = await response.json();
            throw new ClientError(error);
        }
    }
    
    // 更多方法...
    
    // WebSocket连接
    connectToExecution(executionId, callbacks = {}) {
        const wsUrl = this.baseUrl.replace(/^http/, 'ws');
        const wsEndpoint = `${wsUrl}/ws/executions/${executionId}`;
        
        const ws = new WebSocket(wsEndpoint);
        
        ws.onopen = () => {
            callbacks.onOpen && callbacks.onOpen();
        };
        
        ws.onmessage = (event) => {
            const data = JSON.parse(event.data);
            callbacks.onEvent && callbacks.onEvent(data);
        };
        
        ws.onerror = (error) => {
            callbacks.onError && callbacks.onError(error);
        };
        
        ws.onclose = () => {
            callbacks.onClose && callbacks.onClose();
        };
        
        // 保存连接
        this.connections.set(executionId, ws);
        
        return {
            send: (command) => {
                ws.send(JSON.stringify(command));
            },
            close: () => {
                ws.close();
                this.connections.delete(executionId);
            }
        };
    }
    
    _getHeaders() {
        const headers = {
            'Content-Type': 'application/json'
        };
        
        if (this.token) {
            headers['Authorization'] = `Bearer ${this.token}`;
        }
        
        return headers;
    }
}
*/
```

SDK支持的语言：

- **Rust**：原生SDK，提供最完整功能
- **JavaScript/TypeScript**：前端和Node.js集成
- **Python**：数据科学和自动化集成
- **Java**：企业应用集成
- **Go**：云原生应用集成
- **C#**：.NET应用集成

### 8.4 第三方系统集成

系统提供多种集成机制连接第三方系统：

```rust
// 通用第三方系统连接器
pub trait SystemConnector: Send + Sync {
    fn get_name(&self) -> &str;
    fn get_type(&self) -> &str;
    fn supports_activity(&self, activity_type: &str) -> bool;
    fn execute_activity(&self, activity_type: &str, input: &serde_json::Value) -> BoxFuture<'static, Result<serde_json::Value, ConnectorError>>;
    fn supports_event(&self, event_type: &str) -> bool;
    fn subscribe_to_events(&self, event_types: &[String], callback: Box<dyn Fn(ExternalEvent) -> BoxFuture<'static, ()> + Send + Sync>) -> BoxFuture<'static, Result<SubscriptionHandle, ConnectorError>>;
}

// 连接器管理器
pub struct ConnectorManager {
    connectors: Arc<RwLock<HashMap<String, Arc<dyn SystemConnector>>>>,
    event_bus: Arc<dyn MessageBroker>,
}

impl ConnectorManager {
    pub fn new(event_bus: Arc<dyn MessageBroker>) -> Self {
        Self {
            connectors: Arc::new(RwLock::new(HashMap::new())),
            event_bus,
        }
    }
    
    pub async fn register_connector(&self, connector: Arc<dyn SystemConnector>) -> Result<(), ConnectorError> {
        let name = connector.get_name().to_string();
        
        // 注册连接器
        {
            let mut connectors = self.connectors.write().await;
            connectors.insert(name.clone(), connector.clone());
        }
        
        // 订阅连接器支持的事件
        let event_types = {
            let supported_events = vec![
                "github.push", 
                "github.pull_request", 
                "jira.issue_created",
                // 更多第三方系统事件...
            ];
            
            supported_events.into_iter()
                .filter(|event_type| connector.supports_event(event_type))
                .map(|s| s.to_string())
                .collect::<Vec<_>>()
        };
        
        if !event_types.is_empty() {
            let event_bus = self.event_bus.clone();
            
            // 创建外部事件处理器
            connector.subscribe_to_events(&event_types, Box::new(move |external_event| {
                let event_bus = event_bus.clone();
                
                Box::pin(async move {
                    // 转换为内部事件并发布
                    let event = Event {
                        id: format!("evt-{}", uuid::Uuid::new_v4()),
                        event_type: external_event.event_type.clone(),
                        source: format!("external:{}", external_event.source),
                        timestamp: chrono::Utc::now(),
                        correlation_id: None,
                        causation_id: None,
                        data: external_event.data.clone(),
                        metadata: external_event.metadata.clone(),
                        target_node: None,
                    };
                    
                    if let Err(e) = event_bus.publish(&external_event.event_type, &event).await {
                        log::error!("发布外部事件失败: {}", e);
                    }
                })
            })).await?;
        }
        
        // 记录连接器注册
        log::info!("注册连接器: {} (类型: {})", name, connector.get_type());
        
        Ok(())
    }
    
    pub async fn execute_activity(&self, activity_type: &str, input: &serde_json::Value) -> Result<serde_json::Value, ConnectorError> {
        // 查找支持此活动类型的连接器
        let connectors = self.connectors.read().await;
        
        for connector in connectors.values() {
            if connector.supports_activity(activity_type) {
                return connector.execute_activity(activity_type, input).await;
            }
        }
        
        Err(ConnectorError::UnsupportedActivity(activity_type.to_string()))
    }
    
    // 获取所有注册的连接器
    pub async fn get_connectors(&self) -> Vec<ConnectorInfo> {
        let connectors = self.connectors.read().await;
        
        connectors.values()
            .map(|c| ConnectorInfo {
                name: c.get_name().to_string(),
                connector_type: c.get_type().to_string(),
            })
            .collect()
    }
}

// 具体连接器实现示例
pub struct GitHubConnector {
    name: String,
    client: octocrab::Octocrab,
    webhook_secret: String,
}

impl GitHubConnector {
    pub fn new(name: &str, token: &str, webhook_secret: &str) -> Result<Self, ConnectorError> {
        let client = octocrab::OctocrabBuilder::new()
            .personal_token(token.to_string())
            .build()
            .map_err(|e| ConnectorError::InitializationError(format!("GitHub API初始化错误: {}", e)))?;
            
        Ok(Self {
            name: name.to_string(),
            client,
            webhook_secret: webhook_secret.to_string(),
        })
    }
}

impl SystemConnector for GitHubConnector {
    fn get_name(&self) -> &str {
        &self.name
    }
    
    fn get_type(&self) -> &str {
        "github"
    }
    
    fn supports_activity(&self, activity_type: &str) -> bool {
        matches!(activity_type, 
            "github.create_issue" | 
            "github.comment_issue" | 
            "github.create_pr" |
            "github.merge_pr" |
            "github.check_branch_status"
        )
    }
    
    fn execute_activity(&self, activity_type: &str, input: &serde_json::Value) -> BoxFuture<'static, Result<serde_json::Value, ConnectorError>> {
        let client = self.client.clone();
        let input = input.clone();
        
        Box::pin(async move {
            match activity_type {
                "github.create_issue" => {
                    // 提取输入参数
                    let owner = input.get("owner")
                        .and_then(|v| v.as_str())
                        .ok_or_else(|| ConnectorError::InvalidInput("缺少owner参数".to_string()))?;
                        
                    let repo = input.get("repo")
                        .and_then(|v| v.as_str())
                        .ok_or_else(|| ConnectorError::InvalidInput("缺少repo参数".to_string()))?;
                        
                    let title = input.get("title")
                        .and_then(|v| v.as_str())
                        .ok_or_else(|| ConnectorError::InvalidInput("缺少title参数".to_string()))?;
                        
                    let body = input.get("body")
                        .and_then(|v| v.as_str())
                        .unwrap_or("");
                        
                    let labels = input.get("labels")
                        .and_then(|v| v.as_array())
                        .map(|arr| {
                            arr.iter()
                                .filter_map(|v| v.as_str())
                                .map(|s| s.to_string())
                                .collect::<Vec<_>>()
                        })
                        .unwrap_or_default();
                        
                    // 创建Issue
                    let issue = client.issues(owner, repo)
                        .create(title)
                        .body(body)
                        .labels(labels)
                        .send()
                        .await
                        .map_err(|e| ConnectorError::ActivityError(format!("创建Issue失败: {}", e)))?;
                        
                    // 返回结果
                    Ok(json!({
                        "issue_number": issue.number,
                        "issue_url": issue.html_url,
                        "issue_id": issue.id
                    }))
                },
                // 其他活动类型处理...
                _ => Err(ConnectorError::UnsupportedActivity(activity_type.to_string())),
            }
        })
    }
    
    fn supports_event(&self, event_type: &str) -> bool {
        matches!(event_type, 
            "github.push" | 
            "github.pull_request" | 
            "github.issues" |
            "github.release"
        )
    }
    
    fn subscribe_to_events(&self, event_types: &[String], callback: Box<dyn Fn(ExternalEvent) -> BoxFuture<'static, ()> + Send + Sync>) -> BoxFuture<'static, Result<SubscriptionHandle, ConnectorError>> {
        // 在实际实现中，可能需要设置Webhook或轮询
        // 这里简化为返回空的订阅句柄
        Box::pin(async move {
            Ok(SubscriptionHandle { id: uuid::Uuid::new_v4().to_string() })
        })
    }
}

// 类似地，可以实现其他系统的连接器：
// - JiraConnector
// - SlackConnector
// - DockerConnector
// - KubernetesConnector
// - SalesforceConnector
// - DatabaseConnector
// 等等
```

系统提供的预构建集成：

1. **GitHub/GitLab**：代码仓库集成
2. **Jira/Linear**：项目管理集成
3. **Slack/Teams**：通信平台集成
4. **Kubernetes/Docker**：容器平台集成
5. **各类数据库**：SQL和NoSQL数据库
6. **Salesforce/HubSpot**：CRM系统集成
7. **Stripe/PayPal**：支付系统集成
8. **AWS/GCP/Azure**：云服务集成

## 9. 安全与访问控制

### 9.1 身份验证

系统实现强大的身份验证机制：

```rust
pub struct AuthManager {
    jwt_secret: String,
    token_expiration: std::time::Duration,
    storage: Arc<dyn WorkflowStorage>,
}

impl AuthManager {
    pub fn new(
        jwt_secret: &str,
        token_expiration_minutes: u64,
        storage: Arc<dyn WorkflowStorage>
    ) -> Self {
        Self {
            jwt_secret: jwt_secret.to_string(),
            token_expiration: std::time::Duration::from_secs(token_expiration_minutes * 60),
            storage,
        }
    }
    
    pub async fn authenticate_user(&self, username: &str, password: &str) -> Result<String, AuthError> {
        // 验证用户凭据
        let user = self.storage.get_user_by_username(username).await?;
        
        // 验证密码
        if !self.verify_password(&user.password_hash, password)? {
            return Err(AuthError::InvalidCredentials);
        }
        
        // 生成JWT令牌
        self.generate_token(username, &user.roles)
    }
    
    pub fn verify_token(&self, token: &str) -> Result<UserClaims, AuthError> {
        // 验证JWT令牌
        let mut validation = jsonwebtoken::Validation::default();
        validation.leeway = 60; // 1分钟的时间偏差容忍
        
        let token_data = jsonwebtoken::decode::<UserClaims>(
            token,
            &jsonwebtoken::DecodingKey::from_secret(self.jwt_secret.as_bytes()),
            &validation
        ).map_err(|e| match e.kind() {
            jsonwebtoken::errors::ErrorKind::ExpiredSignature => AuthError::TokenExpired,
            jsonwebtoken::errors::ErrorKind::InvalidToken => AuthError::InvalidToken,
            _ => AuthError::TokenValidationError(e.to_string()),
        })?;
        
        Ok(token_data.claims)
    }
    
    fn generate_token(&self, username: &str, roles: &[String]) -> Result<String, AuthError> {
        let expiration = chrono::Utc::now()
            .checked_add_signed(chrono::Duration::from_std(self.token_expiration).unwrap())
            .unwrap();
            
        let claims = UserClaims {
            sub: username.to_string(),
            exp: expiration.timestamp() as usize,
            iat: chrono::Utc::now().timestamp() as usize,
            roles: roles.to_vec(),
        };
        
        let
# 分布式工作流执行引擎设计方案（续）

## 9. 安全与访问控制（续）

### 9.1 身份验证（续）

```rust
    fn generate_token(&self, username: &str, roles: &[String]) -> Result<String, AuthError> {
        let expiration = chrono::Utc::now()
            .checked_add_signed(chrono::Duration::from_std(self.token_expiration).unwrap())
            .unwrap();
            
        let claims = UserClaims {
            sub: username.to_string(),
            exp: expiration.timestamp() as usize,
            iat: chrono::Utc::now().timestamp() as usize,
            roles: roles.to_vec(),
        };
        
        let token = jsonwebtoken::encode(
            &jsonwebtoken::Header::default(),
            &claims,
            &jsonwebtoken::EncodingKey::from_secret(self.jwt_secret.as_bytes())
        ).map_err(|e| AuthError::TokenGenerationError(e.to_string()))?;
        
        Ok(token)
    }
    
    fn verify_password(&self, hashed_password: &str, password: &str) -> Result<bool, AuthError> {
        bcrypt::verify(password, hashed_password)
            .map_err(|e| AuthError::PasswordVerificationError(e.to_string()))
    }
    
    pub async fn create_api_key(&self, username: &str, description: &str, expiration_days: Option<u32>) -> Result<ApiKey, AuthError> {
        // 查询用户
        let user = self.storage.get_user_by_username(username).await?;
        
        // 生成API密钥
        let key = format!("wf-{}", uuid::Uuid::new_v4());
        let secret = format!("{}", uuid::Uuid::new_v4());
        let secret_hash = bcrypt::hash(&secret, bcrypt::DEFAULT_COST)
            .map_err(|e| AuthError::ApiKeyGenerationError(e.to_string()))?;
            
        // 计算过期时间
        let expires_at = expiration_days.map(|days| {
            chrono::Utc::now() + chrono::Duration::days(days as i64)
        });
        
        // 保存API密钥
        let api_key = ApiKey {
            key: key.clone(),
            user_id: user.id.clone(),
            description: description.to_string(),
            secret_hash,
            created_at: chrono::Utc::now(),
            expires_at,
            last_used_at: None,
        };
        
        self.storage.save_api_key(&api_key).await?;
        
        // 返回包含明文密钥的对象（仅此一次返回明文）
        Ok(ApiKey {
            secret_hash: secret,  // 仅用于返回，不会存储明文
            ..api_key
        })
    }
    
    pub async fn authenticate_api_key(&self, key: &str, secret: &str) -> Result<String, AuthError> {
        // 获取API密钥
        let api_key = self.storage.get_api_key(key).await?;
        
        // 检查是否过期
        if let Some(expires_at) = api_key.expires_at {
            if expires_at < chrono::Utc::now() {
                return Err(AuthError::ApiKeyExpired);
            }
        }
        
        // 验证密钥
        if !bcrypt::verify(secret, &api_key.secret_hash)
            .map_err(|e| AuthError::ApiKeyVerificationError(e.to_string()))? {
            return Err(AuthError::InvalidApiKey);
        }
        
        // 更新使用时间
        let mut updated_key = api_key.clone();
        updated_key.last_used_at = Some(chrono::Utc::now());
        self.storage.update_api_key(&updated_key).await?;
        
        // 获取用户
        let user = self.storage.get_user_by_id(&api_key.user_id).await?;
        
        // 生成JWT令牌
        self.generate_token(&user.username, &user.roles)
    }
}

// Warp过滤器，用于要求认证
fn with_auth(auth_manager: Arc<AuthManager>) -> impl Filter<Extract = (UserClaims,), Error = warp::Rejection> + Clone {
    warp::header::<String>("authorization")
        .and(warp::any().map(move || auth_manager.clone()))
        .and_then(|auth_header: String, auth_manager: Arc<AuthManager>| async move {
            if auth_header.starts_with("Bearer ") {
                let token = auth_header.trim_start_matches("Bearer ").trim();
                match auth_manager.verify_token(token) {
                    Ok(claims) => Ok(claims),
                    Err(e) => Err(warp::reject::custom(ApiError::from(e))),
                }
            } else if auth_header.starts_with("ApiKey ") {
                let parts: Vec<&str> = auth_header.trim_start_matches("ApiKey ").split(':').collect();
                if parts.len() == 2 {
                    let key = parts[0];
                    let secret = parts[1];
                    match auth_manager.authenticate_api_key(key, secret).await {
                        Ok(token) => {
                            match auth_manager.verify_token(&token) {
                                Ok(claims) => Ok(claims),
                                Err(e) => Err(warp::reject::custom(ApiError::from(e))),
                            }
                        },
                        Err(e) => Err(warp::reject::custom(ApiError::from(e))),
                    }
                } else {
                    Err(warp::reject::custom(ApiError::invalid_auth("无效的API密钥格式")))
                }
            } else {
                Err(warp::reject::custom(ApiError::invalid_auth("无效的授权头")))
            }
        })
}

// JWT用户声明
#[derive(Debug, Serialize, Deserialize)]
struct UserClaims {
    sub: String,  // 用户名
    exp: usize,   // 过期时间
    iat: usize,   // 签发时间
    roles: Vec<String>,  // 用户角色
}

// API密钥模型
#[derive(Debug, Clone)]
struct ApiKey {
    key: String,
    user_id: String,
    description: String,
    secret_hash: String,
    created_at: chrono::DateTime<chrono::Utc>,
    expires_at: Option<chrono::DateTime<chrono::Utc>>,
    last_used_at: Option<chrono::DateTime<chrono::Utc>>,
}
```

系统支持的认证方法：

1. **用户名/密码**：基本认证方法
2. **JWT令牌**：基于角色的令牌认证
3. **API密钥**：长期API访问
4. **OAuth2**：第三方授权集成
5. **SAML**：企业单点登录

### 9.2 授权模型

基于RBAC(基于角色的访问控制)实现细粒度权限：

```rust
pub struct AuthorizationManager {
    storage: Arc<dyn WorkflowStorage>,
    permission_cache: Arc<RwLock<LruCache<String, Vec<Permission>>>>,
}

impl AuthorizationManager {
    pub fn new(storage: Arc<dyn WorkflowStorage>) -> Self {
        Self {
            storage,
            permission_cache: Arc::new(RwLock::new(LruCache::new(1000))),
        }
    }
    
    pub async fn authorize(
        &self,
        user_claims: &UserClaims,
        resource_type: ResourceType,
        resource_id: Option<&str>,
        action: Action
    ) -> Result<(), AuthError> {
        // 检查是否管理员，管理员拥有所有权限
        if user_claims.roles.contains(&"admin".to_string()) {
            return Ok(());
        }
        
        // 获取用户角色的权限
        let mut has_permission = false;
        
        for role in &user_claims.roles {
            // 检查缓存
            let cache_key = format!("{}:{}", role, resource_type);
            let permissions = {
                let mut cache = self.permission_cache.write().await;
                
                if let Some(perms) = cache.get(&cache_key) {
                    perms.clone()
                } else {
                    // 从存储获取权限
                    let perms = self.storage.get_role_permissions(role, resource_type).await?;
                    cache.put(cache_key, perms.clone());
                    perms
                }
            };
            
            // 检查是否有权限
            for permission in permissions {
                if permission.action == action || permission.action == Action::All {
                    // 如果有特定资源ID，需要检查是否匹配
                    if let Some(res_id) = resource_id {
                        if permission.resource_id.as_deref() == Some(res_id) || permission.resource_id.is_none() {
                            has_permission = true;
                            break;
                        }
                    } else {
                        // 没有特定资源ID，只需要匹配资源类型和操作
                        if permission.resource_id.is_none() {
                            has_permission = true;
                            break;
                        }
                    }
                }
            }
            
            if has_permission {
                break;
            }
        }
        
        if has_permission {
            Ok(())
        } else {
            Err(AuthError::InsufficientPermissions)
        }
    }
    
    // 添加角色权限
    pub async fn add_role_permission(&self, role: &str, permission: Permission) -> Result<(), AuthError> {
        self.storage.add_role_permission(role, &permission).await?;
        
        // 清除缓存
        let cache_key = format!("{}:{}", role, permission.resource_type);
        let mut cache = self.permission_cache.write().await;
        cache.pop(&cache_key);
        
        Ok(())
    }
    
    // 移除角色权限
    pub async fn remove_role_permission(
        &self,
        role: &str,
        resource_type: ResourceType,
        resource_id: Option<&str>,
        action: Action
    ) -> Result<(), AuthError> {
        self.storage.remove_role_permission(role, resource_type, resource_id, action).await?;
        
        // 清除缓存
        let cache_key = format!("{}:{}", role, resource_type);
        let mut cache = self.permission_cache.write().await;
        cache.pop(&cache_key);
        
        Ok(())
    }
    
    // 创建角色
    pub async fn create_role(&self, role_name: &str, description: &str) -> Result<(), AuthError> {
        self.storage.create_role(role_name, description).await?;
        Ok(())
    }
    
    // 为用户分配角色
    pub async fn assign_role_to_user(&self, username: &str, role: &str) -> Result<(), AuthError> {
        self.storage.assign_role_to_user(username, role).await?;
        Ok(())
    }
    
    // 移除用户角色
    pub async fn remove_role_from_user(&self, username: &str, role: &str) -> Result<(), AuthError> {
        self.storage.remove_role_from_user(username, role).await?;
        Ok(())
    }
}

// 资源类型
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ResourceType {
    Workflow,
    WorkflowExecution,
    Task,
    User,
    Role,
    ApiKey,
    SystemConfiguration,
    Connector,
    Metrics,
    Alert,
}

// 操作类型
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Action {
    Create,
    Read,
    Update,
    Delete,
    Execute,
    Cancel,
    Pause,
    Resume,
    SendEvent,
    All,
}

// 权限结构
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Permission {
    pub resource_type: ResourceType,
    pub resource_id: Option<String>,  // 特定资源ID，None表示所有资源
    pub action: Action,
}

// Warp过滤器，用于要求特定权限
fn require_permission(
    auth_manager: Arc<AuthorizationManager>,
    resource_type: ResourceType,
    resource_id: Option<String>,
    action: Action
) -> impl Filter<Extract = (), Error = warp::Rejection> + Clone {
    with_user_claims()
        .and(warp::any().map(move || auth_manager.clone()))
        .and(warp::any().map(move || resource_type.clone()))
        .and(warp::any().map(move || resource_id.clone()))
        .and(warp::any().map(move || action.clone()))
        .and_then(|claims: UserClaims, auth_manager: Arc<AuthorizationManager>, res_type: ResourceType, res_id: Option<String>, action: Action| async move {
            match auth_manager.authorize(&claims, res_type, res_id.as_deref(), action).await {
                Ok(()) => Ok(()),
                Err(e) => Err(warp::reject::custom(ApiError::from(e))),
            }
        })
}

// 获取当前用户声明的过滤器
fn with_user_claims() -> impl Filter<Extract = (UserClaims,), Error = warp::Rejection> + Clone {
    warp::filters::ext::get::<UserClaims>()
        .or_else(|_| async { Err(warp::reject::custom(ApiError::unauthorized("需要认证"))) })
}
```

授权模型特点：

1. **细粒度权限**：控制到特定资源和操作
2. **角色继承**：支持角色之间的继承关系
3. **权限缓存**：提高授权决策性能
4. **动态权限**：支持运行时更改权限
5. **权限委派**：支持临时委派权限

### 9.3 数据加密

系统实现多层数据加密保护：

```rust
pub struct EncryptionManager {
    master_key: [u8; 32],
    keys_cache: Arc<RwLock<LruCache<String, EncryptionKey>>>,
    storage: Arc<dyn WorkflowStorage>,
}

impl EncryptionManager {
    pub fn new(master_key_hex: &str, storage: Arc<dyn WorkflowStorage>) -> Result<Self, EncryptionError> {
        // 解析主密钥
        let master_key = hex::decode(master_key_hex)
            .map_err(|e| EncryptionError::KeyDecodingError(e.to_string()))?;
            
        if master_key.len() != 32 {
            return Err(EncryptionError::InvalidKeyLength);
        }
        
        let mut key_bytes = [0u8; 32];
        key_bytes.copy_from_slice(&master_key);
        
        Ok(Self {
            master_key: key_bytes,
            keys_cache: Arc::new(RwLock::new(LruCache::new(100))),
            storage,
        })
    }
    
    // 加密敏感数据
    pub async fn encrypt(&self, data: &str, context: &str) -> Result<String, EncryptionError> {
        // 获取或生成上下文的加密密钥
        let key = self.get_or_create_key(context).await?;
        
        // 生成随机IV
        let iv = self.generate_iv()?;
        
        // 加密数据
        let cipher = Aes256Gcm::new(GenericArray::from_slice(&key.key));
        let nonce = GenericArray::from_slice(&iv);
        
        let ciphertext = cipher
            .encrypt(nonce, data.as_bytes())
            .map_err(|e| EncryptionError::EncryptionFailed(e.to_string()))?;
            
        // 组合IV和加密数据
        let mut result = iv.to_vec();
        result.extend_from_slice(&ciphertext);
        
        // Base64编码结果
        Ok(base64::encode(&result))
    }
    
    // 解密敏感数据
    pub async fn decrypt(&self, encrypted_data: &str, context: &str) -> Result<String, EncryptionError> {
        // 获取上下文的加密密钥
        let key = self.get_key(context).await?;
        
        // Base64解码
        let data = base64::decode(encrypted_data)
            .map_err(|e| EncryptionError::DecodingError(e.to_string()))?;
            
        if data.len() < 12 {
            return Err(EncryptionError::InvalidEncryptedData);
        }
        
        // 分离IV和加密数据
        let iv = &data[0..12];
        let ciphertext = &data[12..];
        
        // 解密数据
        let cipher = Aes256Gcm::new(GenericArray::from_slice(&key.key));
        let nonce = GenericArray::from_slice(iv);
        
        let plaintext = cipher
            .decrypt(nonce, ciphertext)
            .map_err(|e| EncryptionError::DecryptionFailed(e.to_string()))?;
            
        // 转换为字符串
        String::from_utf8(plaintext)
            .map_err(|e| EncryptionError::DecodingError(e.to_string()))
    }
    
    // 生成随机IV
    fn generate_iv(&self) -> Result<[u8; 12], EncryptionError> {
        let mut iv = [0u8; 12];
        rand::thread_rng().fill_bytes(&mut iv);
        Ok(iv)
    }
    
    // 获取或创建上下文密钥
    async fn get_or_create_key(&self, context: &str) -> Result<EncryptionKey, EncryptionError> {
        // 首先检查缓存
        {
            let cache = self.keys_cache.read().await;
            if let Some(key) = cache.get(context) {
                return Ok(key.clone());
            }
        }
        
        // 检查存储中是否有密钥
        match self.storage.get_encryption_key(context).await {
            Ok(key) => {
                // 解密密钥
                let decrypted_key = self.decrypt_key(&key)?;
                
                // 更新缓存
                {
                    let mut cache = self.keys_cache.write().await;
                    cache.put(context.to_string(), decrypted_key.clone());
                }
                
                Ok(decrypted_key)
            },
            Err(_) => {
                // 生成新密钥
                let new_key = self.generate_key()?;
                
                // 加密密钥
                let encrypted_key = self.encrypt_key(&new_key)?;
                
                // 保存密钥
                self.storage.save_encryption_key(context, &encrypted_key).await?;
                
                // 更新缓存
                {
                    let mut cache = self.keys_cache.write().await;
                    cache.put(context.to_string(), new_key.clone());
                }
                
                Ok(new_key)
            }
        }
    }
    
    // 获取已存在的密钥
    async fn get_key(&self, context: &str) -> Result<EncryptionKey, EncryptionError> {
        // 首先检查缓存
        {
            let cache = self.keys_cache.read().await;
            if let Some(key) = cache.get(context) {
                return Ok(key.clone());
            }
        }
        
        // 从存储获取密钥
        let key = self.storage.get_encryption_key(context).await?;
        
        // 解密密钥
        let decrypted_key = self.decrypt_key(&key)?;
        
        // 更新缓存
        {
            let mut cache = self.keys_cache.write().await;
            cache.put(context.to_string(), decrypted_key.clone());
        }
        
        Ok(decrypted_key)
    }
    
    // 生成新密钥
    fn generate_key(&self) -> Result<EncryptionKey, EncryptionError> {
        let mut key = [0u8; 32];
        rand::thread_rng().fill_bytes(&mut key);
        
        Ok(EncryptionKey {
            key,
            created_at: chrono::Utc::now(),
        })
    }
    
    // 加密密钥（使用主密钥）
    fn encrypt_key(&self, key: &EncryptionKey) -> Result<StoredEncryptionKey, EncryptionError> {
        // 生成随机IV
        let iv = self.generate_iv()?;
        
        // 加密密钥
        let cipher = Aes256Gcm::new(GenericArray::from_slice(&self.master_key));
        let nonce = GenericArray::from_slice(&iv);
        
        let ciphertext = cipher
            .encrypt(nonce, &key.key)
            .map_err(|e| EncryptionError::EncryptionFailed(e.to_string()))?;
            
        // 组合IV和加密数据
        let mut result = iv.to_vec();
        result.extend_from_slice(&ciphertext);
        
        Ok(StoredEncryptionKey {
            encrypted_key: base64::encode(&result),
            created_at: key.created_at,
        })
    }
    
    // 解密密钥（使用主密钥）
    fn decrypt_key(&self, stored_key: &StoredEncryptionKey) -> Result<EncryptionKey, EncryptionError> {
        // Base64解码
        let data = base64::decode(&stored_key.encrypted_key)
            .map_err(|e| EncryptionError::DecodingError(e.to_string()))?;
            
        if data.len() < 12 {
            return Err(EncryptionError::InvalidEncryptedData);
        }
        
        // 分离IV和加密数据
        let iv = &data[0..12];
        let ciphertext = &data[12..];
        
        // 解密密钥
        let cipher = Aes256Gcm::new(GenericArray::from_slice(&self.master_key));
        let nonce = GenericArray::from_slice(iv);
        
        let plaintext = cipher
            .decrypt(nonce, ciphertext)
            .map_err(|e| EncryptionError::DecryptionFailed(e.to_string()))?;
            
        if plaintext.len() != 32 {
            return Err(EncryptionError::InvalidKeyLength);
        }
        
        let mut key = [0u8; 32];
        key.copy_from_slice(&plaintext);
        
        Ok(EncryptionKey {
            key,
            created_at: stored_key.created_at,
        })
    }
    
    // 数据脱敏函数
    pub fn mask_sensitive_data(&self, data: &str, pattern: &str) -> String {
        // 根据模式替换敏感数据
        // 支持正则表达式匹配并替换敏感信息
        // 简化实现
        data.replace(pattern, "********")
    }
}

// 密钥模型
#[derive(Clone)]
struct EncryptionKey {
    key: [u8; 32],
    created_at: chrono::DateTime<chrono::Utc>,
}

// 存储中的加密密钥
#[derive(Serialize, Deserialize)]
struct StoredEncryptionKey {
    encrypted_key: String,
    created_at: chrono::DateTime<chrono::Utc>,
}
```

加密功能特点：

1. **多密钥管理**：不同上下文使用不同密钥
2. **主密钥轮换**：支持定期轮换主密钥
3. **加密密钥缓存**：减少解密开销
4. **数据脱敏**：敏感日志和输出自动脱敏
5. **字段级加密**：选择性加密敏感字段
6. **传输加密**：所有API通信通过TLS加密

### 9.4 审计跟踪

全面的审计跟踪记录系统操作：

```rust
pub struct AuditLogger {
    storage: Arc<dyn WorkflowStorage>,
    event_bus: Arc<dyn MessageBroker>,
    encryption_manager: Arc<EncryptionManager>,
    config: AuditLogConfig,
}

impl AuditLogger {
    pub fn new(
        storage: Arc<dyn WorkflowStorage>,
        event_bus: Arc<dyn MessageBroker>,
        encryption_manager: Arc<EncryptionManager>,
        config: AuditLogConfig
    ) -> Self {
        let logger = Self {
            storage,
            event_bus,
            encryption_manager,
            config,
        };
        
        // 启动审计日志监听器
        tokio::spawn(logger.clone().start_audit_listener());
        
        logger
    }
    
    async fn start_audit_listener(&self) {
        // 订阅需要审计的事件
        for event_type in &self.config.audited_events {
            let storage = self.storage.clone();
            let encryption_manager = self.encryption_manager.clone();
            let config = self.config.clone();
            
            self.event_bus.subscribe(event_type, Box::new(move |event| {
                let storage = storage.clone();
                let encryption_manager = encryption_manager.clone();
                let config = config.clone();
                
                Box::pin(async move {
                    // 创建审计日志
                    let mut audit_log = AuditLog {
                        id: format!("audit-{}", uuid::Uuid::new_v4()),
                        timestamp: chrono::Utc::now(),
                        event_type: event.event_type.clone(),
                        user: event.metadata.get("user").cloned(),
                        resource_type: event.metadata.get("resource_type").cloned(),
                        resource_id: event.metadata.get("resource_id").cloned(),
                        action: event.metadata.get("action").cloned(),
                        status: event.metadata.get("status").cloned().unwrap_or_else(|| "success".to_string()),
                        client_ip: event.metadata.get("client_ip").cloned(),
                        user_agent: event.metadata.get("user_agent").cloned(),
                        details: None,
                    };
                    
                    // 处理敏感数据
                    if let Some(data) = &event.data {
                        // 如果包含敏感数据且需要加密
                        if config.encrypt_sensitive_data && is_sensitive_event(&event.event_type) {
                            // 加密数据
                            if let Ok(encrypted) = encryption_manager.encrypt(&data.to_string(), "audit_log").await {
                                audit_log.details = Some(json!({ "encrypted_data": encrypted }));
                            }
                        } else {
                            // 脱敏处理
                            let mut data_str = data.to_string();
                            for pattern in &config.sensitive_patterns {
                                data_str = encryption_manager.mask_sensitive_data(&data_str, pattern);
                            }
                            
                            audit_log.details = Some(json!(data_str));
                        }
                    }
                    
                    // 存储审计日志
                    if let Err(e) = storage.save_audit_log(&audit_log).await {
                        log::error!("保存审计日志失败: {}", e);
                    }
                })
            })).await.unwrap();
        }
    }
    
    // 直接记录审计日志
    pub async fn log_audit(
        &self,
        event_type: &str,
        user: Option<&str>,
        resource_type: Option<&str>,
        resource_id: Option<&str>,
        action: Option<&str>,
        status: &str,
        client_ip: Option<&str>,
        user_agent: Option<&str>,
        details: Option<serde_json::Value>
    ) -> Result<(), WorkflowError> {
        let audit_log = AuditLog {
            id: format!("audit-{}", uuid::Uuid::new_v4()),
            timestamp: chrono::Utc::now(),
            event_type: event_type.to_string(),
            user: user.map(|s| s.to_string()),
            resource_type: resource_type.map(|s| s.to_string()),
            resource_id: resource_id.map(|s| s.to_string()),
            action: action.map(|s| s.to_string()),
            status: status.to_string(),
            client_ip: client_ip.map(|s| s.to_string()),
            user_agent: user_agent.map(|s| s.to_string()),
            details,
        };
        
        self.storage.save_audit_log(&audit_log).await?;
        Ok(())
    }
    
    //
# 分布式工作流执行引擎设计方案（续）

## 9. 安全与访问控制（续）

### 9.4 审计跟踪（续）

```rust
    // 查询审计日志
    pub async fn query_audit_logs(
        &self,
        filter: AuditLogFilter,
        limit: usize,
        offset: usize
    ) -> Result<(Vec<AuditLog>, usize), WorkflowError> {
        let (logs, total) = self.storage.query_audit_logs(&filter, limit, offset).await?;
        
        // 如果需要解密敏感数据
        if filter.decrypt_sensitive_data {
            let mut decrypted_logs = Vec::with_capacity(logs.len());
            
            for log in logs {
                let mut decrypted_log = log.clone();
                
                if let Some(details) = &log.details {
                    // 如果有加密数据，尝试解密
                    if let Some(encrypted_data) = details.get("encrypted_data").and_then(|v| v.as_str()) {
                        if let Ok(decrypted) = self.encryption_manager.decrypt(encrypted_data, "audit_log").await {
                            // 尝试解析为JSON
                            if let Ok(json) = serde_json::from_str::<serde_json::Value>(&decrypted) {
                                decrypted_log.details = Some(json);
                            } else {
                                decrypted_log.details = Some(json!(decrypted));
                            }
                        }
                    }
                }
                
                decrypted_logs.push(decrypted_log);
            }
            
            Ok((decrypted_logs, total))
        } else {
            Ok((logs, total))
        }
    }
    
    // 导出审计日志
    pub async fn export_audit_logs(
        &self,
        filter: AuditLogFilter,
        format: ExportFormat
    ) -> Result<Vec<u8>, WorkflowError> {
        // 获取所有匹配的日志
        let (logs, _) = self.storage.query_audit_logs(&filter, 10000, 0).await?;
        
        match format {
            ExportFormat::Csv => {
                // 创建CSV writer
                let mut wtr = csv::WriterBuilder::new()
                    .has_headers(true)
                    .from_writer(vec![]);
                    
                // 写入每个日志
                for log in &logs {
                    let details = match &log.details {
                        Some(d) => d.to_string(),
                        None => "".to_string(),
                    };
                    
                    wtr.serialize((
                        log.id.clone(),
                        log.timestamp.to_rfc3339(),
                        log.event_type.clone(),
                        log.user.clone().unwrap_or_default(),
                        log.resource_type.clone().unwrap_or_default(),
                        log.resource_id.clone().unwrap_or_default(),
                        log.action.clone().unwrap_or_default(),
                        log.status.clone(),
                        log.client_ip.clone().unwrap_or_default(),
                        log.user_agent.clone().unwrap_or_default(),
                        details,
                    )).map_err(|e| WorkflowError::ExportError(format!("CSV序列化错误: {}", e)))?;
                }
                
                // 获取结果
                let result = wtr.into_inner()
                    .map_err(|e| WorkflowError::ExportError(format!("获取CSV数据错误: {}", e)))?;
                    
                Ok(result)
            },
            ExportFormat::Json => {
                serde_json::to_vec(&logs)
                    .map_err(|e| WorkflowError::ExportError(format!("JSON序列化错误: {}", e)))
            },
        }
    }
}

// 审计日志模型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuditLog {
    pub id: String,
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub event_type: String,
    pub user: Option<String>,
    pub resource_type: Option<String>,
    pub resource_id: Option<String>,
    pub action: Option<String>,
    pub status: String,
    pub client_ip: Option<String>,
    pub user_agent: Option<String>,
    pub details: Option<serde_json::Value>,
}

// 审计日志过滤条件
#[derive(Debug, Clone)]
pub struct AuditLogFilter {
    pub start_time: Option<chrono::DateTime<chrono::Utc>>,
    pub end_time: Option<chrono::DateTime<chrono::Utc>>,
    pub event_types: Option<Vec<String>>,
    pub users: Option<Vec<String>>,
    pub resource_types: Option<Vec<String>>,
    pub resource_ids: Option<Vec<String>>,
    pub actions: Option<Vec<String>>,
    pub status: Option<Vec<String>>,
    pub decrypt_sensitive_data: bool,
}

// 审计日志配置
#[derive(Debug, Clone)]
pub struct AuditLogConfig {
    pub audited_events: Vec<String>,
    pub retention_days: u32,
    pub encrypt_sensitive_data: bool,
    pub sensitive_patterns: Vec<String>,
}

// 导出格式
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExportFormat {
    Csv,
    Json,
}

// 判断事件是否包含敏感数据
fn is_sensitive_event(event_type: &str) -> bool {
    matches!(event_type, 
        "user.login" | 
        "user.password_changed" | 
        "api_key.created" | 
        "workflow.input_received" |
        "workflow.output_produced"
    )
}

// Warp过滤器，用于记录审计日志
fn with_audit_log(
    audit_logger: Arc<AuditLogger>,
    event_type: String,
    resource_type: Option<String>,
    action: Option<String>
) -> impl Filter<Extract = (), Error = std::convert::Infallible> + Clone {
    warp::filters::method::method()
        .and(warp::filters::addr::remote())
        .and(warp::header::optional::<String>("user-agent"))
        .and(warp::filters::ext::get::<Option<UserClaims>>())
        .and(warp::path::param::<String>().optional())
        .and(warp::any().map(move || audit_logger.clone()))
        .and(warp::any().map(move || event_type.clone()))
        .and(warp::any().map(move || resource_type.clone()))
        .and(warp::any().map(move || action.clone()))
        .map(move |method: warp::http::Method, addr: Option<std::net::SocketAddr>, user_agent: Option<String>, 
                   claims: Option<UserClaims>, resource_id: Option<String>, 
                   audit_logger: Arc<AuditLogger>, event_type: String, 
                   resource_type: Option<String>, action: Option<String>| {
            
            let client_ip = addr.map(|a| a.ip().to_string());
            let user = claims.map(|c| c.sub);
            
            // 异步记录审计日志
            tokio::spawn(async move {
                let _ = audit_logger.log_audit(
                    &event_type,
                    user.as_deref(),
                    resource_type.as_deref(),
                    resource_id.as_deref(),
                    action.as_deref(),
                    "success",
                    client_ip.as_deref(),
                    user_agent.as_deref(),
                    Some(json!({ "method": method.as_str() }))
                ).await;
            });
        })
}
```

审计系统特点：

1. **全面记录**：记录所有安全相关操作
2. **敏感数据保护**：加密或脱敏敏感信息
3. **可查询**：支持复杂查询和过滤
4. **不可篡改**：审计记录一旦创建不可修改
5. **合规性支持**：满足各种法规要求(GDPR, HIPAA等)
6. **导出功能**：支持多种格式导出审计数据

## 10. 形式化验证与证明

### 10.1 工作流属性验证

系统提供强大的形式化验证功能，确保工作流定义的正确性：

```rust
pub struct WorkflowVerifier {
    type_checker: Arc<TypeChecker>,
    control_flow_analyzer: Arc<ControlFlowAnalyzer>,
    model_checker: Arc<CTLModelChecker>,
    resource_analyzer: Arc<ResourceAnalyzer>,
    data_flow_analyzer: Arc<DataFlowAnalyzer>,
}

impl WorkflowVerifier {
    pub fn new() -> Self {
        Self {
            type_checker: Arc::new(TypeChecker::new()),
            control_flow_analyzer: Arc::new(ControlFlowAnalyzer::new()),
            model_checker: Arc::new(CTLModelChecker::new()),
            resource_analyzer: Arc::new(ResourceAnalyzer::new()),
            data_flow_analyzer: Arc::new(DataFlowAnalyzer::new()),
        }
    }
    
    // 验证工作流定义
    pub async fn verify(&self, workflow: &WorkflowDefinition) -> Result<VerificationResult, VerificationError> {
        // 完整验证结果
        let mut result = VerificationResult {
            workflow_id: workflow.id.clone(),
            is_valid: true,
            type_errors: Vec::new(),
            control_flow_errors: Vec::new(),
            resource_errors: Vec::new(),
            data_flow_errors: Vec::new(),
            temporal_properties: Vec::new(),
            warnings: Vec::new(),
        };
        
        // 类型检查
        match self.type_checker.check_workflow(workflow).await {
            Ok(type_result) => {
                if !type_result.errors.is_empty() {
                    result.is_valid = false;
                    result.type_errors = type_result.errors;
                }
                
                result.warnings.extend(type_result.warnings);
            },
            Err(e) => {
                return Err(VerificationError::TypeCheckError(e.to_string()));
            }
        }
        
        // 控制流分析
        match self.control_flow_analyzer.analyze(workflow).await {
            Ok(cf_result) => {
                if !cf_result.errors.is_empty() {
                    result.is_valid = false;
                    result.control_flow_errors = cf_result.errors;
                }
                
                result.warnings.extend(cf_result.warnings);
            },
            Err(e) => {
                return Err(VerificationError::ControlFlowError(e.to_string()));
            }
        }
        
        // 资源分析
        match self.resource_analyzer.analyze(workflow).await {
            Ok(res_result) => {
                if !res_result.errors.is_empty() {
                    result.is_valid = false;
                    result.resource_errors = res_result.errors;
                }
                
                result.warnings.extend(res_result.warnings);
            },
            Err(e) => {
                return Err(VerificationError::ResourceAnalysisError(e.to_string()));
            }
        }
        
        // 数据流分析
        match self.data_flow_analyzer.analyze(workflow).await {
            Ok(df_result) => {
                if !df_result.errors.is_empty() {
                    result.is_valid = false;
                    result.data_flow_errors = df_result.errors;
                }
                
                result.warnings.extend(df_result.warnings);
            },
            Err(e) => {
                return Err(VerificationError::DataFlowError(e.to_string()));
            }
        }
        
        // 时态逻辑属性检查
        let properties = self.get_standard_properties();
        
        for property in properties {
            match self.model_checker.check_property(workflow, &property).await {
                Ok(satisfied) => {
                    result.temporal_properties.push(PropertyResult {
                        property: property.clone(),
                        satisfied,
                        counterexample: if satisfied { None } else {
                            Some(self.model_checker.get_counterexample(workflow, &property).await?)
                        },
                    });
                    
                    if !satisfied && property.is_required {
                        result.is_valid = false;
                    }
                },
                Err(e) => {
                    return Err(VerificationError::ModelCheckingError(format!("属性 '{}' 验证失败: {}", property.name, e)));
                }
            }
        }
        
        Ok(result)
    }
    
    // 检查特定属性
    pub async fn check_property(
        &self, 
        workflow: &WorkflowDefinition, 
        property: &Property
    ) -> Result<bool, VerificationError> {
        self.model_checker.check_property(workflow, property).await
            .map_err(|e| VerificationError::ModelCheckingError(e.to_string()))
    }
    
    // 获取标准内置属性
    fn get_standard_properties(&self) -> Vec<Property> {
        vec![
            // 可终止性：所有执行最终都能到达终止状态
            Property {
                name: "Termination".to_string(),
                description: "工作流保证最终会终止".to_string(),
                formula: "AF end_reached".to_string(),
                property_type: PropertyType::LTL,
                is_required: true,
            },
            
            // 无死锁：不存在非终止状态无法继续执行
            Property {
                name: "DeadlockFreedom".to_string(),
                description: "工作流不包含死锁".to_string(),
                formula: "AG ((!end_reached) -> EX true)".to_string(),
                property_type: PropertyType::CTL,
                is_required: true,
            },
            
            // 无活锁：不存在无限循环且不取得进展的执行
            Property {
                name: "LivelockFreedom".to_string(),
                description: "工作流不包含活锁".to_string(),
                formula: "AG (EF end_reached)".to_string(),
                property_type: PropertyType::CTL,
                is_required: true,
            },
            
            // 所有步骤可达：每个定义的步骤在某些执行路径中都会被执行
            Property {
                name: "AllStepsReachable".to_string(),
                description: "所有步骤都是可达的".to_string(),
                formula: "AND_STEPS(EF step_active_ID)".to_string(),
                property_type: PropertyType::CTL,
                is_required: false,
            },
            
            // 容错能力：错误后可恢复并最终终止
            Property {
                name: "ErrorRecovery".to_string(),
                description: "出现错误后可以恢复并完成".to_string(),
                formula: "AG (error_occurred -> EF end_reached)".to_string(),
                property_type: PropertyType::CTL,
                is_required: false,
            },
        ]
    }
    
    // 生成测试用例
    pub async fn generate_test_cases(
        &self, 
        workflow: &WorkflowDefinition
    ) -> Result<Vec<TestCase>, VerificationError> {
        // 构建状态空间
        let states = self.control_flow_analyzer.build_state_space(workflow).await?;
        
        let mut test_cases = Vec::new();
        
        // 基本路径：从开始到结束的最短路径
        if let Some(basic_path) = self.find_shortest_path(&states).await {
            test_cases.push(TestCase {
                name: "BasicPath".to_string(),
                description: "从开始到结束的最短路径".to_string(),
                execution_path: basic_path.clone(),
                expected_outcome: TestOutcome::Success,
                coverage_goals: vec!["BasicFlow".to_string()],
            });
        }
        
        // 生成覆盖每个决策分支的测试用例
        for step in &workflow.steps {
            if let StepType::Decision { conditions, .. } = &step.step_type {
                for condition in conditions {
                    if let Some(path) = self.find_path_through_condition(&states, &step.id, &condition.transition_to).await {
                        test_cases.push(TestCase {
                            name: format!("Decision_{}_To_{}", step.id, condition.transition_to),
                            description: format!("测试从决策 {} 到 {} 的条件分支", step.id, condition.transition_to),
                            execution_path: path,
                            expected_outcome: TestOutcome::Success,
                            coverage_goals: vec![format!("Decision.{}.{}", step.id, condition.transition_to)],
                        });
                    }
                }
            }
        }
        
        // 生成错误路径测试用例
        for step in &workflow.steps {
            if let Some(error_policy) = &step.error_policy {
                match error_policy {
                    ErrorPolicy::Retry { .. } => {
                        // 生成重试路径
                        test_cases.push(TestCase {
                            name: format!("Retry_{}", step.id),
                            description: format!("测试步骤 {} 失败后的重试行为", step.id),
                            execution_path: vec![ExecutionStep {
                                step_id: step.id.clone(),
                                input: Some(json!({})),
                                result: Some(json!({"error": "simulated_error"})),
                                outcome: StepOutcome::Retry,
                            }],
                            expected_outcome: TestOutcome::Success,
                            coverage_goals: vec![format!("ErrorHandling.Retry.{}", step.id)],
                        });
                    },
                    ErrorPolicy::ContinueWorkflow => {
                        // 生成继续执行路径
                        test_cases.push(TestCase {
                            name: format!("Continue_{}", step.id),
                            description: format!("测试步骤 {} 失败后的继续执行行为", step.id),
                            execution_path: vec![ExecutionStep {
                                step_id: step.id.clone(),
                                input: Some(json!({})),
                                result: Some(json!({"error": "simulated_error"})),
                                outcome: StepOutcome::Continue,
                            }],
                            expected_outcome: TestOutcome::Success,
                            coverage_goals: vec![format!("ErrorHandling.Continue.{}", step.id)],
                        });
                    },
                    ErrorPolicy::FailWorkflow => {
                        // 生成工作流失败路径
                        test_cases.push(TestCase {
                            name: format!("Fail_{}", step.id),
                            description: format!("测试步骤 {} 失败导致工作流失败的行为", step.id),
                            execution_path: vec![ExecutionStep {
                                step_id: step.id.clone(),
                                input: Some(json!({})),
                                result: Some(json!({"error": "simulated_error"})),
                                outcome: StepOutcome::Fail,
                            }],
                            expected_outcome: TestOutcome::Failure,
                            coverage_goals: vec![format!("ErrorHandling.Fail.{}", step.id)],
                        });
                    },
                }
            }
        }
        
        Ok(test_cases)
    }
    
    // 查找最短路径
    async fn find_shortest_path(&self, states: &[State]) -> Option<Vec<ExecutionStep>> {
        // 使用广度优先搜索查找从开始状态到结束状态的最短路径
        // 简化实现
        None
    }
    
    // 查找通过特定条件的路径
    async fn find_path_through_condition(&self, states: &[State], decision_step_id: &str, target_step_id: &str) -> Option<Vec<ExecutionStep>> {
        // 查找经过特定决策条件的执行路径
        // 简化实现
        None
    }
}

// 验证结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerificationResult {
    pub workflow_id: String,
    pub is_valid: bool,
    pub type_errors: Vec<TypeError>,
    pub control_flow_errors: Vec<ControlFlowError>,
    pub resource_errors: Vec<ResourceError>,
    pub data_flow_errors: Vec<DataFlowError>,
    pub temporal_properties: Vec<PropertyResult>,
    pub warnings: Vec<VerificationWarning>,
}

// 时态逻辑属性
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Property {
    pub name: String,
    pub description: String,
    pub formula: String,
    pub property_type: PropertyType,
    pub is_required: bool,
}

// 属性类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PropertyType {
    CTL,
    LTL,
}

// 属性验证结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PropertyResult {
    pub property: Property,
    pub satisfied: bool,
    pub counterexample: Option<Vec<State>>,
}

// 测试用例
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TestCase {
    pub name: String,
    pub description: String,
    pub execution_path: Vec<ExecutionStep>,
    pub expected_outcome: TestOutcome,
    pub coverage_goals: Vec<String>,
}

// 执行步骤
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExecutionStep {
    pub step_id: String,
    pub input: Option<serde_json::Value>,
    pub result: Option<serde_json::Value>,
    pub outcome: StepOutcome,
}

// 步骤结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum StepOutcome {
    Success,
    Fail,
    Retry,
    Continue,
}

// 测试预期结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TestOutcome {
    Success,
    Failure,
}
```

工作流验证功能：

1. **类型检查**：验证输入、输出和步骤参数类型正确性
2. **控制流分析**：检测死锁、活锁和不可达代码
3. **资源分析**：验证资源使用约束和限制
4. **数据流分析**：检测未初始化变量和数据依赖问题
5. **时态逻辑验证**：使用CTL/LTL验证复杂行为属性
6. **测试用例生成**：自动生成覆盖关键路径的测试用例

### 10.2 死锁检测

系统使用Petri网模型检测工作流死锁：

```rust
pub struct DeadlockDetector {
    petri_net_builder: Arc<PetriNetBuilder>,
}

impl DeadlockDetector {
    pub fn new() -> Self {
        Self {
            petri_net_builder: Arc::new(PetriNetBuilder::new()),
        }
    }
    
    // 检测工作流中的死锁
    pub async fn detect_deadlocks(&self, workflow: &WorkflowDefinition) -> Result<DeadlockAnalysisResult, VerificationError> {
        // 从工作流定义构建Petri网
        let petri_net = self.petri_net_builder.build_from_workflow(workflow).await?;
        
        // 构建可达性图
        let reachability_graph = self.build_reachability_graph(&petri_net).await?;
        
        // 查找死锁状态
        let deadlocks = self.find_deadlock_states(&reachability_graph, &petri_net).await?;
        
        if deadlocks.is_empty() {
            Ok(DeadlockAnalysisResult {
                has_deadlock: false,
                deadlock_states: Vec::new(),
                potential_fixes: Vec::new(),
            })
        } else {
            // 分析死锁原因并提出修复建议
            let potential_fixes = self.suggest_deadlock_fixes(workflow, &deadlocks, &petri_net).await?;
            
            Ok(DeadlockAnalysisResult {
                has_deadlock: true,
                deadlock_states: deadlocks,
                potential_fixes,
            })
        }
    }
    
    // 构建Petri网可达性图
    async fn build_reachability_graph(&self, petri_net: &PetriNet) -> Result<ReachabilityGraph, VerificationError> {
        let mut graph = ReachabilityGraph {
            nodes: Vec::new(),
            edges: Vec::new(),
        };
        
        // 初始标记
        let initial_marking = petri_net.initial_marking.clone();
        graph.nodes.push(ReachabilityNode {
            id: 0,
            marking: initial_marking.clone(),
            is_final: self.is_final_marking(&initial_marking, petri_net),
        });
        
        let mut visited_markings = HashMap::new();
        visited_markings.insert(initial_marking.clone(), 0);
        
        let mut queue = VecDeque::new();
        queue.push_back(0);
        
        // 广度优先搜索构建可达性图
        while let Some(node_id) = queue.pop_front() {
            let marking = &graph.nodes[node_id].marking;
            
            // 尝试发射每个转换
            for (transition_id, transition) in &petri_net.transitions {
                // 检查转换是否启用
                if self.is_transition_enabled(transition, marking) {
                    // 执行转换
                    let new_marking = self.fire_transition(transition, marking);
                    
                    // 检查是否已访问过此标记
                    if let Some(existing_node_id) = visited_markings.get(&new_marking) {
                        // 添加边到现有节点
                        graph.edges.push(ReachabilityEdge {
                            from: node_id,
                            to: *existing_node_id,
                            transition: transition_id.clone(),
                        });
                    } else {
                        // 创建新节点
                        let new_node_id = graph.nodes.len();
                        
                        graph.nodes.push(ReachabilityNode {
                            id: new_node_id,
                            marking: new_marking.clone(),
                            is_final: self.is_final_marking(&new_marking, petri_net),
                        });
                        
                        // 添加边
                        graph.edges.push(ReachabilityEdge {
                            from: node_id,
                            to: new_node_id,
                            transition: transition_id.clone(),
                        });
                        
                        // 记录访问
                        visited_markings.insert(new_marking.clone(), new_node_id);
                        
                        // 入队新节点
                        queue.push_back(new_node_id);
                    }
                }
            }
        }
        
        Ok(graph)
    }
    
    // 查找死锁状态
    async fn find_deadlock_states(&self, graph: &ReachabilityGraph, petri_net: &PetriNet) -> Result<Vec<DeadlockState>, VerificationError> {
        let mut deadlocks = Vec::new();
        
        for node in &graph.nodes {
            // 如果不是终止状态且没有出边，则为死锁
            if !node.is_final && !self.has_outgoing_edges(graph, node.id) {
                // 查找哪些转换是不可发射的
                let blocked_transitions = self.find_blocked_transitions(petri_net, &node.marking);
                
                deadlocks.push(DeadlockState {
                    marking: node.marking.clone(),
                    blocked_transitions,
                    node_id: node.id,
                });
            }
        }
        
        Ok(deadlocks)
    }
    
    // 检查节点是否有出边
    fn has_outgoing_edges(&self, graph: &ReachabilityGraph, node_id: usize) -> bool {
        graph.edges.iter().any(|edge| edge.from == node_id)
    }
    
    // 查找被阻塞的转换
    fn find_blocked_transitions(&self, petri_net: &PetriNet, marking: &HashMap<String, u32>) -> Vec<BlockedTransitionInfo> {
        let mut blocked = Vec::new();
        
        for (transition_id, transition) in &petri_net.transitions {
            if !self.is_transition_enabled(transition, marking) {
                // 找出哪些输入位置不满足条件
                let missing_tokens = transition.inputs.iter()
                    .filter_map(|(place_id, required)| {
                        let available = *marking.get(place_id).unwrap_or(&0);
                        if available < *required {
                            Some(MissingTokens {
                                place_id: place_id.clone(),
                                required: *required,
                                available,
                            })
                        } else {
# 分布式工作流执行引擎设计方案（续）

## 10. 形式化验证与证明（续）

### 10.2 死锁检测（续）

```rust
                let missing_tokens = transition.inputs.iter()
                    .filter_map(|(place_id, required)| {
                        let available = *marking.get(place_id).unwrap_or(&0);
                        if available < *required {
                            Some(MissingTokens {
                                place_id: place_id.clone(),
                                required: *required,
                                available,
                            })
                        } else {
                            None
                        }
                    })
                    .collect::<Vec<_>>();
                
                blocked.push(BlockedTransitionInfo {
                    transition_id: transition_id.clone(),
                    missing_tokens,
                });
            }
        }
        
        blocked
    }
    
    // 检查标记是否为终止标记
    fn is_final_marking(&self, marking: &HashMap<String, u32>, petri_net: &PetriNet) -> bool {
        // 终止标记：只有终止位置有token
        for (place_id, tokens) in marking {
            if *tokens > 0 && !petri_net.final_places.contains(place_id) {
                return false;
            }
        }
        
        // 确保至少有一个终止位置有token
        petri_net.final_places.iter().any(|place_id| *marking.get(place_id).unwrap_or(&0) > 0)
    }
    
    // 检查转换是否可执行
    fn is_transition_enabled(&self, transition: &Transition, marking: &HashMap<String, u32>) -> bool {
        for (place_id, required) in &transition.inputs {
            let available = *marking.get(place_id).unwrap_or(&0);
            if available < *required {
                return false;
            }
        }
        true
    }
    
    // 执行转换并返回新标记
    fn fire_transition(&self, transition: &Transition, marking: &HashMap<String, u32>) -> HashMap<String, u32> {
        let mut new_marking = marking.clone();
        
        // 移除输入token
        for (place_id, required) in &transition.inputs {
            if let Some(current) = new_marking.get_mut(place_id) {
                *current -= *required;
            }
        }
        
        // 添加输出token
        for (place_id, produced) in &transition.outputs {
            *new_marking.entry(place_id.clone()).or_insert(0) += *produced;
        }
        
        new_marking
    }
    
    // 提出死锁修复建议
    async fn suggest_deadlock_fixes(
        &self, 
        workflow: &WorkflowDefinition,
        deadlocks: &[DeadlockState],
        petri_net: &PetriNet
    ) -> Result<Vec<DeadlockFix>, VerificationError> {
        let mut fixes = Vec::new();
        
        for deadlock in deadlocks {
            // 分析死锁模式
            let deadlock_pattern = self.analyze_deadlock_pattern(deadlock, petri_net).await?;
            
            match deadlock_pattern {
                DeadlockPattern::MissingTransition { from_places, to_places } => {
                    // 建议添加转换
                    fixes.push(DeadlockFix {
                        description: "添加缺失的转换".to_string(),
                        fix_type: FixType::AddTransition { 
                            from_steps: from_places.into_iter().map(|p| self.map_place_to_step(p, workflow)).collect(),
                            to_steps: to_places.into_iter().map(|p| self.map_place_to_step(p, workflow)).collect(),
                        },
                        deadlock_id: deadlock.node_id,
                    });
                },
                DeadlockPattern::CircularWait { places, transitions } => {
                    // 建议打破循环等待
                    fixes.push(DeadlockFix {
                        description: "打破循环等待依赖".to_string(),
                        fix_type: FixType::BreakDependencyCycle { 
                            steps: places.into_iter().map(|p| self.map_place_to_step(p, workflow)).collect(),
                            transitions: transitions.clone(),
                        },
                        deadlock_id: deadlock.node_id,
                    });
                },
                DeadlockPattern::ResourceStarvation { resource_places } => {
                    // 建议增加资源
                    fixes.push(DeadlockFix {
                        description: "增加资源初始分配".to_string(),
                        fix_type: FixType::IncreaseResources { 
                            resource_ids: resource_places.into_iter().map(|p| self.map_place_to_resource(p, workflow)).collect(),
                        },
                        deadlock_id: deadlock.node_id,
                    });
                },
                DeadlockPattern::InconsistentConditions { decision_step, conditions } => {
                    // 建议修复条件
                    fixes.push(DeadlockFix {
                        description: "修复不一致的条件".to_string(),
                        fix_type: FixType::FixConditions { 
                            step_id: self.map_place_to_step(decision_step, workflow),
                            conditions: conditions.clone(),
                        },
                        deadlock_id: deadlock.node_id,
                    });
                },
                DeadlockPattern::Unknown => {
                    // 一般性建议
                    fixes.push(DeadlockFix {
                        description: "检查步骤和转换逻辑".to_string(),
                        fix_type: FixType::Generic,
                        deadlock_id: deadlock.node_id,
                    });
                },
            }
        }
        
        Ok(fixes)
    }
    
    // 分析死锁模式
    async fn analyze_deadlock_pattern(
        &self, 
        deadlock: &DeadlockState,
        petri_net: &PetriNet
    ) -> Result<DeadlockPattern, VerificationError> {
        // 分析死锁中的标记分布
        let places_with_tokens: Vec<&String> = deadlock.marking.iter()
            .filter(|(_, &count)| count > 0)
            .map(|(place, _)| place)
            .collect();
            
        // 检查是否存在循环等待
        if let Some(cycle) = self.detect_cycle(places_with_tokens, petri_net) {
            return Ok(DeadlockPattern::CircularWait {
                places: cycle.places,
                transitions: cycle.transitions,
            });
        }
        
        // 检查是否有资源不足
        let resource_places: Vec<String> = petri_net.places.iter()
            .filter(|(place_id, _)| place_id.starts_with("resource_"))
            .map(|(place_id, _)| place_id.clone())
            .collect();
            
        if !resource_places.is_empty() && deadlock.blocked_transitions.iter().any(|bt| {
            bt.missing_tokens.iter().any(|mt| resource_places.contains(&mt.place_id))
        }) {
            return Ok(DeadlockPattern::ResourceStarvation {
                resource_places: resource_places.clone(),
            });
        }
        
        // 检查是否有不一致的条件
        // 查找决策步骤的位置
        let decision_places: Vec<(String, Vec<String>)> = petri_net.places.iter()
            .filter(|(place_id, _)| place_id.starts_with("decision_"))
            .map(|(place_id, _)| {
                let conditions = petri_net.transitions.iter()
                    .filter(|(_, t)| t.inputs.contains_key(place_id))
                    .map(|(id, _)| id.clone())
                    .collect();
                
                (place_id.clone(), conditions)
            })
            .collect();
            
        for (decision_place, conditions) in decision_places {
            if deadlock.marking.get(&decision_place).copied().unwrap_or(0) > 0 
               && deadlock.blocked_transitions.iter().all(|bt| conditions.contains(&bt.transition_id)) {
                return Ok(DeadlockPattern::InconsistentConditions {
                    decision_step: decision_place,
                    conditions,
                });
            }
        }
        
        // 检查是否缺少转换
        let to_places: Vec<String> = deadlock.blocked_transitions.iter()
            .flat_map(|bt| bt.missing_tokens.iter().map(|mt| mt.place_id.clone()))
            .collect();
            
        if !to_places.is_empty() {
            return Ok(DeadlockPattern::MissingTransition {
                from_places: places_with_tokens.into_iter().cloned().collect(),
                to_places,
            });
        }
        
        Ok(DeadlockPattern::Unknown)
    }
    
    // 检测循环等待
    fn detect_cycle(&self, places: Vec<&String>, petri_net: &PetriNet) -> Option<CycleInfo> {
        // 使用深度优先搜索检测循环
        // 简化实现
        None
    }
    
    // 将位置映射到工作流步骤
    fn map_place_to_step(&self, place_id: String, workflow: &WorkflowDefinition) -> String {
        // Petri网位置ID到工作流步骤ID的映射
        // 简化实现，假设位置ID包含步骤ID
        if place_id.starts_with("step_") {
            place_id.trim_start_matches("step_").to_string()
        } else if place_id.starts_with("decision_") {
            place_id.trim_start_matches("decision_").to_string()
        } else {
            place_id
        }
    }
    
    // 将位置映射到资源
    fn map_place_to_resource(&self, place_id: String, workflow: &WorkflowDefinition) -> String {
        // Petri网位置ID到资源ID的映射
        if place_id.starts_with("resource_") {
            place_id.trim_start_matches("resource_").to_string()
        } else {
            place_id
        }
    }
}

// 死锁分析结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeadlockAnalysisResult {
    pub has_deadlock: bool,
    pub deadlock_states: Vec<DeadlockState>,
    pub potential_fixes: Vec<DeadlockFix>,
}

// 死锁状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeadlockState {
    pub marking: HashMap<String, u32>,
    pub blocked_transitions: Vec<BlockedTransitionInfo>,
    pub node_id: usize,
}

// 阻塞的转换信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BlockedTransitionInfo {
    pub transition_id: String,
    pub missing_tokens: Vec<MissingTokens>,
}

// 缺少的token
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MissingTokens {
    pub place_id: String,
    pub required: u32,
    pub available: u32,
}

// 死锁修复建议
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeadlockFix {
    pub description: String,
    pub fix_type: FixType,
    pub deadlock_id: usize,
}

// 修复类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum FixType {
    AddTransition {
        from_steps: Vec<String>,
        to_steps: Vec<String>,
    },
    BreakDependencyCycle {
        steps: Vec<String>,
        transitions: Vec<String>,
    },
    IncreaseResources {
        resource_ids: Vec<String>,
    },
    FixConditions {
        step_id: String,
        conditions: Vec<String>,
    },
    Generic,
}

// 死锁模式
#[derive(Debug, Clone)]
pub enum DeadlockPattern {
    CircularWait {
        places: Vec<String>,
        transitions: Vec<String>,
    },
    ResourceStarvation {
        resource_places: Vec<String>,
    },
    MissingTransition {
        from_places: Vec<String>,
        to_places: Vec<String>,
    },
    InconsistentConditions {
        decision_step: String,
        conditions: Vec<String>,
    },
    Unknown,
}

// 循环信息
pub struct CycleInfo {
    pub places: Vec<String>,
    pub transitions: Vec<String>,
}

// 可达性图节点
pub struct ReachabilityNode {
    pub id: usize,
    pub marking: HashMap<String, u32>,
    pub is_final: bool,
}

// 可达性图边
pub struct ReachabilityEdge {
    pub from: usize,
    pub to: usize,
    pub transition: String,
}

// 可达性图
pub struct ReachabilityGraph {
    pub nodes: Vec<ReachabilityNode>,
    pub edges: Vec<ReachabilityEdge>,
}
```

死锁检测的优势：

1. **形式化模型**：基于数学理论的Petri网模型
2. **可达性分析**：全面探索状态空间
3. **死锁分类**：识别不同类型的死锁模式
4. **解决建议**：提供针对性的修复方案
5. **图形化表示**：可视化死锁状态和执行路径

### 10.3 Petri网模型

系统使用Petri网为工作流提供精确的形式化模型：

```rust
pub struct PetriNetBuilder {
    // 用于缓存已构建的Petri网
    cache: Arc<RwLock<LruCache<String, PetriNet>>>,
}

impl PetriNetBuilder {
    pub fn new() -> Self {
        Self {
            cache: Arc::new(RwLock::new(LruCache::new(100))),
        }
    }
    
    // 从工作流定义构建Petri网
    pub async fn build_from_workflow(&self, workflow: &WorkflowDefinition) -> Result<PetriNet, VerificationError> {
        // 检查缓存
        let cache_key = format!("{}:{}", workflow.id, workflow.version);
        
        {
            let cache = self.cache.read().await;
            if let Some(petri_net) = cache.get(&cache_key) {
                return Ok(petri_net.clone());
            }
        }
        
        // 创建新的Petri网
        let mut petri_net = PetriNet {
            places: HashMap::new(),
            transitions: HashMap::new(),
            initial_marking: HashMap::new(),
            final_places: HashSet::new(),
        };
        
        // 为每个步骤创建位置
        for step in &workflow.steps {
            let place_id = format!("step_{}", step.id);
            petri_net.places.insert(place_id.clone(), Place {
                id: place_id.clone(),
                name: step.name.clone(),
                is_resource: false,
            });
            
            // 如果是开始步骤，在初始标记中放置一个token
            if let StepType::Start = step.step_type {
                petri_net.initial_marking.insert(place_id.clone(), 1);
            }
            
            // 如果是结束步骤，标记为终止位置
            if let StepType::End = step.step_type {
                petri_net.final_places.insert(place_id);
            }
            
            // 为决策步骤创建额外位置
            if let StepType::Decision { conditions, .. } = &step.step_type {
                let decision_place_id = format!("decision_{}", step.id);
                petri_net.places.insert(decision_place_id.clone(), Place {
                    id: decision_place_id.clone(),
                    name: format!("Decision {}", step.name),
                    is_resource: false,
                });
                
                // 创建从步骤到决策位置的转换
                let to_decision_id = format!("step_{}_to_decision", step.id);
                let mut inputs = HashMap::new();
                inputs.insert(format!("step_{}", step.id), 1);
                
                let mut outputs = HashMap::new();
                outputs.insert(decision_place_id, 1);
                
                petri_net.transitions.insert(to_decision_id.clone(), Transition {
                    id: to_decision_id,
                    name: format!("{} to decision", step.name),
                    inputs,
                    outputs,
                    guard: None,
                });
                
                // 为每个条件创建转换
                for condition in conditions {
                    let condition_id = format!("condition_{}_{}", step.id, condition.transition_to);
                    let mut inputs = HashMap::new();
                    inputs.insert(format!("decision_{}", step.id), 1);
                    
                    let mut outputs = HashMap::new();
                    outputs.insert(format!("step_{}", condition.transition_to), 1);
                    
                    petri_net.transitions.insert(condition_id.clone(), Transition {
                        id: condition_id,
                        name: format!("Condition {} to {}", step.name, condition.transition_to),
                        inputs,
                        outputs,
                        guard: Some(condition.condition.clone()),
                    });
                }
            }
        }
        
        // 为转换创建转换
        for transition in &workflow.transitions {
            if let StepType::Decision { .. } = workflow.steps.iter()
                .find(|s| s.id == transition.from)
                .map(|s| &s.step_type)
                .unwrap_or(&StepType::Start) {
                // 决策步骤的转换已经在上面处理过
                continue;
            }
            
            let transition_id = format!("transition_{}_{}", transition.from, transition.to);
            let mut inputs = HashMap::new();
            inputs.insert(format!("step_{}", transition.from), 1);
            
            let mut outputs = HashMap::new();
            outputs.insert(format!("step_{}", transition.to), 1);
            
            let guard = if transition.condition != "*" {
                Some(transition.condition.clone())
            } else {
                None
            };
            
            petri_net.transitions.insert(transition_id.clone(), Transition {
                id: transition_id,
                name: format!("From {} to {}", transition.from, transition.to),
                inputs,
                outputs,
                guard,
            });
        }
        
        // 处理并行步骤
        for step in &workflow.steps {
            if let StepType::Parallel { branches, completion_strategy, .. } = &step.step_type {
                // 创建分支位置
                for branch in branches {
                    let branch_place_id = format!("branch_{}_{}", step.id, branch.name);
                    petri_net.places.insert(branch_place_id.clone(), Place {
                        id: branch_place_id.clone(),
                        name: format!("Branch {} {}", step.name, branch.name),
                        is_resource: false,
                    });
                    
                    // 创建从步骤到分支的转换
                    let to_branch_id = format!("step_{}_to_branch_{}", step.id, branch.name);
                    let mut inputs = HashMap::new();
                    inputs.insert(format!("step_{}", step.id), 1);
                    
                    let mut outputs = HashMap::new();
                    outputs.insert(branch_place_id.clone(), 1);
                    
                    petri_net.transitions.insert(to_branch_id.clone(), Transition {
                        id: to_branch_id,
                        name: format!("{} to branch {}", step.name, branch.name),
                        inputs,
                        outputs,
                        guard: None,
                    });
                    
                    // 创建从分支到入口步骤的转换
                    let to_entry_id = format!("branch_{}_to_entry_{}", branch.name, branch.entry_step_id);
                    let mut inputs = HashMap::new();
                    inputs.insert(branch_place_id, 1);
                    
                    let mut outputs = HashMap::new();
                    outputs.insert(format!("step_{}", branch.entry_step_id), 1);
                    
                    petri_net.transitions.insert(to_entry_id.clone(), Transition {
                        id: to_entry_id,
                        name: format!("Branch {} to {}", branch.name, branch.entry_step_id),
                        inputs,
                        outputs,
                        guard: None,
                    });
                }
                
                // 创建合并位置
                let join_place_id = format!("join_{}", step.id);
                petri_net.places.insert(join_place_id.clone(), Place {
                    id: join_place_id.clone(),
                    name: format!("Join {}", step.name),
                    is_resource: false,
                });
                
                // 根据完成策略创建合并转换
                match completion_strategy {
                    CompletionStrategy::All => {
                        // 需要所有分支完成
                        let join_transition_id = format!("join_all_{}", step.id);
                        let mut inputs = HashMap::new();
                        let mut outputs = HashMap::new();
                        
                        for branch in branches {
                            // 查找分支出口步骤
                            let exit_step_ids = workflow.transitions.iter()
                                .filter(|t| {
                                    workflow.steps.iter().any(|s| {
                                        s.id == t.from && 
                                        workflow.steps.iter().any(|entry| {
                                            entry.id == branch.entry_step_id &&
                                            self.is_step_reachable_from(entry.id.as_str(), s.id.as_str(), workflow)
                                        })
                                    }) && 
                                    !workflow.steps.iter().any(|s| {
                                        s.id == t.to && 
                                        workflow.steps.iter().any(|entry| {
                                            entry.id == branch.entry_step_id &&
                                            self.is_step_reachable_from(entry.id.as_str(), s.id.as_str(), workflow)
                                        })
                                    })
                                })
                                .map(|t| t.from.clone())
                                .collect::<Vec<_>>();
                                
                            for exit_id in exit_step_ids {
                                inputs.insert(format!("step_{}", exit_id), 1);
                            }
                        }
                        
                        outputs.insert(join_place_id.clone(), 1);
                        
                        petri_net.transitions.insert(join_transition_id.clone(), Transition {
                            id: join_transition_id,
                            name: format!("Join all branches of {}", step.name),
                            inputs,
                            outputs,
                            guard: None,
                        });
                    },
                    CompletionStrategy::Any => {
                        // 任何一个分支完成即可
                        for branch in branches {
                            // 查找分支出口步骤
                            let exit_step_ids = workflow.transitions.iter()
                                .filter(|t| {
                                    workflow.steps.iter().any(|s| {
                                        s.id == t.from && 
                                        workflow.steps.iter().any(|entry| {
                                            entry.id == branch.entry_step_id &&
                                            self.is_step_reachable_from(entry.id.as_str(), s.id.as_str(), workflow)
                                        })
                                    }) && 
                                    !workflow.steps.iter().any(|s| {
                                        s.id == t.to && 
                                        workflow.steps.iter().any(|entry| {
                                            entry.id == branch.entry_step_id &&
                                            self.is_step_reachable_from(entry.id.as_str(), s.id.as_str(), workflow)
                                        })
                                    })
                                })
                                .map(|t| t.from.clone())
                                .collect::<Vec<_>>();
                                
                            for exit_id in exit_step_ids {
                                let join_transition_id = format!("join_any_{}_{}", step.id, exit_id);
                                let mut inputs = HashMap::new();
                                inputs.insert(format!("step_{}", exit_id), 1);
                                
                                let mut outputs = HashMap::new();
                                outputs.insert(join_place_id.clone(), 1);
                                
                                petri_net.transitions.insert(join_transition_id.clone(), Transition {
                                    id: join_transition_id,
                                    name: format!("Join branch {} of {}", exit_id, step.name),
                                    inputs,
                                    outputs,
                                    guard: None,
                                });
                            }
                        }
                    },
                    CompletionStrategy::N(n) => {
                        // 至少N个分支完成
                        // 这需要使用更复杂的Petri网结构，简化实现
                    },
                }
                
                // 创建从合并位置到下一个步骤的转换
                let next_steps: Vec<String> = workflow.transitions.iter()
                    .filter(|t| t.from == step.id)
                    .map(|t| t.to.clone())
                    .collect();
                    
                for next_step in next_steps {
                    let to_next_id = format!("join_{}_to_{}", step.id, next_step);
                    let mut inputs = HashMap::new();
                    inputs.insert(join_place_id.clone(), 1);
                    
                    let mut outputs = HashMap::new();
                    outputs.insert(format!("step_{}", next_step), 1);
                    
                    petri_net.transitions.insert(to_next_id.clone(), Transition {
                        id: to_next_id,
                        name: format!("From join {} to {}", step.name, next_step),
                        inputs,
                        outputs,
                        guard: None,
                    });
                }
            }
        }
        
        // 处理资源约束
        // 查找工作流中的资源标记
        let resource_tags: HashMap<String, u32> = workflow.tags.iter()
            .filter(|(k, _)| k.starts_with("resource."))
            .map(|(k, v)| (k.trim_start_matches("resource.").to_string(), v.parse::<u32>().unwrap_or(1)))
            .collect();
            
        for (resource_id, capacity) in resource_tags {
            let resource_place_id = format!("resource_{}", resource_id);
            petri_net.places.insert(resource_place_id.clone(), Place {
                id: resource_place_id.clone(),
                name: format!("Resource {}", resource_id),
                is_resource: true,
            });
            
            // 在初始标记中设置资源容量
            petri_net.initial_marking.insert(resource_place_id.clone(), capacity);
            
            // 查找使用此资源的步骤
            for step in &workflow.steps {
                if step.tags.get(&format!("uses.{}", resource_id)).is_some() {
                    // 修改使用资源的步骤的输入转换
                    for (transition_id, transition) in petri_net.transitions.iter_mut() {
                        if transition.outputs.contains_key(&format!("step_{}", step.id)) {
                            // 添加资源作为输入
                            transition.inputs.insert(resource_place_id.clone(), 1);
                        }
                    }
                    
                    // 修改释放资源的步骤的输出转换
                    for (transition_id, transition) in petri_net.transitions.iter_mut() {
                        if transition.inputs.contains_key(&format!("step_{}", step.id)) {
                            // 添加资源作为输出
                            transition.outputs.insert(resource_place_id.clone(), 1);
                        }
                    }
                }
            }
        }
        
        // 更新缓存
        {
            let mut cache = self.cache.write().await;
            cache.put(cache_key, petri_net.clone());
        }
        
        Ok(petri_net)
    }
    
    // 检查一个步骤是否可以从另一个步骤可达
    fn is_step_reachable_from(&self, from_id: &str, to_id: &str, workflow: &WorkflowDefinition) -> bool {
        // 使用广度优先搜索检查可达性
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();
        
        queue.push_back(from_id.to_string());
        visited.insert(from_id.to_string());
        
        while let Some(current) = queue.pop_front() {
            if current == to_id {
                return true;
            }
            
            for transition in &workflow.transitions {
                if transition.from == current && !visited.contains(&transition.to) {
                    visited.insert(transition.to.clone());
                    queue.push_back(transition.to.clone());
                }
            }
        }
        
        
# 分布式工作流执行引擎设计方案（续）

## 10. 形式化验证与证明（续）

### 10.3 Petri网模型（续）

```rust
    // 检查一个步骤是否可以从另一个步骤可达
    fn is_step_reachable_from(&self, from_id: &str, to_id: &str, workflow: &WorkflowDefinition) -> bool {
        // 使用广度优先搜索检查可达性
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();
        
        queue.push_back(from_id.to_string());
        visited.insert(from_id.to_string());
        
        while let Some(current) = queue.pop_front() {
            if current == to_id {
                return true;
            }
            
            for transition in &workflow.transitions {
                if transition.from == current && !visited.contains(&transition.to) {
                    visited.insert(transition.to.clone());
                    queue.push_back(transition.to.clone());
                }
            }
        }
        
        false
    }
    
    // 生成工作流的Petri网可视化
    pub fn generate_petri_net_visualization(&self, petri_net: &PetriNet) -> Result<String, VerificationError> {
        // 生成DOT格式的Petri网可视化
        let mut dot = String::from("digraph PetriNet {\n");
        dot.push_str("  rankdir=LR;\n");
        dot.push_str("  node [shape=circle, fontname=\"Arial\"];\n");
        
        // 添加位置节点
        for (place_id, place) in &petri_net.places {
            let label = place.name.replace("\"", "\\\"");
            let shape = if place.is_resource { "doublecircle" } else { "circle" };
            let color = if petri_net.final_places.contains(place_id) { "blue" } else { "black" };
            let initial_tokens = petri_net.initial_marking.get(place_id).cloned().unwrap_or(0);
            let token_label = if initial_tokens > 0 {
                format!("{}\\n({})", label, initial_tokens)
            } else {
                label
            };
            
            dot.push_str(&format!("  \"{}\" [label=\"{}\", shape={}, color={}];\n", 
                place_id, token_label, shape, color));
        }
        
        // 添加转换节点
        for (transition_id, transition) in &petri_net.transitions {
            let label = transition.name.replace("\"", "\\\"");
            let guard_label = if let Some(guard) = &transition.guard {
                format!("{}\\n[{}]", label, guard)
            } else {
                label
            };
            
            dot.push_str(&format!("  \"{}\" [label=\"{}\", shape=box, color=black];\n", 
                transition_id, guard_label));
                
            // 添加输入弧
            for (input_place, weight) in &transition.inputs {
                let label = if *weight > 1 { format!("{}", weight) } else { "".to_string() };
                dot.push_str(&format!("  \"{}\" -> \"{}\" [label=\"{}\"];\n", 
                    input_place, transition_id, label));
            }
            
            // 添加输出弧
            for (output_place, weight) in &transition.outputs {
                let label = if *weight > 1 { format!("{}", weight) } else { "".to_string() };
                dot.push_str(&format!("  \"{}\" -> \"{}\" [label=\"{}\"];\n", 
                    transition_id, output_place, label));
            }
        }
        
        dot.push_str("}\n");
        
        Ok(dot)
    }
}

// Petri网模型
#[derive(Debug, Clone)]
pub struct PetriNet {
    pub places: HashMap<String, Place>,
    pub transitions: HashMap<String, Transition>,
    pub initial_marking: HashMap<String, u32>,
    pub final_places: HashSet<String>,
}

// 位置
#[derive(Debug, Clone)]
pub struct Place {
    pub id: String,
    pub name: String,
    pub is_resource: bool,
}

// 转换
#[derive(Debug, Clone)]
pub struct Transition {
    pub id: String,
    pub name: String,
    pub inputs: HashMap<String, u32>,  // 输入位置ID -> 权重
    pub outputs: HashMap<String, u32>, // 输出位置ID -> 权重
    pub guard: Option<String>,         // 条件表达式
}
```

Petri网模型的优势：

1. **精确建模**：准确捕获工作流的并发和同步行为
2. **数学基础**：基于扎实的数学理论
3. **可视化**：支持直观的图形表示
4. **形式化分析**：支持死锁、活锁、到达性等属性验证
5. **资源建模**：能精确表示资源约束和竞争

### 10.4 时间和资源约束验证

系统通过扩展Petri网验证时间和资源约束：

```rust
pub struct ResourceTimeAnalyzer {
    petri_net_builder: Arc<PetriNetBuilder>,
}

impl ResourceTimeAnalyzer {
    pub fn new() -> Self {
        Self {
            petri_net_builder: Arc::new(PetriNetBuilder::new()),
        }
    }
    
    // 分析工作流的资源和时间约束
    pub async fn analyze(&self, workflow: &WorkflowDefinition) -> Result<ResourceTimeAnalysisResult, VerificationError> {
        // 分析资源使用
        let resource_usage = self.analyze_resource_usage(workflow).await?;
        
        // 分析时间约束
        let time_constraints = self.analyze_time_constraints(workflow).await?;
        
        // 验证资源约束
        let resource_violations = self.check_resource_violations(&resource_usage, workflow).await?;
        
        // 验证时间约束
        let time_violations = self.check_time_violations(&time_constraints, workflow).await?;
        
        // 生成临界路径
        let critical_path = self.find_critical_path(workflow, &time_constraints).await?;
        
        // 计算资源利用率
        let resource_utilization = self.calculate_resource_utilization(&resource_usage, workflow).await?;
        
        Ok(ResourceTimeAnalysisResult {
            resource_usage,
            time_constraints,
            resource_violations,
            time_violations,
            critical_path,
            resource_utilization,
        })
    }
    
    // 分析资源使用
    async fn analyze_resource_usage(&self, workflow: &WorkflowDefinition) -> Result<HashMap<String, ResourceUsage>, VerificationError> {
        let mut resources = HashMap::new();
        
        // 从工作流标签中解析资源定义
        for (key, value) in &workflow.tags {
            if key.starts_with("resource.") {
                let resource_id = key.trim_start_matches("resource.").to_string();
                let capacity = value.parse::<u32>().unwrap_or(1);
                
                resources.insert(resource_id.clone(), ResourceUsage {
                    resource_id: resource_id.clone(),
                    capacity,
                    allocation_points: Vec::new(),
                    release_points: Vec::new(),
                    peak_usage: 0,
                    bottleneck_likelihood: 0.0,
                });
            }
        }
        
        // 分析步骤的资源使用
        for step in &workflow.steps {
            for (tag_key, tag_value) in &step.tags {
                if tag_key.starts_with("uses.") {
                    let resource_id = tag_key.trim_start_matches("uses.").to_string();
                    
                    if let Some(resource) = resources.get_mut(&resource_id) {
                        // 解析资源使用量
                        let usage_amount = tag_value.parse::<u32>().unwrap_or(1);
                        
                        // 添加资源分配点
                        resource.allocation_points.push(ResourceAllocationPoint {
                            step_id: step.id.clone(),
                            amount: usage_amount,
                        });
                        
                        // 查找释放点
                        for transition in &workflow.transitions {
                            if transition.from == step.id {
                                resource.release_points.push(ResourceReleasePoint {
                                    step_id: step.id.clone(),
                                    transition_id: transition.id.clone(),
                                    target_step_id: transition.to.clone(),
                                });
                            }
                        }
                    }
                }
            }
        }
        
        // 使用Petri网模拟计算峰值使用和瓶颈可能性
        let petri_net = self.petri_net_builder.build_from_workflow(workflow).await?;
        
        // 执行资源使用分析
        for resource in resources.values_mut() {
            // 计算峰值使用
            resource.peak_usage = self.calculate_peak_resource_usage(&petri_net, resource).await?;
            
            // 计算瓶颈可能性
            resource.bottleneck_likelihood = self.calculate_bottleneck_likelihood(&petri_net, resource).await?;
        }
        
        Ok(resources)
    }
    
    // 计算资源峰值使用
    async fn calculate_peak_resource_usage(&self, petri_net: &PetriNet, resource: &ResourceUsage) -> Result<u32, VerificationError> {
        // 使用状态空间探索计算峰值资源使用
        // 简化实现
        Ok(resource.allocation_points.iter().map(|p| p.amount).sum())
    }
    
    // 计算资源成为瓶颈的可能性
    async fn calculate_bottleneck_likelihood(&self, petri_net: &PetriNet, resource: &ResourceUsage) -> Result<f64, VerificationError> {
        // 分析资源使用模式和容量
        let usage_ratio = resource.peak_usage as f64 / resource.capacity as f64;
        
        // 简化实现，实际应该考虑更多因素
        if usage_ratio >= 0.9 {
            Ok(0.9)
        } else if usage_ratio >= 0.7 {
            Ok(0.5)
        } else {
            Ok(0.1)
        }
    }
    
    // 分析时间约束
    async fn analyze_time_constraints(&self, workflow: &WorkflowDefinition) -> Result<TimeConstraintAnalysis, VerificationError> {
        let mut step_durations = HashMap::new();
        let mut path_durations = HashMap::new();
        let mut deadline_constraints = Vec::new();
        
        // 获取步骤估计时长
        for step in &workflow.steps {
            let duration = match step.tags.get("duration_ms") {
                Some(duration_str) => duration_str.parse::<u64>().unwrap_or(0),
                None => {
                    // 根据步骤类型估计默认持续时间
                    match &step.step_type {
                        StepType::Activity { .. } => 1000,  // 1秒
                        StepType::Decision { .. } => 100,   // 0.1秒
                        StepType::Parallel { .. } => 100,   // 0.1秒
                        StepType::Wait { .. } => 10000,     // 10秒
                        StepType::Timer { duration_ms, .. } => *duration_ms,
                        StepType::Human { .. } => 3600000,  // 1小时
                        StepType::SubWorkflow { .. } => 10000, // 10秒
                        StepType::Start => 0,
                        StepType::End => 0,
                    }
                }
            };
            
            step_durations.insert(step.id.clone(), duration);
        }
        
        // 查找工作流级别截止时间
        if let Some(timeout) = &workflow.timeout {
            match timeout {
                Timeout::DurationMs(duration_ms) => {
                    deadline_constraints.push(DeadlineConstraint {
                        constraint_type: DeadlineType::WorkflowDuration,
                        duration_ms: *duration_ms,
                        step_id: None,
                    });
                },
                Timeout::AbsoluteTime(timestamp) => {
                    deadline_constraints.push(DeadlineConstraint {
                        constraint_type: DeadlineType::WorkflowAbsolute,
                        duration_ms: 0,  // 不适用
                        step_id: None,
                    });
                },
            }
        }
        
        // 查找步骤级别截止时间
        for step in &workflow.steps {
            if let StepType::Human { intervention_point_id, .. } = &step.step_type {
                // 检查人工任务截止时间
                if let Some(intervention_point) = workflow.human_intervention_points.iter().find(|p| &p.id == intervention_point_id) {
                    if let Some(deadline) = &intervention_point.deadline {
                        match &deadline.deadline_type {
                            DeadlineType::Relative { hours } => {
                                deadline_constraints.push(DeadlineConstraint {
                                    constraint_type: DeadlineType::StepDuration,
                                    duration_ms: hours * 3600 * 1000,
                                    step_id: Some(step.id.clone()),
                                });
                            },
                            DeadlineType::Absolute { datetime: _ } => {
                                deadline_constraints.push(DeadlineConstraint {
                                    constraint_type: DeadlineType::StepAbsolute,
                                    duration_ms: 0,  // 不适用
                                    step_id: Some(step.id.clone()),
                                });
                            },
                            DeadlineType::BusinessDays { days, calendar_id: _ } => {
                                deadline_constraints.push(DeadlineConstraint {
                                    constraint_type: DeadlineType::StepBusinessDays,
                                    duration_ms: days * 24 * 3600 * 1000,
                                    step_id: Some(step.id.clone()),
                                });
                            },
                        }
                    }
                }
            } else if let StepType::Timer { duration_ms, .. } = &step.step_type {
                // 计时器固有的时间约束
                deadline_constraints.push(DeadlineConstraint {
                    constraint_type: DeadlineType::StepDuration,
                    duration_ms: *duration_ms,
                    step_id: Some(step.id.clone()),
                });
            }
        }
        
        // 计算所有可能路径的持续时间
        let paths = self.find_all_paths(workflow).await?;
        
        for (i, path) in paths.iter().enumerate() {
            let path_duration: u64 = path.iter()
                .map(|step_id| *step_durations.get(step_id).unwrap_or(&0))
                .sum();
                
            path_durations.insert(format!("path_{}", i), PathDuration {
                path_id: format!("path_{}", i),
                steps: path.clone(),
                duration_ms: path_duration,
            });
        }
        
        Ok(TimeConstraintAnalysis {
            step_durations,
            path_durations,
            deadline_constraints,
            total_min_duration: path_durations.values().map(|p| p.duration_ms).min().unwrap_or(0),
            total_max_duration: path_durations.values().map(|p| p.duration_ms).max().unwrap_or(0),
            total_avg_duration: if path_durations.is_empty() { 
                0 
            } else {
                path_durations.values().map(|p| p.duration_ms).sum::<u64>() / path_durations.len() as u64
            },
        })
    }
    
    // 查找所有可能的执行路径
    async fn find_all_paths(&self, workflow: &WorkflowDefinition) -> Result<Vec<Vec<String>>, VerificationError> {
        // 找到开始步骤
        let start_step = workflow.steps.iter()
            .find(|s| matches!(s.step_type, StepType::Start))
            .ok_or_else(|| VerificationError::ModelError("工作流缺少开始步骤".to_string()))?;
            
        // 使用深度优先搜索查找所有路径
        let mut paths = Vec::new();
        let mut current_path = vec![start_step.id.clone()];
        let mut visited = HashSet::new();
        
        self.dfs_find_paths(
            workflow, 
            &start_step.id, 
            &mut current_path, 
            &mut visited, 
            &mut paths
        ).await?;
        
        Ok(paths)
    }
    
    // 深度优先搜索找出所有路径
    async fn dfs_find_paths(
        &self,
        workflow: &WorkflowDefinition,
        current_step_id: &str,
        current_path: &mut Vec<String>,
        visited: &mut HashSet<String>,
        paths: &mut Vec<Vec<String>>
    ) -> Result<(), VerificationError> {
        visited.insert(current_step_id.to_string());
        
        // 检查是否到达终止步骤
        if workflow.steps.iter().any(|s| s.id == *current_step_id && matches!(s.step_type, StepType::End)) {
            paths.push(current_path.clone());
            visited.remove(current_step_id);
            return Ok(());
        }
        
        // 查找所有可能的下一步
        let next_steps: Vec<String> = workflow.transitions.iter()
            .filter(|t| t.from == *current_step_id)
            .map(|t| t.to.clone())
            .collect();
            
        // 如果没有下一步，则当前路径终止
        if next_steps.is_empty() {
            paths.push(current_path.clone());
        } else {
            // 继续深度搜索
            for next_step in next_steps {
                // 避免循环
                if !visited.contains(&next_step) {
                    current_path.push(next_step.clone());
                    self.dfs_find_paths(workflow, &next_step, current_path, visited, paths).await?;
                    current_path.pop();
                }
            }
        }
        
        visited.remove(current_step_id);
        Ok(())
    }
    
    // 检查资源违规情况
    async fn check_resource_violations(
        &self,
        resource_usage: &HashMap<String, ResourceUsage>,
        workflow: &WorkflowDefinition
    ) -> Result<Vec<ResourceViolation>, VerificationError> {
        let mut violations = Vec::new();
        
        for (resource_id, usage) in resource_usage {
            // 检查资源超额分配
            if usage.peak_usage > usage.capacity {
                violations.push(ResourceViolation {
                    resource_id: resource_id.clone(),
                    violation_type: ResourceViolationType::Overallocation,
                    description: format!(
                        "资源 '{}' 的最大并发使用 ({}) 超过了其容量 ({})",
                        resource_id, usage.peak_usage, usage.capacity
                    ),
                    affected_steps: usage.allocation_points.iter()
                        .map(|p| p.step_id.clone())
                        .collect(),
                });
            }
            
            // 检查资源泄漏
            let mut leaked_steps = Vec::new();
            for allocation in &usage.allocation_points {
                let step_id = &allocation.step_id;
                
                // 检查步骤是否有释放点
                if !usage.release_points.iter().any(|r| &r.step_id == step_id) {
                    leaked_steps.push(step_id.clone());
                }
            }
            
            if !leaked_steps.is_empty() {
                violations.push(ResourceViolation {
                    resource_id: resource_id.clone(),
                    violation_type: ResourceViolationType::ResourceLeak,
                    description: format!(
                        "资源 '{}' 在某些步骤中被分配但没有被释放",
                        resource_id
                    ),
                    affected_steps: leaked_steps,
                });
            }
            
            // 检查资源瓶颈
            if usage.bottleneck_likelihood > 0.8 {
                violations.push(ResourceViolation {
                    resource_id: resource_id.clone(),
                    violation_type: ResourceViolationType::PotentialBottleneck,
                    description: format!(
                        "资源 '{}' 很可能成为性能瓶颈 (可能性: {:.1}%)",
                        resource_id, usage.bottleneck_likelihood * 100.0
                    ),
                    affected_steps: usage.allocation_points.iter()
                        .map(|p| p.step_id.clone())
                        .collect(),
                });
            }
        }
        
        Ok(violations)
    }
    
    // 检查时间约束违规
    async fn check_time_violations(
        &self, 
        time_analysis: &TimeConstraintAnalysis,
        workflow: &WorkflowDefinition
    ) -> Result<Vec<TimeViolation>, VerificationError> {
        let mut violations = Vec::new();
        
        // 检查工作流整体超时
        for constraint in &time_analysis.deadline_constraints {
            if constraint.step_id.is_none() {
                // 工作流级别约束
                match constraint.constraint_type {
                    DeadlineType::WorkflowDuration => {
                        if time_analysis.total_max_duration > constraint.duration_ms {
                            // 找出超时的路径
                            let timeout_paths: Vec<String> = time_analysis.path_durations.iter()
                                .filter(|(_, p)| p.duration_ms > constraint.duration_ms)
                                .map(|(id, _)| id.clone())
                                .collect();
                                
                            violations.push(TimeViolation {
                                violation_type: TimeViolationType::WorkflowDeadlineExceeded,
                                description: format!(
                                    "工作流最大执行时间 ({} ms) 超过了截止时间 ({} ms)",
                                    time_analysis.total_max_duration, constraint.duration_ms
                                ),
                                constraint: constraint.clone(),
                                affected_paths: timeout_paths,
                            });
                        }
                    },
                    _ => {
                        // 其他类型的工作流约束
                    }
                }
            } else {
                // 步骤级别约束
                match constraint.constraint_type {
                    DeadlineType::StepDuration => {
                        if let Some(step_id) = &constraint.step_id {
                            if let Some(&step_duration) = time_analysis.step_durations.get(step_id) {
                                if step_duration > constraint.duration_ms {
                                    violations.push(TimeViolation {
                                        violation_type: TimeViolationType::StepDeadlineExceeded,
                                        description: format!(
                                            "步骤 '{}' 的执行时间 ({} ms) 超过了截止时间 ({} ms)",
                                            step_id, step_duration, constraint.duration_ms
                                        ),
                                        constraint: constraint.clone(),
                                        affected_paths: Vec::new(),
                                    });
                                }
                            }
                        }
                    },
                    _ => {
                        // 其他类型的步骤约束
                    }
                }
            }
        }
        
        Ok(violations)
    }
    
    // 查找临界路径
    async fn find_critical_path(
        &self,
        workflow: &WorkflowDefinition,
        time_analysis: &TimeConstraintAnalysis
    ) -> Result<CriticalPathInfo, VerificationError> {
        // 找出持续时间最长的路径
        if let Some((path_id, path_info)) = time_analysis.path_durations.iter()
            .max_by_key(|(_, info)| info.duration_ms) {
                
            // 计算每一步在临界路径上的松弛时间（始终为0）
            let mut slack_times = HashMap::new();
            for step_id in &path_info.steps {
                slack_times.insert(step_id.clone(), 0u64);
            }
            
            // 找出瓶颈步骤（持续时间最长的步骤）
            let bottleneck_step = path_info.steps.iter()
                .filter_map(|step_id| {
                    time_analysis.step_durations.get(step_id)
                        .map(|&duration| (step_id, duration))
                })
                .max_by_key(|(_, duration)| *duration);
                
            // 构建临界路径信息
            Ok(CriticalPathInfo {
                path_id: path_id.clone(),
                steps: path_info.steps.clone(),
                duration_ms: path_info.duration_ms,
                bottleneck_step: bottleneck_step.map(|(step_id, _)| step_id.clone()),
                slack_times,
            })
        } else {
            Err(VerificationError::ModelError("无法找到临界路径".to_string()))
        }
    }
    
    // 计算资源利用率
    async fn calculate_resource_utilization(
        &self,
        resource_usage: &HashMap<String, ResourceUsage>,
        workflow: &WorkflowDefinition
    ) -> Result<HashMap<String, f64>, VerificationError> {
        let mut utilization = HashMap::new();
        
        for (resource_id, usage) in resource_usage {
            // 简化实现，假设资源利用率与峰值使用成正比
            let util_rate = usage.peak_usage as f64 / usage.capacity as f64;
            utilization.insert(resource_id.clone(), util_rate);
        }
        
        Ok(utilization)
    }
    
    // 生成资源时间分析报告
    pub fn generate_report(
        &self,
        analysis: &ResourceTimeAnalysisResult
    ) -> String {
        let mut report = String::new();
        
        report.push_str("# 工作流资源与时间分析报告\n\n");
        
        // 添加时间分析摘要
        report.push_str("## 时间分析\n\n");
        report.push_str(&format!("- 最短路径执行时间: {} ms\n", analysis.time_constraints.total_min_duration));
        report.push_str(&format!("- 最长路径执行时间: {} ms\n", analysis.time_constraints.total_max_duration));
        report.push_str(&format!("- 平均路径执行时间: {} ms\n\n", analysis.time_constraints.total_avg_duration));
        
        // 添加临界路径信息
        report.push_str("### 临界路径\n\n");
        report.push_str(&format!("- 路径ID: {}\n", analysis.critical_path.path_id));
        report.push_str(&format!("- 持续时间: {} ms\n", analysis.critical_path.duration_ms));
        report.push_str("- 步骤序列:\n");
        
        for step in &analysis.critical_path.steps {
            report.push_str(&format!("  - {}\n", step));
        }
        
        if let Some(bottleneck) = &analysis.critical_path.bottleneck_step {
            report.push_str(&format!("\n- 瓶颈步骤: {}\n", bottleneck));
        }
        
        report.push_str("\n## 资源分析\n\n");
        
        // 添加资源使用摘要
        for (resource_id, usage) in &analysis.resource_usage {
            report.push_str(&format!("### 资源: {}\n\n", resource_id));
            report.push_str(&format!("- 资源容量: {}\n", usage.capacity));
            report.push_str(&format!("- 峰值使用: {}\n", usage.peak_usage));
            report.push_str(&format!("- 利用率: {:.1}%\n", 
                analysis.resource_utilization.get(resource_id).unwrap_or(&0.0) * 100.0));
            report.push_str(&format!("- 瓶颈可能性: {:.1}%\n\n", usage.bottleneck_likelihood * 100.0));
            
            report.push_str("#### 资源分配点\n\n");
            for point in &usage.allocation_points {
                report.push_str(&format!("- 步骤 {} (使用量: {})\n", point.step_id, point.amount));
            }
            
            report.push_str("\n");
        }
        
        // 添加违规信息
        if !analysis.resource_violations.is_empty() || !analysis.time_violations.is_empty() {
            report.push_str("## 违规情况\n\n");
            
            if !analysis.resource_violations.is_empty() {
                report.push
# 分布式工作流执行引擎设计方案（续）

## 10. 形式化验证与证明（续）

### 10.4 时间和资源约束验证（续）

```rust
            if !analysis.resource_violations.is_empty() {
                report.push_str("### 资源违规\n\n");
                
                for violation in &analysis.resource_violations {
                    report.push_str(&format!("- **{}**: {}\n", violation.resource_id, violation.description));
                    report.push_str("  影响的步骤:\n");
                    
                    for step in &violation.affected_steps {
                        report.push_str(&format!("  - {}\n", step));
                    }
                    
                    report.push_str("\n");
                }
            }
            
            if !analysis.time_violations.is_empty() {
                report.push_str("### 时间违规\n\n");
                
                for violation in &analysis.time_violations {
                    report.push_str(&format!("- {}\n", violation.description));
                    
                    if !violation.affected_paths.is_empty() {
                        report.push_str("  影响的路径:\n");
                        
                        for path in &violation.affected_paths {
                            report.push_str(&format!("  - {}\n", path));
                        }
                    }
                    
                    report.push_str("\n");
                }
            }
        }
        
        // 添加优化建议
        report.push_str("## 优化建议\n\n");
        
        // 基于瓶颈提供建议
        if let Some(bottleneck) = &analysis.critical_path.bottleneck_step {
            report.push_str(&format!("- 考虑优化步骤 {} 的执行时间，它是临界路径上的瓶颈。\n", bottleneck));
        }
        
        // 基于资源使用提供建议
        for (resource_id, usage) in &analysis.resource_usage {
            if usage.bottleneck_likelihood > 0.7 {
                report.push_str(&format!("- 考虑增加资源 {} 的容量，当前利用率为 {:.1}%。\n", 
                    resource_id, 
                    analysis.resource_utilization.get(resource_id).unwrap_or(&0.0) * 100.0));
            } else if let Some(util) = analysis.resource_utilization.get(resource_id) {
                if *util < 0.3 {
                    report.push_str(&format!("- 资源 {} 的利用率较低 ({:.1}%)，考虑减少其分配或与其他资源共享。\n", 
                        resource_id, util * 100.0));
                }
            }
        }
        
        report
    }
}

// 资源时间分析结果
#[derive(Debug, Clone)]
pub struct ResourceTimeAnalysisResult {
    pub resource_usage: HashMap<String, ResourceUsage>,
    pub time_constraints: TimeConstraintAnalysis,
    pub resource_violations: Vec<ResourceViolation>,
    pub time_violations: Vec<TimeViolation>,
    pub critical_path: CriticalPathInfo,
    pub resource_utilization: HashMap<String, f64>,
}

// 资源使用
#[derive(Debug, Clone)]
pub struct ResourceUsage {
    pub resource_id: String,
    pub capacity: u32,
    pub allocation_points: Vec<ResourceAllocationPoint>,
    pub release_points: Vec<ResourceReleasePoint>,
    pub peak_usage: u32,
    pub bottleneck_likelihood: f64,
}

// 资源分配点
#[derive(Debug, Clone)]
pub struct ResourceAllocationPoint {
    pub step_id: String,
    pub amount: u32,
}

// 资源释放点
#[derive(Debug, Clone)]
pub struct ResourceReleasePoint {
    pub step_id: String,
    pub transition_id: String,
    pub target_step_id: String,
}

// 时间约束分析
#[derive(Debug, Clone)]
pub struct TimeConstraintAnalysis {
    pub step_durations: HashMap<String, u64>,
    pub path_durations: HashMap<String, PathDuration>,
    pub deadline_constraints: Vec<DeadlineConstraint>,
    pub total_min_duration: u64,
    pub total_max_duration: u64,
    pub total_avg_duration: u64,
}

// 路径持续时间
#[derive(Debug, Clone)]
pub struct PathDuration {
    pub path_id: String,
    pub steps: Vec<String>,
    pub duration_ms: u64,
}

// 截止时间约束
#[derive(Debug, Clone)]
pub struct DeadlineConstraint {
    pub constraint_type: DeadlineType,
    pub duration_ms: u64,
    pub step_id: Option<String>,
}

// 截止时间类型
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeadlineType {
    WorkflowDuration,
    WorkflowAbsolute,
    StepDuration,
    StepAbsolute,
    StepBusinessDays,
}

// 临界路径信息
#[derive(Debug, Clone)]
pub struct CriticalPathInfo {
    pub path_id: String,
    pub steps: Vec<String>,
    pub duration_ms: u64,
    pub bottleneck_step: Option<String>,
    pub slack_times: HashMap<String, u64>,
}

// 资源违规
#[derive(Debug, Clone)]
pub struct ResourceViolation {
    pub resource_id: String,
    pub violation_type: ResourceViolationType,
    pub description: String,
    pub affected_steps: Vec<String>,
}

// 资源违规类型
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResourceViolationType {
    Overallocation,
    ResourceLeak,
    PotentialBottleneck,
}

// 时间违规
#[derive(Debug, Clone)]
pub struct TimeViolation {
    pub violation_type: TimeViolationType,
    pub description: String,
    pub constraint: DeadlineConstraint,
    pub affected_paths: Vec<String>,
}

// 时间违规类型
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TimeViolationType {
    WorkflowDeadlineExceeded,
    StepDeadlineExceeded,
}
```

时间和资源约束验证的优势：

1. **精确建模**：同时捕获时间和资源约束
2. **冲突检测**：识别资源争用和时间冲突
3. **临界路径分析**：确定性能瓶颈
4. **资源优化**：提供资源利用率优化建议
5. **截止时间验证**：确保满足业务SLA需求

## 11. 部署与运维

### 11.1 容器化部署

系统设计为原生云应用，支持容器化部署：

```rust
// Dockerfile
/*
FROM rust:1.67 as builder

WORKDIR /usr/src/workflow-engine

# 拷贝Cargo配置文件
COPY Cargo.toml Cargo.lock ./

# 创建空的主文件，以便缓存依赖编译结果
RUN mkdir -p src && echo "fn main() {}" > src/main.rs

# 编译依赖项
RUN cargo build --release

# 拷贝源代码
COPY src ./src

# 修改文件以触发重新编译
RUN touch src/main.rs

# 编译应用
RUN cargo build --release

# 最终镜像
FROM debian:bullseye-slim

# 安装运行时依赖
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    libssl-dev \
    && rm -rf /var/lib/apt/lists/*

# 设置工作目录
WORKDIR /app

# 拷贝编译好的二进制文件
COPY --from=builder /usr/src/workflow-engine/target/release/workflow-engine /app/

# 拷贝配置文件
COPY config /app/config/

# 暴露API端口
EXPOSE 8080

# 暴露监控端口
EXPOSE 9090

# 设置环境变量
ENV RUST_LOG=info
ENV CONFIG_PATH=/app/config/config.yaml

# 运行应用
CMD ["/app/workflow-engine"]
*/

// docker-compose.yml
/*
version: '3.8'

services:
  workflow-api:
    image: workflow-engine:latest
    ports:
      - "8080:8080"
      - "9090:9090"
    environment:
      - RUST_LOG=info
      - DATABASE_URL=postgres://postgres:password@postgres:5432/workflow
      - REDIS_URL=redis://redis:6379
      - KAFKA_BROKERS=kafka:9092
      - JWT_SECRET=${JWT_SECRET}
      - MASTER_KEY=${MASTER_KEY}
    volumes:
      - ./config:/app/config
    depends_on:
      - postgres
      - redis
      - kafka
    restart: unless-stopped
    deploy:
      replicas: 3
      update_config:
        parallelism: 1
        delay: 10s
      restart_policy:
        condition: on-failure
      resources:
        limits:
          cpus: '1'
          memory: 1G
        reservations:
          cpus: '0.5'
          memory: 512M

  postgres:
    image: postgres:14
    environment:
      - POSTGRES_PASSWORD=password
      - POSTGRES_DB=workflow
    volumes:
      - postgres-data:/var/lib/postgresql/data
      - ./init-scripts:/docker-entrypoint-initdb.d
    ports:
      - "5432:5432"
    restart: unless-stopped
    deploy:
      resources:
        limits:
          cpus: '2'
          memory: 2G

  redis:
    image: redis:6
    command: redis-server --appendonly yes
    volumes:
      - redis-data:/data
    ports:
      - "6379:6379"
    restart: unless-stopped
    deploy:
      resources:
        limits:
          cpus: '0.5'
          memory: 512M

  kafka:
    image: wurstmeister/kafka:2.13-2.8.1
    ports:
      - "9092:9092"
    environment:
      - KAFKA_ADVERTISED_HOST_NAME=kafka
      - KAFKA_ZOOKEEPER_CONNECT=zookeeper:2181
      - KAFKA_CREATE_TOPICS=workflow-events:8:1,task-events:8:1
    depends_on:
      - zookeeper
    restart: unless-stopped
    deploy:
      resources:
        limits:
          cpus: '1'
          memory: 1G

  zookeeper:
    image: wurstmeister/zookeeper:3.4.6
    ports:
      - "2181:2181"
    restart: unless-stopped
    deploy:
      resources:
        limits:
          cpus: '0.5'
          memory: 512M

  grafana:
    image: grafana/grafana:9.3.2
    ports:
      - "3000:3000"
    volumes:
      - grafana-data:/var/lib/grafana
      - ./grafana/provisioning:/etc/grafana/provisioning
    environment:
      - GF_SECURITY_ADMIN_PASSWORD=${GRAFANA_PASSWORD}
      - GF_USERS_ALLOW_SIGN_UP=false
    depends_on:
      - prometheus
    restart: unless-stopped
    deploy:
      resources:
        limits:
          cpus: '0.5'
          memory: 512M

  prometheus:
    image: prom/prometheus:v2.41.0
    ports:
      - "9091:9090"
    volumes:
      - ./prometheus/prometheus.yml:/etc/prometheus/prometheus.yml
      - prometheus-data:/prometheus
    command:
      - '--config.file=/etc/prometheus/prometheus.yml'
      - '--storage.tsdb.path=/prometheus'
      - '--web.console.libraries=/usr/share/prometheus/console_libraries'
      - '--web.console.templates=/usr/share/prometheus/consoles'
    restart: unless-stopped
    deploy:
      resources:
        limits:
          cpus: '0.5'
          memory: 512M

volumes:
  postgres-data:
  redis-data:
  grafana-data:
  prometheus-data:
*/
```

容器化部署的优势：

1. **环境一致性**：消除"在我机器上可以运行"的问题
2. **易于扩展**：水平扩展API和执行节点
3. **资源隔离**：控制每个组件的资源使用
4. **部署自动化**：支持CI/CD流水线
5. **版本控制**：镜像标签和版本管理
6. **快速恢复**：容器失败时快速重启

### 11.2 Kubernetes集成

系统提供Kubernetes原生支持：

```yaml
# kubernetes/workflow-namespace.yaml
apiVersion: v1
kind: Namespace
metadata:
  name: workflow-engine

---
# kubernetes/workflow-configmap.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: workflow-config
  namespace: workflow-engine
data:
  config.yaml: |
    server:
      host: "0.0.0.0"
      port: 8080
    
    storage:
      type: "postgres"
      connection_string: "${DATABASE_URL}"
      
    messaging:
      type: "kafka"
      connection_string: "${KAFKA_BROKERS}"
      
    cache:
      type: "redis"
      connection_string: "${REDIS_URL}"
      
    auth:
      jwt_expiration_minutes: 60
      api_key_enabled: true
      
    encryption:
      enabled: true
      
    monitoring:
      metrics_enabled: true
      metrics_port: 9090
      trace_enabled: true
      log_level: "info"
    
    workflow:
      max_concurrent_tasks: 1000
      default_task_timeout_seconds: 300
      max_retry_attempts: 3
      scheduler_interval_ms: 100

---
# kubernetes/workflow-secrets.yaml
apiVersion: v1
kind: Secret
metadata:
  name: workflow-secrets
  namespace: workflow-engine
type: Opaque
data:
  jwt-secret: ${JWT_SECRET_BASE64}
  master-key: ${MASTER_KEY_BASE64}
  db-password: ${DB_PASSWORD_BASE64}
  redis-password: ${REDIS_PASSWORD_BASE64}

---
# kubernetes/workflow-deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: workflow-api
  namespace: workflow-engine
  labels:
    app: workflow-api
spec:
  replicas: 3
  selector:
    matchLabels:
      app: workflow-api
  strategy:
    type: RollingUpdate
    rollingUpdate:
      maxSurge: 1
      maxUnavailable: 0
  template:
    metadata:
      labels:
        app: workflow-api
      annotations:
        prometheus.io/scrape: "true"
        prometheus.io/port: "9090"
        prometheus.io/path: "/metrics"
    spec:
      containers:
      - name: workflow-api
        image: workflow-engine:latest
        imagePullPolicy: Always
        ports:
        - containerPort: 8080
          name: http
        - containerPort: 9090
          name: metrics
        env:
        - name: RUST_LOG
          value: "info"
        - name: CONFIG_PATH
          value: "/app/config/config.yaml"
        - name: DATABASE_URL
          valueFrom:
            secretKeyRef:
              name: workflow-secrets
              key: database-url
        - name: REDIS_URL
          valueFrom:
            secretKeyRef:
              name: workflow-secrets
              key: redis-url
        - name: KAFKA_BROKERS
          valueFrom:
            configMapKeyRef:
              name: workflow-config
              key: kafka-brokers
        - name: JWT_SECRET
          valueFrom:
            secretKeyRef:
              name: workflow-secrets
              key: jwt-secret
        - name: MASTER_KEY
          valueFrom:
            secretKeyRef:
              name: workflow-secrets
              key: master-key
        - name: NODE_ID
          valueFrom:
            fieldRef:
              fieldPath: metadata.name
        resources:
          limits:
            cpu: "1"
            memory: "1Gi"
          requests:
            cpu: "500m"
            memory: "512Mi"
        readinessProbe:
          httpGet:
            path: /health
            port: http
          initialDelaySeconds: 5
          periodSeconds: 10
        livenessProbe:
          httpGet:
            path: /health
            port: http
          initialDelaySeconds: 15
          periodSeconds: 20
        volumeMounts:
        - name: config-volume
          mountPath: /app/config
      volumes:
      - name: config-volume
        configMap:
          name: workflow-config

---
# kubernetes/workflow-service.yaml
apiVersion: v1
kind: Service
metadata:
  name: workflow-api
  namespace: workflow-engine
  labels:
    app: workflow-api
spec:
  selector:
    app: workflow-api
  ports:
  - name: http
    port: 80
    targetPort: 8080
  - name: metrics
    port: 9090
    targetPort: 9090
  type: ClusterIP

---
# kubernetes/workflow-ingress.yaml
apiVersion: networking.k8s.io/v1
kind: Ingress
metadata:
  name: workflow-api
  namespace: workflow-engine
  annotations:
    kubernetes.io/ingress.class: nginx
    nginx.ingress.kubernetes.io/ssl-redirect: "true"
    cert-manager.io/cluster-issuer: letsencrypt-prod
spec:
  tls:
  - hosts:
    - workflow-api.example.com
    secretName: workflow-api-tls
  rules:
  - host: workflow-api.example.com
    http:
      paths:
      - path: /
        pathType: Prefix
        backend:
          service:
            name: workflow-api
            port:
              name: http

---
# kubernetes/workflow-hpa.yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: workflow-api
  namespace: workflow-engine
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: workflow-api
  minReplicas: 3
  maxReplicas: 10
  metrics:
  - type: Resource
    resource:
      name: cpu
      target:
        type: Utilization
        averageUtilization: 70
  - type: Resource
    resource:
      name: memory
      target:
        type: Utilization
        averageUtilization: 80
  behavior:
    scaleDown:
      stabilizationWindowSeconds: 300
      policies:
      - type: Percent
        value: 10
        periodSeconds: 60
    scaleUp:
      stabilizationWindowSeconds: 60
      policies:
      - type: Percent
        value: 100
        periodSeconds: 60
      selectPolicy: Max
```

Kubernetes集成优势：

1. **声明式配置**：基础设施即代码
2. **自动扩展**：基于负载自动扩展组件
3. **自我修复**：自动重启失败的容器
4. **滚动更新**：无停机部署新版本
5. **服务发现**：自动发现和连接服务
6. **负载均衡**：在多个实例间分配流量
7. **配置管理**：通过ConfigMaps和Secrets管理配置

### 11.3 配置管理

系统提供灵活的配置管理：

```rust
pub struct ConfigManager {
    config: Arc<RwLock<Config>>,
    file_path: Option<String>,
    environment_prefix: String,
    refresh_interval: Option<Duration>,
    refresh_task: Option<JoinHandle<()>>,
}

impl ConfigManager {
    pub fn new() -> Self {
        Self {
            config: Arc::new(RwLock::new(Config::default())),
            file_path: None,
            environment_prefix: "WORKFLOW_".to_string(),
            refresh_interval: None,
            refresh_task: None,
        }
    }
    
    pub fn with_file(mut self, file_path: &str) -> Self {
        self.file_path = Some(file_path.to_string());
        self
    }
    
    pub fn with_environment_prefix(mut self, prefix: &str) -> Self {
        self.environment_prefix = prefix.to_string();
        self
    }
    
    pub fn with_refresh_interval(mut self, interval: Duration) -> Self {
        self.refresh_interval = Some(interval);
        self
    }
    
    pub async fn initialize(&mut self) -> Result<(), ConfigError> {
        // 加载初始配置
        self.reload_config().await?;
        
        // 如果设置了刷新间隔，启动刷新任务
        if let Some(interval) = self.refresh_interval {
            let config = self.config.clone();
            let file_path = self.file_path.clone();
            let prefix = self.environment_prefix.clone();
            
            self.refresh_task = Some(tokio::spawn(async move {
                let mut interval_timer = tokio::time::interval(interval);
                
                loop {
                    interval_timer.tick().await;
                    
                    // 尝试重新加载配置
                    if let Err(e) = Self::reload_from_sources(config.clone(), file_path.as_deref(), &prefix).await {
                        log::error!("刷新配置失败: {}", e);
                    } else {
                        log::debug!("配置已刷新");
                    }
                }
            }));
        }
        
        Ok(())
    }
    
    async fn reload_config(&self) -> Result<(), ConfigError> {
        Self::reload_from_sources(
            self.config.clone(), 
            self.file_path.as_deref(), 
            &self.environment_prefix
        ).await
    }
    
    async fn reload_from_sources(
        config: Arc<RwLock<Config>>,
        file_path: Option<&str>,
        env_prefix: &str
    ) -> Result<(), ConfigError> {
        // 从默认值开始
        let mut new_config = Config::default();
        
        // 从文件加载
        if let Some(path) = file_path {
            if let Ok(file_content) = tokio::fs::read_to_string(path).await {
                // 尝试YAML格式
                if path.ends_with(".yaml") || path.ends_with(".yml") {
                    if let Ok(file_config) = serde_yaml::from_str::<Config>(&file_content) {
                        new_config = file_config;
                    } else {
                        return Err(ConfigError::ParseError("无法解析YAML配置文件".to_string()));
                    }
                } 
                // 尝试JSON格式
                else if path.ends_with(".json") {
                    if let Ok(file_config) = serde_json::from_str::<Config>(&file_content) {
                        new_config = file_config;
                    } else {
                        return Err(ConfigError::ParseError("无法解析JSON配置文件".to_string()));
                    }
                } 
                // 尝试TOML格式
                else if path.ends_with(".toml") {
                    #[cfg(feature = "toml")]
                    if let Ok(file_config) = toml::from_str::<Config>(&file_content) {
                        new_config = file_config;
                    } else {
                        return Err(ConfigError::ParseError("无法解析TOML配置文件".to_string()));
                    }
                    
                    #[cfg(not(feature = "toml"))]
                    return Err(ConfigError::UnsupportedFormat("TOML格式不受支持".to_string()));
                } else {
                    return Err(ConfigError::UnsupportedFormat("未知的配置文件格式".to_string()));
                }
            } else {
                log::warn!("无法读取配置文件: {}", path);
            }
        }
        
        // 从环境变量覆盖
        Self::override_from_env(&mut new_config, env_prefix);
        
        // 更新配置
        let mut config_guard = config.write().await;
        *config_guard = new_config;
        
        Ok(())
    }
    
    fn override_from_env(config: &mut Config, prefix: &str) {
        // 重写服务器配置
        if let Ok(host) = std::env::var(format!("{}SERVER_HOST", prefix)) {
            config.server.host = host;
        }
        
        if let Ok(port) = std::env::var(format!("{}SERVER_PORT", prefix))
            .map(|s| s.parse::<u16>())
            .and_then(|r| r.map_err(|_| std::env::VarError::NotPresent)) {
            config.server.port = port;
        }
        
        // 重写数据库配置
        if let Ok(url) = std::env::var(format!("{}DATABASE_URL", prefix)) {
            config.storage.connection_string = url;
        }
        
        // 重写消息队列配置
        if let Ok(brokers) = std::env::var(format!("{}KAFKA_BROKERS", prefix)) {
            config.messaging.connection_string = brokers;
        }
        
        if let Ok(msg_type) = std::env::var(format!("{}MESSAGING_TYPE", prefix)) {
            config.messaging.messaging_type = match msg_type.to_lowercase().as_str() {
                "kafka" => MessagingType::Kafka,
                "nats" => MessagingType::Nats,
                "rabbitmq" => MessagingType::RabbitMQ,
                "redis" => MessagingType::Redis,
                "mqtt" => MessagingType::Mqtt,
                _ => config.messaging.messaging_type,
            };
        }
        
        // 其他配置项...
    }
    
    pub async fn get_config(&self) -> Config {
        self.config.read().await.clone()
    }
    
    pub async fn get_server_config(&self) -> ServerConfig {
        self.config.read().await.server.clone()
    }
    
    pub async fn get_storage_config(&self) -> StorageConfig {
        self.config.read().await.storage.clone()
    }
    
    pub async fn get_messaging_config(&self) -> MessagingConfig {
        self.config.read().await.messaging.clone()
    }
    
    // 其他getter方法...
}

// 配置结构
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Config {
    #[serde(default)]
    pub server: ServerConfig,
    
    #[serde(default)]
    pub storage: StorageConfig,
    
    #[serde(default)]
    pub messaging: MessagingConfig,
    
    #[serde(default)]
    pub cache: CacheConfig,
    
    #[serde(default)]
    pub auth: AuthConfig,
    
    #[serde(default)]
    pub encryption: EncryptionConfig,
    
    #[serde(default)]
    pub monitoring: MonitoringConfig,
    
    #[serde(default)]
    pub workflow: WorkflowConfig,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            server: ServerConfig::default(),
            storage: StorageConfig::default(),
            messaging: MessagingConfig::default(),
            cache: CacheConfig::default(),
            auth: AuthConfig::default(),
            encryption: EncryptionConfig::default(),
            monitoring: MonitoringConfig::default(),
            workflow: WorkflowConfig::default(),
        }
    }
}

// 服务器配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServerConfig {
    pub host: String,
    pub port: u16,
    pub cors_allowed_origins: Vec<String>,
    pub request_timeout_seconds: u64,
}

impl Default for ServerConfig {
    fn default() -> Self {
        Self {
            host: "127.0.0.1".to_string(),
            port: 8080,
            cors_allowed_origins: vec!["*".to_string()],
            request_timeout_seconds: 30,
        }
    }
}

// 存储配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StorageConfig {
    pub storage_type: StorageType,
    pub connection_string: String,
    pub min_connections: u32,
    pub max_connections: u32,
    pub connection_timeout_seconds: u64,
}

impl Default for StorageConfig {
    fn default() -> Self {
        Self {
            storage_type: StorageType::Postgres,
            connection_string: "postgres://postgres:password@localhost/workflow".to_string(),
            min_connections: 5,
            max_connections: 20,
            connection_timeout_seconds: 30,
        }
    }
}

// 消息队列配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MessagingConfig {
    pub messaging_type: MessagingType,
    pub connection_string: String,
    pub max_retries: u32,
    pub retry_interval_ms: u64,
}

impl Default for MessagingConfig {
    fn default() -> Self {
        Self {
            messaging_type: MessagingType::Kafka,
            connection_string: "localhost:9092".to_string(),
            max_retries: 3,
            retry_
# 分布式工作流执行引擎设计方案（续）

## 11. 部署与运维（续）

### 11.3 配置管理（续）

```rust
impl Default for MessagingConfig {
    fn default() -> Self {
        Self {
            messaging_type: MessagingType::Kafka,
            connection_string: "localhost:9092".to_string(),
            max_retries: 3,
            retry_interval_ms: 1000,
        }
    }
}

// 存储类型
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum StorageType {
    #[serde(rename = "postgres")]
    Postgres,
    
    #[serde(rename = "mysql")]
    MySQL,
    
    #[serde(rename = "mongodb")]
    MongoDB,
    
    #[serde(rename = "sqlite")]
    SQLite,
}

// 消息队列类型
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum MessagingType {
    #[serde(rename = "kafka")]
    Kafka,
    
    #[serde(rename = "nats")]
    Nats,
    
    #[serde(rename = "rabbitmq")]
    RabbitMQ,
    
    #[serde(rename = "redis")]
    Redis,
    
    #[serde(rename = "mqtt")]
    Mqtt,
}

// 缓存配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheConfig {
    pub cache_type: CacheType,
    pub connection_string: String,
    pub ttl_seconds: u64,
    pub max_size: usize,
}

impl Default for CacheConfig {
    fn default() -> Self {
        Self {
            cache_type: CacheType::Redis,
            connection_string: "redis://localhost:6379".to_string(),
            ttl_seconds: 3600,
            max_size: 10000,
        }
    }
}

// 缓存类型
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum CacheType {
    #[serde(rename = "redis")]
    Redis,
    
    #[serde(rename = "memory")]
    Memory,
}

// 认证配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuthConfig {
    pub jwt_secret: String,
    pub jwt_expiration_minutes: u64,
    pub api_key_enabled: bool,
    pub api_key_expiration_days: Option<u32>,
}

impl Default for AuthConfig {
    fn default() -> Self {
        Self {
            jwt_secret: "change_me_in_production".to_string(),
            jwt_expiration_minutes: 60,
            api_key_enabled: true,
            api_key_expiration_days: Some(90),
        }
    }
}

// 加密配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EncryptionConfig {
    pub enabled: bool,
    pub master_key: String,
    pub key_rotation_days: u32,
}

impl Default for EncryptionConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            master_key: "change_me_in_production".to_string(),
            key_rotation_days: 90,
        }
    }
}

// 监控配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MonitoringConfig {
    pub metrics_enabled: bool,
    pub metrics_port: u16,
    pub trace_enabled: bool,
    pub trace_sample_rate: f64,
    pub log_level: String,
}

impl Default for MonitoringConfig {
    fn default() -> Self {
        Self {
            metrics_enabled: true,
            metrics_port: 9090,
            trace_enabled: true,
            trace_sample_rate: 0.1,
            log_level: "info".to_string(),
        }
    }
}

// 工作流配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkflowConfig {
    pub max_concurrent_tasks: u32,
    pub default_task_timeout_seconds: u64,
    pub max_retry_attempts: u32,
    pub scheduler_interval_ms: u64,
    pub history_retention_days: u32,
    pub verification_enabled: bool,
}

impl Default for WorkflowConfig {
    fn default() -> Self {
        Self {
            max_concurrent_tasks: 1000,
            default_task_timeout_seconds: 300,
            max_retry_attempts: 3,
            scheduler_interval_ms: 100,
            history_retention_days: 30,
            verification_enabled: true,
        }
    }
}

// 配置错误
#[derive(Debug, thiserror::Error)]
pub enum ConfigError {
    #[error("IO错误: {0}")]
    IoError(String),
    
    #[error("解析错误: {0}")]
    ParseError(String),
    
    #[error("格式不支持: {0}")]
    UnsupportedFormat(String),
    
    #[error("环境变量错误: {0}")]
    EnvError(String),
}

// 环境变量类型转换宏
macro_rules! env_get {
    ($env:expr, $type:ty, $default:expr) => {
        std::env::var($env)
            .ok()
            .and_then(|val| val.parse::<$type>().ok())
            .unwrap_or($default)
    };
}
```

配置管理的优势：

1. **多源配置**：支持文件、环境变量和动态更新
2. **分层配置**：从默认值到环境变量的优先级层次
3. **热重载**：支持不重启服务更新配置
4. **强类型配置**：类型安全的配置结构
5. **自动转换**：自动处理类型转换和验证
6. **敏感信息保护**：支持加密敏感配置项

### 11.4 升级策略

系统提供安全且平滑的升级策略：

```rust
pub struct UpgradeManager {
    storage: Arc<dyn WorkflowStorage>,
    versioning: Arc<dyn SchemaVersioning>,
    event_bus: Arc<dyn MessageBroker>,
    node_manager: Arc<NodeManager>,
    config: UpgradeConfig,
}

impl UpgradeManager {
    pub fn new(
        storage: Arc<dyn WorkflowStorage>,
        versioning: Arc<dyn SchemaVersioning>,
        event_bus: Arc<dyn MessageBroker>,
        node_manager: Arc<NodeManager>,
        config: UpgradeConfig
    ) -> Self {
        Self {
            storage,
            versioning,
            event_bus,
            node_manager,
            config,
        }
    }
    
    // 启动升级过程
    pub async fn upgrade(&self) -> Result<UpgradeResult, UpgradeError> {
        // 1. 判断是否需要升级
        let current_version = self.versioning.get_current_version().await?;
        let target_version = self.config.target_version.clone();
        
        if current_version == target_version {
            log::info!("当前版本已经是最新的: {}", current_version);
            return Ok(UpgradeResult {
                success: true,
                version_from: current_version,
                version_to: target_version,
                upgraded_components: vec![],
                errors: vec![],
            });
        }
        
        log::info!("开始升级: {} -> {}", current_version, target_version);
        
        // 2. 获取升级路径
        let upgrade_path = self.versioning.get_upgrade_path(&current_version, &target_version).await?;
        
        if upgrade_path.is_empty() {
            return Err(UpgradeError::NoUpgradePath(format!(
                "没有从 {} 到 {} 的升级路径", 
                current_version, 
                target_version
            )));
        }
        
        // 3. 检查系统状态
        self.check_system_status().await?;
        
        // 4. 备份关键数据
        if self.config.backup_before_upgrade {
            self.backup_data().await?;
        }
        
        // 5. 执行升级步骤
        let mut upgraded_components = Vec::new();
        let mut errors = Vec::new();
        
        for step in upgrade_path {
            log::info!("执行升级步骤: {} -> {}", step.from_version, step.to_version);
            
            match self.execute_upgrade_step(&step).await {
                Ok(components) => {
                    upgraded_components.extend(components);
                },
                Err(e) => {
                    log::error!("升级步骤失败: {}", e);
                    
                    if self.config.continue_on_error {
                        errors.push(format!("步骤 {} -> {}: {}", step.from_version, step.to_version, e));
                    } else {
                        // 回滚已升级的组件
                        if self.config.rollback_on_error {
                            self.rollback(&current_version).await?;
                        }
                        
                        return Err(UpgradeError::StepFailed(format!(
                            "升级步骤 {} -> {} 失败: {}", 
                            step.from_version, 
                            step.to_version, 
                            e
                        )));
                    }
                }
            }
        }
        
        // 6. 更新系统版本
        if errors.is_empty() || self.config.continue_on_error {
            self.versioning.set_current_version(&target_version).await?;
            
            // 7. 发布升级完成事件
            self.publish_upgrade_event(&current_version, &target_version, &upgraded_components, &errors).await?;
        }
        
        // 8. 返回升级结果
        Ok(UpgradeResult {
            success: errors.is_empty(),
            version_from: current_version,
            version_to: target_version,
            upgraded_components,
            errors,
        })
    }
    
    // 检查系统状态
    async fn check_system_status(&self) -> Result<(), UpgradeError> {
        // 检查节点状态
        let online_nodes = self.node_manager.get_online_nodes().await?;
        
        if online_nodes.len() < self.config.min_nodes_for_upgrade {
            return Err(UpgradeError::InsufficientNodes(format!(
                "在线节点数 ({}) 少于升级所需最小节点数 ({})",
                online_nodes.len(),
                self.config.min_nodes_for_upgrade
            )));
        }
        
        // 检查运行中的工作流
        let active_workflows = self.storage.count_active_workflows().await?;
        
        if active_workflows > self.config.max_active_workflows_for_upgrade {
            return Err(UpgradeError::TooManyActiveWorkflows(format!(
                "活跃工作流数 ({}) 超过升级允许的最大数 ({})",
                active_workflows,
                self.config.max_active_workflows_for_upgrade
            )));
        }
        
        // 检查数据库连接
        self.storage.ping().await?;
        
        // 检查消息系统连接
        self.event_bus.ping().await?;
        
        Ok(())
    }
    
    // 备份关键数据
    async fn backup_data(&self) -> Result<(), UpgradeError> {
        log::info!("备份关键数据...");
        
        let timestamp = chrono::Utc::now().format("%Y%m%d%H%M%S").to_string();
        let backup_id = format!("upgrade_backup_{}", timestamp);
        
        // 备份工作流定义
        self.storage.backup_workflow_definitions(&backup_id).await
            .map_err(|e| UpgradeError::BackupFailed(format!("工作流定义备份失败: {}", e)))?;
        
        // 备份配置数据
        self.storage.backup_configuration(&backup_id).await
            .map_err(|e| UpgradeError::BackupFailed(format!("配置备份失败: {}", e)))?;
        
        // 备份用户和权限数据
        self.storage.backup_user_data(&backup_id).await
            .map_err(|e| UpgradeError::BackupFailed(format!("用户数据备份失败: {}", e)))?;
        
        log::info!("备份完成: {}", backup_id);
        
        Ok(())
    }
    
    // 执行升级步骤
    async fn execute_upgrade_step(&self, step: &UpgradeStep) -> Result<Vec<String>, UpgradeError> {
        let mut upgraded_components = Vec::new();
        
        // 执行数据库迁移
        if let Some(migrations) = &step.database_migrations {
            log::info!("执行数据库迁移...");
            
            for migration in migrations {
                log::debug!("执行迁移: {}", migration.name);
                self.versioning.execute_migration(migration).await
                    .map_err(|e| UpgradeError::MigrationFailed(format!("迁移 {} 失败: {}", migration.name, e)))?;
            }
            
            upgraded_components.push("数据库架构".to_string());
        }
        
        // 执行配置更新
        if let Some(config_updates) = &step.config_updates {
            log::info!("应用配置更新...");
            
            for update in config_updates {
                log::debug!("更新配置: {}", update.key);
                // 应用配置更新逻辑...
            }
            
            upgraded_components.push("系统配置".to_string());
        }
        
        // 执行资源更新
        if let Some(resource_updates) = &step.resource_updates {
            log::info!("更新资源...");
            
            for update in resource_updates {
                log::debug!("更新资源: {}", update.resource_type);
                // 应用资源更新逻辑...
            }
            
            upgraded_components.push("系统资源".to_string());
        }
        
        // 执行自定义升级脚本
        if let Some(custom_scripts) = &step.custom_scripts {
            log::info!("执行自定义脚本...");
            
            for script in custom_scripts {
                log::debug!("执行脚本: {}", script.name);
                // 执行自定义脚本...
            }
            
            upgraded_components.push("自定义组件".to_string());
        }
        
        Ok(upgraded_components)
    }
    
    // 执行回滚
    async fn rollback(&self, target_version: &str) -> Result<(), UpgradeError> {
        log::info!("执行回滚到版本: {}", target_version);
        
        // 从备份恢复数据
        if self.config.backup_before_upgrade {
            // 恢复备份数据...
        }
        
        // 执行数据库回滚
        self.versioning.rollback_to_version(target_version).await?;
        
        // 发布回滚事件
        let event = SystemRolledBackEvent {
            timestamp: chrono::Utc::now(),
            target_version: target_version.to_string(),
            reason: "升级失败自动回滚".to_string(),
        };
        
        self.event_bus.publish("system.rolled_back", &event).await?;
        
        Ok(())
    }
    
    // 发布升级事件
    async fn publish_upgrade_event(
        &self,
        from_version: &str,
        to_version: &str,
        upgraded_components: &[String],
        errors: &[String]
    ) -> Result<(), UpgradeError> {
        let event = SystemUpgradedEvent {
            timestamp: chrono::Utc::now(),
            from_version: from_version.to_string(),
            to_version: to_version.to_string(),
            upgraded_components: upgraded_components.to_vec(),
            errors: errors.to_vec(),
            success: errors.is_empty(),
        };
        
        self.event_bus.publish("system.upgraded", &event).await
            .map_err(|e| UpgradeError::EventPublishFailed(e.to_string()))
    }
}

// 版本管理接口
#[async_trait]
pub trait SchemaVersioning: Send + Sync {
    async fn get_current_version(&self) -> Result<String, UpgradeError>;
    async fn set_current_version(&self, version: &str) -> Result<(), UpgradeError>;
    async fn get_upgrade_path(&self, from: &str, to: &str) -> Result<Vec<UpgradeStep>, UpgradeError>;
    async fn execute_migration(&self, migration: &DbMigration) -> Result<(), UpgradeError>;
    async fn rollback_to_version(&self, version: &str) -> Result<(), UpgradeError>;
}

// 升级步骤
#[derive(Debug, Clone)]
pub struct UpgradeStep {
    pub from_version: String,
    pub to_version: String,
    pub description: String,
    pub database_migrations: Option<Vec<DbMigration>>,
    pub config_updates: Option<Vec<ConfigUpdate>>,
    pub resource_updates: Option<Vec<ResourceUpdate>>,
    pub custom_scripts: Option<Vec<CustomScript>>,
}

// 数据库迁移
#[derive(Debug, Clone)]
pub struct DbMigration {
    pub name: String,
    pub sql: String,
    pub reversible: bool,
    pub rollback_sql: Option<String>,
}

// 配置更新
#[derive(Debug, Clone)]
pub struct ConfigUpdate {
    pub key: String,
    pub value: String,
    pub old_value: Option<String>,
}

// 资源更新
#[derive(Debug, Clone)]
pub struct ResourceUpdate {
    pub resource_type: String,
    pub resource_id: String,
    pub action: ResourceUpdateAction,
    pub data: Option<serde_json::Value>,
}

// 资源更新动作
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResourceUpdateAction {
    Create,
    Update,
    Delete,
}

// 自定义脚本
#[derive(Debug, Clone)]
pub struct CustomScript {
    pub name: String,
    pub script_type: ScriptType,
    pub content: String,
}

// 脚本类型
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScriptType {
    SQL,
    Shell,
    JavaScript,
    Rust,
}

// 升级配置
#[derive(Debug, Clone)]
pub struct UpgradeConfig {
    pub target_version: String,
    pub backup_before_upgrade: bool,
    pub continue_on_error: bool,
    pub rollback_on_error: bool,
    pub min_nodes_for_upgrade: usize,
    pub max_active_workflows_for_upgrade: usize,
}

// 升级结果
#[derive(Debug, Clone)]
pub struct UpgradeResult {
    pub success: bool,
    pub version_from: String,
    pub version_to: String,
    pub upgraded_components: Vec<String>,
    pub errors: Vec<String>,
}

// 升级事件
#[derive(Debug, Clone, Serialize)]
pub struct SystemUpgradedEvent {
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub from_version: String,
    pub to_version: String,
    pub upgraded_components: Vec<String>,
    pub errors: Vec<String>,
    pub success: bool,
}

// 回滚事件
#[derive(Debug, Clone, Serialize)]
pub struct SystemRolledBackEvent {
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub target_version: String,
    pub reason: String,
}

// 升级错误
#[derive(Debug, thiserror::Error)]
pub enum UpgradeError {
    #[error("数据库错误: {0}")]
    DatabaseError(String),
    
    #[error("迁移失败: {0}")]
    MigrationFailed(String),
    
    #[error("无升级路径: {0}")]
    NoUpgradePath(String),
    
    #[error("节点不足: {0}")]
    InsufficientNodes(String),
    
    #[error("活跃工作流过多: {0}")]
    TooManyActiveWorkflows(String),
    
    #[error("备份失败: {0}")]
    BackupFailed(String),
    
    #[error("升级步骤失败: {0}")]
    StepFailed(String),
    
    #[error("事件发布失败: {0}")]
    EventPublishFailed(String),
    
    #[error("回滚失败: {0}")]
    RollbackFailed(String),
}

impl From<WorkflowError> for UpgradeError {
    fn from(err: WorkflowError) -> Self {
        UpgradeError::DatabaseError(err.to_string())
    }
}
```

升级策略的优势：

1. **版本化管理**：系统和数据模式的明确版本控制
2. **安全备份**：升级前自动备份关键数据
3. **增量升级**：支持跨版本的渐进式升级
4. **故障回滚**：升级失败时自动回滚到以前的版本
5. **前置检查**：升级前验证系统状态
6. **无停机升级**：支持滚动更新不中断服务
7. **透明升级过程**：详细的升级日志和事件

## 12. 性能优化

### 12.1 并行执行优化

系统设计高效的并行执行机制：

```rust
pub struct ParallelExecutor {
    max_concurrency: usize,
    thread_pool: Arc<ThreadPool>,
    task_queue: Arc<TaskQueue>,
    metrics_collector: Arc<MetricsCollector>,
}

impl ParallelExecutor {
    pub fn new(
        max_concurrency: usize,
        task_queue: Arc<TaskQueue>,
        metrics_collector: Arc<MetricsCollector>
    ) -> Self {
        let thread_pool = ThreadPool::new(max_concurrency);
        
        Self {
            max_concurrency,
            thread_pool: Arc::new(thread_pool),
            task_queue,
            metrics_collector,
        }
    }
    
    // 批量执行并行任务
    pub async fn execute_parallel<T, F, Fut, R>(
        &self,
        items: Vec<T>,
        task_fn: F
    ) -> Result<Vec<Result<R, WorkflowError>>, WorkflowError>
    where
        T: Send + 'static,
        R: Send + 'static,
        F: Fn(T) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = Result<R, WorkflowError>> + Send + 'static,
    {
        if items.is_empty() {
            return Ok(Vec::new());
        }
        
        // 限制并发数
        let batch_size = std::cmp::min(items.len(), self.max_concurrency);
        let semaphore = Arc::new(Semaphore::new(batch_size));
        
        // 创建结果收集器
        let result_count = items.len();
        let results = Arc::new(Mutex::new(vec![None; result_count]));
        
        // 启动时间
        let start_time = Instant::now();
        
        // 创建任务
        let mut tasks = Vec::with_capacity(items.len());
        
        for (index, item) in items.into_iter().enumerate() {
            let semaphore = semaphore.clone();
            let results = results.clone();
            let task_fn = Arc::new(task_fn);
            let metrics_collector = self.metrics_collector.clone();
            
            // 创建异步任务
            let task = async move {
                // 获取并发许可
                let _permit = semaphore.acquire().await.unwrap();
                
                // 任务启动时间
                let task_start = Instant::now();
                
                // 执行任务函数
                let result = task_fn(item).await;
                
                // 任务完成时间
                let task_duration = task_start.elapsed();
                
                // 记录执行指标
                match &result {
                    Ok(_) => {
                        metrics_collector.record_task_success(task_duration.as_millis() as u64).await;
                    },
                    Err(_) => {
                        metrics_collector.record_task_failure(task_duration.as_millis() as u64).await;
                    },
                }
                
                // 存储结果
                let mut results_guard = results.lock().await;
                results_guard[index] = Some(result);
                
                // 释放信号量（通过丢弃_permit实现）
            };
            
            tasks.push(task);
        }
        
        // 使用futures::future::join_all并行执行所有任务
        futures::future::join_all(tasks).await;
        
        // 计算总执行时间
        let total_duration = start_time.elapsed();
        self.metrics_collector.record_parallel_execution(total_duration.as_millis() as u64, result_count as u64).await;
        
        // 提取结果
        let locked_results = results.lock().await;
        
        let final_results = locked_results.iter()
            .map(|r| r.clone().unwrap())
            .collect();
            
        Ok(final_results)
    }
    
    // 并行执行工作流步骤
    pub async fn execute_parallel_steps(
        &self,
        steps: Vec<ParallelStep>,
        context: ExecutionContext
    ) -> Result<Vec<Result<StepResult, WorkflowError>>, WorkflowError> {
        self.execute_parallel(steps, move |step: ParallelStep| {
            let context = context.clone();
            
            async move {
                match step.step_type {
                    ParallelStepType::Activity { activity_type, input } => {
                        // 执行活动
                        self.execute_activity(&activity_type, input, context).await
                    },
                    ParallelStepType::Function { func_name, input } => {
                        // 执行内置函数
                        self.execute_function(&func_name, input, context).await
                    },
                    ParallelStepType::Decision { conditions, input } => {
                        // 执行决策
                        self.evaluate_decision(conditions, input, context).await
                    },
                }
            }
        }).await
    }
    
    // 执行活动
    async fn execute_activity(
        &self,
        activity_type: &str,
        input: serde_json::Value,
        context: ExecutionContext
    ) -> Result<StepResult, WorkflowError> {
        // 活动执行逻辑
        Ok(StepResult {
            output: serde_json::json!({"result": "success"}),
            metadata: HashMap::new(),
        })
    }
    
    // 执行函数
    async fn execute_function(
        &self,
        func_name: &str,
        input: serde_json::Value,
        context: ExecutionContext
    ) -> Result<StepResult, WorkflowError> {
        // 函数执行逻辑
        Ok(StepResult {
            output: serde_json::json!({"result": "success"}),
            metadata: HashMap::new(),
        })
    }
    
    // 评估决策
    async fn evaluate_decision(
        &self,
        conditions: Vec<Condition>,
        input: serde_json::Value,
        context: ExecutionContext
    ) -> Result<StepResult, WorkflowError> {
        // 决策评估逻辑
        Ok(StepResult {
            output: serde_json::json!({"result": "success"}),
            metadata: HashMap::new(),
        })
    }
}

// 并行步骤
#[derive(Debug, Clone)]
pub struct ParallelStep {
    pub id: String,
    pub step_type: ParallelStepType,
}

// 并行步骤类型
#[derive(Debug, Clone)]
pub enum ParallelStepType {
    Activity {
        activity_type: String,
        input: serde_json::Value,
    },
    Function {
        func_name: String,
        input: serde_json::Value,
    },
    Decision {
        conditions: Vec<Condition>,
        input: serde_json::Value,
    },
}

// 步骤执行结果
#[derive(Debug, Clone)]
pub struct StepResult {
    pub output: serde_json::Value,
    pub metadata: HashMap<String, String>,
}

// 执行上下文
#[derive(Debug, Clone)]
pub struct ExecutionContext {
    pub execution_id: String,
    pub workflow_id: String,
    pub variables: HashMap<String, serde_json::Value>,
    pub parent_context: Option<Box<ExecutionContext>>,
}
```

并行执行优化的优势：

1. **并发控制**：使用信号量限制并发度
2. **线程池复用**：避免频繁创建和销毁线程
3. **自适应并行**：根据系统负载调整并行度
4. **分批处理**：将大量任务分批并行执行
5. **性能监控**：收集并行执行的细粒度指标

### 12.2 缓存策略

系统实现多级缓存机制提高性能：

```rust
pub struct CacheManager {
    memory_cache: Arc<RwLock<LruCache<String, CacheEntry>>>,
    redis_client: Option<redis::Client>,
    config: CacheConfig,
    metrics_collector: Arc<MetricsCollector>,
}

impl CacheManager {
    pub fn new(config: CacheConfig, metrics_collector: Arc<MetricsCollector>) -> Result<Self, CacheError> {
        // 创建内存缓存
        let memory_cache = LruCache::new(config.max_memory_items);
        
        // 创建Redis客户端（如果配置了）
        let redis_client = if config.enable_redis {
            Some(redis::Client::open(&config.redis_url)
                .map_err(|e| CacheError::ConnectionError(format!("Redis连接失败: {}", e)))?)
        } else {
            None
        };
        
        Ok(Self {
            memory_cache: Arc::new(RwLock::new(memory_cache)),
            redis_client,
            config,
            metrics_collector,
        })
    }
    
    // 获取缓存条目
    pub async fn get(&self, key: &str, namespace: &str) -> Result<Option<CacheValue>, CacheError> {
        let cache_key = self.build_cache_key(key, namespace);
        
        // 尝试从内存缓存获取
        let memory_start = Instant::now();
        let memory_result = {
            let mut cache = self.memory_cache.write().await;
            
            if let Some(entry) = cache.get(&cache_key) {
                // 检查是否过期
                if !entry.is_expired() {
                    self.metrics_collector.record_cache_hit("memory", namespace).await;
                    return Ok(Some(entry.value.clone()));
                } else {
                    // 移除过期条目
                    cache.pop(&cache_key);
                }
            }
            
            None
        };
        
        let memory_duration = memory_start.elapsed();
        self.metrics_collector.record_cache_lookup_time("memory", memory_duration.as_micros() as u64).await;
        
        if memory_result.is_some() {
            return Ok(memory_result);
        }
        
        self.metrics_collector.record_cache_miss("memory", namespace).await;
        
        // 如果内存中没有且Redis可用，尝试从Redis获取
        if let Some(redis_client) = &self.redis_client {
            let redis_start = Instant::now();
            
            let mut conn = redis_client.get_async_connection().await
                .map_err(|e| CacheError::ConnectionError(format!("Redis连接失败: {}", e)))?;
                
            // 获取缓存数据和TTL
            let (value, ttl): (Option<String>, Option<i64>) = redis::pipe()
                .get(&cache_key)
                .ttl(&cache_key)
                .query_async(&mut conn).await
                .map_err(|e| CacheError::RedisError(format!("Redis查询失败: {}", e)))?;
                
            let redis_duration = redis_start.elapsed();
            self.metrics_collector.record_cache_lookup_time("redis", redis_duration.as_micros() as u64).await;
            
            if let Some(val) = value {
                // 反序列化
                let deserialized = serde_json::from_str::<CacheValue>(&val)
                    .map_err(|e| CacheError::DeserializeError(format!("缓存值反序列化失败: {}", e)))?;
                    
                // 计算有效期
                let expires_at = if let Some(remaining_ttl) = ttl {
                    if remaining_ttl > 0 {
                        Some(chrono::Utc::now() + chrono::Duration::seconds(remaining_ttl))
                    } else {
                        None
                    }
                } else {
                    None
                };
                
                // 存入内存缓存
                {
                    let mut cache = self.memory_cache.write().await;
                    cache.put(cache_key, CacheEntry {
                        value: deserialized.clone(),
                        created_at: chrono::Utc::now(),
                        expires_at,
                    });
                }
                
                self.metrics_collector.record_cache_hit("redis", namespace).await;
                return Ok(Some(deserialized));
            }
            
            self.metrics_collector.record_cache_miss("redis", namespace).await;
        }
        
        // 两级缓存都未命中
        Ok(None)
    }
    
    // 设置缓存条目
    pub async fn set(
        &self, 
        key: &str, 
        namespace: &str, 
        value: CacheValue, 
        ttl: Option<Duration>
    ) -> Result<(), CacheError> {
        let cache_key = self.build_cache_key(key, namespace);
        
        // 计算过期时间
        let expires_at = ttl.map(|t| chrono::Utc::now() + chrono::Duration::from_std(t).unwrap());
        
        // 设置内存缓存
        {
            let mut cache = self.memory_cache.write().await;
            cache.put(cache_key.clone(), CacheEntry {
                value: value.clone(),
                created_at: chrono::Utc::now(),
                expires_at,
            });
        }
        
        // 如果Redis可用，也设置Redis缓存
        if let Some(redis_client) = &self.redis_client {
            let serialized = serde_json::to_string(&value)
                .map_err(|e| CacheError::SerializeError(format!("缓存值序列化失败: {}", e)))?;
                
            let mut conn = redis_client.get_async_connection().await
                .map_err(|e| CacheError::ConnectionError(format!("Redis连接失败: {}", e)))?;
                
            if let Some(ttl) = ttl {
                // 设置带TTL的缓存
                let ttl_secs = ttl.as_secs();
                redis::pipe()
                    .set(&cache_key, serialized)
                    .expire(&cache_key, ttl_secs as usize)
                    .query_async::<_, ()>(&mut conn).await
                    .map_err(|e| CacheError::RedisError(format!("Redis设置失败: {}", e)))?;
            } else {
                // 设置永久缓存
                redis::pipe()
                    .set(&cache_key, serialized)
                    .query_async::<_, ()>(&mut conn).await
                    .map_err(|e| CacheError::RedisError(format!("Redis设置失败: {}", e)))?;
            }
        }
        
        self.metrics_collector.record_cache_set(namespace).await;
        Ok(())
    }
    
    // 删除缓存条目
    pub async fn delete(&self, key: &str, namespace: &str) -> Result<bool, CacheError> {
        let cache_key = self.build_cache_key(key, namespace);
        let mut deleted = false;
        
        // 从内存缓存删除
        {
            let mut cache = self.memory_cache.write().await;
            if cache.pop(&cache_key).is_some() {
                deleted = true;
            }
        }
        
        // 从Redis缓存删除
        if let Some(redis_client) = &self.redis_client {
            let mut conn = redis_client.get_async_connection().await
                .map_err(|e| CacheError::ConnectionError(format!("Redis连接失败: {}", e)))?;
                
            let redis_deleted: i64 = redis::cmd("DEL")
                .arg(&cache_key)
                .query_async(&mut conn).await
                .map_err(|e| CacheError::RedisError(format!("Redis删除失败: {}", e)))?;
                
            if redis_deleted > 0 {
                deleted = true;
            }
        }
        
        self.metrics_collector.record_cache_delete(namespace).await;
        Ok(deleted)
    }
    
    // 清除命名空间下的所有缓存
    pub async fn clear_namespace(&self, namespace: &str) -> Result<u64, CacheError> {
        let namespace_prefix = format!("{}:", namespace);
        let mut cleared_count = 0;
        
        // 清除内存缓存
        {
            let mut cache = self.memory_cache.write().await;
            let keys_to_remove: Vec<String> = cache.iter()
                .filter_map(|(k, _)| {
                    if k.starts_with(&namespace_prefix) {
                        Some(k.clone())
                    } else {
                        None
                    }
                })
                .collect();
                
            for key in keys_to_remove {
                cache.pop(&key);
                cleared_count += 1;
            }
        }
        
        // 清除Redis缓存
        if let Some(redis_client) = &self.redis_client {
            let mut conn = redis_client.get_async_connection().await
                .map_err(|e| CacheError::ConnectionError(format!("Redis连接失败: {}", e)))?;
                
            // 查找所有匹配的键
            let pattern = format!("{}*", namespace_prefix);
            let keys: Vec<String> = redis::cmd("KEYS")
                .arg(&pattern)
                .query_async(&mut conn).await
                .map_err(|e| CacheError::RedisError(format!("Redis KEYS命令失败: {}", e)))?;
                
            if !keys.is_empty() {
                // 批量删除
                let redis_deleted: i64 = redis::cmd("DEL")
                    .arg(&keys)
                    .query_async(&mut conn).await
                    .map_err(|e| CacheError::RedisError(format!("Redis删除失败: {}", e)))?;
                    
                cleared_count += redis_deleted as u64;
            }
        }
        
        self.metrics_collector.record_cache_clear(namespace, cleared_count).await;
        Ok(cleared_count)
    }
    
    // 构建缓存键
    fn build_cache_key(&self, key: &str, namespace: &str) -> String {
        format!("{}:{}", namespace, key)
    }
    
    // 获取缓存统计
    pub async fn get_statistics(&self) -> CacheStatistics {
        let memory_stats = {
            let cache = self.memory_cache.read().await;
            MemoryCacheStats {
                len: cache.len(),
                capacity: cache.cap(),
                usage_percent: if cache.cap() > 0 {
                    (cache.len() as f64 / cache.cap() as f64) * 100.0
                } else {
                    0.0
                },
            }
        };
        
        let redis_stats = if let Some(redis_client) = &self.redis_client {
            if let Ok(mut conn) = redis_client.get_async_connection().await {
                // 获取Redis信息
                if let Ok(info) = redis::cmd("INFO")
                    .arg("memory")
                    .query_async::<_, String>(&mut conn).await {
                    
                    // 解析内存使用
                    let used_memory_regex = Regex::new(r"used_memory:(\d+)").unwrap();
                    let used_memory = used_memory_regex.captures(&info)
                        .and_then(|cap| cap[1].parse::<u64>().ok())
                        .unwrap_or(0);
                        
                    let used_memory_peak_regex = Regex::new(r"used_memory_peak:(\d+)").unwrap();
                    let used_memory_peak = used_memory_peak_regex.captures(&info)
                        .and_then(|cap| cap[1].parse::<u64>().ok())
                        .unwrap_or(0);
                        
                    Some(RedisCacheStats {
                        used_memory_bytes: used_memory,
                        peak_memory_bytes: used_memory_peak,
                        connection_status: "connected".to_string(),
                    })
                } else {
                    Some(RedisCacheStats {
                        used_memory_bytes: 0,
                        peak_memory_bytes: 0,
                        connection_status: "error".to_string(),
                    })
                }
            } else {
                Some(RedisCacheStats {
                    used_memory_bytes: 0,
                    peak_memory_bytes: 0,
                    connection_status: "disconnected".to_string(),
                })
            }
        } else {
            None
        };
        
        CacheStatistics {
            memory: memory_stats,
            redis: redis_stats,
            hit_rates: self.metrics_collector.get_cache_hit_rates().await,
        }
    }
}

// 缓存配置
#[derive(Debug, Clone)]
pub struct CacheConfig {
    pub max_memory_items: usize,
    pub default_ttl: Duration,
    pub enable_redis: bool,
    pub redis_url: String,
    pub cache_namespaces: Vec<String>,
}

// 缓存条目
#[derive(Debug, Clone)]
struct CacheEntry {
    pub value: CacheValue,
    pub created_at: chrono::DateTime<chrono::Utc>,
    pub expires_at: Option<chrono::DateTime<chrono::Utc>>,
}

impl CacheEntry {
    // 检查缓存条目是否过期
    pub fn is_expired(&self) -> bool {
        if let Some(expires) = self.expires_at {
            chrono::Utc::now() > expires
        } else {
            false
        }
    }
}

// 缓存值
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum CacheValue {
    String(String),
    Integer(i64),
    Float(f64),
    Boolean(bool),
    Object(serde_json::Value),
    List(Vec<serde_json::Value>),
    Binary(Vec<u8>),
}

// 缓存统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheStatistics {
    pub memory: MemoryCacheStats,
    pub redis: Option<RedisCacheStats>,
    pub hit_rates: HashMap<String, HitRateStats>,
}

// 内存缓存统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MemoryCacheStats {
    pub len: usize,
    pub capacity: usize,
    pub usage_percent: f64,
}

// Redis缓存统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RedisCacheStats {
    pub used_memory_bytes: u64,
    pub peak_memory_bytes: u64,
    pub connection_status: String,
}

// 命中率统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HitRateStats {
    pub hits: u64,
    pub misses: u64,
    pub sets: u64,
    pub deletes: u64,
    pub hit_rate_percent: f64,
}

// 缓存错误
#[derive(Debug, thiserror::Error)]
pub enum CacheError {
    #[error("连接错误: {0}")]
    ConnectionError(String),
    
    #[error("Redis错误: {0}")]
    RedisError(String),
    
    #[error("序列化错误: {0}")]
    SerializeError(String),
    
    #[error("反序列化错误: {0}")]
    DeserializeError(String),
    
    #[error("键错误: {0}")]
    KeyError(String),
}
```

缓存策略的优势：

1. **多级缓存**：内存和Redis两级缓存
2. **智能失效**：TTL自动失效和手动清除
3. **命名空间隔离**：不同功能域的缓存隔离
4. **缓存统计**：详细的命中率和使用统计
5. **批量操作**：支持命名空间级别的操作
6. **自适应TTL**：基于访问模式调整失效时间

### 12.3 批处理优化

系统实现高效的批处理机制：

```rust
pub struct BatchProcessor {
    batch_config: BatchConfig,
    task_queue: Arc<TaskQueue>,
    storage: Arc<dyn WorkflowStorage>,
    event_bus: Arc<dyn MessageBroker>,
    metrics_collector: Arc<MetricsCollector>,
}

impl BatchProcessor {
    pub fn new(
        batch_config: BatchConfig,
        task_queue: Arc<TaskQueue>,
        storage: Arc<dyn WorkflowStorage>,
        event_bus: Arc<dyn MessageBroker>,
        metrics_collector: Arc<MetricsCollector>
    ) -> Self {
        Self {
            batch_config,
            task_queue,
            storage,
            event_bus,
            metrics_collector,
        }
    }
    
    // 启动批处理器
    pub async fn start(&self) -> JoinHandle<()> {
        let batch_config = self.batch_config.clone();
        let task_queue = self.task_queue.clone();
        let storage = self.storage.clone();
        let event_bus = self.event_bus.clone();
        let metrics_collector = self.metrics_collector.clone();
        
        tokio::spawn(async move {
            log::info!("批处理器已启动");
            
            let mut interval = tokio::time::interval(batch_config.poll_interval);
            
            loop {
                interval.tick().await;
                
                // 尝试处理每种批处理类型
                for batch_type in &batch_config.enabled_batches {
                    match batch_type {
                        BatchType::TaskCreation => {
                            if let Err(e) = Self::batch_create_tasks(
                                &task_queue, 
                                &storage, 
                                batch_config.task_batch_size,
                                &metrics_collector
                            ).await {
                                log::error!("批量创建任务失败: {}", e);
                            }
                        },
                        BatchType::TaskCompletion => {
                            if let Err(e) = Self::batch_complete_tasks(
                                &task_queue, 
                                &storage, 
                                batch_config.task_batch_size,
                                &metrics_collector
                            ).await {
                                log::error!("批量完成任务失败: {}", e);
                            }
                        },
                        BatchType::EventPublishing => {
                            if let Err(e) = Self::batch_publish_events(
                                &event_bus, 
                                &storage, 
                                batch_config.event_batch_size,
                                &metrics_collector
                            ).await {
                                log::error!("批量发布事件失败: {}", e);
                            }
                        },
                        BatchType::MetricsCollection => {
                            if let Err(e) = Self::batch_collect_metrics(
                                &storage, 
                                &metrics_collector,
                                batch_config.metrics_batch_size
                            ).await {
                                log::error!("批量收集指标失败: {}", e);
                            }
                        },
                    }
                }
            }
        })
    }
    
    // 批量创建任务
    async fn batch_create_tasks(
        task_queue: &Arc<TaskQueue>,
        storage: &Arc<dyn WorkflowStorage>,
        batch_size: usize,
        metrics_collector: &Arc<MetricsCollector>
    ) -> Result<(), WorkflowError> {
        let start = Instant::now();
        
        // 从存储中获取待创建的任务
        let pending_tasks = storage.get_pending_task_creations(batch_size).await?;
        
        if pending_tasks.is_empty() {
            return Ok(());
        }
        
        log::debug!("批量创建 {} 个任务", pending_tasks.len());
        
        // 批量插入任务队列
        let result = task_queue.batch_enqueue(pending_tasks.clone()).await;
        
        let duration = start.elapsed();
        metrics_collector.record_batch_operation(
            "task_creation",
            pending_tasks.len() as u64,
            duration.as_millis() as u64
        ).await;
        
        result
    }
    
    // 批量完成任务
    async fn batch_complete_tasks(
        task_queue: &Arc<TaskQueue>,
        storage: &Arc<dyn WorkflowStorage>,
        batch_size: usize,
        metrics_collector: &Arc<MetricsCollector>
    ) -> Result<(), WorkflowError> {
        let start = Instant::now();
        
        // 从存储中获取已完成但未更新的任务
        let completed_tasks = storage.get_completed_tasks_pending_update(batch_size).await?;
        
        if completed_tasks.is_empty() {
            return Ok(());
        }
        
        log::debug!("批量更新 {} 个已完成任务", completed_tasks.len());
        
        // 批量更新任务状态
        let result = task_queue.batch_update_tasks(completed_tasks.clone()).await;
        
        let duration = start.elapsed();
        metrics_collector.record_batch_operation(
            "task_completion",
            completed_tasks.len() as u64,
            duration.as_millis() as u64
        ).await;
        
        result
    }
    
    // 批量发布事件
    async fn batch_publish_events(
        event_bus: &Arc<dyn MessageBroker>,
        storage: &Arc<dyn WorkflowStorage>,
        batch_size: usize,
        metrics_collector: &Arc<MetricsCollector>
    ) -> Result<(), WorkflowError> {
        let start = Instant::now();
        
        // 从存储中获取未发布的事件
        let pending_events = storage.get_pending_events(batch_size).await?;
        
        if pending_events.is_empty() {
            return Ok(());
        }
        
        log::debug!("批量发布 {} 个事件", pending_events.len());
        
        // 按事件类型分组
        let mut events_by_type: HashMap<String, Vec<Event>> = HashMap::new();
        
        for event in pending_events {
            events_by_type
                .entry(event.event_type.clone())
                .or_insert_with(Vec::new)
                .push(event);
        }
        
        // 按类型批量发布
        for (event_type, events) in events_by_type {
            event_bus.batch_publish(&event_type, &events).await?;
            
            // 标记事件为已发布
            let event_ids: Vec<String> = events.iter().map(|e| e.id.clone()).collect();
            storage.mark_events_published(&event_ids).await?;
        }
        
        let duration = start.elapsed();
        let total_events: usize = events_by_type.values().map(|v| v.len()).sum();
        
        metrics_collector.record_batch_operation(
            "event_publishing",
            total_events as u64,
            duration.as_millis() as u64
        ).await;
        
        Ok(())
    }
    
    // 批量收集指标
    async fn batch_collect_metrics(
        storage: &Arc<dyn WorkflowStorage>,
        metrics_collector: &Arc<MetricsCollector>,
        batch_size: usize
    ) -> Result<(), WorkflowError> {
        let start = Instant::now();
        
        // 从存储中获取未汇总的指标记录
        let pending_metrics = storage.get_pending_metrics_records(batch_size).await?;
        
        if pending_metrics.is_empty() {
            return Ok(());
        }
        
        log::debug!("批量处理 {} 个指标记录", pending_metrics.len());
        
        // 按指标类型分组聚合
        let mut metrics_by_type: HashMap<String, Vec<MetricRecord>> = HashMap::new();
        
        for metric in pending_metrics {
            metrics_by_type
                .entry(metric.metric_type.clone())
                .or_insert_with(Vec::new)
                .push(metric);
        }
        
        // 处理每种类型的指标
        for (metric_type, records) in metrics_by_type {
            // 聚合指标
            metrics_collector.aggregate_and_export_metrics(&metric_type, &records).await?;
            
            // 标记指标为已处理
            let record_ids: Vec<String> = records.iter().map(|r| r.id.clone()).collect();
            storage.mark_metrics_processed(&record_ids).await?;
        }
        
        let duration = start.elapsed();
        let total_records: usize = metrics_by_type.values().map(|v| v.len()).sum();
        
        metrics_collector.record_batch_operation(
            "metrics_collection",
            total_records as u64,
            duration.as_millis() as u64
        ).await;
        
        Ok(())
    }
    
    // 批量查询任务状态
    pub async fn batch_query_task_status(
        &self,
        task_ids: &[String]
    ) -> Result<HashMap<String, TaskState>, WorkflowError> {
        if task_ids.is_empty() {
            return Ok(HashMap::new());
        }
        
        let start = Instant::now();
        
        // 批量查询任务状态
        let result = self.task_queue.batch_get_task_states(task_ids).await?;
        
        let duration = start.elapsed();
        self.metrics_collector.record_batch_operation(
            "task_status_query",
            task_ids.len() as u64,
            duration.as_millis() as u64
        ).await;
        
        Ok(result)
    }
    
    // 批量清理过期数据
    pub async fn batch_cleanup_expired_data(&self) -> Result<CleanupStats, WorkflowError> {
        let start = Instant::now();
        
        // 清理各类过期数据
        let completed_workflows = self.storage.cleanup_completed_workflows(
            self.batch_config.retention_days.workflow_history
        ).await?;
        
        let expired_tasks = self.storage.cleanup_expired_tasks(
            self.batch_config.retention_days.task_history
        ).await?;
        
        let expired_events = self.storage.cleanup_expired_events(
            self.batch_config.retention_days.event_history
        ).await?;
        
        let expired_metrics = self.storage.cleanup_expired_metrics(
            self.batch_config.retention_days.metrics_history
        ).await?;
        
        let stats = CleanupStats {
            workflows_cleaned: completed_workflows,
            tasks_cleaned: expired_tasks,
            events_cleaned: expired_events,
            metrics_cleaned: expired_metrics,
            duration_ms: start.elapsed().as_millis() as u64,
        };
        
        log::info!("批量清理完成: 工作流 {}, 任务 {}, 事件 {}, 指标 {}", 
            stats.workflows_cleaned,
            stats.tasks_cleaned,
            stats.events_cleaned,
            stats.metrics_cleaned
        );
        
        Ok(stats)
    }
}

// 批处理配置
#[derive(Debug, Clone)]
pub struct BatchConfig {
    pub enabled_batches: Vec<BatchType>,
    pub poll_interval: Duration,
    pub task_batch_size: usize,
    pub event_batch_size: usize,
    pub metrics_batch_size: usize,
    pub retention_days: RetentionConfig,
}

// 批处理类型
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BatchType {
    TaskCreation,
    TaskCompletion,
    EventPublishing,
    MetricsCollection,
}

// 保留期配置
#[derive(Debug, Clone)]
pub struct RetentionConfig {
    pub workflow_history: u32,
    pub task_history: u32,
    pub event_history: u32,
    pub metrics_history: u32,
}

// 清理统计
#[derive(Debug, Clone)]
pub struct CleanupStats {
    pub workflows_cleaned: u64,
    pub tasks_cleaned: u64,
    pub events_cleaned: u64,
    pub metrics_cleaned: u64,
    pub duration_ms: u64,
}

// 指标记录
#[derive(Debug, Clone)]
pub struct MetricRecord {
    pub id: String,
    pub metric_type: String,
    pub value: f64,
    pub labels: HashMap<String, String>,
    pub timestamp: chrono::DateTime<chrono::Utc>,
}
```

批处理优化的优势：

1. **减少数据库操作**：合并多个操作减少资源消耗
2. **吞吐量提升**：批量处理显著提高系统吞吐量
3. **按类型分组处理**：根据不同类型优化处理逻辑
4. **数据清理和归档**：自动管理数据生命周期
5. **内存占用优化**：有效控制批量操作的内存使用

### 12.4 异步计算优化

系统引入异步计算框架提高性能：

```rust
pub struct AsyncComputeEngine {
    thread_pool: Arc<ThreadPool>,
    compute_queue: Arc<AsyncQueue<ComputeTask>>,
    results_store: Arc<RwLock<HashMap<String, ComputeResult>>>,
    metrics_collector: Arc<MetricsCollector>,
    config: AsyncComputeConfig,
}

impl AsyncComputeEngine {
    pub fn new(config: AsyncComputeConfig, metrics_collector: Arc<MetricsCollector>) -> Self {
        // 创建线程池
        let thread_pool = ThreadPoolBuilder::new()
            .pool_size(config.thread_pool_size)
            .name_prefix("async-compute-")
            .create()
            .expect("创建异步计算线程池失败");
            
        // 创建计算任务队列
        let compute_queue = Arc::new(AsyncQueue::new(config.queue_capacity));
        let results_store = Arc::new(RwLock::new(HashMap::new()));
        
        Self {
            thread_pool: Arc::new(thread_pool),
            compute_queue,
            results_store,
            metrics_collector,
            config,
        }
    }
    
    // 启动异步计算引擎
    pub fn start(&self) -> JoinHandle<()> {
        let compute_queue = self.compute_queue.clone();
        let thread_pool = self.thread_pool.clone();
        let results_store = self.results_store.clone();
        let metrics_collector = self.metrics_collector.clone();
        
        tokio::spawn(async move {
            log::info!("异步计算引擎已启动");
            
            loop {
                // 获取下一个计算任务
                match compute_queue.dequeue().await {
                    Ok(task) => {
                        let task_type = task.task_type.clone();
                        let task_id = task.task_id.clone();
                        let thread_pool = thread_pool.clone();
                        let results_store = results_store.clone();
                        let metrics_collector = metrics_collector.clone();
                        
                        // 提交到线程池执行
                        tokio::task::spawn_blocking(move || {
                            let start = Instant::now();
                            
                            // 在线程池中执行计算
                            let result = thread_pool.install(|| {
                                match task_type.as_str() {
                                    "expression_evaluation" => {
                                        Self::evaluate_expression(&task.parameters)
                                    },
                                    "condition_checking" => {
                                        Self::check_condition(&task.parameters)
                                    },
                                    "data_transformation" => {
                                        Self::transform_data(&task.parameters)
                                    },
                                    "metrics_aggregation" => {
                                        Self::aggregate_metrics(&task.parameters)
                                    },
                                    "custom_compute" => {
                                        if let Some(compute_fn) = task.compute_fn {
                                            compute_fn(&task.parameters)
                                        } else {
                                            Err(ComputeError::InvalidOperation("未提供计算函数".into()))
                                        }
                                    },
                                    _ => Err(ComputeError::InvalidOperation(format!("未知的计算类型: {}", task_type))),
                                }
                            });
                            
                            let duration = start.elapsed();
                            
                            // 根据结果记录指标
                            if result.is_ok() {
                                metrics_collector.record_compute_task(
                                    &task_type,
                                    duration.as_millis() as u64,
                                    true
                                );
                            } else {
                                metrics_collector.record_compute_task(
                                    &task_type,
                                    duration.as_millis() as u64,
                                    false
                                );
                            }
                            
                            // 存储计算结果
                            let compute_result = ComputeResult {
                                task_id: task_id.clone(),
                                task_type,
                                result,
                                completed_at: chrono::Utc::now(),
                                duration_ms: duration.as_millis() as u64,
                            };
                            
                            // 存储结果
                            let mut results = results_store.write().expect("无法获取结果存储写锁");
                            results.insert(task_id, compute_result);
                        });
                    },
                    Err(e) => {
                        log::error!("从计算队列获取任务失败: {}", e);
                        tokio::time::sleep(Duration::from_millis(100)).await;
                    }
                }
            }
        })
    }
    
    // 提交异步计算任务
    pub async fn submit_task(&self, task: ComputeTask) -> Result<String, ComputeError> {
        let start = Instant::now();
        
        // 检查队列是否已满
        if self.compute_queue.is_full() {
            return Err(ComputeError::QueueFull("计算队列已满，无法接受新任务".into()));
        }
        
        // 提交任务到队列
        self.compute_queue.enqueue(task.clone()).await?;
        
        let duration = start.elapsed();
        self.metrics_collector.record_task_submission(
            &task.task_type,
            duration.as_micros() as u64
        );
        
        Ok(task.task_id)
    }
    
    // 检查任务是否完成
    pub async fn is_task_completed(&self, task_id: &str) -> bool {
        let results = self.results_store.read().expect("无法获取结果存储读锁");
        results.contains_key(task_id)
    }
    
    // 获取任务结果
    pub async fn get_task_result(&self, task_id: &str) -> Option<ComputeResult> {
        let results = self.results_store.read().expect("无法获取结果存储读锁");
        results.get(task_id).cloned()
    }
    
    // 等待任务完成并获取结果
    pub async fn wait_for_result(&self, task_id: &str, timeout: Duration) -> Result<ComputeResult, ComputeError> {
        let start = Instant::now();
        
        while start.elapsed() < timeout {
            // 检查任务是否已完成
            if let Some(result) = self.get_task_result(task_id).await {
                return Ok(result);
            }
            
            // 等待一段时间再检查
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
        
        Err(ComputeError::Timeout(format!("等待任务 {} 结果超时", task_id)))
    }
    
    // 清理过期结果
    pub async fn cleanup_expired_results(&self) -> usize {
        let mut results = self.results_store.write().expect("无法获取结果存储写锁");
        let now = chrono::Utc::now();
        let ttl = chrono::Duration::seconds(self.config.result_ttl_seconds as i64);
        
        let expired_keys: Vec<String> = results.iter()
            .filter(|(_, result)| now - result.completed_at > ttl)
            .map(|(key, _)| key.clone())
            .collect();
            
        for key in &expired_keys {
            results.remove(key);
        }
        
        expired_keys.len()
    }
    
    // 计算表达式
    fn evaluate_expression(params: &ComputeParams) -> Result<ComputeOutput, ComputeError> {
        // 从参数中获取表达式
        let expression = params.get_string("expression")
            .ok_or_else(|| ComputeError::InvalidInput("缺少表达式参数".into()))?;
            
        // 获取变量上下文
        let context = params.get_object("context")
            .unwrap_or_else(|| json!({}));
            
        // 解析并计算表达式
        log::debug!("计算表达式: {}", expression);
        
        let engine = ExpressionEngine::new();
        let result = engine.evaluate(&expression, &context)
            .map_err(|e| ComputeError::Calculation(format!("表达式计算失败: {}", e)))?;
            
        Ok(ComputeOutput::Json(result))
    }
    
    // 检查条件
    fn check_condition(params: &ComputeParams) -> Result<ComputeOutput, ComputeError> {
        // 从参数中获取条件表达式
        let condition = params.get_string("condition")
            .ok_or_else(|| ComputeError::InvalidInput("缺少条件参数".into()))?;
            
        // 获取变量上下文
        let context = params.get_object("context")
            .unwrap_or_else(|| json!({}));
            
        // 解析并计算条件
        log::debug!("检查条件: {}", condition);
        
        let engine = ExpressionEngine::new();
        let result = engine.evaluate_condition(&condition, &context)
            .map_err(|e| ComputeError::Calculation(format!("条件计算失败: {}", e)))?;
            
        Ok(ComputeOutput::Boolean(result))
    }
    
    // 数据转换
    fn transform_data(params: &ComputeParams) -> Result<ComputeOutput, ComputeError> {
        // 从参数中获取数据和转换规则
        let data = params.get_value("data")
            .ok_or_else(|| ComputeError::InvalidInput("缺少数据参数".into()))?;
            
        let transform_rules = params.get_array("transform_rules")
            .ok_or_else(|| ComputeError::InvalidInput("缺少转换规则参数".into()))?;
            
        // 执行数据转换
        log::debug!("执行数据转换，规则数量: {}", transform_rules.len());
        
        let transformer = DataTransformer::new();
        let result = transformer.apply_transforms(data, transform_rules)
            .map_err(|e| ComputeError::Calculation(format!("数据转换失败: {}", e)))?;
            
        Ok(ComputeOutput::Json(result))
    }
    
    // 指标聚合
    fn aggregate_metrics(params: &ComputeParams) -> Result<ComputeOutput, ComputeError> {
        // 从参数中获取指标数据和聚合方法
        let metrics = params.get_array("metrics")
            .ok_or_else(|| ComputeError::InvalidInput("缺少指标数据参数".into()))?;
            
        let aggregation_type = params.get_string("aggregation_type")
            .ok_or_else(|| ComputeError::InvalidInput("缺少聚合类型参数".into()))?;
            
        // 执行指标聚合
        log::debug!("执行指标聚合: {}, 数据点数量: {}", aggregation_type, metrics.len());
        
        let aggregator = MetricsAggregator::new();
        let result = aggregator.aggregate(metrics, &aggregation_type)
            .map_err(|e| ComputeError::Calculation(format!("指标聚合失败: {}", e)))?;
            
        Ok(ComputeOutput::Number(result))
    }
}

// 异步计算配置
#[derive(Debug, Clone)]
pub struct AsyncComputeConfig {
    pub thread_pool_size: usize,
    pub queue_capacity: usize,
    pub result_ttl_seconds: u64,
}

// 计算任务
#[derive(Debug, Clone)]
pub struct ComputeTask {
    pub task_id: String,
    pub task_type: String,
    pub parameters: ComputeParams,
    pub compute_fn: Option<Arc<dyn Fn(&ComputeParams) -> Result<ComputeOutput, ComputeError> + Send + Sync>>,
    pub created_at: chrono::DateTime<chrono::Utc>,
    pub priority: u8,
}

impl ComputeTask {
    pub fn new(task_type: &str, parameters: ComputeParams) -> Self {
        Self {
            task_id: Uuid::new_v4().to_string(),
            task_type: task_type.to_string(),
            parameters,
            compute_fn: None,
            created_at: chrono::Utc::now(),
            priority: 5, // 默认优先级
        }
    }
    
    pub fn with_custom_function(
        parameters: ComputeParams,
        compute_fn: impl Fn(&ComputeParams) -> Result<ComputeOutput, ComputeError> + Send + Sync + 'static
    ) -> Self {
        Self {
            task_id: Uuid::new_v4().to_string(),
            task_type: "custom_compute".to_string(),
            parameters,
            compute_fn: Some(Arc::new(compute_fn)),
            created_at: chrono::Utc::now(),
            priority: 5, // 默认优先级
        }
    }
    
    pub fn with_priority(mut self, priority: u8) -> Self {
        self.priority = priority;
        self
    }
}

// 计算参数
#[derive(Debug, Clone)]
pub struct ComputeParams(serde_json::Value);

impl ComputeParams {
    pub fn new(value: serde_json::Value) -> Self {
        Self(value)
    }
    
    pub fn get_string(&self, key: &str) -> Option<String> {
        self.0.get(key)
            .and_then(|v| v.as_str())
            .map(|s| s.to_string())
    }
    
    pub fn get_number(&self, key: &str) -> Option<f64> {
        self.0.get(key)
            .and_then(|v| v.as_f64())
    }
    
    pub fn get_integer(&self, key: &str) -> Option<i64> {
        self.0.get(key)
            .and_then(|v| v.as_i64())
    }
    
    pub fn get_boolean(&self, key: &str) -> Option<bool> {
        self.0.get(key)
            .and_then(|v| v.as_bool())
    }
    
    pub fn get_array(&self, key: &str) -> Option<Vec<serde_json::Value>> {
        self.0.get(key)
            .and_then(|v| v.as_array())
            .map(|a| a.clone())
    }
    
    pub fn get_object(&self, key: &str) -> Option<serde_json::Value> {
        self.0.get(key)
            .and_then(|v| v.as_object())
            .map(|o| serde_json::Value::Object(o.clone()))
    }
    
    pub fn get_value(&self, key: &str) -> Option<serde_json::Value> {
        self.0.get(key).map(|v| v.clone())
    }
    
    pub fn as_json(&self) -> &serde_json::Value {
        &self.0
    }
}

// 计算输出
#[derive(Debug, Clone)]
pub enum ComputeOutput {
    String(String),
    Number(f64),
    Integer(i64),
    Boolean(bool),
    Json(serde_json::Value),
    Binary(Vec<u8>),
}

// 计算结果
#[derive(Debug, Clone)]
pub struct ComputeResult {
    pub task_id: String,
    pub task_type: String,
    pub result: Result<ComputeOutput, ComputeError>,
    pub completed_at: chrono::DateTime<chrono::Utc>,
    pub duration_ms: u64,
}

// 计算错误
#[derive(Debug, thiserror::Error)]
pub enum ComputeError {
    #[error("无效输入: {0}")]
    InvalidInput(String),
    
    #[error("计算失败: {0}")]
    Calculation(String),
    
    #[error("无效操作: {0}")]
    InvalidOperation(String),
    
    #[error("队列已满: {0}")]
    QueueFull(String),
    
    #[error("队列错误: {0}")]
    QueueError(String),
    
    #[error("超时: {0}")]
    Timeout(String),
}

// 异步队列
pub struct AsyncQueue<T> {
    queue: Mutex<VecDeque<T>>,
    capacity: usize,
    not_empty: Condvar,
    not_full: Condvar,
}

impl<T> AsyncQueue<T> {
    pub fn new(capacity: usize) -> Self {
        Self {
            queue: Mutex::new(VecDeque::with_capacity(capacity)),
            capacity,
            not_empty: Condvar::new(),
            not_full: Condvar::new(),
        }
    }
    
    pub async fn enqueue(&self, item: T) -> Result<(), ComputeError> {
        let mut guard = self.queue.lock().await;
        
        if guard.len() >= self.capacity {
            return Err(ComputeError::QueueFull("队列已满".into()));
        }
        
        guard.push_back(item);
        self.not_empty.notify_one();
        
        Ok(())
    }
    
    pub async fn dequeue(&self) -> Result<T, ComputeError> {
        let mut guard = self.queue.lock().await;
        
        if guard.is_empty() {
            // 等待直到队列非空
            let result = tokio::time::timeout(
                Duration::from_secs(60),
                self.not_empty.wait(guard)
            ).await;
            
            match result {
                Ok(new_guard) => {
                    guard = new_guard;
                    if guard.is_empty() {
                        return Err(ComputeError::QueueError("队列为空，但收到非空通知".into()));
                    }
                },
                Err(_) => {
                    return Err(ComputeError::Timeout("等待队列项目超时".into()));
                }
            }
        }
        
        let item = guard.pop_front().ok_or_else(|| {
            ComputeError::QueueError("无法从非空队列获取项目".into())
        })?;
        
        self.not_full.notify_one();
        
        Ok(item)
    }
    
    pub async fn is_empty(&self) -> bool {
        let guard = self.queue.lock().await;
        guard.is_empty()
    }
    
    pub async fn is_full(&self) -> bool {
        let guard = self.queue.lock().await;
        guard.len() >= self.capacity
    }
    
    pub async fn len(&self) -> usize {
        let guard = self.queue.lock().await;
        guard.len()
    }
}
```

异步计算优化的优势：

1. **非阻塞计算**：计算任务在后台线程池执行
2. **计算隔离**：复杂计算不影响主要工作流程
3. **优先级支持**：可以为不同计算任务设置优先级
4. **动态扩展**：支持自定义计算函数扩展
5. **统一接口**：各种计算任务的一致处理方式
6. **内置超时处理**：防止计算任务长时间阻塞

## 13. 可观测性设计

### 13.1 分布式追踪

实现端到端分布式追踪：

```rust
pub struct TracingSystem {
    tracer: opentelemetry::sdk::trace::Tracer,
    context: HashMap<String, String>,
    config: TracingConfig,
    sampling_strategy: Box<dyn SamplingStrategy>,
}

impl TracingSystem {
    pub fn new(config: TracingConfig) -> Result<Self, TracingError> {
        // 创建采样策略
        let sampling_strategy: Box<dyn SamplingStrategy> = match config.sampling_type.as_str() {
            "always" => Box::new(AlwaysSamplingStrategy {}),
            "probability" => Box::new(ProbabilitySamplingStrategy::new(config.sampling_probability)),
            "adaptive" => Box::new(AdaptiveSamplingStrategy::new(
                config.adaptive_min_rate, 
                config.adaptive_max_rate
            )),
            _ => return Err(TracingError::ConfigError("无效的采样策略类型".into())),
        };
        
        // 初始化 OpenTelemetry 导出器
        let exporter = match config.exporter_type.as_str() {
            "jaeger" => {
                let jaeger_endpoint = config.jaeger_endpoint.clone()
                    .ok_or_else(|| TracingError::ConfigError("未提供Jaeger终端地址".into()))?;
                    
                opentelemetry_jaeger::new_pipeline()
                    .with_service_name(&config.service_name)
                    .with_collector_endpoint(&jaeger_endpoint)
                    .install_batch(opentelemetry::runtime::Tokio)?
            },
            "zipkin" => {
                let zipkin_endpoint = config.zipkin_endpoint.clone()
                    .ok_or_else(|| TracingError::ConfigError("未提供Zipkin终端地址".into()))?;
                    
                opentelemetry_zipkin::new_pipeline()
                    .with_service_name(&config.service_name)
                    .with_collector_endpoint(&zipkin_endpoint)
                    .install_batch(opentelemetry::runtime::Tokio)?
            },
            "otlp" => {
                let otlp_endpoint = config.otlp_endpoint.clone()
                    .ok_or_else(|| TracingError::ConfigError("未提供OTLP终端地址".into()))?;
                    
                opentelemetry_otlp::new_pipeline()
                    .tracing()
                    .with_exporter(opentelemetry_otlp::new_exporter()
                        .tonic()
                        .with_endpoint(&otlp_endpoint))
                    .install_batch(opentelemetry::runtime::Tokio)?
            },
            _ => return Err(TracingError::ConfigError("无效的导出器类型".into())),
        };
        
        // 设置全局上下文
        let mut context = HashMap::new();
        context.insert("service.name".to_string(), config.service_name.clone());
        context.insert("service.version".to_string(), config.service_version.clone());
        context.insert("deployment.environment".to_string(), config.environment.clone());
        
        Ok(Self {
            tracer: exporter,
            context,
            config,
            sampling_strategy,
        })
    }
    
    // 创建新的跟踪
    pub fn create_trace(
        &self,
        name: &str,
        kind: SpanKind,
        attributes: HashMap<String, String>,
    ) -> Result<TraceContext, TracingError> {
        // 决定是否采样此跟踪
        if !self.sampling_strategy.should_sample(name, &attributes) {
            return Ok(TraceContext::new_not_sampled(name));
        }
        
        // 创建跟踪上下文
        let mut ctx_builder = SpanBuilder::from_name(name.to_string())
            .with_kind(kind);
            
        // 添加全局上下文属性
        for (key, value) in &self.context {
            ctx_builder = ctx_builder.with_attribute(KeyValue::new(key.clone(), value.clone()));
        }
        
        // 添加自定义属性
        for (key, value) in attributes {
            ctx_builder = ctx_builder.with_attribute(KeyValue::new(key, value));
        }
        
        // 创建跟踪
        let span = self.tracer.build(ctx_builder);
        
        Ok(TraceContext {
            span: Some(span),
            name: name.to_string(),
            is_sampled: true,
            start_time: chrono::Utc::now(),
        })
    }
    
    // 从传入的头部信息恢复跟踪上下文
    pub fn extract_context(&self, headers: &HashMap<String, String>) -> Result<Option<TraceContext>, TracingError> {
        // 提取 trace ID 和 parent span ID
        let trace_id = headers.get("x-trace-id");
        let parent_span_id = headers.get("x-span-id");
        let sampled = headers.get("x-sampled").map(|s| s == "1").unwrap_or(false);
        
        if trace_id.is_none() || parent_span_id.is_none() {
            return Ok(None);
        }
        
        // 使用 OpenTelemetry 的 propagator 提取上下文
        let context = opentelemetry::global::get_text_map_propagator(|propagator| {
            let extractor = HeaderExtractor::new(headers);
            propagator.extract(&extractor)
        });
        
        // 返回恢复的上下文
        if context.span().is_recording() {
            let span = context.span();
            
            Ok(Some(TraceContext {
                span: Some(span),
                name: "extracted".to_string(),
                is_sampled: sampled,
                start_time: chrono::Utc::now(),
            }))
        } else {
            Ok(None)
        }
    }
    
    // 注入当前跟踪上下文到头部信息
    pub fn inject_context(&self, trace_ctx: &TraceContext, headers: &mut HashMap<String, String>) -> Result<(), TracingError> {
        if !trace_ctx.is_sampled || trace_ctx.span.is_none() {
            headers.insert("x-sampled".to_string(), "0".to_string());
            return Ok(());
        }
        
        if let Some(span) = &trace_ctx.span {
            // 使用 OpenTelemetry 的 propagator 注入上下文
            let mut injector = HeaderInjector::new(headers);
            
            opentelemetry::global::get_text_map_propagator(|propagator| {
                propagator.inject_context(&opentelemetry::Context::current_with_span(span.clone()), &mut injector)
            });
            
            headers.insert("x-sampled".to_string(), "1".to_string());
        }
        
        Ok(())
    }
    
    // 关闭追踪系统
    pub fn shutdown(&self) -> Result<(), TracingError> {
        opentelemetry::global::shutdown_tracer_provider();
        Ok(())
    }
}

// 跟踪上下文
#[derive(Debug)]
pub struct TraceContext {
    span: Option<opentelemetry::trace::Span>,
    name: String,
    is_sampled: bool,
    start_time: chrono::DateTime<chrono::Utc>,
}

impl TraceContext {
    // 创建未采样的跟踪上下文
    pub fn new_not_sampled(name: &str) -> Self {
        Self {
            span: None,
            name: name.to_string(),
            is_sampled: false,
            start_time: chrono::Utc::now(),
        }
    }
    
    // 添加事件
    pub fn add_event(&self, name: &str, attributes: HashMap<String, String>) -> Result<(), TracingError> {
        if let Some(span) = &self.span {
            let mut event_attributes = Vec::new();
            for (key, value) in attributes {
                event_attributes.push(KeyValue::new(key, value));
            }
            
            span.add_event(name.to_string(), event_attributes);
        }
        
        Ok(())
    }
    
    // 设置状态
    pub fn set_status(&self, code: StatusCode, message: Option<&str>) -> Result<(), TracingError> {
        if let Some(span) = &self.span {
            match code {
                StatusCode::Ok => span.set_status(Status::Ok),
                StatusCode::Error => {
                    if let Some(msg) = message {
                        span.set_status(Status::error(msg));
                    } else {
                        span.set_status(Status::error("发生错误"));
                    }
                }
                StatusCode::Unset => span.set_status(Status::Unset),
            }
        }
        
        Ok(())
    }
    
    // 添加属性
    pub fn add_attribute(&self, key: &str, value: &str) -> Result<(), TracingError> {
        if let Some(span) = &self.span {
            span.set_attribute(KeyValue::new(key, value.to_string()));
        }
        
        Ok(())
    }
    
    // 记录异常
    pub fn recor
# 分布式工作流执行引擎设计方案（续）

## 13. 可观测性设计（续）

### 13.1 分布式追踪（续）

```rust
// 记录异常
pub fn record_exception(&self, exception_type: &str, message: &str, stack_trace: Option<&str>) -> Result<(), TracingError> {
    if let Some(span) = &self.span {
        let mut attributes = vec![
            KeyValue::new("exception.type", exception_type.to_string()),
            KeyValue::new("exception.message", message.to_string()),
        ];
        
        if let Some(trace) = stack_trace {
            attributes.push(KeyValue::new("exception.stacktrace", trace.to_string()));
        }
        
        span.add_event("exception", attributes);
        span.set_status(Status::error(message));
    }
    
    Ok(())
}

// 结束跟踪
pub fn end(self) -> Result<(), TracingError> {
    if let Some(span) = self.span {
        span.end();
    }
    
    Ok(())
}

// 获取跟踪持续时间
pub fn duration(&self) -> Duration {
    chrono::Utc::now().signed_duration_since(self.start_time).to_std()
        .unwrap_or(Duration::from_secs(0))
}

// 是否被采样
pub fn is_sampled(&self) -> bool {
    self.is_sampled
}

// 头部注入器
struct HeaderInjector<'a> {
    headers: &'a mut HashMap<String, String>,
}

impl<'a> HeaderInjector<'a> {
    fn new(headers: &'a mut HashMap<String, String>) -> Self {
        HeaderInjector { headers }
    }
}

impl<'a> Injector for HeaderInjector<'a> {
    fn set(&mut self, key: &str, value: String) {
        self.headers.insert(key.to_string(), value);
    }
}

// 头部提取器
struct HeaderExtractor<'a> {
    headers: &'a HashMap<String, String>,
}

impl<'a> HeaderExtractor<'a> {
    fn new(headers: &'a HashMap<String, String>) -> Self {
        HeaderExtractor { headers }
    }
}

impl<'a> Extractor for HeaderExtractor<'a> {
    fn get(&self, key: &str) -> Option<&str> {
        self.headers.get(key).map(|v| v.as_str())
    }
    
    fn keys(&self) -> Vec<&str> {
        self.headers.keys().map(|k| k.as_str()).collect()
    }
}

// 采样策略接口
trait SamplingStrategy: Send + Sync {
    fn should_sample(&self, operation_name: &str, attributes: &HashMap<String, String>) -> bool;
}

// 总是采样策略
struct AlwaysSamplingStrategy {}

impl SamplingStrategy for AlwaysSamplingStrategy {
    fn should_sample(&self, _operation_name: &str, _attributes: &HashMap<String, String>) -> bool {
        true
    }
}

// 概率采样策略
struct ProbabilitySamplingStrategy {
    probability: f64,
}

impl ProbabilitySamplingStrategy {
    fn new(probability: f64) -> Self {
        let prob = probability.clamp(0.0, 1.0);
        Self { probability: prob }
    }
}

impl SamplingStrategy for ProbabilitySamplingStrategy {
    fn should_sample(&self, _operation_name: &str, _attributes: &HashMap<String, String>) -> bool {
        let random_value: f64 = rand::random();
        random_value <= self.probability
    }
}

// 自适应采样策略
struct AdaptiveSamplingStrategy {
    min_rate: f64,
    max_rate: f64,
    current_rate: AtomicF64,
    last_adjustment: AtomicU64,
    operations: RwLock<HashMap<String, OperationStats>>,
}

impl AdaptiveSamplingStrategy {
    fn new(min_rate: f64, max_rate: f64) -> Self {
        let current_rate = (min_rate + max_rate) / 2.0;
        Self {
            min_rate,
            max_rate,
            current_rate: AtomicF64::new(current_rate),
            last_adjustment: AtomicU64::new(chrono::Utc::now().timestamp() as u64),
            operations: RwLock::new(HashMap::new()),
        }
    }
    
    // 自适应调整采样率
    fn adjust_sampling_rate(&self) {
        let now = chrono::Utc::now().timestamp() as u64;
        let last = self.last_adjustment.load(Ordering::Relaxed);
        
        // 每60秒调整一次
        if now - last < 60 {
            return;
        }
        
        if self.last_adjustment.compare_exchange(
            last, now, Ordering::Relaxed, Ordering::Relaxed
        ).is_err() {
            return; // 其他线程正在调整
        }
        
        let operations = self.operations.read().unwrap();
        if operations.is_empty() {
            return;
        }
        
        // 计算平均错误率
        let mut total_error_rate = 0.0;
        let mut count = 0;
        
        for stats in operations.values() {
            if stats.total_count > 0 {
                total_error_rate += stats.error_count as f64 / stats.total_count as f64;
                count += 1;
            }
        }
        
        if count == 0 {
            return;
        }
        
        let avg_error_rate = total_error_rate / count as f64;
        let current_rate = self.current_rate.load(Ordering::Relaxed);
        
        // 根据错误率调整采样率
        let new_rate = if avg_error_rate > 0.1 {
            // 错误率高，增加采样率
            (current_rate * 1.5).min(self.max_rate)
        } else if avg_error_rate < 0.01 {
            // 错误率低，减少采样率
            (current_rate * 0.8).max(self.min_rate)
        } else {
            current_rate
        };
        
        self.current_rate.store(new_rate, Ordering::Relaxed);
        
        // 清除老数据
        let mut operations = self.operations.write().unwrap();
        operations.clear();
    }
    
    // 更新操作统计
    fn update_stats(&self, operation_name: &str, is_error: bool) {
        let mut operations = self.operations.write().unwrap();
        
        let stats = operations.entry(operation_name.to_string())
            .or_insert_with(|| OperationStats {
                total_count: 0,
                error_count: 0,
            });
            
        stats.total_count += 1;
        if is_error {
            stats.error_count += 1;
        }
    }
}

impl SamplingStrategy for AdaptiveSamplingStrategy {
    fn should_sample(&self, operation_name: &str, attributes: &HashMap<String, String>) -> bool {
        // 调整采样率
        self.adjust_sampling_rate();
        
        // 对错误总是采样
        if let Some(error_flag) = attributes.get("error") {
            if error_flag == "true" || error_flag == "1" {
                self.update_stats(operation_name, true);
                return true;
            }
        }
        
        // 按当前采样率决定
        let current_rate = self.current_rate.load(Ordering::Relaxed);
        let random_value: f64 = rand::random();
        let should_sample = random_value <= current_rate;
        
        if should_sample {
            // 记录采样的操作统计
            self.update_stats(operation_name, false);
        }
        
        should_sample
    }
}

// 操作统计
struct OperationStats {
    total_count: u64,
    error_count: u64,
}

// 追踪配置
#[derive(Clone, Debug)]
pub struct TracingConfig {
    pub service_name: String,
    pub service_version: String,
    pub environment: String,
    pub exporter_type: String,
    pub jaeger_endpoint: Option<String>,
    pub zipkin_endpoint: Option<String>,
    pub otlp_endpoint: Option<String>,
    pub sampling_type: String,
    pub sampling_probability: f64,
    pub adaptive_min_rate: f64,
    pub adaptive_max_rate: f64,
}

// 追踪错误
#[derive(Debug, thiserror::Error)]
pub enum TracingError {
    #[error("配置错误: {0}")]
    ConfigError(String),
    
    #[error("初始化错误: {0}")]
    InitError(String),
    
    #[error("OpenTelemetry错误: {0}")]
    OtelError(#[from] opentelemetry::trace::TraceError),
}

// 状态码
#[derive(Debug, Clone, Copy)]
pub enum StatusCode {
    Unset,
    Ok,
    Error,
}

分布式追踪的优势：
1. **多种导出器**：支持Jaeger、Zipkin和OTLP
2. **可配置采样**：支持固定、概率和自适应采样
3. **上下文传播**：跨服务跟踪链路
4. **异常记录**：自动记录错误和堆栈
5. **自适应采样**：根据错误率动态调整采样率
6. **可观测指标**：记录跟踪持续时间与状态

### 13.2 结构化日志

实现高性能结构化日志系统：

```rust
pub struct LoggingSystem {
    logger: Logger,
    config: LoggingConfig,
}

impl LoggingSystem {
    pub fn new(config: LoggingConfig) -> Result<Self, LoggingError> {
        // 创建日志环境
        let environment = Environment::new();
        
        // 创建日志输出目标
        let mut drain = Self::build_drain(&config)?;
        
        // 设置日志级别
        let log_level = match config.log_level.as_str() {
            "trace" => Level::TRACE,
            "debug" => Level::DEBUG,
            "info" => Level::INFO,
            "warn" => Level::WARNING,
            "error" => Level::ERROR,
            _ => Level::INFO,
        };
        
        drain = drain.filter_level(log_level).fuse();
        
        // 设置异步处理
        let drain = if config.async_logging {
            let (async_drain, guard) = slog_async::Async::new(drain)
                .chan_size(config.async_queue_size)
                .overflow_strategy(Self::get_overflow_strategy(&config.overflow_strategy))
                .build_with_guard();
                
            // 存储guard防止提前释放
            std::mem::forget(guard);
            
            async_drain.fuse()
        } else {
            drain
        };
        
        // 创建logger
        let logger = Logger::root(drain, o!("version" => env!("CARGO_PKG_VERSION")));
        
        Ok(Self {
            logger,
            config,
        })
    }
    
    // 构建日志输出配置
    fn build_drain(config: &LoggingConfig) -> Result<Drain, LoggingError> {
        // 创建格式化器
        let formatter = Self::build_formatter(config)?;
        
        match config.output_type.as_str() {
            "console" => {
                // 控制台输出
                let decorator = slog_term::TermDecorator::new().build();
                let drain = slog_term::FullFormat::new(decorator)
                    .use_original_order()
                    .build().fuse();
                
                Ok(drain)
            },
            "json" => {
                // JSON格式输出
                let drain = slog_json::Json::new(std::io::stdout())
                    .add_default_keys()
                    .build().fuse();
                
                Ok(drain)
            },
            "file" => {
                // 文件输出
                let file_path = config.file_path.as_ref()
                    .ok_or_else(|| LoggingError::ConfigError("未指定日志文件路径".into()))?;
                
                // 创建日志目录
                if let Some(parent) = std::path::Path::new(file_path).parent() {
                    std::fs::create_dir_all(parent)
                        .map_err(|e| LoggingError::IoError(format!("无法创建日志目录: {}", e)))?;
                }
                
                // 创建文件
                let file = std::fs::OpenOptions::new()
                    .create(true)
                    .append(true)
                    .open(file_path)
                    .map_err(|e| LoggingError::IoError(format!("无法打开日志文件: {}", e)))?;
                
                let drain = match config.file_format.as_deref() {
                    Some("json") => {
                        slog_json::Json::new(file)
                            .add_default_keys()
                            .build().fuse()
                    },
                    _ => {
                        let decorator = slog_term::PlainDecorator::new(file);
                        slog_term::FullFormat::new(decorator)
                            .use_original_order()
                            .build().fuse()
                    }
                };
                
                Ok(drain)
            },
            "rotating_file" => {
                // 滚动日志文件
                let file_path = config.file_path.as_ref()
                    .ok_or_else(|| LoggingError::ConfigError("未指定日志文件路径".into()))?;
                
                // 创建日志目录
                if let Some(parent) = std::path::Path::new(file_path).parent() {
                    std::fs::create_dir_all(parent)
                        .map_err(|e| LoggingError::IoError(format!("无法创建日志目录: {}", e)))?;
                }
                
                // 创建滚动日志
                let file = slog_rotating_file::RotatingFileAppender::new(
                    slog_rotating_file::RotationPolicy::new_size_limit(config.rotation_size_bytes),
                    file_path,
                    config.max_files,
                    true
                ).map_err(|e| LoggingError::IoError(format!("无法创建滚动日志: {}", e)))?;
                
                let drain = match config.file_format.as_deref() {
                    Some("json") => {
                        slog_json::Json::new(file)
                            .add_default_keys()
                            .build().fuse()
                    },
                    _ => {
                        let decorator = slog_term::PlainDecorator::new(file);
                        slog_term::FullFormat::new(decorator)
                            .use_original_order()
                            .build().fuse()
                    }
                };
                
                Ok(drain)
            },
            "syslog" => {
                // 系统日志
                let formatter = slog_syslog::SyslogFormatter::new();
                let drain = slog_syslog::unix_3164(formatter)
                    .map_err(|e| LoggingError::IoError(format!("无法创建系统日志: {}", e)))?
                    .fuse();
                
                Ok(drain)
            },
            _ => Err(LoggingError::ConfigError(format!("未知的日志输出类型: {}", config.output_type))),
        }
    }
    
    // 构建格式化器
    fn build_formatter(config: &LoggingConfig) -> Result<Box<dyn Format>, LoggingError> {
        match config.format.as_str() {
            "simple" => {
                Ok(Box::new(SimpleFormatter))
            },
            "detailed" => {
                Ok(Box::new(DetailedFormatter))
            },
            "json" => {
                Ok(Box::new(JsonFormatter))
            },
            _ => Err(LoggingError::ConfigError(format!("未知的日志格式: {}", config.format))),
        }
    }
    
    // 获取溢出策略
    fn get_overflow_strategy(strategy: &str) -> slog_async::OverflowStrategy {
        match strategy {
            "block" => slog_async::OverflowStrategy::Block,
            "drop_newest" => slog_async::OverflowStrategy::DropAndReport,
            "drop_oldest" => slog_async::OverflowStrategy::DropOld,
            _ => slog_async::OverflowStrategy::Block,
        }
    }
    
    // 获取logger
    pub fn get_logger(&self) -> Logger {
        self.logger.clone()
    }
    
    // 获取带上下文的logger
    pub fn with_context(&self, context: HashMap<String, String>) -> Logger {
        let mut logger = self.logger.clone();
        
        for (key, value) in context {
            logger = logger.new(o!(key => value));
        }
        
        logger
    }
    
    // 获取带跟踪上下文的logger
    pub fn with_trace_context(&self, trace_ctx: &TraceContext) -> Logger {
        let mut logger = self.logger.clone();
        
        // 添加跟踪ID
        logger = logger.new(o!(
            "trace_id" => trace_ctx.trace_id().unwrap_or_default(),
            "span_id" => trace_ctx.span_id().unwrap_or_default(),
            "sampled" => trace_ctx.is_sampled()
        ));
        
        logger
    }
    
    // 创建带工作流上下文的logger
    pub fn workflow_logger(&self, workflow_id: &str, instance_id: &str) -> Logger {
        self.logger.new(o!(
            "workflow_id" => workflow_id.to_string(),
            "instance_id" => instance_id.to_string(),
            "component" => "workflow"
        ))
    }
    
    // 创建带任务上下文的logger
    pub fn task_logger(&self, workflow_id: &str, instance_id: &str, task_id: &str) -> Logger {
        self.logger.new(o!(
            "workflow_id" => workflow_id.to_string(),
            "instance_id" => instance_id.to_string(),
            "task_id" => task_id.to_string(),
            "component" => "task"
        ))
    }
    
    // 提供静态 trace 日志方法
    pub fn trace(logger: &Logger, msg: &str, values: Vec<(&str, String)>) {
        let mut log_args = vec![];
        for (key, value) in values {
            log_args.push((key, value));
        }
        
        trace!(logger, "{}", msg; log_args);
    }
    
    // 提供静态 debug 日志方法
    pub fn debug(logger: &Logger, msg: &str, values: Vec<(&str, String)>) {
        let mut log_args = vec![];
        for (key, value) in values {
            log_args.push((key, value));
        }
        
        debug!(logger, "{}", msg; log_args);
    }
    
    // 提供静态 info 日志方法
    pub fn info(logger: &Logger, msg: &str, values: Vec<(&str, String)>) {
        let mut log_args = vec![];
        for (key, value) in values {
            log_args.push((key, value));
        }
        
        info!(logger, "{}", msg; log_args);
    }
    
    // 提供静态 warn 日志方法
    pub fn warn(logger: &Logger, msg: &str, values: Vec<(&str, String)>) {
        let mut log_args = vec![];
        for (key, value) in values {
            log_args.push((key, value));
        }
        
        warn!(logger, "{}", msg; log_args);
    }
    
    // 提供静态 error 日志方法
    pub fn error(logger: &Logger, msg: &str, values: Vec<(&str, String)>) {
        let mut log_args = vec![];
        for (key, value) in values {
            log_args.push((key, value));
        }
        
        error!(logger, "{}", msg; log_args);
    }
}

// 日志格式化接口
trait Format: Send + Sync {
    fn format(&self, record: &Record) -> String;
}

// 简单格式化器
struct SimpleFormatter;

impl Format for SimpleFormatter {
    fn format(&self, record: &Record) -> String {
        format!("[{}] {} - {}", record.level(), record.timestamp(), record.msg())
    }
}

// 详细格式化器
struct DetailedFormatter;

impl Format for DetailedFormatter {
    fn format(&self, record: &Record) -> String {
        let mut result = format!(
            "[{}] [{}] [{}] {} - {}",
            record.timestamp(),
            record.level(),
            record.module(),
            record.thread_name().unwrap_or("unknown"),
            record.msg()
        );
        
        // 添加额外字段
        for field in record.fields() {
            result.push_str(&format!(", {}={}", field.name(), field.value()));
        }
        
        result
    }
}

// JSON格式化器
struct JsonFormatter;

impl Format for JsonFormatter {
    fn format(&self, record: &Record) -> String {
        let mut map = serde_json::Map::new();
        
        map.insert("timestamp".to_string(), serde_json::Value::String(record.timestamp()));
        map.insert("level".to_string(), serde_json::Value::String(record.level().to_string()));
        map.insert("message".to_string(), serde_json::Value::String(record.msg().to_string()));
        map.insert("module".to_string(), serde_json::Value::String(record.module().to_string()));
        
        if let Some(thread) = record.thread_name() {
            map.insert("thread".to_string(), serde_json::Value::String(thread.to_string()));
        }
        
        // 添加额外字段
        for field in record.fields() {
            map.insert(
                field.name().to_string(),
                serde_json::Value::String(field.value().to_string())
            );
        }
        
        serde_json::to_string(&map).unwrap_or_else(|_| "{}".to_string())
    }
}

// 日志配置
#[derive(Clone, Debug)]
pub struct LoggingConfig {
    pub log_level: String,
    pub output_type: String,
    pub format: String,
    pub file_path: Option<String>,
    pub file_format: Option<String>,
    pub rotation_size_bytes: u64,
    pub max_files: u32,
    pub async_logging: bool,
    pub async_queue_size: usize,
    pub overflow_strategy: String,
}

// 日志错误
#[derive(Debug, thiserror::Error)]
pub enum LoggingError {
    #[error("配置错误: {0}")]
    ConfigError(String),
    
    #[error("IO错误: {0}")]
    IoError(String),
}
```

结构化日志的优势：

1. **多种输出目标**：控制台、文件、滚动文件和系统日志
2. **结构化格式化**：简单、详细和JSON格式
3. **异步处理**：非阻塞日志记录
4. **上下文丰富**：支持工作流、任务和追踪上下文
5. **集成追踪**：与分布式追踪系统无缝集成
6. **滚动日志**：自动管理日志文件大小和数量

### 13.3 指标收集

实现全面的指标收集系统：

```rust
pub struct MetricsCollector {
    registry: prometheus::Registry,
    config: MetricsConfig,
    exporters: Vec<Box<dyn MetricsExporter>>,
    counters: RwLock<HashMap<String, prometheus::IntCounter>>,
    gauges: RwLock<HashMap<String, prometheus::Gauge>>,
    histograms: RwLock<HashMap<String, prometheus::Histogram>>,
}

impl MetricsCollector {
    pub fn new(config: MetricsConfig) -> Result<Self, MetricsError> {
        let registry = prometheus::Registry::new();
        
        // 创建指标导出器
        let mut exporters: Vec<Box<dyn MetricsExporter>> = Vec::new();
        
        for exporter_config in &config.exporters {
            match exporter_config.exporter_type.as_str() {
                "prometheus" => {
                    let exporter = PrometheusExporter::new(
                        exporter_config.endpoint.clone().unwrap_or_else(|| "/metrics".to_string()),
                        registry.clone()
                    )?;
                    exporters.push(Box::new(exporter));
                },
                "statsd" => {
                    let host = exporter_config.host.clone()
                        .ok_or_else(|| MetricsError::ConfigError("StatsD导出器需要host参数".into()))?;
                    let port = exporter_config.port
                        .ok_or_else(|| MetricsError::ConfigError("StatsD导出器需要port参数".into()))?;
                    
                    let exporter = StatsdExporter::new(&host, port)?;
                    exporters.push(Box::new(exporter));
                },
                "prometheus_pushgateway" => {
                    let endpoint = exporter_config.endpoint.clone()
                        .ok_or_else(|| MetricsError::ConfigError("Prometheus Pushgateway导出器需要endpoint参数".into()))?;
                    
                    let exporter = PrometheusPushgatewayExporter::new(
                        &endpoint,
                        &config.service_name,
                        registry.clone()
                    )?;
                    exporters.push(Box::new(exporter));
                },
                "log" => {
                    let exporter = LogExporter::new();
                    exporters.push(Box::new(exporter));
                },
                _ => return Err(MetricsError::ConfigError(format!("未知的指标导出器类型: {}", exporter_config.exporter_type))),
            }
        }
        
        Ok(Self {
            registry,
            config,
            exporters,
            counters: RwLock::new(HashMap::new()),
            gauges: RwLock::new(HashMap::new()),
            histograms: RwLock::new(HashMap::new()),
        })
    }
    
    // 启动指标收集
    pub fn start(&self) -> Result<Vec<JoinHandle<()>>, MetricsError> {
        let mut handles = Vec::new();
        
        // 启动所有导出器
        for exporter in &self.exporters {
            if let Some(handle) = exporter.start()? {
                handles.push(handle);
            }
        }
        
        // 注册默认指标
        self.register_default_metrics()?;
        
        Ok(handles)
    }
    
    // 注册默认指标
    fn register_default_metrics(&self) -> Result<(), MetricsError> {
        // 系统信息
        let process_start_time = prometheus::Gauge::new(
            "process_start_time_seconds",
            "Process start time in seconds since Unix epoch"
        )?;
        
        process_start_time.set(std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs_f64());
            
        self.registry.register(Box::new(process_start_time))?;
        
        // JVM信息（如果在Java环境中运行）
        if cfg!(target_os = "java") {
            // 添加JVM相关指标
        }
        
        // 注册系统指标
        let system_metrics = self.register_system_metrics()?;
        for metric in system_metrics {
            self.registry.register(metric)?;
        }
        
        Ok(())
    }
    
    // 注册系统指标
    fn register_system_metrics(&self) -> Result<Vec<Box<dyn prometheus::core::Collector>>, MetricsError> {
        let mut collectors: Vec<Box<dyn prometheus::core::Collector>> = Vec::new();
        
        // CPU使用率
        let cpu_usage = prometheus::Gauge::new(
            "system_cpu_usage",
            "System CPU usage (percentage)"
        )?;
        
        collectors.push(Box::new(cpu_usage));
        
        // 内存使用
        let memory_usage = prometheus::Gauge::new(
            "system_memory_usage_bytes",
            "System memory usage in bytes"
        )?;
        
        collectors.push(Box::new(memory_usage));
        
        // 可用内存
        let memory_available = prometheus::Gauge::new(
            "system_memory_available_bytes",
            "System memory available in bytes"
        )?;
        
        collectors.push(Box::new(memory_available));
        
        // 磁盘使用
        let disk_usage = prometheus::Gauge::new(
            "system_disk_usage_bytes",
            "System disk usage
# 分布式工作流执行引擎设计方案（续）

## 13. 可观测性设计（续）

### 13.3 指标收集（续）

```rust
// 磁盘使用
let disk_usage = prometheus::Gauge::new(
    "system_disk_usage_bytes",
    "System disk usage in bytes"
)?;

collectors.push(Box::new(disk_usage));

// 磁盘空闲
let disk_free = prometheus::Gauge::new(
    "system_disk_free_bytes",
    "System disk free space in bytes"
)?;

collectors.push(Box::new(disk_free));

// 网络流量 - 接收
let network_receive = prometheus::Counter::new(
    "system_network_receive_bytes_total",
    "Total bytes received from network"
)?;

collectors.push(Box::new(network_receive));

// 网络流量 - 发送
let network_transmit = prometheus::Counter::new(
    "system_network_transmit_bytes_total",
    "Total bytes transmitted to network"
)?;

collectors.push(Box::new(network_transmit));

// 文件描述符
let open_fds = prometheus::Gauge::new(
    "system_open_file_descriptors",
    "Number of open file descriptors"
)?;

collectors.push(Box::new(open_fds));

Ok(collectors)
}

// 记录计数器
pub fn increment_counter(&self, name: &str, help: &str, labels: HashMap<String, String>, value: u64) -> Result<(), MetricsError> {
    let counter = self.get_or_create_counter(name, help, labels.clone())?;
    counter.inc_by(value as f64);
    
    // 同时发送到所有导出器
    for exporter in &self.exporters {
        if let Err(e) = exporter.export_counter(name, value, &labels) {
            log::warn!("指标导出失败: {}", e);
        }
    }
    
    Ok(())
}

// 获取或创建计数器
fn get_or_create_counter(&self, name: &str, help: &str, labels: HashMap<String, String>) -> Result<prometheus::IntCounter, MetricsError> {
    let counters = self.counters.read().unwrap();
    
    // 构建唯一键，包括标签
    let key = Self::build_metric_key(name, &labels);
    
    if let Some(counter) = counters.get(&key) {
        return Ok(counter.clone());
    }
    
    // 如果不存在，则需要创建
    drop(counters);
    let mut counters = self.counters.write().unwrap();
    
    // 再次检查，避免竞态条件
    if let Some(counter) = counters.get(&key) {
        return Ok(counter.clone());
    }
    
    // 创建新计数器
    let counter = if labels.is_empty() {
        prometheus::IntCounter::new(name, help)?
    } else {
        // 创建带标签的计数器
        let mut label_keys: Vec<&str> = labels.keys().map(|k| k.as_str()).collect();
        label_keys.sort(); // 确保标签顺序一致
        
        let label_values: Vec<&str> = label_keys.iter()
            .map(|&k| labels.get(k).unwrap().as_str())
            .collect();
            
        let counter_vec = prometheus::IntCounterVec::new(
            prometheus::opts!(name, help),
            &label_keys
        )?;
        
        self.registry.register(Box::new(counter_vec.clone()))?;
        counter_vec.with_label_values(&label_values)
    };
    
    if labels.is_empty() {
        self.registry.register(Box::new(counter.clone()))?;
    }
    
    counters.insert(key, counter.clone());
    
    Ok(counter)
}

// 设置仪表盘值
pub fn set_gauge(&self, name: &str, help: &str, labels: HashMap<String, String>, value: f64) -> Result<(), MetricsError> {
    let gauge = self.get_or_create_gauge(name, help, labels.clone())?;
    gauge.set(value);
    
    // 同时发送到所有导出器
    for exporter in &self.exporters {
        if let Err(e) = exporter.export_gauge(name, value, &labels) {
            log::warn!("指标导出失败: {}", e);
        }
    }
    
    Ok(())
}

// 获取或创建仪表盘
fn get_or_create_gauge(&self, name: &str, help: &str, labels: HashMap<String, String>) -> Result<prometheus::Gauge, MetricsError> {
    let gauges = self.gauges.read().unwrap();
    
    // 构建唯一键，包括标签
    let key = Self::build_metric_key(name, &labels);
    
    if let Some(gauge) = gauges.get(&key) {
        return Ok(gauge.clone());
    }
    
    // 如果不存在，则需要创建
    drop(gauges);
    let mut gauges = self.gauges.write().unwrap();
    
    // 再次检查，避免竞态条件
    if let Some(gauge) = gauges.get(&key) {
        return Ok(gauge.clone());
    }
    
    // 创建新仪表盘
    let gauge = if labels.is_empty() {
        prometheus::Gauge::new(name, help)?
    } else {
        // 创建带标签的仪表盘
        let mut label_keys: Vec<&str> = labels.keys().map(|k| k.as_str()).collect();
        label_keys.sort(); // 确保标签顺序一致
        
        let label_values: Vec<&str> = label_keys.iter()
            .map(|&k| labels.get(k).unwrap().as_str())
            .collect();
            
        let gauge_vec = prometheus::GaugeVec::new(
            prometheus::opts!(name, help),
            &label_keys
        )?;
        
        self.registry.register(Box::new(gauge_vec.clone()))?;
        gauge_vec.with_label_values(&label_values)
    };
    
    if labels.is_empty() {
        self.registry.register(Box::new(gauge.clone()))?;
    }
    
    gauges.insert(key, gauge.clone());
    
    Ok(gauge)
}

// 记录直方图
pub fn observe_histogram(&self, name: &str, help: &str, buckets: Option<Vec<f64>>, labels: HashMap<String, String>, value: f64) -> Result<(), MetricsError> {
    let histogram = self.get_or_create_histogram(name, help, buckets, labels.clone())?;
    histogram.observe(value);
    
    // 同时发送到所有导出器
    for exporter in &self.exporters {
        if let Err(e) = exporter.export_histogram(name, value, &labels) {
            log::warn!("指标导出失败: {}", e);
        }
    }
    
    Ok(())
}

// 获取或创建直方图
fn get_or_create_histogram(&self, name: &str, help: &str, buckets: Option<Vec<f64>>, labels: HashMap<String, String>) -> Result<prometheus::Histogram, MetricsError> {
    let histograms = self.histograms.read().unwrap();
    
    // 构建唯一键，包括标签
    let key = Self::build_metric_key(name, &labels);
    
    if let Some(histogram) = histograms.get(&key) {
        return Ok(histogram.clone());
    }
    
    // 如果不存在，则需要创建
    drop(histograms);
    let mut histograms = self.histograms.write().unwrap();
    
    // 再次检查，避免竞态条件
    if let Some(histogram) = histograms.get(&key) {
        return Ok(histogram.clone());
    }
    
    // 创建新直方图
    let histogram = if labels.is_empty() {
        let mut opts = prometheus::HistogramOpts::new(name, help);
        if let Some(b) = buckets {
            opts = opts.buckets(b);
        }
        prometheus::Histogram::with_opts(opts)?
    } else {
        // 创建带标签的直方图
        let mut label_keys: Vec<&str> = labels.keys().map(|k| k.as_str()).collect();
        label_keys.sort(); // 确保标签顺序一致
        
        let label_values: Vec<&str> = label_keys.iter()
            .map(|&k| labels.get(k).unwrap().as_str())
            .collect();
            
        let mut opts = prometheus::HistogramOpts::new(name, help);
        if let Some(b) = buckets {
            opts = opts.buckets(b);
        }
        
        let histogram_vec = prometheus::HistogramVec::new(
            opts,
            &label_keys
        )?;
        
        self.registry.register(Box::new(histogram_vec.clone()))?;
        histogram_vec.with_label_values(&label_values)
    };
    
    if labels.is_empty() {
        self.registry.register(Box::new(histogram.clone()))?;
    }
    
    histograms.insert(key, histogram.clone());
    
    Ok(histogram)
}

// 构建指标唯一键
fn build_metric_key(name: &str, labels: &HashMap<String, String>) -> String {
    if labels.is_empty() {
        return name.to_string();
    }
    
    let mut keys: Vec<&str> = labels.keys().map(|k| k.as_str()).collect();
    keys.sort();
    
    let labels_str: String = keys.iter()
        .map(|k| format!("{}={}", k, labels.get(*k).unwrap()))
        .collect::<Vec<String>>()
        .join(",");
        
    format!("{}:{}", name, labels_str)
}

// 记录工作流指标
pub fn record_workflow_metrics(&self, workflow_id: &str, instance_id: &str, state: &str, duration_ms: u64) -> Result<(), MetricsError> {
    let mut labels = HashMap::new();
    labels.insert("workflow_id".to_string(), workflow_id.to_string());
    labels.insert("instance_id".to_string(), instance_id.to_string());
    labels.insert("state".to_string(), state.to_string());
    
    // 记录工作流执行计数
    self.increment_counter(
        "workflow_executions_total",
        "Total number of workflow executions",
        labels.clone(),
        1
    )?;
    
    // 记录工作流执行时间
    self.observe_histogram(
        "workflow_execution_duration_milliseconds",
        "Duration of workflow execution in milliseconds",
        Some(vec![10.0, 50.0, 100.0, 500.0, 1000.0, 5000.0, 10000.0, 50000.0]),
        labels,
        duration_ms as f64
    )?;
    
    Ok(())
}

// 记录任务指标
pub fn record_task_metrics(&self, workflow_id: &str, task_id: &str, task_type: &str, state: &str, duration_ms: u64) -> Result<(), MetricsError> {
    let mut labels = HashMap::new();
    labels.insert("workflow_id".to_string(), workflow_id.to_string());
    labels.insert("task_id".to_string(), task_id.to_string());
    labels.insert("task_type".to_string(), task_type.to_string());
    labels.insert("state".to_string(), state.to_string());
    
    // 记录任务执行计数
    self.increment_counter(
        "task_executions_total",
        "Total number of task executions",
        labels.clone(),
        1
    )?;
    
    // 记录任务执行时间
    self.observe_histogram(
        "task_execution_duration_milliseconds",
        "Duration of task execution in milliseconds",
        Some(vec![5.0, 20.0, 50.0, 100.0, 500.0, 1000.0, 5000.0, 10000.0]),
        labels,
        duration_ms as f64
    )?;
    
    Ok(())
}

// 记录任务队列指标
pub fn record_queue_metrics(&self, queue_name: &str, size: u64, processed: u64, waiting_time_ms: u64) -> Result<(), MetricsError> {
    let mut labels = HashMap::new();
    labels.insert("queue_name".to_string(), queue_name.to_string());
    
    // 记录队列大小
    self.set_gauge(
        "task_queue_size",
        "Current size of the task queue",
        labels.clone(),
        size as f64
    )?;
    
    // 记录处理任务数
    self.increment_counter(
        "tasks_processed_total",
        "Total number of tasks processed",
        labels.clone(),
        processed
    )?;
    
    // 记录等待时间
    if waiting_time_ms > 0 {
        self.observe_histogram(
            "task_queue_waiting_time_milliseconds",
            "Task waiting time in the queue in milliseconds",
            Some(vec![1.0, 5.0, 10.0, 50.0, 100.0, 500.0, 1000.0, 5000.0]),
            labels,
            waiting_time_ms as f64
        )?;
    }
    
    Ok(())
}

// 记录系统资源指标
pub fn record_system_metrics(&self) -> Result<(), MetricsError> {
    // 获取当前系统信息
    let sys_info = sysinfo::System::new_all();
    
    // CPU使用率
    let cpu_usage = sys_info.global_cpu_info().cpu_usage();
    self.set_gauge(
        "system_cpu_usage",
        "System CPU usage (percentage)",
        HashMap::new(),
        cpu_usage
    )?;
    
    // 内存使用
    let total_memory = sys_info.total_memory();
    let used_memory = sys_info.used_memory();
    
    self.set_gauge(
        "system_memory_usage_bytes",
        "System memory usage in bytes",
        HashMap::new(),
        used_memory as f64
    )?;
    
    self.set_gauge(
        "system_memory_available_bytes",
        "System memory available in bytes",
        HashMap::new(),
        (total_memory - used_memory) as f64
    )?;
    
    // 磁盘信息
    for disk in sys_info.disks() {
        let mut labels = HashMap::new();
        labels.insert("mount_point".to_string(), disk.mount_point().to_string_lossy().to_string());
        
        self.set_gauge(
            "system_disk_usage_bytes",
            "System disk usage in bytes",
            labels.clone(),
            (disk.total_space() - disk.available_space()) as f64
        )?;
        
        self.set_gauge(
            "system_disk_free_bytes",
            "System disk free space in bytes",
            labels,
            disk.available_space() as f64
        )?;
    }
    
    // 网络信息
    for (interface_name, data) in sys_info.networks() {
        let mut labels = HashMap::new();
        labels.insert("interface".to_string(), interface_name.to_string());
        
        self.increment_counter(
            "system_network_receive_bytes_total",
            "Total bytes received from network",
            labels.clone(),
            data.received() as u64
        )?;
        
        self.increment_counter(
            "system_network_transmit_bytes_total",
            "Total bytes transmitted to network",
            labels,
            data.transmitted() as u64
        )?;
    }
    
    // 文件描述符
    if let Ok(count) = get_open_fd_count() {
        self.set_gauge(
            "system_open_file_descriptors",
            "Number of open file descriptors",
            HashMap::new(),
            count as f64
        )?;
    }
    
    Ok(())
}

// 获取打开的文件描述符数量
fn get_open_fd_count() -> Result<usize, std::io::Error> {
    #[cfg(target_family = "unix")]
    {
        let entries = std::fs::read_dir("/proc/self/fd")?;
        let count = entries.count();
        Ok(count)
    }
    
    #[cfg(not(target_family = "unix"))]
    {
        // Windows等系统不支持直接获取文件描述符数量
        Ok(0)
    }
}
}

// 指标导出器接口
trait MetricsExporter: Send + Sync {
    fn start(&self) -> Result<Option<JoinHandle<()>>, MetricsError>;
    fn export_counter(&self, name: &str, value: u64, labels: &HashMap<String, String>) -> Result<(), MetricsError>;
    fn export_gauge(&self, name: &str, value: f64, labels: &HashMap<String, String>) -> Result<(), MetricsError>;
    fn export_histogram(&self, name: &str, value: f64, labels: &HashMap<String, String>) -> Result<(), MetricsError>;
}

// Prometheus 导出器
struct PrometheusExporter {
    endpoint: String,
    registry: prometheus::Registry,
    server: Option<HttpServer>,
}

impl PrometheusExporter {
    fn new(endpoint: String, registry: prometheus::Registry) -> Result<Self, MetricsError> {
        Ok(Self {
            endpoint,
            registry,
            server: None,
        })
    }
}

impl MetricsExporter for PrometheusExporter {
    fn start(&self) -> Result<Option<JoinHandle<()>>, MetricsError> {
        let endpoint = self.endpoint.clone();
        let registry = self.registry.clone();
        
        let server = HttpServer::new(move |req| {
            if req.uri() == endpoint {
                let mut buffer = Vec::new();
                let encoder = prometheus::TextEncoder::new();
                let metric_families = registry.gather();
                
                if let Err(e) = encoder.encode(&metric_families, &mut buffer) {
                    return HttpResponse::InternalServerError()
                        .body(format!("ERROR: {}", e));
                }
                
                HttpResponse::Ok()
                    .content_type("text/plain")
                    .body(buffer)
            } else {
                HttpResponse::NotFound().body("Not found")
            }
        });
        
        let handle = tokio::spawn(async move {
            if let Err(e) = server.bind("0.0.0.0:9091").run().await {
                log::error!("Prometheus指标服务器错误: {}", e);
            }
        });
        
        Ok(Some(handle))
    }
    
    fn export_counter(&self, _name: &str, _value: u64, _labels: &HashMap<String, String>) -> Result<(), MetricsError> {
        // Prometheus导出器不需要额外操作，指标已通过注册表导出
        Ok(())
    }
    
    fn export_gauge(&self, _name: &str, _value: f64, _labels: &HashMap<String, String>) -> Result<(), MetricsError> {
        // Prometheus导出器不需要额外操作，指标已通过注册表导出
        Ok(())
    }
    
    fn export_histogram(&self, _name: &str, _value: f64, _labels: &HashMap<String, String>) -> Result<(), MetricsError> {
        // Prometheus导出器不需要额外操作，指标已通过注册表导出
        Ok(())
    }
}

// StatsD 导出器
struct StatsdExporter {
    client: statsd::Client,
}

impl StatsdExporter {
    fn new(host: &str, port: u16) -> Result<Self, MetricsError> {
        let addr = format!("{}:{}", host, port);
        let client = statsd::Client::new(addr, "workflow_engine")
            .map_err(|e| MetricsError::ExporterError(format!("StatsD客户端创建失败: {}", e)))?;
            
        Ok(Self { client })
    }
}

impl MetricsExporter for StatsdExporter {
    fn start(&self) -> Result<Option<JoinHandle<()>>, MetricsError> {
        // StatsD导出器不需要启动服务
        Ok(None)
    }
    
    fn export_counter(&self, name: &str, value: u64, labels: &HashMap<String, String>) -> Result<(), MetricsError> {
        let metric_name = Self::build_metric_name(name, labels);
        self.client.incr_by(&metric_name, value)
            .map_err(|e| MetricsError::ExporterError(format!("StatsD导出计数器失败: {}", e)))?;
            
        Ok(())
    }
    
    fn export_gauge(&self, name: &str, value: f64, labels: &HashMap<String, String>) -> Result<(), MetricsError> {
        let metric_name = Self::build_metric_name(name, labels);
        self.client.gauge(&metric_name, value)
            .map_err(|e| MetricsError::ExporterError(format!("StatsD导出仪表盘失败: {}", e)))?;
            
        Ok(())
    }
    
    fn export_histogram(&self, name: &str, value: f64, labels: &HashMap<String, String>) -> Result<(), MetricsError> {
        let metric_name = Self::build_metric_name(name, labels);
        self.client.time(&metric_name, value as u64)
            .map_err(|e| MetricsError::ExporterError(format!("StatsD导出直方图失败: {}", e)))?;
            
        Ok(())
    }
}

impl StatsdExporter {
    // 构建StatsD格式的指标名称
    fn build_metric_name(name: &str, labels: &HashMap<String, String>) -> String {
        if labels.is_empty() {
            return name.to_string();
        }
        
        let labels_str: String = labels.iter()
            .map(|(k, v)| format!("{}.{}", k, v))
            .collect::<Vec<String>>()
            .join(".");
            
        format!("{}.{}", name, labels_str)
    }
}

// Prometheus Pushgateway 导出器
struct PrometheusPushgatewayExporter {
    endpoint: String,
    job_name: String,
    registry: prometheus::Registry,
}

impl PrometheusPushgatewayExporter {
    fn new(endpoint: &str, job_name: &str, registry: prometheus::Registry) -> Result<Self, MetricsError> {
        Ok(Self {
            endpoint: endpoint.to_string(),
            job_name: job_name.to_string(),
            registry,
        })
    }
}

impl MetricsExporter for PrometheusPushgatewayExporter {
    fn start(&self) -> Result<Option<JoinHandle<()>>, MetricsError> {
        // 启动定期推送任务
        let endpoint = self.endpoint.clone();
        let job_name = self.job_name.clone();
        let registry = self.registry.clone();
        
        let handle = tokio::spawn(async move {
            let mut interval = tokio::time::interval(Duration::from_secs(15));
            
            loop {
                interval.tick().await;
                
                // 推送指标到Pushgateway
                if let Err(e) = push_to_pushgateway(&endpoint, &job_name, &registry) {
                    log::error!("向Prometheus Pushgateway推送指标失败: {}", e);
                }
            }
        });
        
        Ok(Some(handle))
    }
    
    fn export_counter(&self, _name: &str, _value: u64, _labels: &HashMap<String, String>) -> Result<(), MetricsError> {
        // Pushgateway导出器不需要额外操作，指标将定期批量推送
        Ok(())
    }
    
    fn export_gauge(&self, _name: &str, _value: f64, _labels: &HashMap<String, String>) -> Result<(), MetricsError> {
        // Pushgateway导出器不需要额外操作，指标将定期批量推送
        Ok(())
    }
    
    fn export_histogram(&self, _name: &str, _value: f64, _labels: &HashMap<String, String>) -> Result<(), MetricsError> {
        // Pushgateway导出器不需要额外操作，指标将定期批量推送
        Ok(())
    }
}

// 向Pushgateway推送指标
fn push_to_pushgateway(endpoint: &str, job_name: &str, registry: &prometheus::Registry) -> Result<(), prometheus::Error> {
    let metric_families = registry.gather();
    let push_endpoint = format!("{}/metrics/job/{}", endpoint, job_name);
    
    let client = reqwest::blocking::Client::new();
    let mut buffer = Vec::new();
    let encoder = prometheus::TextEncoder::new();
    encoder.encode(&metric_families, &mut buffer)?;
    
    client.post(&push_endpoint)
        .header("Content-Type", "text/plain")
        .body(buffer)
        .send()
        .map_err(|e| prometheus::Error::Msg(format!("推送请求失败: {}", e)))?;
        
    Ok(())
}

// 日志导出器
struct LogExporter;

impl LogExporter {
    fn new() -> Self {
        Self
    }
}

impl MetricsExporter for LogExporter {
    fn start(&self) -> Result<Option<JoinHandle<()>>, MetricsError> {
        // 日志导出器不需要启动服务
        Ok(None)
    }
    
    fn export_counter(&self, name: &str, value: u64, labels: &HashMap<String, String>) -> Result<(), MetricsError> {
        let labels_str = Self::format_labels(labels);
        log::info!("指标 | 计数器 | {} | {} | {}", name, value, labels_str);
        Ok(())
    }
    
    fn export_gauge(&self, name: &str, value: f64, labels: &HashMap<String, String>) -> Result<(), MetricsError> {
        let labels_str = Self::format_labels(labels);
        log::info!("指标 | 仪表盘 | {} | {} | {}", name, value, labels_str);
        Ok(())
    }
    
    fn export_histogram(&self, name: &str, value: f64, labels: &HashMap<String, String>) -> Result<(), MetricsError> {
        let labels_str = Self::format_labels(labels);
        log::info!("指标 | 直方图 | {} | {} | {}", name, value, labels_str);
        Ok(())
    }
}

impl LogExporter {
    // 格式化标签为字符串
    fn format_labels(labels: &HashMap<String, String>) -> String {
        if labels.is_empty() {
            return "".to_string();
        }
        
        labels.iter()
            .map(|(k, v)| format!("{}={}", k, v))
            .collect::<Vec<String>>()
            .join(",")
    }
}

// 指标配置
#[derive(Clone, Debug)]
pub struct MetricsConfig {
    pub service_name: String,
    pub exporters: Vec<ExporterConfig>,
    pub collection_interval_seconds: u64,
    pub enable_system_metrics: bool,
}

// 导出器配置
#[derive(Clone, Debug)]
pub struct ExporterConfig {
    pub exporter_type: String,
    pub endpoint: Option<String>,
    pub host: Option<String>,
    pub port: Option<u16>,
}

// 指标错误
#[derive(Debug, thiserror::Error)]
pub enum MetricsError {
    #[error("配置错误: {0}")]
    ConfigError(String),
    
    #[error("导出器错误: {0}")]
    ExporterError(String),
    
    #[error("注册表错误: {0}")]
    RegistryError(#[from] prometheus::Error),
    
    #[error("IO错误: {0}")]
    IoError(#[from] std::io::Error),
}
```

指标收集的优势：

1. **多种导出器支持**：Prometheus、StatsD和日志
2. **系统资源监控**：CPU、内存、磁盘和网络
3. **多种指标类型**：计数器、仪表盘和直方图
4. **标签丰富**：支持多维度标签分类
5. **自动注册**：按需创建和缓存指标
6. **批量推送**：支持Pushgateway批量推送模式

## 14. 系统集成设计

### 14.1 REST API接口

实现与第三方系统集成的REST API：

```rust
#[derive(Clone)]
pub struct WorkflowApiService {
    workflow_service: Arc<WorkflowService>,
    metrics_collector: Arc<MetricsCollector>,
    tracing_system: Arc<TracingSystem>,
    auth_service: Arc<AuthService>,
}

impl WorkflowApiService {
    pub fn new(
        workflow_service: Arc<WorkflowService>,
        metrics_collector: Arc<MetricsCollector>,
        tracing_system: Arc<TracingSystem>,
        auth_service: Arc<AuthService>,
    ) -> Self {
        Self {
            workflow_service,
            metrics_collector,
            tracing_system,
            auth_service,
        }
    }
    
    // 配置API路由
    pub fn configure_routes(
        &self,
        cfg: &mut web::ServiceConfig
    ) {
        let service = self.clone();
        
        cfg.service(
            web::scope("/api/v1")
                // 通用中间件
                .wrap(TracingMiddleware::new(self.tracing_system.clone()))
                .wrap(MetricsMiddleware::new(self.metrics_collector.clone()))
                .wrap(JwtAuthMiddleware::new(self.auth_service.clone()))
                
                // 工作流定义管理
                .service(
                    web::scope("/workflow-definitions")
                        .route("", web::get().to(move |req| service.list_workflow_definitions(req)))
                        .route("", web::post().to(move |req| service.register_workflow_definition(req)))
                        .route("/{id}", web::get().to(move |req| service.get_workflow_definition(req)))
                        .route("/{id}", web::put().to(move |req| service.update_workflow_definition(req)))
                        .route("/{id}", web::delete().to(move |req| service.delete_workflow_definition(req)))
                        .route("/{id}/validate", web::post().to(move |req| service.validate_workflow_definition(req)))
                )
                
                // 工作流实例管理
                .service(
                    web::scope("/workflows")
                        .route("", web::get().to(move |req| service.list_workflow_instances(req)))
                        .route("", web::post().to(move |req| service.start_workflow(req)))
                        .route("/{id}", web::get().to(move |req| service.get_workflow_status(req)))
                        .route("/{id}/cancel", web::post().to(move |req| service.cancel_workflow(req)))
                        .route("/{id}/pause", web::post().to(move |req| service.pause_workflow(req)))
                        .route("/{id}/resume", web::post().to(move |req| service.resume_workflow(req)))
                        .route("/{id}/retry", web::post().to(move |req| service.retry_workflow(req)))
                        .route("/{id}/signal", web::post().to(move |req| service.send_signal_to_workflow(req)))
                        .route("/{id}/tasks", web::get().to(move |req| service.list_workflow_tasks(req)))
                        .route("/{id}/history", web::get().to(move |req| service.get_workflow_history(req)))
                        .route("/{id}/metadata", web::get().to(move |req| service.get_workflow_metadata(req)))
                        .route("/{id}/metadata", web::put().to(move |req| service.update_workflow_metadata(req)))
                )
                
                // 任务管理
                .service(
                    web::scope("/tasks")
                        .route("", web::get().to(move |req| service.list_tasks(req)))
                        .route("/{id}", web::get().to(move |req| service.get_task_status(req)))
                        .route("/{id}/complete", web::post().to(move |req| service.complete_task(req)))
                        .route("/{id}/fail", web::post().to(move |req| service.fail_task(req)))
                        .route("/{id}/claim", web::post().to(move |req| service.claim_task(req)))
                        .route("/{id}/heartbeat", web::post().to(move |req| service.send_task_heartbeat(req)))
                )
                
                // 事件管理
                .service(
                    web::scope("/events")
                        .route("", web::post().to(move |req| service.publish_external_event(req)))
                        .route("/subscriptions", web::post().to(move |req| service.create_event_subscription(req)))
                        .route("/subscriptions/{id}", web::delete().to(move |req| service.delete_event_subscription(req)))
                        .route("/subscriptions", web::get().to(move |req| service.list_event_subscriptions(req)))
                )
                
                // 监控和指标
                .service(
                    web::scope("/metrics")
                        .route("/workflow/{id}", web::get().to(move |req| service.get_workflow_metrics(req)))
                        .route("/tasks", web::get().to(move |req| service.get_task_metrics(req)))
                        .route("/system", web::get().to(move |req| service.get_system_metrics(req)))
                )
                
                // 系统管理
                .service(
                    web::scope("/system")
                        .route("/health", web::get().to(move |req| service.health_check(req)))
                        .route("/nodes", web::get().to(move |req| service.list_nodes(req)))
                        .route("/config", web::get().to(move |req| service.get_system_config(req)))
                        .route("/config", web::put().to(move |req| service.update_system_config(req)))
                )
        );
    }
    
    // ==========工作流定义管理==========
    
    // 列出工作流定义
    async fn list_workflow_definitions(&self, req: HttpRequest) -> HttpResponse {
        let trace_ctx = self.extract_trace_context(&req);
        let query = web::Query::<ListWorkflowDefinitionsQuery>::from_query(req.query_string())
            .unwrap_or_default();
        
        // 提取分页参数
        let page = query.page.unwrap_or(1);
        let per_page = query.per_page.unwrap_or(20).min(100);
        let filter = query.filter.clone().unwrap_or_default();
        
        let result = self.workflow_service.list_workflow_definitions(
            page, 
            per_page, 
            &filter,
            trace_ctx
        ).await;
        
        match result {
            Ok(definitions) => {
                let total = definitions.total;
                let response = PaginatedResponse {
                    data: definitions.items,
                    meta: PaginationMeta {
                        total,
                        page,
                        per_page,
                        total_pages: (total as f64 / per_page as f64).ceil() as u32,
                    },
                };
                
                HttpResponse::Ok().json(response)
            },
            Err(e) => {
                log::error!("获取工作流定义列表失败: {}", e);
                HttpResponse::InternalServerError().json(ErrorResponse {
                    error: "获取工作流定义列表失败".to_string(),
                    message: e.to_string(),
                    code: "WORKFLOW_LIST_ERROR".to_string(),
                })
            }
        }
    }
    
    // 注册工作流定义
    async fn register_workflow_definition(&self, req: HttpRequest, body: web::Json<RegisterWorkflowRequest>) -> HttpResponse {
        let trace_ctx = self.extract_trace_context(&req);
        
        // 提取用户信息用于审计
        let user_id = self.extract_user_id(&req).unwrap_or_else(|| "anonymous".to_string());
        
        log::info!("用户 {} 注册工作流定义 {}", user_id, body.name);
        
        let result = self.workflow_service.register_workflow_definition(
            body.into_inner(),
            user_id,
            trace_ctx
        ).await;
        
        match result {
            Ok(definition_id) => {
                HttpResponse::Created().json(RegisterWorkflowResponse {
                    id: definition_id,
                    message: "工作流定义注册成功".to_string(),
                })
            },
            Err(e) => {
                log::error!("注册工作流定义失败: {}", e);
                
                match e {
                    WorkflowError::ValidationError(message) => {
                        HttpResponse::BadRequest().json(ErrorResponse {
                            error: "工作流定义验证失败".to_string(),
                            message,
                            code: "VALIDATION_ERROR".to_string(),
                        })
                    },
                    WorkflowError::DuplicateError(message) => {
                        HttpResponse::Conflict().json(ErrorResponse {
                            error: "工作流定义已存在".to_string(),
                            message,
                            code: "DUPLICATE_ERROR".to_string(),
                        })
                    },
                    _ => {
                        HttpResponse::InternalServerError().json(ErrorResponse {
                            error: "注册工作流定义失败".to_string(),
                            message: e.to_string(),
                            code: "REGISTRATION_ERROR".to_string(),
                        })
                    }
                }
            }
        }
    }
    
    // 获取工作流定义
    async fn get_workflow_definition(&self, req: HttpRequest) -> HttpResponse {
        let trace_ctx = self.extract_trace_context(&req);
        let path = web::Path::<String>::extract(&req).await.unwrap();
        let definition_id = path.into_inner();
        
        let result = self.workflow_service.get_workflow_definition(&definition_id, trace_ctx).await;
        
        match result {
            Ok(definition) => {
                HttpResponse::Ok().json(definition)
            },
            Err(e) => {
                log::error!("获取工作流定义失败: {}", e);
                
                match e {
                    WorkflowError::NotFoundError(_) => {
                        HttpResponse::NotFound().json(ErrorResponse {
                            error: "工作流定义不存在".to_string(),
                            message: format!("未找到ID为{}的工作流定义", definition_id),
                            code: "NOT_FOUND".to_string(),
                        })
                    },
                    _ => {
                        HttpResponse::InternalServerError().json(ErrorResponse {
                            error: "获取工作流定义失败".to_string(),
                            message: e.to_string(),
                            code: "FETCH_ERROR".to_string(),
                        })
                    }
                }
            }
        }
    }
    
    // 更新工作流定义
    async fn update_workflow_definition(&self, req: HttpRequest, body: web::Json<UpdateWorkflowRequest>) -> HttpResponse {
        let trace_ctx = self.extract_trace_context(&req);
        let path = web::Path::<String>::extract(&req).await.unwrap();
        let definition_id = path.into_inner();
        
        // 提取用户信息用于审计
        let user_id = self.extract_user_id(&req).unwrap_or_else(|| "anonymous".to_string());
        
        log::info!("用户 {} 更新工作流定义 {}", user_id, definition_id);
        
        let mut request = body.into_inner();
        request.id = definition_id.clone();
        
        let result = self.workflow_service.update_workflow_definition(request, user_id, trace_ctx).await;
        
        match result {
            Ok(_) => {
                HttpResponse::Ok().json(UpdateWorkflowResponse {
                    id: definition_id,
                    message: "工作流定义更新成功".to_string(),
                })
            },
            Err(e) => {
                log::error!("更新工作流定义失败: {}", e);
                
                match e {
                    WorkflowError::ValidationError(message) => {
                        HttpResponse::BadRequest().json(ErrorResponse {
                            error: "工作流定义验证失败".to_string(),
                            message,
                            code: "VALIDATION_ERROR".to_string(),
                        })
                    },
                    WorkflowError::NotFoundError(_) => {
                        HttpResponse::NotFound().json(ErrorResponse {
                            error: "工作流定义不存在".to_string(),
                            message: format!("未找到ID为{}的工作流定义", definition_id),
                            code: "NOT_FOUND".to_string(),
                        })
                    },
                    WorkflowError::VersionConflictError(message) => {
                        HttpResponse::Conflict().json(ErrorResponse {
                            error: "工作流定义版本冲突".to_string(),
                            message,
                            code: "VERSION_CONFLICT".to_string(),
                        })
                    },
                    _ => {
                        HttpResponse::InternalServerError().json(ErrorResponse {
                            error: "更新工作流定义失败".to_string(),
                            message: e.to_string(),
                            code: "UPDATE_ERROR".to_string(),
                        })
                    }
                }
            }
        }
    }
    
    // 删除工作流定义
    async fn delete_workflow_definition(&self, req: HttpRequest) -> HttpResponse {
        let trace_ctx = self.extract_trace_context(&req);
        let path = web::Path::<String>::extract(&req).await.unwrap();
        let definition_id = path.into_inner();
        
        // 提取用户信息用于审计
        let user_id = self.extract_user_id(&req).unwrap_or_else(|| "anonymous".to_string());
        
        log::info!("用户 {} 删除工作流定义 {}", user_id, definition_id);
        
        let result = self.workflow_service.delete_workflow_definition(&definition_id, user_id, trace_ctx).await;
        
        match result {
            Ok(_) => {
                HttpResponse::Ok().json(DeleteWorkflowResponse {
                    id: definition_id,
                    message: "工作流定义删除成功".to_string(),
                })
            },
            Err(e) => {
                log::error!("删除工作流定义失败: {}", e);
                
                match e {
                    WorkflowError::NotFoundError(_) => {
                        HttpResponse::NotFound().json(ErrorResponse {
                            error: "工作流定义不存在".to_string(),
                            message: format!("未找到ID为{}的工作流定义", definition_id),
                            code: "NOT_FOUND".to_string(),
                        })
                    },
                    WorkflowError::DependencyError(message) => {
                        HttpResponse::Conflict().json(ErrorResponse {
                            error: "工作流定义存在依赖".to_string(),
                            message,
                            code: "DEPENDENCY_ERROR".to_string(),
                        })
                    },
                    _ => {
                        HttpResponse::InternalServerError().json(ErrorResponse {
                            error: "删除工作流定义失败".to_string(),
                            message: e.to_string(),
                            code: "DELETE_ERROR".to_string(),
                        })
                    }
                }
            }
        }
    }
    
    // 验证工作流定义
    async fn validate_workflow_definition(&self, req: HttpRequest, body: web::Json<ValidateWorkflowRequest>) -> HttpResponse {
        let trace_ctx = self.extract_trace_context(&req);
        
        let result = self.workflow_service.validate_workflow_definition(body.into_inner(), trace_ctx).await;
        
        match result {
            Ok(validation_result) => {
                HttpResponse::Ok().json(validation_result)
            },
            Err(e) => {
                log::error!("验证工作流定义失败: {}", e);
                
                HttpResponse::InternalServerError().json(ErrorResponse {
                    error: "验证工作流定义失败".to_string(),
                    message: e.to_string(),
                    code: "VALIDATION_ERROR".to_string(),
                })
            }
        }
    }
    
    // ==========工作流实例管理==========
    
    // 列出工作流实例
    async fn list_workflow_instances(&self, req: HttpRequest) -> HttpResponse {
        let trace_ctx = self.extract_trace_context(&req);
        let query = web::Query::<ListWorkflowInstancesQuery>::from_query(req.query_string())
            .unwrap_or_default();
        
        // 提取查询参数
        let page = query.page.unwrap_or(1);
        let per_page = query.per_page.unwrap_or(20).min(100);
        let status = query.status.clone();
        let definition_id = query.definition_id.clone();
        let start_date = query.start_date.clone();
        let end_date = query.end_date.clone();
        
        let result = self.workflow_service.list_workflow_instances(
            page,
            per_page,
            status.as_deref(),
            definition_id.as_deref(),
            start_date.as_deref(),
            end_date.as_deref(),
            trace_ctx
        ).await;
        
        match result {
            Ok(instances) => {
                let total = instances.total;
                let response = PaginatedResponse {
                    data: instances.items,
                    meta: PaginationMeta {
                        total,
                        page,
                        per_page,
                        total_pages: (total as f64 / per_page as f64).ceil() as u32,
                    },
                };
                
                HttpResponse::Ok().json(response)
            },
            Err(e) => {
                log::error!("获取工作流实例列表失败: {}", e);
                
                HttpResponse::InternalServerError().json(ErrorResponse {
                    error: "获取工作流实例列表失败".to_string(),
                    message: e.to_string(),
                    code: "WORKFLOW_LIST_ERROR".to_string(),
                })
            }
        }
    }
    
    // 启动工作流
    async fn start_workflow(&self, req: HttpRequest, body: web::Json<StartWorkflowRequest>) -> HttpResponse {
        let trace_ctx = self.extract_trace_context(&req);
        
        // 提取用户信息用于审计
        let user_id = self.extract_user_id(&req).unwrap_or_else(|| "anonymous".to_string());
        
        log::info!("用户 {} 启动工作流 {}", user_id, body.definition_id);
        
        let mut request = body.into_inner();
        request.initiated_by = Some(user_id);
        
        let result = self.workflow_service.start_workflow(request, trace_ctx).await;
        
        match result {
            Ok(instance) => {
                HttpResponse::Created().json(StartWorkflowResponse {
                    workflow_id: instance.id,
                    message: "工作流启动成功".to_string(),
                })
            },
            Err(e) => {
                log::error!("启动工作流失败: {}", e);
                
                match e {
                    WorkflowError::ValidationError(message) => {
                        HttpResponse::BadRequest().json(ErrorResponse {
                            error: "工作流启动参数验证失败".to_string(),
                            message,
                            code: "VALIDATION_ERROR".to_string(),
                        })
                    },
                    WorkflowError::NotFoundError(message) => {
                        HttpResponse::NotFound().json(ErrorResponse {
                            error: "工作流定义不存在".to_string(),
                            message,
                            code: "NOT_FOUND".to_string(),
                        })
                    },
                    _ => {
                        HttpResponse::InternalServerError().json(ErrorResponse {
                            error: "启动工作流失败".to_string(),
                            message: e.to_string(),
                            code: "START_ERROR".to_string(),
                        })
                    }
                }
            }
        }
    }
    
    // 获取工作流状态
    async fn get_workflow_status(&self, req: HttpRequest) -> HttpResponse {
        let trace_ctx = self.extract_trace_context(&req);
        let path = web::Path::<String>::extract(&req).await.unwrap();
        let workflow_id = path.into_inner();
        
        // 检查是否需要包含详细信息
        let query = web::Query::<GetWorkflowStatusQuery>::from_query(req.query_string())
            .unwrap_or_default();
        let include_tasks = query.include_tasks.unwrap_or(false);
        let include_variables = query.include_variables.unwrap_or(false);
        
        let result = self.workflow_service.get_workflow_status(
            &workflow_id,
            include_tasks,
            include_variables,
            trace_ctx
        ).await;
        
        match result {
            Ok(status) => {
                HttpResponse::Ok().json(status)
            },
            Err(e) => {
                log::error!("获取工作流状态失败: {}", e);
                
                match e {
                    WorkflowError::NotFoundError(_) => {
                        HttpResponse::NotFound().json(ErrorResponse {
                            error: "工作流实例不存在".to_string(),
                            message: format!("未找到ID为{}的工作流实例", workflow_id),
                            code: "NOT_FOUND".to_string(),
                        })
                    },
                    _ => {
                        HttpResponse::InternalServerError().json(ErrorResponse {
                            error: "获取工作流状态失败".to_string(),
                            message: e.to_string(),
                            code: "STATUS_ERROR".to_string(),
                        })
                    }
                }
            }
        }
    }
    
    // 取消工作流
    async fn cancel_workflow(&self, req: HttpRequest, body: web::Json<CancelWorkflowRequest>) -> HttpResponse {
        let trace_ctx = self.extract_trace_context(&req);
        let path = web::Path::<String>::extract(&req).await.unwrap();
        let workflow_id = path.into_inner();
        
        // 提取用户信息用于审计
        let user_id = self.extract_user_id(&req).unwrap_or_else(|| "anonymous".to_string());
        
        log::info!("用户 {} 取消工作流 {}", user_id, workflow_id);
        
        let mut request = body.into_inner();
        request.workflow_id = workflow_id.clone();
        request.cancelled_by = Some(user_id);
        
        let result = self.workflow_service.cancel_workflow(request, trace_ctx).await;
        
        match result {
            Ok(_) => {
                HttpResponse::Ok().json(CancelWorkflowResponse {
                    workflow_id,
                    message: "工作流取消成功".to_string(),
                })
            },
            Err(e) => {
                log::error!("取消工作流失败: {}", e);
                
                match e {
                    WorkflowError::NotFoundError(_) => {
                        HttpResponse::NotFound().json(ErrorResponse {
                            error: "工作流实例不存在".to_string(),
                            message: format!("未找到ID为{}的工作流实例", workflow_id),
                            code: "NOT_FOUND".to_string(),
                        })
                    },
                    WorkflowError::InvalidStateError(message) => {
                        HttpResponse::BadRequest().json(ErrorResponse {
                            error: "工作流状态不允许取消".to_string(),
                            message,
                            code: "INVALID_STATE".to_string(),
                        })
                    },
                    _ => {
                        HttpResponse::InternalServerError().json(ErrorResponse {
                            error: "取消工作流失败".to_string(),
                            message: e.to_string(),
                            code: "CANCEL_ERROR".to_string(),
                        })
                    }
                }
            }
        }
    }
    
    // 暂停工作流
    async fn pause_workflow(&self, req: HttpRequest, body: web::Json<PauseWorkflowRequest>) -> HttpResponse {
        let trace_ctx = self.extract_trace_context(&req);
        let path = web::Path::<String>::extract(&req).await.unwrap();
        let workflow_id = path.into_inner();
        
        // 提取用户信息用于审计
        let user_id = self.extract_user_id(&req).unwrap_or_else(|| "anonymous".to_string());
        
        log::info!("用户 {} 暂停工作流 {}", user_id, workflow_id);
        
        let mut request = body.into_inner();
        request.workflow_id = workflow_id.clone();
        request.paused_by = Some(user_id);
        
        let result = self.workflow_service.pause_workflow(request, trace_ctx).await;
        
        match result {
            Ok(_) => {
                HttpResponse::Ok().json(PauseWorkflowResponse {
                    workflow_id,
                    message: "工作流暂停成功".to_string(),
                })
            },
            Err(e) => {
                log::error!("暂停工作流失败: {}", e);
                
                match e {
                    WorkflowError::NotFoundError(_) => {
                        HttpResponse::NotFound().json(ErrorResponse {
                            error: "工作流实例不存在".to_string(),
                            message: format!("未找到ID为{}的工作流实例", workflow_id),
                            code: "NOT_FOUND".to_string(),
                        })
                    },
                    WorkflowError::InvalidStateError(message) => {
                        HttpResponse::BadRequest().json(ErrorResponse {
                            error: "工作流状态不允许暂停".to_string(),
                            message,
                            code: "INVALID_STATE".to_string(),
                        })
                    },
                    _ => {
                        HttpResponse::InternalServerError().json(ErrorResponse {
                            error: "暂停工作流失败".to_string(),
                            message: e.to_string(),
                            code: "PAUSE_ERROR".to_string(),
                        })
                    }
                }
            }
        }
    }
    
    // 恢复工作流
    async fn resume_workflow(&self, req: HttpRequest, body: web::Json<ResumeWorkflowRequest>) -> HttpResponse {
        let trace_ctx = self.extract_trace_context(&req);
        let path = web::Path::<String>::extract(&req).await.unwrap();
        let workflow_id = path.into_inner();
        
        // 提取用户信息用于审计
        let user_id = self.extract_user_id(&req).unwrap_or_else(|| "anonymous".to_string());
        
        log::info!("用户 {} 恢复工作流 {}", user_id, workflow_id);
        
        let mut request = body.into_inner();
        request.workflow_id = workflow_id.clone();
        request.resumed_by = Some(user_id);
        
        let result = self.workflow_service.resume_workflow(request, trace_ctx).await;
        
        match result {
            Ok(_) => {
                HttpResponse::Ok().json(ResumeWorkflowResponse {
                    workflow_id,
                    message: "工作流恢复成功".to_string(),
                })
            },
            Err(e) => {
                log::error!("恢复工作流失败: {}", e);
                
                match e {
                    WorkflowError::NotFoundError(_) => {
                        HttpResponse::NotFound().json(ErrorResponse {
                            error: "工作流实例不存在".to_string(),
                            message: format!("未找到ID为{}的工作流实例", workflow_id),
                            code: "NOT_FOUND".to_string(),
                        })
                    },
                    WorkflowError::InvalidStateError(message) => {
                        HttpResponse::BadRequest().json(ErrorResponse {
                            error: "工作流状态不允许恢复".to_string(),
                            message,
                            code: "INVALID_STATE".to_string(),
                        })
                    },
                    _ => {
                        HttpResponse::InternalServerError().json(ErrorResponse {
                            error: "恢复工作流失败".to_string(),
                            message: e.to_string(),
                            code: "RESUME_ERROR".to_string(),
                        })
                    }
                }
            }
        }
    }
    
    // 重试工作流
    async fn retry_workflow(&self, req: HttpRequest, body: web::Json<RetryWorkflowRequest>) -> HttpResponse {
        let trace_ctx = self.extract_trace_context(&req);
        let path = web::Path::<String>::extract(&req).await.unwrap();
        let workflow_id = path.into_inner();
        
        // 提取用户信息用于审计
        let user_id = self.extract_user_id(&req).unwrap_or_else(|| "anonymous".to_string());
        
        log::info!("用户 {} 重试工作流 {}", user_id, workflow_id);
        
        let mut request = body.into_inner();
        request.workflow_id = workflow_id.clone();
        request.retried_by = Some(user_id);
        
        let result = self.workflow_service.retry_workflow(request, trace_ctx).await;
        
        match result {
            Ok(_) => {
                HttpResponse::Ok().json(RetryWorkflowResponse {
                    workflow_id,
                    message: "工作流重试成功".to_string(),
                })
            },
            Err(e) => {
                log::error!("重试工作流失败: {}", e);
                
                match e {
                    WorkflowError::NotFoundError(_) => {
                        HttpResponse::NotFound().json(ErrorResponse {
                            error: "工作流实例不存在".to_string(),
                            message: format!("未找到ID为{}的工作流实例", workflow_id),
                            code: "NOT_FOUND".to_string(),
                        })
                    },
                    WorkflowError::InvalidStateError(message) => {
                        HttpResponse::BadRequest().json(ErrorResponse {
                            error: "工作流状态不允许重试".to_string(),
                            message,
                            code: "INVALID_STATE".to_string(),
                        })
                    },
                    _ => {
                        HttpResponse::InternalServerError().json(ErrorResponse {
                            error: "重试工作流失败".to_string(),
                            message: e.to_string(),
                            code: "RETRY_ERROR".to_string(),
                        })
                    }
                }
            }
        }
    }

// 向工作流发送信号
async fn send_signal_to_workflow(&self, req: HttpRequest, body: web::Json<WorkflowSignalRequest>) -> HttpResponse {
    let trace_ctx = self.extract_trace_context(&req);
    let path = web::Path::<String>::extract(&req).await.unwrap();
    let workflow_id = path.into_inner();
    
    // 提取用户信息用于审计
    let user_id = self.extract_user_id(&req).unwrap_or_else(|| "anonymous".to_string());
    
    log::info!("用户 {} 向工作流 {} 发送信号 {}", 
        user_id, workflow_id, body.signal_name);
    
    let mut request = body.into_inner();
    request.workflow_id = workflow_id.clone();
    request.signaled_by = Some(user_id);
    
    let result = self.workflow_service.send_signal(request, trace_ctx).await;
    
    match result {
        Ok(_) => {
            HttpResponse::Ok().json(WorkflowSignalResponse {
                workflow_id,
                message: "信号发送成功".to_string(),
            })
        },
        Err(e) => {
            log::error!("发送工作流信号失败: {}", e);
            
            match e {
                WorkflowError::NotFoundError(_) => {
                    HttpResponse::NotFound().json(ErrorResponse {
                        error: "工作流实例不存在".to_string(),
                        message: format!("未找到ID为{}的工作流实例", workflow_id),
                        code: "NOT_FOUND".to_string(),
                    })
                },
                WorkflowError::SignalError(message) => {
                    HttpResponse::BadRequest().json(ErrorResponse {
                        error: "信号处理错误".to_string(),
                        message,
                        code: "SIGNAL_ERROR".to_string(),
                    })
                },
                _ => {
                    HttpResponse::InternalServerError().json(ErrorResponse {
                        error: "发送工作流信号失败".to_string(),
                        message: e.to_string(),
                        code: "SIGNAL_ERROR".to_string(),
                    })
                }
            }
        }
    }
}

// 列出工作流任务
async fn list_workflow_tasks(&self, req: HttpRequest) -> HttpResponse {
    let trace_ctx = self.extract_trace_context(&req);
    let path = web::Path::<String>::extract(&req).await.unwrap();
    let workflow_id = path.into_inner();
    
    // 提取查询参数
    let query = web::Query::<ListWorkflowTasksQuery>::from_query(req.query_string())
        .unwrap_or_default();
    
    let result = self.workflow_service.list_workflow_tasks(
        &workflow_id,
        query.status.as_deref(),
        query.task_type.as_deref(),
        trace_ctx
    ).await;
    
    match result {
        Ok(tasks) => {
            HttpResponse::Ok().json(tasks)
        },
        Err(e) => {
            log::error!("获取工作流任务列表失败: {}", e);
            
            match e {
                WorkflowError::NotFoundError(_) => {
                    HttpResponse::NotFound().json(ErrorResponse {
                        error: "工作流实例不存在".to_string(),
                        message: format!("未找到ID为{}的工作流实例", workflow_id),
                        code: "NOT_FOUND".to_string(),
                    })
                },
                _ => {
                    HttpResponse::InternalServerError().json(ErrorResponse {
                        error: "获取工作流任务列表失败".to_string(),
                        message: e.to_string(),
                        code: "TASK_LIST_ERROR".to_string(),
                    })
                }
            }
        }
    }
}

// 获取工作流历史
async fn get_workflow_history(&self, req: HttpRequest) -> HttpResponse {
    let trace_ctx = self.extract_trace_context(&req);
    let path = web::Path::<String>::extract(&req).await.unwrap();
    let workflow_id = path.into_inner();
    
    let result = self.workflow_service.get_workflow_history(&workflow_id, trace_ctx).await;
    
    match result {
        Ok(history) => {
            HttpResponse::Ok().json(history)
        },
        Err(e) => {
            log::error!("获取工作流历史失败: {}", e);
            
            match e {
                WorkflowError::NotFoundError(_) => {
                    HttpResponse::NotFound().json(ErrorResponse {
                        error: "工作流实例不存在".to_string(),
                        message: format!("未找到ID为{}的工作流实例", workflow_id),
                        code: "NOT_FOUND".to_string(),
                    })
                },
                _ => {
                    HttpResponse::InternalServerError().json(ErrorResponse {
                        error: "获取工作流历史失败".to_string(),
                        message: e.to_string(),
                        code: "HISTORY_ERROR".to_string(),
                    })
                }
            }
        }
    }
}

// 获取工作流元数据
async fn get_workflow_metadata(&self, req: HttpRequest) -> HttpResponse {
    let trace_ctx = self.extract_trace_context(&req);
    let path = web::Path::<String>::extract(&req).await.unwrap();
    let workflow_id = path.into_inner();
    
    let result = self.workflow_service.get_workflow_metadata(&workflow_id, trace_ctx).await;
    
    match result {
        Ok(metadata) => {
            HttpResponse::Ok().json(metadata)
        },
        Err(e) => {
            log::error!("获取工作流元数据失败: {}", e);
            
            match e {
                WorkflowError::NotFoundError(_) => {
                    HttpResponse::NotFound().json(ErrorResponse {
                        error: "工作流实例不存在".to_string(),
                        message: format!("未找到ID为{}的工作流实例", workflow_id),
                        code: "NOT_FOUND".to_string(),
                    })
                },
                _ => {
                    HttpResponse::InternalServerError().json(ErrorResponse {
                        error: "获取工作流元数据失败".to_string(),
                        message: e.to_string(),
                        code: "METADATA_ERROR".to_string(),
                    })
                }
            }
        }
    }
}

// 更新工作流元数据
async fn update_workflow_metadata(&self, req: HttpRequest, body: web::Json<UpdateMetadataRequest>) -> HttpResponse {
    let trace_ctx = self.extract_trace_context(&req);
    let path = web::Path::<String>::extract(&req).await.unwrap();
    let workflow_id = path.into_inner();
    
    // 提取用户信息用于审计
    let user_id = self.extract_user_id(&req).unwrap_or_else(|| "anonymous".to_string());
    
    log::info!("用户 {} 更新工作流 {} 元数据", user_id, workflow_id);
    
    let mut request = body.into_inner();
    request.workflow_id = workflow_id.clone();
    request.updated_by = Some(user_id);
    
    let result = self.workflow_service.update_workflow_metadata(request, trace_ctx).await;
    
    match result {
        Ok(_) => {
            HttpResponse::Ok().json(UpdateMetadataResponse {
                workflow_id,
                message: "工作流元数据更新成功".to_string(),
            })
        },
        Err(e) => {
            log::error!("更新工作流元数据失败: {}", e);
            
            match e {
                WorkflowError::NotFoundError(_) => {
                    HttpResponse::NotFound().json(ErrorResponse {
                        error: "工作流实例不存在".to_string(),
                        message: format!("未找到ID为{}的工作流实例", workflow_id),
                        code: "NOT_FOUND".to_string(),
                    })
                },
                WorkflowError::ValidationError(message) => {
                    HttpResponse::BadRequest().json(ErrorResponse {
                        error: "元数据验证失败".to_string(),
                        message,
                        code: "VALIDATION_ERROR".to_string(),
                    })
                },
                _ => {
                    HttpResponse::InternalServerError().json(ErrorResponse {
                        error: "更新工作流元数据失败".to_string(),
                        message: e.to_string(),
                        code: "METADATA_UPDATE_ERROR".to_string(),
                    })
                }
            }
        }
    }
}

// ==========任务管理==========

// 列出任务
async fn list_tasks(&self, req: HttpRequest) -> HttpResponse {
    let trace_ctx = self.extract_trace_context(&req);
    let query = web::Query::<ListTasksQuery>::from_query(req.query_string())
        .unwrap_or_default();
    
    // 提取查询参数
    let page = query.page.unwrap_or(1);
    let per_page = query.per_page.unwrap_or(20).min(100);
    let status = query.status.clone();
    let task_type = query.task_type.clone();
    let assignee = query.assignee.clone();
    
    let result = self.workflow_service.list_tasks(
        page,
        per_page,
        status.as_deref(),
        task_type.as_deref(),
        assignee.as_deref(),
        trace_ctx
    ).await;
    
    match result {
        Ok(tasks) => {
            let total = tasks.total;
            let response = PaginatedResponse {
                data: tasks.items,
                meta: PaginationMeta {
                    total,
                    page,
                    per_page,
                    total_pages: (total as f64 / per_page as f64).ceil() as u32,
                },
            };
            
            HttpResponse::Ok().json(response)
        },
        Err(e) => {
            log::error!("获取任务列表失败: {}", e);
            
            HttpResponse::InternalServerError().json(ErrorResponse {
                error: "获取任务列表失败".to_string(),
                message: e.to_string(),
                code: "TASK_LIST_ERROR".to_string(),
            })
        }
    }
}

// 获取任务状态
async fn get_task_status(&self, req: HttpRequest) -> HttpResponse {
    let trace_ctx = self.extract_trace_context(&req);
    let path = web::Path::<String>::extract(&req).await.unwrap();
    let task_id = path.into_inner();
    
    let result = self.workflow_service.get_task_status(&task_id, trace_ctx).await;
    
    match result {
        Ok(task) => {
            HttpResponse::Ok().json(task)
        },
        Err(e) => {
            log::error!("获取任务状态失败: {}", e);
            
            match e {
                WorkflowError::NotFoundError(_) => {
                    HttpResponse::NotFound().json(ErrorResponse {
                        error: "任务不存在".to_string(),
                        message: format!("未找到ID为{}的任务", task_id),
                        code: "NOT_FOUND".to_string(),
                    })
                },
                _ => {
                    HttpResponse::InternalServerError().json(ErrorResponse {
                        error: "获取任务状态失败".to_string(),
                        message: e.to_string(),
                        code: "TASK_STATUS_ERROR".to_string(),
                    })
                }
            }
        }
    }
}

// 完成任务
async fn complete_task(&self, req: HttpRequest, body: web::Json<CompleteTaskRequest>) -> HttpResponse {
    let trace_ctx = self.extract_trace_context(&req);
    let path = web::Path::<String>::extract(&req).await.unwrap();
    let task_id = path.into_inner();
    
    // 提取用户信息用于审计
    let user_id = self.extract_user_id(&req).unwrap_or_else(|| "anonymous".to_string());
    
    log::info!("用户 {} 完成任务 {}", user_id, task_id);
    
    let mut request = body.into_inner();
    request.task_id = task_id.clone();
    request.completed_by = Some(user_id);
    
    let result = self.workflow_service.complete_task(request, trace_ctx).await;
    
    match result {
        Ok(_) => {
            HttpResponse::Ok().json(CompleteTaskResponse {
                task_id,
                message: "任务完成成功".to_string(),
            })
        },
        Err(e) => {
            log::error!("完成任务失败: {}", e);
            
            match e {
                WorkflowError::NotFoundError(_) => {
                    HttpResponse::NotFound().json(ErrorResponse {
                        error: "任务不存在".to_string(),
                        message: format!("未找到ID为{}的任务", task_id),
                        code: "NOT_FOUND".to_string(),
                    })
                },
                WorkflowError::InvalidStateError(message) => {
                    HttpResponse::BadRequest().json(ErrorResponse {
                        error: "任务状态不允许完成".to_string(),
                        message,
                        code: "INVALID_STATE".to_string(),
                    })
                },
                WorkflowError::ValidationError(message) => {
                    HttpResponse::BadRequest().json(ErrorResponse {
                        error: "输出数据验证失败".to_string(),
                        message,
                        code: "VALIDATION_ERROR".to_string(),
                    })
                },
                _ => {
                    HttpResponse::InternalServerError().json(ErrorResponse {
                        error: "完成任务失败".to_string(),
                        message: e.to_string(),
                        code: "TASK_COMPLETE_ERROR".to_string(),
                    })
                }
            }
        }
    }
}

// 任务失败
async fn fail_task(&self, req: HttpRequest, body: web::Json<FailTaskRequest>) -> HttpResponse {
    let trace_ctx = self.extract_trace_context(&req);
    let path = web::Path::<String>::extract(&req).await.unwrap();
    let task_id = path.into_inner();
    
    // 提取用户信息用于审计
    let user_id = self.extract_user_id(&req).unwrap_or_else(|| "anonymous".to_string());
    
    log::info!("用户 {} 标记任务 {} 失败", user_id, task_id);
    
    let mut request = body.into_inner();
    request.task_id = task_id.clone();
    request.failed_by = Some(user_id);
    
    let result = self.workflow_service.fail_task(request, trace_ctx).await;
    
    match result {
        Ok(_) => {
            HttpResponse::Ok().json(FailTaskResponse {
                task_id,
                message: "任务标记失败成功".to_string(),
            })
        },
        Err(e) => {
            log::error!("标记任务失败出错: {}", e);
            
            match e {
                WorkflowError::NotFoundError(_) => {
                    HttpResponse::NotFound().json(ErrorResponse {
                        error: "任务不存在".to_string(),
                        message: format!("未找到ID为{}的任务", task_id),
                        code: "NOT_FOUND".to_string(),
                    })
                },
                WorkflowError::InvalidStateError(message) => {
                    HttpResponse::BadRequest().json(ErrorResponse {
                        error: "任务状态不允许标记失败".to_string(),
                        message,
                        code: "INVALID_STATE".to_string(),
                    })
                },
                _ => {
                    HttpResponse::InternalServerError().json(ErrorResponse {
                        error: "标记任务失败出错".to_string(),
                        message: e.to_string(),
                        code: "TASK_FAIL_ERROR".to_string(),
                    })
                }
            }
        }
    }
}

// 认领任务
async fn claim_task(&self, req: HttpRequest, body: web::Json<ClaimTaskRequest>) -> HttpResponse {
    let trace_ctx = self.extract_trace_context(&req);
    let path = web::Path::<String>::extract(&req).await.unwrap();
    let task_id = path.into_inner();
    
    // 提取用户信息用于审计
    let user_id = self.extract_user_id(&req).unwrap_or_else(|| "anonymous".to_string());
    
    log::info!("用户 {} 认领任务 {}", user_id, task_id);
    
    let mut request = body.into_inner();
    request.task_id = task_id.clone();
    
    // 如果未指定认领者，则使用当前用户
    if request.assignee.is_none() {
        request.assignee = Some(user_id);
    }
    
    let result = self.workflow_service.claim_task(request, trace_ctx).await;
    
    match result {
        Ok(_) => {
            HttpResponse::Ok().json(ClaimTaskResponse {
                task_id,
                message: "任务认领成功".to_string(),
            })
        },
        Err(e) => {
            log::error!("认领任务失败: {}", e);
            
            match e {
                WorkflowError::NotFoundError(_) => {
                    HttpResponse::NotFound().json(ErrorResponse {
                        error: "任务不存在".to_string(),
                        message: format!("未找到ID为{}的任务", task_id),
                        code: "NOT_FOUND".to_string(),
                    })
                },
                WorkflowError::InvalidStateError(message) => {
                    HttpResponse::BadRequest().json(ErrorResponse {
                        error: "任务状态不允许认领".to_string(),
                        message,
                        code: "INVALID_STATE".to_string(),
                    })
                },
                WorkflowError::AuthorizationError(message) => {
                    HttpResponse::Forbidden().json(ErrorResponse {
                        error: "无权认领任务".to_string(),
                        message,
                        code: "UNAUTHORIZED".to_string(),
                    })
                },
                _ => {
                    HttpResponse::InternalServerError().json(ErrorResponse {
                        error: "认领任务失败".to_string(),
                        message: e.to_string(),
                        code: "TASK_CLAIM_ERROR".to_string(),
                    })
                }
            }
        }
    }
}

// 发送任务心跳
async fn send_task_heartbeat(&self, req: HttpRequest, body: web::Json<TaskHeartbeatRequest>) -> HttpResponse {
    let trace_ctx = self.extract_trace_context(&req);
    let path = web::Path::<String>::extract(&req).await.unwrap();
    let task_id = path.into_inner();
    
    let mut request = body.into_inner();
    request.task_id = task_id.clone();
    
    let result = self.workflow_service.send_task_heartbeat(request, trace_ctx).await;
    
    match result {
        Ok(_) => {
            HttpResponse::Ok().json(TaskHeartbeatResponse {
                task_id,
                message: "任务心跳发送成功".to_string(),
            })
        },
        Err(e) => {
            log::error!("发送任务心跳失败: {}", e);
            
            match e {
                WorkflowError::NotFoundError(_) => {
                    HttpResponse::NotFound().json(ErrorResponse {
                        error: "任务不存在".to_string(),
                        message: format!("未找到ID为{}的任务", task_id),
                        code: "NOT_FOUND".to_string(),
                    })
                },
                WorkflowError::InvalidStateError(message) => {
                    HttpResponse::BadRequest().json(ErrorResponse {
                        error: "任务状态不允许发送心跳".to_string(),
                        message,
                        code: "INVALID_STATE".to_string(),
                    })
                },
                _ => {
                    HttpResponse::InternalServerError().json(ErrorResponse {
                        error: "发送任务心跳失败".to_string(),
                        message: e.to_string(),
                        code: "HEARTBEAT_ERROR".to_string(),
                    })
                }
            }
        }
    }
}

// ==========事件管理==========

// 发布外部事件
async fn publish_external_event(&self, req: HttpRequest, body: web::Json<PublishEventRequest>) -> HttpResponse {
    let trace_ctx = self.extract_trace_context(&req);
    
    // 提取用户信息用于审计
    let user_id = self.extract_user_id(&req).unwrap_or_else(|| "anonymous".to_string());
    
    log::info!("用户 {} 发布事件 {}", user_id, body.event_type);
    
    let mut request = body.into_inner();
    request.published_by = Some(user_id);
    
    let result = self.workflow_service.publish_external_event(request, trace_ctx).await;
    
    match result {
        Ok(event_id) => {
            HttpResponse::Created().json(PublishEventResponse {
                event_id,
                message: "事件发布成功".to_string(),
            })
        },
        Err(e) => {
            log::error!("发布事件失败: {}", e);
            
            match e {
                WorkflowError::ValidationError(message) => {
                    HttpResponse::BadRequest().json(ErrorResponse {
                        error: "事件验证失败".to_string(),
                        message,
                        code: "VALIDATION_ERROR".to_string(),
                    })
                },
                _ => {
                    HttpResponse::InternalServerError().json(ErrorResponse {
                        error: "发布事件失败".to_string(),
                        message: e.to_string(),
                        code: "EVENT_PUBLISH_ERROR".to_string(),
                    })
                }
            }
        }
    }
}

// 创建事件订阅
async fn create_event_subscription(&self, req: HttpRequest, body: web::Json<CreateSubscriptionRequest>) -> HttpResponse {
    let trace_ctx = self.extract_trace_context(&req);
    
    // 提取用户信息用于审计
    let user_id = self.extract_user_id(&req).unwrap_or_else(|| "anonymous".to_string());
    
    log::info!("用户 {} 创建事件订阅", user_id);
    
    let mut request = body.into_inner();
    request.created_by = Some(user_id);
    
    let result = self.workflow_service.create_event_subscription(request, trace_ctx).await;
    
    match result {
        Ok(subscription_id) => {
            HttpResponse::Created().json(CreateSubscriptionResponse {
                subscription_id,
                message: "事件订阅创建成功".to_string(),
            })
        },
        Err(e) => {
            log::error!("创建事件订阅失败: {}", e);
            
            match e {
                WorkflowError::ValidationError(message) => {
                    HttpResponse::BadRequest().json(ErrorResponse {
                        error: "订阅参数验证失败".to_string(),
                        message,
                        code: "VALIDATION_ERROR".to_string(),
                    })
                },
                WorkflowError::DuplicateError(message) => {
                    HttpResponse::Conflict().json(ErrorResponse {
                        error: "订阅已存在".to_string(),
                        message,
                        code: "DUPLICATE_ERROR".to_string(),
                    })
                },
                _ => {
                    HttpResponse::InternalServerError().json(ErrorResponse {
                        error: "创建事件订阅失败".to_string(),
                        message: e.to_string(),
                        code: "SUBSCRIPTION_CREATE_ERROR".to_string(),
                    })
                }
            }
        }
    }
}

// 删除事件订阅
async fn delete_event_subscription(&self, req: HttpRequest) -> HttpResponse {
    let trace_ctx = self.extract_trace_context(&req);
    let path = web::Path::<String>::extract(&req).await.unwrap();
    let subscription_id = path.into_inner();
    
    // 提取用户信息用于审计
    let user_id = self.extract_user_id(&req).unwrap_or_else(|| "anonymous".to_string());
    
    log::info!("用户 {} 删除事件订阅 {}", user_id, subscription_id);
    
    let result = self.workflow_service.delete_event_subscription(&subscription_id, user_id, trace_ctx).await;
    
    match result {
        Ok(_) => {
            HttpResponse::Ok().json(DeleteSubscriptionResponse {
                subscription_id,
                message: "事件订阅删除成功".to_string(),
            })
        },
        Err(e) => {
            log::error!("删除事件订阅失败: {}", e);
            
            match e {
                WorkflowError::NotFoundError(_) => {
                    HttpResponse::NotFound().json(ErrorResponse {
                        error: "事件订阅不存在".to_string(),
                        message: format!("未找到ID为{}的事件订阅", subscription_id),
                        code: "NOT_FOUND".to_string(),
                    })
                },
                WorkflowError::AuthorizationError(message) => {
                    HttpResponse::Forbidden().json(ErrorResponse {
                        error: "无权删除事件订阅".to_string(),
                        message,
                        code: "UNAUTHORIZED".to_string(),
                    })
                },
                _ => {
                    HttpResponse::InternalServerError().json(ErrorResponse {
                        error: "删除事件订阅失败".to_string(),
                        message: e.to_string(),
                        code: "SUBSCRIPTION_DELETE_ERROR".to_string(),
                    })
                }
            }
        }
    }
}

// 列出事件订阅
async fn list_event_subscriptions(&self, req: HttpRequest) -> HttpResponse {
    let trace_ctx = self.extract_trace_context(&req);
    let query = web::Query::<ListSubscriptionsQuery>::from_query(req.query_string())
        .unwrap_or_default();
    
    // 提取查询参数
    let event_type = query.event_type.clone();
    
    let result = self.workflow_service.list_event_subscriptions(
        event_type.as_deref(),
        trace_ctx
    ).await;
    
    match result {
        Ok(subscriptions) => {
            HttpResponse::Ok().json(subscriptions)
        },
        Err(e) => {
            log::error!("获取事件订阅列表失败: {}", e);
            
            HttpResponse::InternalServerError().json(ErrorResponse {
                error: "获取事件订阅列表失败".to_string(),
                message: e.to_string(),
                code: "SUBSCRIPTION_LIST_ERROR".to_string(),
            })
        }
    }
}

// ==========监控和指标==========

// 获取工作流指标
async fn get_workflow_metrics(&self, req: HttpRequest) -> HttpResponse {
    let trace_ctx = self.extract_trace_context(&req);
    let path = web::Path::<String>::extract(&req).await.unwrap();
    let workflow_id = path.into_inner();
    
    // 提取查询参数
    let query = web::Query::<GetMetricsQuery>::from_query(req.query_string())
        .unwrap_or_default();
    
    let start_time = query.start_time.clone();
    let end_time = query.end_time.clone();
    
    let result = self.workflow_service.get_workflow_metrics(
        &workflow_id,
        start_time.as_deref(),
        end_time.as_deref(),
        trace_ctx
    ).await;
    
    match result {
        Ok(metrics) => {
            HttpResponse::Ok().json(metrics)
        },
        Err(e) => {
            log::error!("获取工作流指标失败: {}", e);
            
            match e {
                WorkflowError::NotFoundError(_) => {
                    HttpResponse::NotFound().json(ErrorResponse {
                        error: "工作流实例不存在".to_string(),
                        message: format!("未找到ID为{}的工作流实例", workflow_id),
                        code: "NOT_FOUND".to_string(),
                    })
                },
                _ => {
                    HttpResponse::InternalServerError().json(ErrorResponse {
                        error: "获取工作流指标失败".to_string(),
                        message: e.to_string(),
                        code: "METRICS_ERROR".to_string(),
                    })
                }
            }
        }
}

// 获取任务指标
async fn get_task_metrics(&self, req: HttpRequest) -> HttpResponse {
    let trace_ctx = self.extract_trace_context(&req);
    
    // 提取查询参数
    let query = web::Query::<GetTaskMetricsQuery>::from_query(req.query_string())
        .unwrap_or_default();
    
    let start_time = query.start_time.clone();
    let end_time = query.end_time.clone();
    let task_type = query.task_type.clone();
    let group_by = query.group_by.clone();
    
    let result = self.workflow_service.get_task_metrics(
        start_time.as_deref(),
        end_time.as_deref(),
        task_type.as_deref(),
        group_by.as_deref(),
        trace_ctx
    ).await;
    
    match result {
        Ok(metrics) => {
            HttpResponse::Ok().json(metrics)
        },
        Err(e) => {
            log::error!("获取任务指标失败: {}", e);
            
            HttpResponse::InternalServerError().json(ErrorResponse {
                error: "获取任务指标失败".to_string(),
                message: e.to_string(),
                code: "METRICS_ERROR".to_string(),
            })
        }
    }
}

// 获取系统指标
async fn get_system_metrics(&self, req: HttpRequest) -> HttpResponse {
    let trace_ctx = self.extract_trace_context(&req);
    
    // 提取查询参数
    let query = web::Query::<GetSystemMetricsQuery>::from_query(req.query_string())
        .unwrap_or_default();
    
    let metric_type = query.metric_type.clone();
    let start_time = query.start_time.clone();
    let end_time = query.end_time.clone();
    let interval = query.interval.unwrap_or(60);
    
    let result = self.workflow_service.get_system_metrics(
        metric_type.as_deref(),
        start_time.as_deref(),
        end_time.as_deref(),
        interval,
        trace_ctx
    ).await;
    
    match result {
        Ok(metrics) => {
            HttpResponse::Ok().json(metrics)
        },
        Err(e) => {
            log::error!("获取系统指标失败: {}", e);
            
            HttpResponse::InternalServerError().json(ErrorResponse {
                error: "获取系统指标失败".to_string(),
                message: e.to_string(),
                code: "METRICS_ERROR".to_string(),
            })
        }
    }
}

// ==========系统管理==========

// 健康检查
async fn health_check(&self, req: HttpRequest) -> HttpResponse {
    let trace_ctx = self.extract_trace_context(&req);
    
    let result = self.workflow_service.health_check(trace_ctx).await;
    
    match result {
        Ok(health) => {
            if health.status == "healthy" {
                HttpResponse::Ok().json(health)
            } else {
                HttpResponse::ServiceUnavailable().json(health)
            }
        },
        Err(e) => {
            log::error!("健康检查失败: {}", e);
            
            HttpResponse::InternalServerError().json(HealthCheckResponse {
                status: "unhealthy".to_string(),
                message: format!("健康检查执行失败: {}", e),
                components: HashMap::new(),
                timestamp: chrono::Utc::now(),
            })
        }
    }
}

// 列出节点
async fn list_nodes(&self, req: HttpRequest) -> HttpResponse {
    let trace_ctx = self.extract_trace_context(&req);
    
    let result = self.workflow_service.list_nodes(trace_ctx).await;
    
    match result {
        Ok(nodes) => {
            HttpResponse::Ok().json(nodes)
        },
        Err(e) => {
            log::error!("获取节点列表失败: {}", e);
            
            HttpResponse::InternalServerError().json(ErrorResponse {
                error: "获取节点列表失败".to_string(),
                message: e.to_string(),
                code: "NODE_LIST_ERROR".to_string(),
            })
        }
    }
}

// 获取系统配置
async fn get_system_config(&self, req: HttpRequest) -> HttpResponse {
    let trace_ctx = self.extract_trace_context(&req);
    
    // 检查权限
    if !self.has_admin_permission(&req) {
        return HttpResponse::Forbidden().json(ErrorResponse {
            error: "无权访问系统配置".to_string(),
            message: "需要管理员权限".to_string(),
            code: "UNAUTHORIZED".to_string(),
        });
    }
    
    let result = self.workflow_service.get_system_config(trace_ctx).await;
    
    match result {
        Ok(config) => {
            HttpResponse::Ok().json(config)
        },
        Err(e) => {
            log::error!("获取系统配置失败: {}", e);
            
            HttpResponse::InternalServerError().json(ErrorResponse {
                error: "获取系统配置失败".to_string(),
                message: e.to_string(),
                code: "CONFIG_ERROR".to_string(),
            })
        }
    }
}

// 更新系统配置
async fn update_system_config(&self, req: HttpRequest, body: web::Json<UpdateConfigRequest>) -> HttpResponse {
    let trace_ctx = self.extract_trace_context(&req);
    
    // 检查权限
    if !self.has_admin_permission(&req) {
        return HttpResponse::Forbidden().json(ErrorResponse {
            error: "无权更新系统配置".to_string(),
            message: "需要管理员权限".to_string(),
            code: "UNAUTHORIZED".to_string(),
        });
    }
    
    // 提取用户信息用于审计
    let user_id = self.extract_user_id(&req).unwrap_or_else(|| "anonymous".to_string());
    
    log::info!("用户 {} 更新系统配置", user_id);
    
    let mut request = body.into_inner();
    request.updated_by = Some(user_id);
    
    let result = self.workflow_service.update_system_config(request, trace_ctx).await;
    
    match result {
        Ok(_) => {
            HttpResponse::Ok().json(UpdateConfigResponse {
                message: "系统配置更新成功".to_string(),
            })
        },
        Err(e) => {
            log::error!("更新系统配置失败: {}", e);
            
            match e {
                WorkflowError::ValidationError(message) => {
                    HttpResponse::BadRequest().json(ErrorResponse {
                        error: "配置验证失败".to_string(),
                        message,
                        code: "VALIDATION_ERROR".to_string(),
                    })
                },
                _ => {
                    HttpResponse::InternalServerError().json(ErrorResponse {
                        error: "更新系统配置失败".to_string(),
                        message: e.to_string(),
                        code: "CONFIG_UPDATE_ERROR".to_string(),
                    })
                }
            }
        }
    }
}

// ==========辅助方法==========

// 从请求中提取追踪上下文
fn extract_trace_context(&self, req: &HttpRequest) -> Option<TraceContext> {
    // 从请求头提取追踪信息
    let mut headers = HashMap::new();
    for (header_name, header_value) in req.headers() {
        if let Ok(value) = header_value.to_str() {
            headers.insert(header_name.as_str().to_string(), value.to_string());
        }
    }
    
    // 提取追踪上下文
    match self.tracing_system.extract_context(&headers) {
        Ok(ctx) => ctx,
        Err(e) => {
            log::warn!("提取追踪上下文失败: {}", e);
            None
        }
    }
}

// 从请求中提取用户ID
fn extract_user_id(&self, req: &HttpRequest) -> Option<String> {
    req.extensions()
        .get::<UserClaims>()
        .map(|claims| claims.user_id.clone())
}

// 检查用户是否有管理员权限
fn has_admin_permission(&self, req: &HttpRequest) -> bool {
    if let Some(claims) = req.extensions().get::<UserClaims>() {
        claims.roles.contains(&"admin".to_string())
    } else {
        false
    }
}
}

// ==========请求和响应模型==========

// 列出工作流定义请求
#[derive(Deserialize, Default)]
struct ListWorkflowDefinitionsQuery {
    page: Option<u32>,
    per_page: Option<u32>,
    filter: Option<String>,
}

// 分页响应元数据
#[derive(Serialize)]
struct PaginationMeta {
    total: u64,
    page: u32,
    per_page: u32,
    total_pages: u32,
}

// 分页响应
#[derive(Serialize)]
struct PaginatedResponse<T> {
    data: Vec<T>,
    meta: PaginationMeta,
}

// 注册工作流定义请求
#[derive(Deserialize)]
struct RegisterWorkflowRequest {
    name: String,
    description: Option<String>,
    version: String,
    definition: WorkflowDefinition,
    labels: Option<HashMap<String, String>>,
}

// 注册工作流定义响应
#[derive(Serialize)]
struct RegisterWorkflowResponse {
    id: String,
    message: String,
}

// 更新工作流定义请求
#[derive(Deserialize)]
struct UpdateWorkflowRequest {
    id: String,
    name: Option<String>,
    description: Option<String>,
    version: String,
    definition: Option<WorkflowDefinition>,
    labels: Option<HashMap<String, String>>,
}

// 更新工作流定义响应
#[derive(Serialize)]
struct UpdateWorkflowResponse {
    id: String,
    message: String,
}

// 删除工作流定义响应
#[derive(Serialize)]
struct DeleteWorkflowResponse {
    id: String,
    message: String,
}

// 验证工作流定义请求
#[derive(Deserialize)]
struct ValidateWorkflowRequest {
    definition: WorkflowDefinition,
}

// 列出工作流实例请求
#[derive(Deserialize, Default)]
struct ListWorkflowInstancesQuery {
    page: Option<u32>,
    per_page: Option<u32>,
    status: Option<String>,
    definition_id: Option<String>,
    start_date: Option<String>,
    end_date: Option<String>,
}

// 启动工作流请求
#[derive(Deserialize)]
struct StartWorkflowRequest {
    definition_id: String,
    version: Option<String>,
    input: Option<serde_json::Value>,
    correlation_id: Option<String>,
    priority: Option<u8>,
    labels: Option<HashMap<String, String>>,
    initiated_by: Option<String>,
}

// 启动工作流响应
#[derive(Serialize)]
struct StartWorkflowResponse {
    workflow_id: String,
    message: String,
}

// 获取工作流状态请求
#[derive(Deserialize, Default)]
struct GetWorkflowStatusQuery {
    include_tasks: Option<bool>,
    include_variables: Option<bool>,
}

// 取消工作流请求
#[derive(Deserialize)]
struct CancelWorkflowRequest {
    workflow_id: String,
    reason: Option<String>,
    cancelled_by: Option<String>,
}

// 取消工作流响应
#[derive(Serialize)]
struct CancelWorkflowResponse {
    workflow_id: String,
    message: String,
}

// 暂停工作流请求
#[derive(Deserialize)]
struct PauseWorkflowRequest {
    workflow_id: String,
    reason: Option<String>,
    paused_by: Option<String>,
}

// 暂停工作流响应
#[derive(Serialize)]
struct PauseWorkflowResponse {
    workflow_id: String,
    message: String,
}

// 恢复工作流请求
#[derive(Deserialize)]
struct ResumeWorkflowRequest {
    workflow_id: String,
    resumed_by: Option<String>,
}

// 恢复工作流响应
#[derive(Serialize)]
struct ResumeWorkflowResponse {
    workflow_id: String,
    message: String,
}

// 重试工作流请求
#[derive(Deserialize)]
struct RetryWorkflowRequest {
    workflow_id: String,
    from_activity: Option<String>,
    retried_by: Option<String>,
}

// 重试工作流响应
#[derive(Serialize)]
struct RetryWorkflowResponse {
    workflow_id: String,
    message: String,
}

// 工作流信号请求
#[derive(Deserialize)]
struct WorkflowSignalRequest {
    workflow_id: String,
    signal_name: String,
    signal_data: Option<serde_json::Value>,
    signaled_by: Option<String>,
}

// 工作流信号响应
#[derive(Serialize)]
struct WorkflowSignalResponse {
    workflow_id: String,
    message: String,
}

// 列出工作流任务请求
#[derive(Deserialize, Default)]
struct ListWorkflowTasksQuery {
    status: Option<String>,
    task_type: Option<String>,
}

// 更新元数据请求
#[derive(Deserialize)]
struct UpdateMetadataRequest {
    workflow_id: String,
    metadata: HashMap<String, String>,
    updated_by: Option<String>,
}

// 更新元数据响应
#[derive(Serialize)]
struct UpdateMetadataResponse {
    workflow_id: String,
    message: String,
}

// 列出任务请求
#[derive(Deserialize, Default)]
struct ListTasksQuery {
    page: Option<u32>,
    per_page: Option<u32>,
    status: Option<String>,
    task_type: Option<String>,
    assignee: Option<String>,
}

// 完成任务请求
#[derive(Deserialize)]
struct CompleteTaskRequest {
    task_id: String,
    output: Option<serde_json::Value>,
    completed_by: Option<String>,
}

// 完成任务响应
#[derive(Serialize)]
struct CompleteTaskResponse {
    task_id: String,
    message: String,
}

// 任务失败请求
#[derive(Deserialize)]
struct FailTaskRequest {
    task_id: String,
    error: String,
    details: Option<serde_json::Value>,
    failed_by: Option<String>,
}

// 任务失败响应
#[derive(Serialize)]
struct FailTaskResponse {
    task_id: String,
    message: String,
}

// 认领任务请求
#[derive(Deserialize)]
struct ClaimTaskRequest {
    task_id: String,
    assignee: Option<String>,
}

// 认领任务响应
#[derive(Serialize)]
struct ClaimTaskResponse {
    task_id: String,
    message: String,
}

// 任务心跳请求
#[derive(Deserialize)]
struct TaskHeartbeatRequest {
    task_id: String,
    progress: Option<u8>,
    details: Option<serde_json::Value>,
}

// 任务心跳响应
#[derive(Serialize)]
struct TaskHeartbeatResponse {
    task_id: String,
    message: String,
}

// 发布事件请求
#[derive(Deserialize)]
struct PublishEventRequest {
    event_type: String,
    data: serde_json::Value,
    correlation_id: Option<String>,
    published_by: Option<String>,
}

// 发布事件响应
#[derive(Serialize)]
struct PublishEventResponse {
    event_id: String,
    message: String,
}

// 创建事件订阅请求
#[derive(Deserialize)]
struct CreateSubscriptionRequest {
    event_type: String,
    callback_url: String,
    filter: Option<serde_json::Value>,
    created_by: Option<String>,
}

// 创建事件订阅响应
#[derive(Serialize)]
struct CreateSubscriptionResponse {
    subscription_id: String,
    message: String,
}

// 删除事件订阅响应
#[derive(Serialize)]
struct DeleteSubscriptionResponse {
    subscription_id: String,
    message: String,
}

// 列出事件订阅请求
#[derive(Deserialize, Default)]
struct ListSubscriptionsQuery {
    event_type: Option<String>,
}

// 获取指标请求
#[derive(Deserialize, Default)]
struct GetMetricsQuery {
    start_time: Option<String>,
    end_time: Option<String>,
}

// 获取任务指标请求
#[derive(Deserialize, Default)]
struct GetTaskMetricsQuery {
    start_time: Option<String>,
    end_time: Option<String>,
    task_type: Option<String>,
    group_by: Option<String>,
}

// 获取系统指标请求
#[derive(Deserialize, Default)]
struct GetSystemMetricsQuery {
    metric_type: Option<String>,
    start_time: Option<String>,
    end_time: Option<String>,
    interval: Option<u32>,
}

// 健康检查响应
#[derive(Serialize)]
struct HealthCheckResponse {
    status: String,
    message: String,
    components: HashMap<String, ComponentHealth>,
    timestamp: chrono::DateTime<chrono::Utc>,
}

// 组件健康状态
#[derive(Serialize)]
struct ComponentHealth {
    status: String,
    message: Option<String>,
    details: Option<serde_json::Value>,
}

// 更新配置请求
#[derive(Deserialize)]
struct UpdateConfigRequest {
    config: HashMap<String, serde_json::Value>,
    updated_by: Option<String>,
}

// 更新配置响应
#[derive(Serialize)]
struct UpdateConfigResponse {
    message: String,
}

// 错误响应
#[derive(Serialize)]
struct ErrorResponse {
    error: String,
    message: String,
    code: String,
}

// 用户声明
struct UserClaims {
    user_id: String,
    username: String,
    roles: Vec<String>,
    exp: u64,
}

// 追踪中间件
struct TracingMiddleware {
    tracing_system: Arc<TracingSystem>,
}

impl TracingMiddleware {
    fn new(tracing_system: Arc<TracingSystem>) -> Self {
        Self { tracing_system }
    }
}

// 实现追踪中间件
impl<S, B> Transform<S, ServiceRequest> for TracingMiddleware
where
    S: Service<ServiceRequest, Response = ServiceResponse<B>, Error = Error>,
    S::Future: 'static,
    B: 'static,
{
    type Response = ServiceResponse<B>;
    type Error = Error;
    type InitError = ();
    type Transform = TracingMiddlewareService<S>;
    type Future = Ready<Result<Self::Transform, Self::InitError>>;

    fn new_transform(&self, service: S) -> Self::Future {
        ok(TracingMiddlewareService {
            service,
            tracing_system: self.tracing_system.clone(),
        })
    }
}

struct TracingMiddlewareService<S> {
    service: S,
    tracing_system: Arc<TracingSystem>,
}

impl<S, B> Service<ServiceRequest> for TracingMiddlewareService<S>
where
    S: Service<ServiceRequest, Response = ServiceResponse<B>, Error = Error>,
    S::Future: 'static,
    B: 'static,
{
    type Response = ServiceResponse<B>;
    type Error = Error;
    type Future = Pin<Box<dyn Future<Output = Result<Self::Response, Self::Error>>>>;

    fn poll_ready(&self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        self.service.poll_ready(cx)
    }

    fn call(&self, req: ServiceRequest) -> Self::Future {
        // 从请求头提取追踪信息
        let mut headers = HashMap::new();
        for (header_name, header_value) in req.headers() {
            if let Ok(value) = header_value.to_str() {
                headers.insert(header_name.as_str().to_string(), value.to_string());
            }
        }
        
        // 提取或创建追踪上下文
        let trace_ctx = match self.tracing_system.extract_context(&headers) {
            Ok(Some(ctx)) => ctx,
            _ => {
                // 创建新的追踪
                let method = req.method().as_str();
                let path = req.uri().path();
                let span_name = format!("{} {}", method, path);
                
                let mut attributes = HashMap::new();
                attributes.insert("http.method".to_string(), method.to_string());
                attributes.insert("http.path".to_string(), path.to_string());
                attributes.insert("http.host".to_string(), 
                    req.headers()
                       .get("host")
                       .and_then(|h| h.to_str().ok())
                       .unwrap_or("unknown")
                       .to_string());
                
                self.tracing_system.create_trace(
                    &span_name,
                    SpanKind::Server,
                    attributes
                ).unwrap_or_else(|_| TraceContext::new_not_sampled(&span_name))
            }
        };
        
        // 复制追踪上下文用于响应处理
        let trace_ctx_for_response = trace_ctx.clone();
        
        // 注入追踪上下文到请求扩展中
        let mut req = req;
        req.extensions_mut().insert(trace_ctx);
        
        let tracing_system = self.tracing_system.clone();
        let future = self.service.call(req);
        
        Box::pin(async move {
            // 记录请求处理结果
            let response = future.await;
            
            match &response {
                Ok(res) => {
                    // 记录响应状态码
                    trace_ctx_for_response.add_attribute(
                        "http.status_code",
                        &res.status().as_u16().to_string()
                    ).ok();
                    
                    if res.status().is_success() {
                        trace_ctx_for_response.set_status(StatusCode::Ok, None).ok();
                    } else {
                        trace_ctx_for_response.set_status(
                            StatusCode::Error, 
                            Some(&format!("HTTP错误: {}", res.status()))
                        ).ok();
                    }
                },
                Err(e) => {
                    // 记录错误
                    trace_ctx_for_response.record_exception(
                        "http_error",
                        &e.to_string(),
                        None
                    ).ok();
                }
            }
            
            // 结束追踪
            trace_ctx_for_response.end().ok();
            
            response
        })
    }
}

// 指标中间件
struct MetricsMiddleware {
    metrics_collector: Arc<MetricsCollector>,
}

impl MetricsMiddleware {
    fn new(metrics_collector: Arc<MetricsCollector>) -> Self {
        Self { metrics_collector }
    }
}

// 实现指标中间件
impl<S, B> Transform<S, ServiceRequest> for MetricsMiddleware
where
    S: Service<ServiceRequest, Response = ServiceResponse<B>, Error = Error>,
    S::Future: 'static,
    B: 'static,
{
    type Response = ServiceResponse<B>;
    type Error = Error;
    type InitError = ();
    type Transform = MetricsMiddlewareService<S>;
    type Future = Ready<Result<Self::Transform, Self::InitError>>;

    fn new_transform(&self, service: S) -> Self::Future {
        ok(MetricsMiddlewareService {
            service,
            metrics_collector: self.metrics_collector.clone(),
        })
    }
}

struct MetricsMiddlewareService<S> {
    service: S,
    metrics_collector: Arc<MetricsCollector>,
}

impl<S, B> Service<ServiceRequest> for MetricsMiddlewareService<S>
where
    S: Service<ServiceRequest, Response = ServiceResponse<B>, Error = Error>,
    S::Future: 'static,
    B: 'static,
{
    type Response = ServiceResponse<B>;
    type Error = Error;
    type Future = Pin<Box<dyn Future<Output = Result<Self::Response, Self::Error>>>>;

    fn poll_ready(&self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        self.service.poll_ready(cx)
    }

    fn call(&self, req: ServiceRequest) -> Self::Future {
        let start = Instant::now();
        let method = req.method().as_str().to_string();
        let path = req.uri().path().to_string();
        
        // 增加请求计数
        let mut labels = HashMap::new();
        labels.insert("method".to_string(), method.clone());
        labels.insert("path".to_string(), path.clone());
        
        if let Err(e) = self.metrics_collector.increment_counter(
            "http_requests_total",
            "Total number of HTTP requests",
            labels.clone(),
            1
        ) {
            log::warn!("记录HTTP请求指标失败: {}", e);
        }
        
        let metrics_collector = self.metrics_collector.clone();
        let future = self.service.call(req);
        
        Box::pin(async move {
            // 记录请求处理结果
            let response = future.await;
            let duration = start.elapsed();
            
            // 添加状态码标签
            let status_code = match &response {
                Ok(res) => res.status().as_u16().to_string(),
                Err(_) => "error".to_string(),
            };
            
            labels.insert("status".to_string(), status_code);
            
            // 记录请求持续时间
            if let Err(e) = metrics_collector.observe_histogram(
                "http_request_duration_milliseconds",
                "HTTP request duration in milliseconds",
                Some(vec![5.0, 10.0, 25.0, 50.0, 100.0, 250.0, 500.0, 1000.0, 2500.0, 5000.0, 10000.0]),
                labels,
                duration.as_millis() as f64
            ) {
                log::warn!("记录HTTP请求持续时间指标失败: {}", e);
            }
            
            response
        })
    }
}

// JWT认证中间件
struct JwtAuthMiddleware {
    auth_service: Arc<AuthService>,
}

impl JwtAuthMiddleware {
    fn new(auth_service: Arc<AuthService>) -> Self {
        Self { auth_service }
    }
}

// 实现JWT认证中间件
impl<S, B> Transform<S, ServiceRequest> for JwtAuthMiddleware
where
    S: Service<ServiceRequest, Response = ServiceResponse<B>, Error = Error>,
    S::Future: 'static,
    B: 'static,
{
    type Response = ServiceResponse<B>;
    type Error = Error;
    type InitError = ();
    type Transform = JwtAuthMiddlewareService<S>;
    type Future = Ready<Result<Self::Transform, Self::InitError>>;

    fn new_transform(&self, service: S) -> Self::Future {
        ok(JwtAuthMiddlewareService {
            service,
            auth_service: self.auth_service.clone(),
        })
    }
}

struct JwtAuthMiddlewareService<S> {
    service: S,
    auth_service: Arc<AuthService>,
}

impl<S, B> Service<ServiceRequest> for JwtAuthMiddlewareService<S>
where
    S: Service<ServiceRequest, Response = ServiceResponse<B>, Error = Error>,
    S::Future: 'static,
    B: 'static,
{
    type Response = ServiceResponse<B>;
    type Error = Error;
    type Future = Pin<Box<dyn Future<Output = Result<Self::Response, Self::Error>>>>;

    fn poll_ready(&self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        self.service.poll_ready(cx)
    }

fn call(&self, req: ServiceRequest) -> Self::Future {
    // 跳过健康检查和选项请求的认证
    let path = req.uri().path();
    let method = req.method();
    
    if path == "/api/v1/system/health" || method == Method::OPTIONS {
        return Box::pin(self.service.call(req));
    }
    
    // 从请求头获取认证信息
    let auth_header = req.headers().get("Authorization");
    let token = match auth_header {
        Some(value) => {
            match value.to_str() {
                Ok(v) => {
                    if v.starts_with("Bearer ") {
                        Some(v[7..].to_string())
                    } else {
                        None
                    }
                },
                Err(_) => None,
            }
        },
        None => None,
    };
    
    // 如果没有令牌，返回未授权错误
    if token.is_none() {
        let response = HttpResponse::Unauthorized()
            .json(ErrorResponse {
                error: "认证失败".to_string(),
                message: "缺少认证令牌".to_string(),
                code: "UNAUTHORIZED".to_string(),
            });
        return Box::pin(async move { Ok(req.into_response(response)) });
    }
    
    let auth_service = self.auth_service.clone();
    let token = token.unwrap();
    let future = self.service.call(req);
    
    Box::pin(async move {
        // 验证令牌
        match auth_service.verify_token(&token).await {
            Ok(claims) => {
                // 将用户信息添加到请求扩展中
                let (request, mut payload) = future.into_inner().parts();
                request.extensions_mut().insert(claims);
                
                // 继续处理请求
                future.call(ServiceRequest::from_parts(request, payload)).await
            },
            Err(e) => {
                log::warn!("令牌验证失败: {}", e);
                
                let response = HttpResponse::Unauthorized()
                    .json(ErrorResponse {
                        error: "认证失败".to_string(),
                        message: "无效的认证令牌".to_string(),
                        code: "INVALID_TOKEN".to_string(),
                    });
                
                Ok(ServiceRequest::from_request(future.into_inner()).into_response(response))
            }
        }
    })
}
```

REST API接口的优势：

1. **完整的工作流管理**：覆盖工作流和任务生命周期的所有操作
2. **结构化错误处理**：统一的错误响应格式和明确的错误代码
3. **分页和筛选**：支持大量数据的高效查询
4. **认证与授权**：基于JWT的安全控制
5. **分布式追踪**：无缝集成追踪系统实现请求可观测性
6. **性能监控**：中间件自动收集API性能指标
7. **审计日志**：记录关键操作的用户和时间

### 14.2 WebSocket接口

实现实时通知和工作流可视化的WebSocket接口：

```rust
pub struct WebSocketService {
    workflow_service: Arc<WorkflowService>,
    metrics_collector: Arc<MetricsCollector>,
    tracing_system: Arc<TracingSystem>,
    auth_service: Arc<AuthService>,
    active_connections: Arc<RwLock<HashMap<String, Vec<WsConnectionInfo>>>>,
}

struct WsConnectionInfo {
    id: String,
    user_id: String,
    subscription_types: Vec<String>,
    actor: Addr<WebSocketActor>,
    connected_at: chrono::DateTime<chrono::Utc>,
    last_activity: Arc<AtomicI64>,
}

impl WebSocketService {
    pub fn new(
        workflow_service: Arc<WorkflowService>,
        metrics_collector: Arc<MetricsCollector>,
        tracing_system: Arc<TracingSystem>,
        auth_service: Arc<AuthService>,
    ) -> Self {
        Self {
            workflow_service,
            metrics_collector,
            tracing_system,
            auth_service,
            active_connections: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    // 配置WebSocket路由
    pub fn configure_routes(
        &self,
        cfg: &mut web::ServiceConfig
    ) {
        let service = self.clone();
        
        cfg.service(
            web::resource("/api/v1/ws/notifications")
                .route(web::get().to(move |req, stream| service.handle_notification_websocket(req, stream)))
        );
        
        cfg.service(
            web::resource("/api/v1/ws/workflow/{id}/visualization")
                .route(web::get().to(move |req, stream| service.handle_workflow_visualization(req, stream)))
        );
    }
    
    // 启动清理超时连接的任务
    pub fn start_cleanup_task(&self) -> JoinHandle<()> {
        let active_connections = self.active_connections.clone();
        let metrics_collector = self.metrics_collector.clone();
        
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(Duration::from_secs(60));
            
            loop {
                interval.tick().await;
                
                let now = chrono::Utc::now().timestamp();
                let mut total_closed = 0;
                
                // 查找并关闭超时连接
                {
                    let mut connections = active_connections.write().await;
                    
                    for (_, user_connections) in connections.iter_mut() {
                        let before_len = user_connections.len();
                        
                        // 筛选出超时连接
                        let timeout_connections: Vec<_> = user_connections
                            .iter()
                            .filter(|conn| {
                                let last_activity = conn.last_activity.load(Ordering::Relaxed);
                                // 如果超过5分钟无活动，则认为超时
                                now - last_activity > 300
                            })
                            .map(|conn| conn.id.clone())
                            .collect();
                        
                        // 关闭超时连接
                        for conn_id in &timeout_connections {
                            if let Some(pos) = user_connections.iter().position(|c| &c.id == conn_id) {
                                let conn = user_connections.remove(pos);
                                log::info!("关闭超时WebSocket连接: {}", conn_id);
                                conn.actor.do_send(WsMessage::Close);
                            }
                        }
                        
                        total_closed += timeout_connections.len();
                    }
                    
                    // 移除没有连接的用户
                    connections.retain(|_, conns| !conns.is_empty());
                }
                
                // 记录清理指标
                if total_closed > 0 {
                    log::info!("已清理 {} 个超时WebSocket连接", total_closed);
                    
                    let mut labels = HashMap::new();
                    labels.insert("reason".to_string(), "timeout".to_string());
                    
                    if let Err(e) = metrics_collector.increment_counter(
                        "websocket_connections_closed_total",
                        "Total number of closed WebSocket connections",
                        labels,
                        total_closed as u64
                    ) {
                        log::warn!("记录WebSocket连接关闭指标失败: {}", e);
                    }
                }
            }
        })
    }
    
    // 处理通知WebSocket连接
    async fn handle_notification_websocket(&self, req: HttpRequest, stream: web::Payload) -> Result<HttpResponse, Error> {
        let trace_ctx = self.extract_trace_context(&req);
        
        // 验证令牌
        let token = self.extract_token(&req);
        let user_claims = match token {
            Some(token) => match self.auth_service.verify_token(&token).await {
                Ok(claims) => claims,
                Err(e) => {
                    log::warn!("WebSocket连接认证失败: {}", e);
                    return Ok(HttpResponse::Unauthorized().finish());
                }
            },
            None => {
                log::warn!("WebSocket连接缺少认证令牌");
                return Ok(HttpResponse::Unauthorized().finish());
            }
        };
        
        // 提取订阅类型参数
        let subscription_types = req.query_string()
            .split('&')
            .filter_map(|param| {
                if param.starts_with("types=") {
                    Some(param[6..].to_string())
                } else {
                    None
                }
            })
            .collect::<Vec<String>>();
        
        // 创建WebSocket响应
        let connection_id = Uuid::new_v4().to_string();
        
        log::info!("用户 {} 创建通知WebSocket连接: {}", user_claims.user_id, connection_id);
        
        // 记录连接指标
        let mut labels = HashMap::new();
        labels.insert("type".to_string(), "notifications".to_string());
        
        if let Err(e) = self.metrics_collector.increment_counter(
            "websocket_connections_total",
            "Total number of WebSocket connections",
            labels.clone(),
            1
        ) {
            log::warn!("记录WebSocket连接指标失败: {}", e);
        }
        
        let active_connections = self.active_connections.clone();
        let metrics_collector = self.metrics_collector.clone();
        let user_id = user_claims.user_id.clone();
        
        // 创建WebSocket actor
        let (addr, resp) = WsResponseBuilder::new(
            move |actor, ctx| WebSocketActor::new(
                connection_id.clone(),
                user_id.clone(),
                subscription_types.clone(),
                active_connections.clone(),
                metrics_collector.clone(),
                actor,
                ctx,
            ),
            &req,
            stream,
        )?;
        
        // 添加连接到活动连接列表
        {
            let mut connections = self.active_connections.write().await;
            
            let user_connections = connections
                .entry(user_claims.user_id.clone())
                .or_insert_with(Vec::new);
                
            user_connections.push(WsConnectionInfo {
                id: connection_id,
                user_id: user_claims.user_id,
                subscription_types,
                actor: addr,
                connected_at: chrono::Utc::now(),
                last_activity: Arc::new(AtomicI64::new(chrono::Utc::now().timestamp())),
            });
        }
        
        trace_ctx.map(|ctx| ctx.end().ok());
        
        Ok(resp)
    }
    
    // 处理工作流可视化WebSocket连接
    async fn handle_workflow_visualization(&self, req: HttpRequest, stream: web::Payload) -> Result<HttpResponse, Error> {
        let trace_ctx = self.extract_trace_context(&req);
        
        // 验证令牌
        let token = self.extract_token(&req);
        let user_claims = match token {
            Some(token) => match self.auth_service.verify_token(&token).await {
                Ok(claims) => claims,
                Err(e) => {
                    log::warn!("工作流可视化WebSocket连接认证失败: {}", e);
                    return Ok(HttpResponse::Unauthorized().finish());
                }
            },
            None => {
                log::warn!("工作流可视化WebSocket连接缺少认证令牌");
                return Ok(HttpResponse::Unauthorized().finish());
            }
        };
        
        // 提取工作流ID
        let workflow_id = match web::Path::<String>::extract(&req).await {
            Ok(path) => path.into_inner(),
            Err(e) => {
                log::warn!("提取工作流ID失败: {}", e);
                return Ok(HttpResponse::BadRequest().finish());
            }
        };
        
        // 检查工作流是否存在
        match self.workflow_service.get_workflow_status(&workflow_id, false, false, trace_ctx.clone()).await {
            Ok(_) => {
                // 工作流存在，继续处理
            },
            Err(e) => {
                log::warn!("工作流 {} 不存在或无法访问: {}", workflow_id, e);
                return Ok(HttpResponse::NotFound().finish());
            }
        }
        
        // 创建WebSocket响应
        let connection_id = Uuid::new_v4().to_string();
        
        log::info!("用户 {} 创建工作流 {} 可视化WebSocket连接: {}", 
            user_claims.user_id, workflow_id, connection_id);
        
        // 记录连接指标
        let mut labels = HashMap::new();
        labels.insert("type".to_string(), "visualization".to_string());
        
        if let Err(e) = self.metrics_collector.increment_counter(
            "websocket_connections_total",
            "Total number of WebSocket connections",
            labels.clone(),
            1
        ) {
            log::warn!("记录WebSocket连接指标失败: {}", e);
        }
        
        let active_connections = self.active_connections.clone();
        let metrics_collector = self.metrics_collector.clone();
        let workflow_service = self.workflow_service.clone();
        let user_id = user_claims.user_id.clone();
        let workflow_id_clone = workflow_id.clone();
        
        // 创建WebSocket actor
        let (addr, resp) = WsResponseBuilder::new(
            move |actor, ctx| WorkflowVisualizationActor::new(
                connection_id.clone(),
                user_id.clone(),
                workflow_id_clone.clone(),
                active_connections.clone(),
                workflow_service.clone(),
                metrics_collector.clone(),
                actor,
                ctx,
            ),
            &req,
            stream,
        )?;
        
        // 添加连接到活动连接列表
        {
            let mut connections = self.active_connections.write().await;
            
            let user_connections = connections
                .entry(user_claims.user_id.clone())
                .or_insert_with(Vec::new);
                
            user_connections.push(WsConnectionInfo {
                id: connection_id,
                user_id: user_claims.user_id,
                subscription_types: vec![format!("workflow.{}", workflow_id)],
                actor: addr,
                connected_at: chrono::Utc::now(),
                last_activity: Arc::new(AtomicI64::new(chrono::Utc::now().timestamp())),
            });
        }
        
        trace_ctx.map(|ctx| ctx.end().ok());
        
        Ok(resp)
    }
    
    // 广播通知给所有相关连接
    pub async fn broadcast_notification(&self, notification: &Notification) -> Result<usize, WebSocketError> {
        let mut sent_count = 0;
        
        // 如果通知是针对特定用户的
        if let Some(target_user_id) = &notification.target_user_id {
            sent_count += self.send_to_user(target_user_id, notification).await?;
            return Ok(sent_count);
        }
        
        // 否则发送给所有订阅了该通知类型的连接
        let connections = self.active_connections.read().await;
        
        for (_, user_connections) in connections.iter() {
            for conn in user_connections {
                // 检查此连接是否订阅了该通知类型
                if conn.subscription_types.is_empty() || 
                   conn.subscription_types.contains(&notification.notification_type) {
                    // 发送通知
                    conn.actor.do_send(WsMessage::Notification(notification.clone()));
                    sent_count += 1;
                }
            }
        }
        
        Ok(sent_count)
    }
    
    // 发送通知给特定用户
    async fn send_to_user(&self, user_id: &str, notification: &Notification) -> Result<usize, WebSocketError> {
        let mut sent_count = 0;
        
        let connections = self.active_connections.read().await;
        
        if let Some(user_connections) = connections.get(user_id) {
            for conn in user_connections {
                // 检查此连接是否订阅了该通知类型
                if conn.subscription_types.is_empty() || 
                   conn.subscription_types.contains(&notification.notification_type) {
                    // 发送通知
                    conn.actor.do_send(WsMessage::Notification(notification.clone()));
                    sent_count += 1;
                }
            }
        }
        
        Ok(sent_count)
    }
    
    // 发送工作流状态更新给所有观察此工作流的连接
    pub async fn broadcast_workflow_status(&self, workflow_id: &str, status: &WorkflowStatus) -> Result<usize, WebSocketError> {
        let mut sent_count = 0;
        
        let connections = self.active_connections.read().await;
        
        for (_, user_connections) in connections.iter() {
            for conn in user_connections {
                // 检查此连接是否订阅了此工作流
                if conn.subscription_types.contains(&format!("workflow.{}", workflow_id)) {
                    // 发送状态更新
                    conn.actor.do_send(WsMessage::WorkflowStatus(workflow_id.to_string(), status.clone()));
                    sent_count += 1;
                }
            }
        }
        
        Ok(sent_count)
    }
    
    // 获取活动连接统计
    pub async fn get_connection_stats(&self) -> ConnectionStats {
        let connections = self.active_connections.read().await;
        
        let mut total_connections = 0;
        let mut users_count = connections.len();
        let mut connection_types = HashMap::new();
        
        for (_, user_connections) in connections.iter() {
            total_connections += user_connections.len();
            
            for conn in user_connections {
                for subtype in &conn.subscription_types {
                    *connection_types.entry(subtype.clone()).or_insert(0) += 1;
                }
            }
        }
        
        ConnectionStats {
            total_connections,
            users_count,
            connection_types,
        }
    }
    
    // 从请求中提取认证令牌
    fn extract_token(&self, req: &HttpRequest) -> Option<String> {
        // 优先从查询参数中获取token
        if let Some(token) = req.query_string()
            .split('&')
            .find_map(|param| {
                if param.starts_with("token=") {
                    Some(param[6..].to_string())
                } else {
                    None
                }
            }) {
            return Some(token);
        }
        
        // 从Authorization头中获取token
        req.headers().get("Authorization")
            .and_then(|value| value.to_str().ok())
            .and_then(|value| {
                if value.starts_with("Bearer ") {
                    Some(value[7..].to_string())
                } else {
                    None
                }
            })
    }
    
    // 从请求中提取追踪上下文
    fn extract_trace_context(&self, req: &HttpRequest) -> Option<TraceContext> {
        // 从请求头提取追踪信息
        let mut headers = HashMap::new();
        for (header_name, header_value) in req.headers() {
            if let Ok(value) = header_value.to_str() {
                headers.insert(header_name.as_str().to_string(), value.to_string());
            }
        }
        
        // 提取追踪上下文
        match self.tracing_system.extract_context(&headers) {
            Ok(ctx) => ctx,
            Err(e) => {
                log::warn!("提取追踪上下文失败: {}", e);
                None
            }
        }
    }
}

impl Clone for WebSocketService {
    fn clone(&self) -> Self {
        Self {
            workflow_service: self.workflow_service.clone(),
            metrics_collector: self.metrics_collector.clone(),
            tracing_system: self.tracing_system.clone(),
            auth_service: self.auth_service.clone(),
            active_connections: self.active_connections.clone(),
        }
    }
}

// WebSocket Actor
struct WebSocketActor {
    id: String,
    user_id: String,
    subscription_types: Vec<String>,
    active_connections: Arc<RwLock<HashMap<String, Vec<WsConnectionInfo>>>>,
    metrics_collector: Arc<MetricsCollector>,
    last_activity: Arc<AtomicI64>,
}

impl WebSocketActor {
    fn new(
        id: String,
        user_id: String,
        subscription_types: Vec<String>,
        active_connections: Arc<RwLock<HashMap<String, Vec<WsConnectionInfo>>>>,
        metrics_collector: Arc<MetricsCollector>,
        _: Actor<Self>,
        _: &mut Context<Self>,
    ) -> Self {
        let last_activity = Arc::new(AtomicI64::new(chrono::Utc::now().timestamp()));
        
        Self {
            id,
            user_id,
            subscription_types,
            active_connections,
            metrics_collector,
            last_activity,
        }
    }
}

impl Actor for WebSocketActor {
    type Context = ws::WebsocketContext<Self>;
    
    fn started(&mut self, ctx: &mut Self::Context) {
        // 发送连接建立确认
        let response = serde_json::json!({
            "type": "connection_established",
            "connection_id": self.id,
            "timestamp": chrono::Utc::now().to_rfc3339(),
            "subscriptions": self.subscription_types,
        });
        
        ctx.text(response.to_string());
        
        // 设置心跳检查
        ctx.run_interval(Duration::from_secs(30), |act, ctx| {
            ctx.ping(b"");
            
            // 更新最后活动时间
            act.last_activity.store(chrono::Utc::now().timestamp(), Ordering::Relaxed);
        });
    }
    
    fn stopping(&mut self, _: &mut Self::Context) -> Running {
        // 从活动连接中移除
        tokio::spawn({
            let active_connections = self.active_connections.clone();
            let id = self.id.clone();
            let user_id = self.user_id.clone();
            let metrics_collector = self.metrics_collector.clone();
            
            async move {
                let mut connections = active_connections.write().await;
                
                if let Some(user_connections) = connections.get_mut(&user_id) {
                    if let Some(pos) = user_connections.iter().position(|c| c.id == id) {
                        user_connections.remove(pos);
                    }
                    
                    // 如果用户没有更多连接，移除用户条目
                    if user_connections.is_empty() {
                        connections.remove(&user_id);
                    }
                }
                
                // 记录连接关闭指标
                let mut labels = HashMap::new();
                labels.insert("reason".to_string(), "closed".to_string());
                
                if let Err(e) = metrics_collector.increment_counter(
                    "websocket_connections_closed_total",
                    "Total number of closed WebSocket connections",
                    labels,
                    1
                ) {
                    log::warn!("记录WebSocket连接关闭指标失败: {}", e);
                }
                
                log::info!("WebSocket连接关闭: {}", id);
            }
        });
        
        Running::Stop
    }
}

impl StreamHandler<Result<ws::Message, ws::ProtocolError>> for WebSocketActor {
    fn handle(&mut self, msg: Result<ws::Message, ws::ProtocolError>, ctx: &mut Self::Context) {
        // 更新最后活动时间
        self.last_activity.store(chrono::Utc::now().timestamp(), Ordering::Relaxed);
        
        match msg {
            Ok(ws::Message::Ping(msg)) => {
                ctx.pong(&msg);
            }
            Ok(ws::Message::Pong(_)) => {
                // 忽略Pong响应
            }
            Ok(ws::Message::Text(text)) => {
                // 处理客户端消息
                match serde_json::from_str::<WebSocketClientMessage>(&text) {
                    Ok(client_msg) => self.handle_client_message(client_msg, ctx),
                    Err(e) => {
                        log::warn!("无法解析WebSocket客户端消息: {}", e);
                        
                        let error_response = serde_json::json!({
                            "type": "error",
                            "error": "无法解析消息",
                            "details": e.to_string(),
                            "timestamp": chrono::Utc::now().to_rfc3339(),
                        });
                        
                        ctx.text(error_response.to_string());
                    }
                }
            }
            Ok(ws::Message::Binary(_)) => {
                // 暂不支持二进制消息
                let error_response = serde_json::json!({
                    "type": "error",
                    "error": "不支持二进制消息",
                    "timestamp": chrono::Utc::now().to_rfc3339(),
                });
                
                ctx.text(error_response.to_string());
            }
            Ok(ws::Message::Close(reason)) => {
                // 客户端请求关闭连接
                ctx.close(reason);
            }
            _ => {
                // 忽略其他消息类型
            }
        }
    }
}

impl WebSocketActor {
    // 处理客户端消息
    fn handle_client_message(&self, msg: WebSocketClientMessage, ctx: &mut ws::WebsocketContext<Self>) {
        match msg.message_type.as_str() {
            "ping" => {
                // 响应ping
                let response = serde_json::json!({
                    "type": "pong",
                    "timestamp": chrono::Utc::now().to_rfc3339(),
                });
                
                ctx.text(response.to_string());
            }
            "subscribe" => {
                // 处理订阅请求
                if let Some(subscription_types) = msg.data.get("types").and_then(|v| v.as_array()) {
                    let types: Vec<String> = subscription_types
                        .iter()
                        .filter_map(|v| v.as_str().map(|s| s.to_string()))
                        .collect();
                    
                    if !types.is_empty() {
                        // 更新订阅
                        tokio::spawn({
                            let active_connections = self.active_connections.clone();
                            let id = self.id.clone();
                            let user_id = self.user_id.clone();
                            let new_types = types.clone();
                            
                            async move {
                                let mut connections = active_connections.write().await;
                                
                                if let Some(user_connections) = connections.get_mut(&user_id) {
                                    if let Some(conn) = user_connections.iter_mut().find(|c| c.id == id) {
                                        // 更新订阅类型
                                        conn.subscription_types = new_types;
                                    }
                                }
                            }
                        });
                        
                        let response = serde_json::json!({
                            "type": "subscribed",
                            "subscriptions": types,
                            "timestamp": chrono::Utc::now().to_rfc3339(),
                        });
                        
                        ctx.text(response.to_string());
                    }
                } else {
                    let error_response = serde_json::json!({
                        "type": "error",
                        "error": "订阅请求格式错误",
                        "details": "缺少types数组",
                        "timestamp": chrono::Utc::now().to_rfc3339(),
                    });
                    
                    ctx.text(error_response.to_string());
                }
            }
            _ => {
                // 未知消息类型
                let error_response = serde_json::json!({
                    "type": "error",
                    "error": "未知消息类型",
                    "details": format!("不支持的消息类型: {}", msg.message_type),
                    "timestamp": chrono::Utc::now().to_rfc3339(),
                });
                
                ctx.text(error_response.to_string());
            }
        }
    }
}

// 工作流可视化Actor
struct WorkflowVisualizationActor {
    id: String,
    user_id: String,
    workflow_id: String,
    active_connections: Arc<RwLock<HashMap<String, Vec<WsConnectionInfo>>>>,
    workflow_service: Arc<WorkflowService>,
    metrics_collector: Arc<MetricsCollector>,
    last_activity: Arc<AtomicI64>,
}

impl WorkflowVisualizationActor {
    fn new(
        id: String,
        user_id: String,
        workflow_id: String,
        active_connections: Arc<RwLock<HashMap<String, Vec<WsConnectionInfo>>>>,
        workflow_service: Arc<WorkflowService>,
        metrics_collector: Arc<MetricsCollector>,
        _: Actor<Self>,
        _: &mut Context<Self>,
    ) -> Self {
        let last_activity = Arc::new(AtomicI64::new(chrono::Utc::now().timestamp()));
        
        Self {
            id,
            user_id,
            workflow_id,
            active_connections,
            workflow_service,
            metrics_collector,
            last_activity,
        }
    }
}

impl Actor for WorkflowVisualizationActor {
    type Context = ws::WebsocketContext<Self>;
    
    fn started(&mut self, ctx: &mut Self::Context) {
        // 发送连接建立确认
        let response = serde_json::json!({
            "type": "connection_established",
            "connection_id": self.id,
            "workflow_id": self.workflow_id,
            "timestamp": chrono::Utc::now().to_rfc3339(),
        });
        
        ctx.text(response.to_string());
        
        // 立即发送当前工作流状态
        self.send_current_workflow_state(ctx);
        
        // 设置心跳检查
        ctx.run_interval(Duration::from_secs(30), |act, ctx| {
            ctx.ping(b"");
            
            // 更新最后活动时间
            act.last_activity.store(chrono::Utc::now().timestamp(), Ordering::Relaxed);
        });
    }
    
    fn stopping(&mut self, _: &mut Self::Context) -> Running {
        // 从活动连接中移除
        tokio::spawn({
            let active_connections = self.active_connections.clone();
            let id = self.id.clone();
            let user_id = self.user_id.clone();
            let metrics_collector = self.metrics_collector.clone();
            
            async move {
                let mut connections = active_connections.write().await;
                
                if let Some(user_connections) = connections.get_mut(&user_id) {
                    if let Some(pos) = user_connections.iter().position(|c| c.id == id) {
                        user_connections.remove(pos);
                    }
                    
                    // 如果用户没有更多连接，移除用户条目
                    if user_connections.is_empty() {
                        connections.remove(&user_id);
                    }
                }
                
                // 记录连接关闭指标
                let mut labels = HashMap::new();
                labels.insert("reason".to_string(), "closed".to_string());
                labels.insert("type".to_string(), "visualization".to_string());
                
                if let Err(e) = metrics_collector.increment_counter(
                    "websocket_connections_closed_total",
                    "Total number of closed WebSocket connections",
                    labels,
                    1
                ) {
                    log::warn!("记录WebSocket连接关闭指标失败: {}", e);
                }
                
                log::info!("工作流可视化WebSocket连接关闭: {}", id);
            }
        });
        
        Running::Stop
    }
}

impl StreamHandler<Result<ws::Message, ws::ProtocolError>> for WorkflowVisualizationActor {
    fn handle(&mut self, msg: Result<ws::Message, ws::ProtocolError>, ctx: &mut Self::Context) {
        // 更新最后活动时间
        self.last_activity.store(chrono::Utc::now().timestamp(), Ordering::Relaxed);
        
        match msg {
            Ok(ws::Message::Ping(msg)) => {
                ctx.pong(&msg);
            }
            Ok(ws::Message::Pong(_)) => {
                // 忽略Pong响应
            }
            Ok(ws::Message::Text(text)) => {
                // 处理客户端消息
                match serde_json::from_str::<WebSocketClientMessage>(&text) {
                    Ok(client_msg) => self.handle_client_message(client_msg, ctx),
                    Err(e) => {
                        log::warn!("无法解析WebSocket客户端消息: {}", e);
                        
                        let error_response = serde_json::json!({
                            "type": "error",
                            "error": "无法解析消息",
                            "details": e.to_string(),
                            "timestamp": chrono::Utc::now().to_rfc3339(),
                        });
                        
                        ctx.text(error_response.to_string());
                    }
                }
            }
            Ok(ws::Message::Binary(_)) => {
                // 暂不支持二进制消息
                let error_response = serde_json::json!({
                    "type": "error",
                    "error": "不支持二进制消息",
                    "timestamp": chrono::Utc::now().to_rfc3339(),
                });
                
                ctx.text(error_response.to_string());
            }
            Ok(ws::Message::Close(reason)) => {
                // 客户端请求关闭连接
                ctx.close(reason);
            }
            _ => {
                // 忽略其他消息类型
            }
        }
    }
}

impl WorkflowVisualizationActor {
    // 处理客户端消息
    fn handle_client_message(&self, msg: WebSocketClientMessage, ctx: &mut ws::WebsocketContext<Self>) {
        match msg.message_type.as_str() {
            "ping" => {
                // 响应ping
                let response = serde_json::json!({
                    "type": "pong",
                    "timestamp": chrono::Utc::now().to_rfc3339(),
                });
                
                ctx.text(response.to_string());
            }
            "refresh" => {
                // 刷新工作流状态
                self.send_current_workflow_state(ctx);
            }
            _ => {
                // 未知消息类型
                let error_response = serde_json::json!({
                    "type": "error",
                    "error": "未知消息类型",
                    "details": format!("不支持的消息类型: {}", msg.message_type),
                    "timestamp": chrono::Utc::now().to_rfc3339(),
                });
                
                ctx.text(error_response.to_string());
            }
        }
    }
    
    // 发送当前工作流状态
    fn send_current_workflow_state(&self, ctx: &mut ws::WebsocketContext<Self>) {
        let workflow_id = self.workflow_id.clone();
        let workflow_service = self.workflow_service.clone();
        
        // 异步获取工作流状态
        ctx.spawn(
            async move {
                // 获取详细的工作流状态，包括任务和变量
                match workflow_service.get_workflow_status(&workflow_id, true, true, None).await {
                    Ok(status) => {
                        // 构建工作流可视化状态
                        let visualization = WorkflowVisualization {
                            workflow_id: workflow_id.clone(),
                            name: status.name.clone(),
                            status: status.status.clone(),
                            nodes: status.tasks.unwrap_or_default()
                                .into_iter()
                                .map(|task| WorkflowNode {
                                    id: task.id,
                                    name: task.name,
                                    task_type: task.task_type,
                                    status: task.status,
                                    started_at: task.started_at,
                                    completed_at: task.completed_at,
                                    details: task.details,
                                })
                                .collect(),
                            edges: Vec::new(), // 需要根据实际工作流定义构建边
                            variables: status.variables,
                            stats: WorkflowStats {
                                total_nodes: status.total_tasks.unwrap_or(0),
                                completed_nodes: status.completed_tasks.unwrap_or(0),
                                failed_nodes: status.failed_tasks.unwrap_or(0),
                                current_state: status.current_state.unwrap_or_default(),
                                elapsed_time: status.elapsed_time,
                                remaining_time: status.estimated_remaining_time,
                            },
                        };
                        
                        // 获取边信息
                        if let Ok(edges) = workflow_service.get_workflow_edges(&workflow_id).await {
                            let mut vis = visualization;
                            vis.edges = edges;
                            return Some(WsMessage::WorkflowVisualization(vis));
                        }
                        
                        return Some(WsMessage::WorkflowVisualization(visualization));
                    },
                    Err(e) => {
                        log::error!("获取工作流状态失败: {}", e);
                        
                        let error_message = serde_json::json!({
                            "type": "error",
                            "error": "获取工作流状态失败",
                            "details": e.to_string(),
                            "timestamp": chrono::Utc::now().to_rfc3339(),
                        });
                        
                        return Some(WsMessage::Text(error_message.to_string()));
                    }
                }
            }
            .into_actor(self)
            .then(|result, _, ctx| {
                if let Some(message) = result {
                    match message {
                        WsMessage::WorkflowVisualization(vis) => {
                            let json = serde_json::json!({
                                "type": "workflow_visualization",
                                "data": vis,
                                "timestamp": chrono::Utc::now().to_rfc3339(),
                            });
                            ctx.text(json.to_string());
                        },
                        WsMessage::Text(text) => {
                            ctx.text(text);
                        },
                        _ => {}
                    }
                }
                fut::ready(())
            })
        );
    }
}

// WebSocket 消息类型
enum WsMessage {
    Text(String),
    Notification(Notification),
    WorkflowStatus(String, WorkflowStatus),
    WorkflowVisualization(WorkflowVisualization),
    Close,
}

impl Message for WsMessage {
    type Result = ();
}

impl Handler<WsMessage> for WebSocketActor {
    type Result = ();
    
    fn handle(&mut self, msg: WsMessage, ctx: &mut Self::Context) {
        match msg {
            WsMessage::Text(text) => {
                ctx.text(text);
            },
            WsMessage::Notification(notification) => {
                // 发送通知
                let json = serde_json::json!({
                    "type": "notification",
                    "notification": notification,
                    "timestamp": chrono::Utc::now().to_rfc3339(),
                });
                ctx.text(json.to_string());
            },
            WsMessage::WorkflowStatus(workflow_id, status) => {
                // 发送工作流状态更新
                let json = serde_json::json!({
                    "type": "workflow_status",
                    "workflow_id": workflow_id,
                    "status": status,
                    "timestamp": chrono::Utc::now().to_rfc3339(),
                });
                ctx.text(json.to_string());
            },
            WsMessage::Close => {
                ctx.close(None);
            },
            _ => {}
        }
    }
}

impl Handler<WsMessage> for WorkflowVisualizationActor {
    type Result = ();
    
    fn handle(&mut self, msg: WsMessage, ctx: &mut Self::Context) {
        match msg {
            WsMessage::Text(text) => {
                ctx.text(text);
            },
            WsMessage::WorkflowStatus(workflow_id, status) => {
                // 只处理与当前工作流相关的状态更新
                if workflow_id == self.workflow_id {
                    // 发送状态更新
                    let json = serde_json::json!({
                        "type": "workflow_status_update",
                        "status": status,
                        "timestamp": chrono::Utc::now().to_rfc3339(),
                    });
                    ctx.text(json.to_string());
                }
            },
            WsMessage::WorkflowVisualization(visualization) => {
                // 发送可视化数据
                let json = serde_json::json!({
                    "type": "workflow_visualization",
                    "data": visualization,
                    "timestamp": chrono::Utc::now().to_rfc3339(),
                });
                ctx.text(json.to_string());
            },
            WsMessage::Close => {
                ctx.close(None);
            },
            _ => {}
        }
    }
}

// 客户端消息模型
#[derive(Deserialize)]
struct WebSocketClientMessage {
    message_type: String,
    #[serde(default)]
    data: HashMap<String, serde_json::Value>,
}

// 通知模型
#[derive(Clone, Serialize, Deserialize)]
struct Notification {
    notification_id: String,
    notification_type: String,
    title: String,
    message: String,
    severity: NotificationSeverity,
    data: Option<serde_json::Value>,
    target_user_id: Option<String>,
    created_at: chrono::DateTime<chrono::Utc>,
    expires_at: Option<chrono::DateTime<chrono::Utc>>,
}

#[derive(Clone, Serialize, Deserialize)]
enum NotificationSeverity {
    Info,
    Success,
    Warning,
    Error,
}

// 工作流可视化模型
#[derive(Clone, Serialize, Deserialize)]
struct WorkflowVisualization {
    workflow_id: String,
    name: String,
    status: String,
    nodes: Vec<WorkflowNode>,
    edges: Vec<WorkflowEdge>,
    variables: Option<HashMap<String, serde_json::Value>>,
    stats: WorkflowStats,
}

#[derive(Clone, Serialize, Deserialize)]
struct WorkflowNode {
    id: String,
    name: String,
    task_type: String,
    status: String,
    started_at: Option<chrono::DateTime<chrono::Utc>>,
    completed_at: Option<chrono::DateTime<chrono::Utc>>,
    details: Option<serde_json::Value>,
}

#[derive(Clone, Serialize, Deserialize)]
struct WorkflowEdge {
    source: String,
    target: String,
    condition: Option<String>,
    traversed: bool,
}

#[derive(Clone, Serialize, Deserialize)]
struct WorkflowStats {
    total_nodes: u32,
    completed_nodes: u32,
    failed_nodes: u32,
    current_state: String,
    elapsed_time: Option<u64>,
    remaining_time: Option<u64>,
}

// 连接统计
#[derive(Serialize)]
struct ConnectionStats {
    total_connections: usize,
    users_count: usize,
    connection_types: HashMap<String, usize>,
}

// WebSocket 错误
#[derive(Debug, thiserror::Error)]
pub enum WebSocketError {
    #[error("发送错误: {0}")]
    SendError(String),
    
    #[error("连接错误: {0}")]
    ConnectionError(String),
    
    #[error("序列化错误: {0}")]
    SerializationError(String),
}
```

WebSocket接口的优势：

1. **实时更新**：工作流执行状态的即时更新
2. **交互式可视化**：提供动态的工作流执行视图
3. **订阅机制**：灵活的通知类型订阅
4. **心跳检测**：保持连接活跃和检测断开
5. **自动清理**：移除空闲和超时连接
6. **多用户支持**：每个用户可以维护多个独立连接
7. **指标收集**：连接和消息传递的性能监控

### 14.3 命令行接口

实现命令行工具以便于管理和操作：

```rust
mod cli {
    use clap::{Parser, Subcommand};
    use std::path::PathBuf;

    #[derive(Parser)]
    #[clap(author, version, about)]
    pub struct Cli {
        /// API服务器地址
        #[clap(short, long, default_value = "http://localhost:8080")]
        pub server: String,

        /// 验证令牌
        #[clap(short, long, env = "WORKFLOW_CLI_TOKEN")]
        pub token: Option<String>,

        /// 命令
        #[clap(subcommand)]
        pub command: Commands,
    }

    #[derive(Subcommand)]
    pub enum Commands {
        /// 工作流管理
        Workflow {
            #[clap(subcommand)]
            command: WorkflowCommands,
        },
        
        /// 任务管理
        Task {
            #[clap(subcommand)]
            command: TaskCommands,
        },
        
        /// 节点管理
        Node {
            #[clap(subcommand)]
            command: NodeCommands,
        },
        
        /// 事件管理
        Event {
            #[clap(subcommand)]
            command: EventCommands,
        },
        
        /// 指标管理
        Metrics {
            #[clap(subcommand)]
            command: MetricsCommands,
        },
        
        /// 系统管理
        System {
            #[clap(subcommand)]
            command: SystemCommands,
        },
    }

    #[derive(Subcommand)]
    pub enum WorkflowCommands {
        /// 列出工作流定义
        ListDefinitions {
            /// 页码
            #[clap(short, long, default_value = "1")]
            page: u32,
            
            /// 每页数量
            #[clap(short, long, default_value = "20")]
            limit: u32,
            
            /// 过滤条件
            #[clap(short, long)]
            filter: Option<String>,
        },
        
        /// 注册工作流定义
        RegisterDefinition {
            /// 定义文件路径
            #[clap(short, long)]
            file: PathBuf,
        },
        
        /// 删除工作流定义
        DeleteDefinition {
            /// 工作流定义ID
            #[clap(required = true)]
            id: String,
        },
        
        /// 验证工作流定义
        ValidateDefinition {
            /// 定义文件路径
            #[clap(short, long)]
            file: PathBuf,
        },
        
        /// 列出工作流实例
        ListInstances {
            /// 页码
            #[clap(short, long, default_value = "1")]
            page: u32,
            
            /// 每页数量
            #[clap(short, long, default_value = "20")]
            limit: u32,
            
            /// 状态过滤
            #[clap(short, long)]
            status: Option<String>,
            
            /// 工作流定义ID过滤
            #[clap(short, long)]
            definition: Option<String>,
        },
        
        /// 启动工作流
        Start {
            /// 工作流定义ID
            #[clap(required = true)]
            definition_id: String,
            
            /// 版本
            #[clap(short, long)]
            version: Option<String>,
            
            /// 输入数据文件路径
            #[clap(short, long)]
            input: Option<PathBuf>,
            
            /// 关联ID
            #[clap(short, long)]
            correlation: Option<String>,
            
            /// 优先级(1-10)
            #[clap(short, long)]
            priority: Option<u8>,
        },
        
        /// 获取工作流状态
        Status {
            /// 工作流实例ID
            #[clap(required = true)]
            id: String,
            
            /// 是否包含任务详情
            #[clap(short, long)]
            include_tasks: bool,
            
            /// 是否包含变量
            #[clap(short, long)]
            include_variables: bool,
        },
        
        /// 取消工作流
        Cancel {
            /// 工作流实例ID
            #[clap(required = true)]
            id: String,
            
            /// 取消原因
            #[clap(short, long)]
            reason: Option<String>,
        },
        
        /// 暂停工作流
        Pause {
            /// 工作流实例ID
            #[clap(required = true)]
            id: String,
            
            /// 暂停原因
            #[clap(short, long)]
            reason: Option<String>,
        },
        
        /// 恢复工作流
        Resume {
            /// 工作流实例ID
            #[clap(required = true)]
            id: String,
        },
        
        /// 重试工作流
        Retry {
            /// 工作流实例ID
            #[clap(required = true)]
            id: String,
            
            /// 从特定活动开始重试
            #[clap(short, long)]
            from_activity: Option<String>,
        },
        
        /// 发送信号
        Signal {
            /// 工作流实例ID
            #[clap(required = true)]
            id: String,
            
            /// 信号名称
            #[clap(short, long, required = true)]
            name: String,
            
            /// 信号数据文件路径
            #[clap(short, long)]
            data: Option<PathBuf>,
        },
        
        /// 获取工作流历史
        History {
            /// 工作流实例ID
            #[clap(required = true)]
            id: String,
        },
        
        /// 获取工作流指标
        Metrics {
            /// 工作流实例ID
            #[clap(required = true)]
            id: String,
            
            /// 开始时间
            #[clap(short, long)]
            start_time: Option<String>,
            
            /// 结束时间
            #[clap(short, long)]
            end_time: Option<String>,
        },
    }

    #[derive(Subcommand)]
    pub enum TaskCommands {
        /// 列出任务
        List {
            /// 页码
            #[clap(short, long, default_value = "1")]
            page: u32,
            
            /// 每页数量
            #[clap(short, long, default_value = "20")]
            limit: u32,
            
            /// 状态过滤
            #[clap(short, long)]
            status: Option<String>,
            
            /// 任务类型过滤
            #[clap(short, long)]
            task_type: Option<String>,
            
            /// 处理人过滤
            #[clap(short, long)]
            assignee: Option<String>,
        },
        
        /// 获取任务状态
        Status {
            /// 任务ID
            #[clap(required = true)]
            id: String,
        },
        
        /// 完成任务
        Complete {
            /// 任务ID
            #[clap(required = true)]
            id: String,
            
            /// 输出数据文件路径
            #[clap(short, long)]
            output: Option<PathBuf>,
        },
        
        /// 任务失败
        Fail {
            /// 任务ID
            #[clap(required = true)]
            id: String,
            
            /// 错误消息
            #[clap(short, long, required = true)]
            error: String,
            
            /// 详细信息文件路径
            #[clap(short, long)]
            details: Option<PathBuf>,
        },
        
        /// 认领任务
        Claim {
            /// 任务ID
            #[clap(required = true)]
            id: String,
            
            /// 处理人
            #[clap(short, long)]
            assignee: Option<String>,
        },
    }

    #[derive(Subcommand)]
    pub enum NodeCommands {
        /// 列出节点
        List,
        
        /// 获取节点详情
        Info {
            /// 节点ID
            #[clap(required = true)]
            id: String,
        },
    }

    #[derive(Subcommand)]
    pub enum EventCommands {
        /// 发布事件
        Publish {
            /// 事件类型
            #[clap(short, long, required = true)]
            event_type: String,
            
            /// 事件数据文件路径
            #[clap(short, long, required = true)]
            data: PathBuf,
            
            /// 关联ID
            #[clap(short, long)]
            correlation: Option<String>,
        },
        
        /// 创建事件订阅
        Subscribe {
            /// 事件类型
            #[clap(short, long, required = true)]
            event_type: String,
            
            /// 回调URL
            #[clap(short, long, required = true)]
            callback: String,
            
            /// 过滤条件文件路径
            #[clap(short, long)]
            filter: Option<PathBuf>,
        },
        
        /// 列出事件订阅
        ListSubscriptions {
            /// 事件类型过滤
            #[clap(short, long)]
            event_type: Option<String>,
        },
        
        /// 删除事件订阅
        Unsubscribe {
            /// 订阅ID
            #[clap(required = true)]
            id: String,
        },
    }

    #[derive(Subcommand)]
    pub enum MetricsCommands {
        /// 获取任务指标
        Tasks {
            /// 开始时间
            #[clap(short, long)]
            start_time: Option<String>,
            
            /// 结束时间
            #[clap(short, long)]
            end_time: Option<String>,
            
            /// 任务类型
            #[clap(short, long)]
            task_type: Option<String>,
            
            /// 分组方式
            #[clap(short, long)]
            group_by: Option<String>,
        },
        
        /// 获取系统指标
        System {
            /// 指标类型
            #[clap(short, long)]
            metric_type: Option<String>,
            
            /// 开始时间
            #[clap(short, long)]
            start_time: Option<String>,
            
            /// 结束时间
            #[clap(short, long)]
            end_time: Option<String>,
            
            /// 间隔(秒)
            #[clap(short, long, default_value = "60")]
            interval: u32,
        },
    }

    #[derive(Subcommand)]
    pub enum SystemCommands {
        /// 健康检查
        HealthCheck,
        
        /// 获取系统配置
        GetConfig,
        
        /// 更新系统配置
        UpdateConfig {
            /// 配置文件路径
            #[clap(short, long, required = true)]
            file: PathBuf,
        },
    }
}

mod client {
    use std::error::Error;
    use std::fs;
    use std::path::Path;
    use reqwest::{Client, StatusCode};
    use serde::{Serialize, Deserialize};
    use serde_json::Value;
    
    pub struct ApiClient {
        base_url: String,
        token: Option<String>,
        client: Client,
    }
    
    impl ApiClient {
        pub fn new(base_url: &str, token: Option<String>) -> Self {
            Self {
                base_url: base_url.to_string(),
                token,
                client: Client::new(),
            }
        }
        
        // 构建授权头
        fn auth_header(&self) -> Option<String> {
            self.token.as_ref().map(|token| format!("Bearer {}", token))
        }
        
        // 读取JSON文件
        fn read_json_file<P: AsRef<Path>>(&self, path: P) -> Result<Value, Box<dyn Error>> {
            let content = fs::read_to_string(path)?;
            let json: Value = serde_json::from_str(&content)?;
            Ok(json)
        }
        
        // ====== 工作流定义管理 ======
        
// 列出工作流定义
pub async fn list_workflow_definitions(&self, page: u32, limit: u32, filter: Option<&str>) -> Result<Value, Box<dyn Error>> {
    let mut url = format!("{}/api/v1/workflow-definitions?page={}&per_page={}", 
        self.base_url, page, limit);
        
    if let Some(f) = filter {
        url.push_str(&format!("&filter={}", f));
    }
    
    let mut req = self.client.get(&url);
    
    if let Some(auth) = self.auth_header() {
        req = req.header("Authorization", auth);
    }
    
    let resp = req.send().await?;
    self.handle_response(resp).await
}

// 注册工作流定义
pub async fn register_workflow_definition<P: AsRef<Path>>(&self, file_path: P) -> Result<Value, Box<dyn Error>> {
    let definition = self.read_json_file(file_path)?;
    
    let url = format!("{}/api/v1/workflow-definitions", self.base_url);
    
    let mut req = self.client.post(&url)
        .json(&definition);
    
    if let Some(auth) = self.auth_header() {
        req = req.header("Authorization", auth);
    }
    
    let resp = req.send().await?;
    self.handle_response(resp).await
}

// 删除工作流定义
pub async fn delete_workflow_definition(&self, id: &str) -> Result<Value, Box<dyn Error>> {
    let url = format!("{}/api/v1/workflow-definitions/{}", self.base_url, id);
    
    let mut req = self.client.delete(&url);
    
    if let Some(auth) = self.auth_header() {
        req = req.header("Authorization", auth);
    }
    
    let resp = req.send().await?;
    self.handle_response(resp).await
}

// 验证工作流定义
pub async fn validate_workflow_definition<P: AsRef<Path>>(&self, file_path: P) -> Result<Value, Box<dyn Error>> {
    let definition = self.read_json_file(file_path)?;
    
    let url = format!("{}/api/v1/workflow-definitions/validate", self.base_url);
    
    let mut req = self.client.post(&url)
        .json(&serde_json::json!({
            "definition": definition
        }));
    
    if let Some(auth) = self.auth_header() {
        req = req.header("Authorization", auth);
    }
    
    let resp = req.send().await?;
    self.handle_response(resp).await
}

// ====== 工作流实例管理 ======

// 列出工作流实例
pub async fn list_workflow_instances(&self, page: u32, limit: u32, status: Option<&str>, definition_id: Option<&str>) -> Result<Value, Box<dyn Error>> {
    let mut url = format!("{}/api/v1/workflows?page={}&per_page={}", 
        self.base_url, page, limit);
        
    if let Some(s) = status {
        url.push_str(&format!("&status={}", s));
    }
    
    if let Some(d) = definition_id {
        url.push_str(&format!("&definition_id={}", d));
    }
    
    let mut req = self.client.get(&url);
    
    if let Some(auth) = self.auth_header() {
        req = req.header("Authorization", auth);
    }
    
    let resp = req.send().await?;
    self.handle_response(resp).await
}

// 启动工作流
pub async fn start_workflow(&self, definition_id: &str, version: Option<&str>, input_file: Option<P>, correlation_id: Option<&str>, priority: Option<u8>) -> Result<Value, Box<dyn Error>> 
    where P: AsRef<Path>
{
    let mut request = serde_json::json!({
        "definition_id": definition_id
    });
    
    if let Some(v) = version {
        request["version"] = v.into();
    }
    
    if let Some(input_path) = input_file {
        let input = self.read_json_file(input_path)?;
        request["input"] = input;
    }
    
    if let Some(c) = correlation_id {
        request["correlation_id"] = c.into();
    }
    
    if let Some(p) = priority {
        request["priority"] = p.into();
    }
    
    let url = format!("{}/api/v1/workflows", self.base_url);
    
    let mut req = self.client.post(&url)
        .json(&request);
    
    if let Some(auth) = self.auth_header() {
        req = req.header("Authorization", auth);
    }
    
    let resp = req.send().await?;
    self.handle_response(resp).await
}

// 获取工作流状态
pub async fn get_workflow_status(&self, id: &str, include_tasks: bool, include_variables: bool) -> Result<Value, Box<dyn Error>> {
    let url = format!("{}/api/v1/workflows/{}?include_tasks={}&include_variables={}", 
        self.base_url, id, include_tasks, include_variables);
    
    let mut req = self.client.get(&url);
    
    if let Some(auth) = self.auth_header() {
        req = req.header("Authorization", auth);
    }
    
    let resp = req.send().await?;
    self.handle_response(resp).await
}

// 取消工作流
pub async fn cancel_workflow(&self, id: &str, reason: Option<&str>) -> Result<Value, Box<dyn Error>> {
    let request = serde_json::json!({
        "reason": reason
    });
    
    let url = format!("{}/api/v1/workflows/{}/cancel", self.base_url, id);
    
    let mut req = self.client.post(&url)
        .json(&request);
    
    if let Some(auth) = self.auth_header() {
        req = req.header("Authorization", auth);
    }
    
    let resp = req.send().await?;
    self.handle_response(resp).await
}

// 暂停工作流
pub async fn pause_workflow(&self, id: &str, reason: Option<&str>) -> Result<Value, Box<dyn Error>> {
    let request = serde_json::json!({
        "reason": reason
    });
    
    let url = format!("{}/api/v1/workflows/{}/pause", self.base_url, id);
    
    let mut req = self.client.post(&url)
        .json(&request);
    
    if let Some(auth) = self.auth_header() {
        req = req.header("Authorization", auth);
    }
    
    let resp = req.send().await?;
    self.handle_response(resp).await
}

// 恢复工作流
pub async fn resume_workflow(&self, id: &str) -> Result<Value, Box<dyn Error>> {
    let url = format!("{}/api/v1/workflows/{}/resume", self.base_url, id);
    
    let mut req = self.client.post(&url)
        .json(&serde_json::json!({}));
    
    if let Some(auth) = self.auth_header() {
        req = req.header("Authorization", auth);
    }
    
    let resp = req.send().await?;
    self.handle_response(resp).await
}

// 重试工作流
pub async fn retry_workflow(&self, id: &str, from_activity: Option<&str>) -> Result<Value, Box<dyn Error>> {
    let mut request = serde_json::json!({});
    
    if let Some(activity) = from_activity {
        request["from_activity"] = activity.into();
    }
    
    let url = format!("{}/api/v1/workflows/{}/retry", self.base_url, id);
    
    let mut req = self.client.post(&url)
        .json(&request);
    
    if let Some(auth) = self.auth_header() {
        req = req.header("Authorization", auth);
    }
    
    let resp = req.send().await?;
    self.handle_response(resp).await
}

// 发送信号
pub async fn send_signal(&self, id: &str, signal_name: &str, data_file: Option<P>) -> Result<Value, Box<dyn Error>> 
    where P: AsRef<Path>
{
    let mut request = serde_json::json!({
        "signal_name": signal_name
    });
    
    if let Some(data_path) = data_file {
        let data = self.read_json_file(data_path)?;
        request["signal_data"] = data;
    }
    
    let url = format!("{}/api/v1/workflows/{}/signal", self.base_url, id);
    
    let mut req = self.client.post(&url)
        .json(&request);
    
    if let Some(auth) = self.auth_header() {
        req = req.header("Authorization", auth);
    }
    
    let resp = req.send().await?;
    self.handle_response(resp).await
}

// 获取工作流历史
pub async fn get_workflow_history(&self, id: &str) -> Result<Value, Box<dyn Error>> {
    let url = format!("{}/api/v1/workflows/{}/history", self.base_url, id);
    
    let mut req = self.client.get(&url);
    
    if let Some(auth) = self.auth_header() {
        req = req.header("Authorization", auth);
    }
    
    let resp = req.send().await?;
    self.handle_response(resp).await
}

// ====== 任务管理 ======

// 列出任务
pub async fn list_tasks(&self, page: u32, limit: u32, status: Option<&str>, task_type: Option<&str>, assignee: Option<&str>) -> Result<Value, Box<dyn Error>> {
    let mut url = format!("{}/api/v1/tasks?page={}&per_page={}", 
        self.base_url, page, limit);
        
    if let Some(s) = status {
        url.push_str(&format!("&status={}", s));
    }
    
    if let Some(t) = task_type {
        url.push_str(&format!("&task_type={}", t));
    }
    
    if let Some(a) = assignee {
        url.push_str(&format!("&assignee={}", a));
    }
    
    let mut req = self.client.get(&url);
    
    if let Some(auth) = self.auth_header() {
        req = req.header("Authorization", auth);
    }
    
    let resp = req.send().await?;
    self.handle_response(resp).await
}

// 获取任务状态
pub async fn get_task_status(&self, id: &str) -> Result<Value, Box<dyn Error>> {
    let url = format!("{}/api/v1/tasks/{}", self.base_url, id);
    
    let mut req = self.client.get(&url);
    
    if let Some(auth) = self.auth_header() {
        req = req.header("Authorization", auth);
    }
    
    let resp = req.send().await?;
    self.handle_response(resp).await
}

// 完成任务
pub async fn complete_task(&self, id: &str, output_file: Option<P>) -> Result<Value, Box<dyn Error>> 
    where P: AsRef<Path>
{
    let mut request = serde_json::json!({});
    
    if let Some(output_path) = output_file {
        let output = self.read_json_file(output_path)?;
        request["output"] = output;
    }
    
    let url = format!("{}/api/v1/tasks/{}/complete", self.base_url, id);
    
    let mut req = self.client.post(&url)
        .json(&request);
    
    if let Some(auth) = self.auth_header() {
        req = req.header("Authorization", auth);
    }
    
    let resp = req.send().await?;
    self.handle_response(resp).await
}

// 任务失败
pub async fn fail_task(&self, id: &str, error: &str, details_file: Option<P>) -> Result<Value, Box<dyn Error>> 
    where P: AsRef<Path>
{
    let mut request = serde_json::json!({
        "error": error
    });
    
    if let Some(details_path) = details_file {
        let details = self.read_json_file(details_path)?;
        request["details"] = details;
    }
    
    let url = format!("{}/api/v1/tasks/{}/fail", self.base_url, id);
    
    let mut req = self.client.post(&url)
        .json(&request);
    
    if let Some(auth) = self.auth_header() {
        req = req.header("Authorization", auth);
    }
    
    let resp = req.send().await?;
    self.handle_response(resp).await
}

// 认领任务
pub async fn claim_task(&self, id: &str, assignee: Option<&str>) -> Result<Value, Box<dyn Error>> {
    let mut request = serde_json::json!({});
    
    if let Some(a) = assignee {
        request["assignee"] = a.into();
    }
    
    let url = format!("{}/api/v1/tasks/{}/claim", self.base_url, id);
    
    let mut req = self.client.post(&url)
        .json(&request);
    
    if let Some(auth) = self.auth_header() {
        req = req.header("Authorization", auth);
    }
    
    let resp = req.send().await?;
    self.handle_response(resp).await
}

// ====== 节点管理 ======

// 列出节点
pub async fn list_nodes(&self) -> Result<Value, Box<dyn Error>> {
    let url = format!("{}/api/v1/system/nodes", self.base_url);
    
    let mut req = self.client.get(&url);
    
    if let Some(auth) = self.auth_header() {
        req = req.header("Authorization", auth);
    }
    
    let resp = req.send().await?;
    self.handle_response(resp).await
}

// ====== 事件管理 ======

// 发布事件
pub async fn publish_event(&self, event_type: &str, data_file: P, correlation_id: Option<&str>) -> Result<Value, Box<dyn Error>> 
    where P: AsRef<Path>
{
    let data = self.read_json_file(data_file)?;
    
    let mut request = serde_json::json!({
        "event_type": event_type,
        "data": data
    });
    
    if let Some(c) = correlation_id {
        request["correlation_id"] = c.into();
    }
    
    let url = format!("{}/api/v1/events", self.base_url);
    
    let mut req = self.client.post(&url)
        .json(&request);
    
    if let Some(auth) = self.auth_header() {
        req = req.header("Authorization", auth);
    }
    
    let resp = req.send().await?;
    self.handle_response(resp).await
}

// 创建事件订阅
pub async fn create_event_subscription(&self, event_type: &str, callback_url: &str, filter_file: Option<P>) -> Result<Value, Box<dyn Error>> 
    where P: AsRef<Path>
{
    let mut request = serde_json::json!({
        "event_type": event_type,
        "callback_url": callback_url
    });
    
    if let Some(filter_path) = filter_file {
        let filter = self.read_json_file(filter_path)?;
        request["filter"] = filter;
    }
    
    let url = format!("{}/api/v1/events/subscriptions", self.base_url);
    
    let mut req = self.client.post(&url)
        .json(&request);
    
    if let Some(auth) = self.auth_header() {
        req = req.header("Authorization", auth);
    }
    
    let resp = req.send().await?;
    self.handle_response(resp).await
}

// 列出事件订阅
pub async fn list_event_subscriptions(&self, event_type: Option<&str>) -> Result<Value, Box<dyn Error>> {
    let mut url = format!("{}/api/v1/events/subscriptions", self.base_url);
    
    if let Some(t) = event_type {
        url.push_str(&format!("?event_type={}", t));
    }
    
    let mut req = self.client.get(&url);
    
    if let Some(auth) = self.auth_header() {
        req = req.header("Authorization", auth);
    }
    
    let resp = req.send().await?;
    self.handle_response(resp).await
}

// 删除事件订阅
pub async fn delete_event_subscription(&self, id: &str) -> Result<Value, Box<dyn Error>> {
    let url = format!("{}/api/v1/events/subscriptions/{}", self.base_url, id);
    
    let mut req = self.client.delete(&url);
    
    if let Some(auth) = self.auth_header() {
        req = req.header("Authorization", auth);
    }
    
    let resp = req.send().await?;
    self.handle_response(resp).await
}

// ====== 指标管理 ======

// 获取任务指标
pub async fn get_task_metrics(&self, start_time: Option<&str>, end_time: Option<&str>, task_type: Option<&str>, group_by: Option<&str>) -> Result<Value, Box<dyn Error>> {
    let mut url = format!("{}/api/v1/metrics/tasks", self.base_url);
    let mut params = Vec::new();
    
    if let Some(s) = start_time {
        params.push(format!("start_time={}", s));
    }
    
    if let Some(e) = end_time {
        params.push(format!("end_time={}", e));
    }
    
    if let Some(t) = task_type {
        params.push(format!("task_type={}", t));
    }
    
    if let Some(g) = group_by {
        params.push(format!("group_by={}", g));
    }
    
    if !params.is_empty() {
        url.push_str(&format!("?{}", params.join("&")));
    }
    
    let mut req = self.client.get(&url);
    
    if let Some(auth) = self.auth_header() {
        req = req.header("Authorization", auth);
    }
    
    let resp = req.send().await?;
    self.handle_response(resp).await
}

// 获取系统指标
pub async fn get_system_metrics(&self, metric_type: Option<&str>, start_time: Option<&str>, end_time: Option<&str>, interval: u32) -> Result<Value, Box<dyn Error>> {
    let mut url = format!("{}/api/v1/metrics/system", self.base_url);
    let mut params = Vec::new();
    
    if let Some(m) = metric_type {
        params.push(format!("metric_type={}", m));
    }
    
    if let Some(s) = start_time {
        params.push(format!("start_time={}", s));
    }
    
    if let Some(e) = end_time {
        params.push(format!("end_time={}", e));
    }
    
    params.push(format!("interval={}", interval));
    
    if !params.is_empty() {
        url.push_str(&format!("?{}", params.join("&")));
    }
    
    let mut req = self.client.get(&url);
    
    if let Some(auth) = self.auth_header() {
        req = req.header("Authorization", auth);
    }
    
    let resp = req.send().await?;
    self.handle_response(resp).await
}

// ====== 系统管理 ======

// 健康检查
pub async fn health_check(&self) -> Result<Value, Box<dyn Error>> {
    let url = format!("{}/api/v1/system/health", self.base_url);
    
    let resp = self.client.get(&url).send().await?;
    self.handle_response(resp).await
}

// 获取系统配置
pub async fn get_system_config(&self) -> Result<Value, Box<dyn Error>> {
    let url = format!("{}/api/v1/system/config", self.base_url);
    
    let mut req = self.client.get(&url);
    
    if let Some(auth) = self.auth_header() {
        req = req.header("Authorization", auth);
    }
    
    let resp = req.send().await?;
    self.handle_response(resp).await
}

// 更新系统配置
pub async fn update_system_config(&self, config_file: P) -> Result<Value, Box<dyn Error>> 
    where P: AsRef<Path>
{
    let config = self.read_json_file(config_file)?;
    
    let request = serde_json::json!({
        "config": config
    });
    
    let url = format!("{}/api/v1/system/config", self.base_url);
    
    let mut req = self.client.put(&url)
        .json(&request);
    
    if let Some(auth) = self.auth_header() {
        req = req.header("Authorization", auth);
    }
    
    let resp = req.send().await?;
    self.handle_response(resp).await
}

// 处理API响应
async fn handle_response(&self, response: reqwest::Response) -> Result<Value, Box<dyn Error>> {
    let status = response.status();
    let text = response.text().await?;
    
    // 尝试解析JSON响应
    let json_result: Result<Value, _> = serde_json::from_str(&text);
    
    match json_result {
        Ok(json) => {
            if status.is_success() {
                Ok(json)
            } else {
                // API错误
                let error_msg = json["error"].as_str().unwrap_or("未知错误");
                let error_details = json["message"].as_str().unwrap_or("");
                
                Err(format!("API错误 ({}): {} - {}", status.as_u16(), error_msg, error_details).into())
            }
        },
        Err(_) => {
            // 非JSON响应
            if status.is_success() {
                Ok(serde_json::json!({
                    "message": text
                }))
            } else {
                Err(format!("HTTP错误 ({}): {}", status.as_u16(), text).into())
            }
        }
    }
}
}

mod app {
    use std::error::Error;
    use crate::cli::{Cli, Commands, WorkflowCommands, TaskCommands, NodeCommands, EventCommands, MetricsCommands, SystemCommands};
    use crate::client::ApiClient;
    use clap::Parser;
    use colored::*;
    use serde_json::Value;

    pub async fn run() -> Result<(), Box<dyn Error>> {
        // 解析命令行参数
        let cli = Cli::parse();
        
        // 创建API客户端
        let client = ApiClient::new(&cli.server, cli.token);
        
        // 根据命令执行相应操作
        match &cli.command {
            Commands::Workflow { command } => handle_workflow_command(command, &client).await?,
            Commands::Task { command } => handle_task_command(command, &client).await?,
            Commands::Node { command } => handle_node_command(command, &client).await?,
            Commands::Event { command } => handle_event_command(command, &client).await?,
            Commands::Metrics { command } => handle_metrics_command(command, &client).await?,
            Commands::System { command } => handle_system_command(command, &client).await?,
        }
        
        Ok(())
    }
    
    async fn handle_workflow_command(command: &WorkflowCommands, client: &ApiClient) -> Result<(), Box<dyn Error>> {
        match command {
            WorkflowCommands::ListDefinitions { page, limit, filter } => {
                println!("列出工作流定义 (页码: {}, 每页: {})...", page, limit);
                let result = client.list_workflow_definitions(*page, *limit, filter.as_deref()).await?;
                print_json_result(&result, "工作流定义列表");
            },
            WorkflowCommands::RegisterDefinition { file } => {
                println!("注册工作流定义 ({})...", file.display());
                let result = client.register_workflow_definition(file).await?;
                print_json_result(&result, "工作流定义注册结果");
            },
            WorkflowCommands::DeleteDefinition { id } => {
                println!("删除工作流定义 ({})...", id);
                let result = client.delete_workflow_definition(id).await?;
                print_json_result(&result, "工作流定义删除结果");
            },
            WorkflowCommands::ValidateDefinition { file } => {
                println!("验证工作流定义 ({})...", file.display());
                let result = client.validate_workflow_definition(file).await?;
                print_json_result(&result, "工作流定义验证结果");
            },
            WorkflowCommands::ListInstances { page, limit, status, definition } => {
                println!("列出工作流实例 (页码: {}, 每页: {})...", page, limit);
                let result = client.list_workflow_instances(*page, *limit, status.as_deref(), definition.as_deref()).await?;
                print_json_result(&result, "工作流实例列表");
            },
            WorkflowCommands::Start { definition_id, version, input, correlation, priority } => {
                println!("启动工作流 ({})...", definition_id);
                let result = client.start_workflow(definition_id, version.as_deref(), input.as_ref(), correlation.as_deref(), *priority).await?;
                print_json_result(&result, "工作流启动结果");
            },
            WorkflowCommands::Status { id, include_tasks, include_variables } => {
                println!("获取工作流状态 ({})...", id);
                let result = client.get_workflow_status(id, *include_tasks, *include_variables).await?;
                print_json_result(&result, "工作流状态");
            },
            WorkflowCommands::Cancel { id, reason } => {
                println!("取消工作流 ({})...", id);
                let result = client.cancel_workflow(id, reason.as_deref()).await?;
                print_json_result(&result, "工作流取消结果");
            },
            WorkflowCommands::Pause { id, reason } => {
                println!("暂停工作流 ({})...", id);
                let result = client.pause_workflow(id, reason.as_deref()).await?;
                print_json_result(&result, "工作流暂停结果");
            },
            WorkflowCommands::Resume { id } => {
                println!("恢复工作流 ({})...", id);
                let result = client.resume_workflow(id).await?;
                print_json_result(&result, "工作流恢复结果");
            },
            WorkflowCommands::Retry { id, from_activity } => {
                println!("重试工作流 ({})...", id);
                let result = client.retry_workflow(id, from_activity.as_deref()).await?;
                print_json_result(&result, "工作流重试结果");
            },
            WorkflowCommands::Signal { id, name, data } => {
                println!("发送信号 ({}, {})...", id, name);
                let result = client.send_signal(id, name, data.as_ref()).await?;
                print_json_result(&result, "信号发送结果");
            },
            WorkflowCommands::History { id } => {
                println!("获取工作流历史 ({})...", id);
                let result = client.get_workflow_history(id).await?;
                print_json_result(&result, "工作流历史");
            },
            WorkflowCommands::Metrics { id, start_time, end_time } => {
                println!("获取工作流指标 ({})...", id);
                let result = client.get_workflow_metrics(id, start_time.as_deref(), end_time.as_deref()).await?;
                print_json_result(&result, "工作流指标");
            },
        }
        
        Ok(())
    }
    

async fn handle_task_command(command: &TaskCommands, client: &ApiClient) -> Result<(), Box<dyn Error>> {
    match command {
        TaskCommands::List { page, limit, status, task_type, assignee } => {
            println!("列出任务 (页码: {}, 每页: {})...", page, limit);
            let result = client.list_tasks(*page, *limit, status.as_deref(), task_type.as_deref(), assignee.as_deref()).await?;
            print_json_result(&result, "任务列表");
        },
        TaskCommands::Status { id } => {
            println!("获取任务状态 ({})...", id);
            let result = client.get_task_status(id).await?;
            print_json_result(&result, "任务状态");
        },
        TaskCommands::Complete { id, output } => {
            println!("完成任务 ({})...", id);
            let result = client.complete_task(id, output.as_ref()).await?;
            print_json_result(&result, "任务完成结果");
        },
        TaskCommands::Fail { id, error, details } => {
            println!("标记任务失败 ({})...", id);
            let result = client.fail_task(id, error, details.as_ref()).await?;
            print_json_result(&result, "任务失败结果");
        },
        TaskCommands::Claim { id, assignee } => {
            println!("认领任务 ({})...", id);
            let result = client.claim_task(id, assignee.as_deref()).await?;
            print_json_result(&result, "任务认领结果");
        },
    }
    
    Ok(())
}

async fn handle_node_command(command: &NodeCommands, client: &ApiClient) -> Result<(), Box<dyn Error>> {
    match command {
        NodeCommands::List => {
            println!("列出节点...");
            let result = client.list_nodes().await?;
            print_json_result(&result, "节点列表");
        },
        NodeCommands::Info { id } => {
            println!("获取节点信息 ({})...", id);
            let result = client.get_node_info(id).await?;
            print_json_result(&result, "节点信息");
        },
    }
    
    Ok(())
}

async fn handle_event_command(command: &EventCommands, client: &ApiClient) -> Result<(), Box<dyn Error>> {
    match command {
        EventCommands::Publish { event_type, data, correlation } => {
            println!("发布事件 ({})...", event_type);
            let result = client.publish_event(event_type, data, correlation.as_deref()).await?;
            print_json_result(&result, "事件发布结果");
        },
        EventCommands::Subscribe { event_type, callback, filter } => {
            println!("创建事件订阅 ({})...", event_type);
            let result = client.create_event_subscription(event_type, callback, filter.as_ref()).await?;
            print_json_result(&result, "事件订阅结果");
        },
        EventCommands::ListSubscriptions { event_type } => {
            println!("列出事件订阅...");
            let result = client.list_event_subscriptions(event_type.as_deref()).await?;
            print_json_result(&result, "事件订阅列表");
        },
        EventCommands::Unsubscribe { id } => {
            println!("删除事件订阅 ({})...", id);
            let result = client.delete_event_subscription(id).await?;
            print_json_result(&result, "事件订阅删除结果");
        },
    }
    
    Ok(())
}

async fn handle_metrics_command(command: &MetricsCommands, client: &ApiClient) -> Result<(), Box<dyn Error>> {
    match command {
        MetricsCommands::Tasks { start_time, end_time, task_type, group_by } => {
            println!("获取任务指标...");
            let result = client.get_task_metrics(start_time.as_deref(), end_time.as_deref(), task_type.as_deref(), group_by.as_deref()).await?;
            print_json_result(&result, "任务指标");
        },
        MetricsCommands::System { metric_type, start_time, end_time, interval } => {
            println!("获取系统指标...");
            let result = client.get_system_metrics(metric_type.as_deref(), start_time.as_deref(), end_time.as_deref(), *interval).await?;
            print_json_result(&result, "系统指标");
        },
    }
    
    Ok(())
}

async fn handle_system_command(command: &SystemCommands, client: &ApiClient) -> Result<(), Box<dyn Error>> {
    match command {
        SystemCommands::HealthCheck => {
            println!("执行健康检查...");
            let result = client.health_check().await?;
            
            // 特殊处理健康检查结果
            let status = result["status"].as_str().unwrap_or("unknown");
            let message = result["message"].as_str().unwrap_or("");
            
            let status_str = match status {
                "healthy" => status.green(),
                "unhealthy" => status.red(),
                _ => status.yellow(),
            };
            
            println!("健康状态: {}", status_str);
            println!("消息: {}", message);
            
            // 输出组件状态
            if let Some(components) = result["components"].as_object() {
                println!("\n组件状态:");
                
                for (name, component) in components {
                    let component_status = component["status"].as_str().unwrap_or("unknown");
                    let component_message = component["message"].as_str().unwrap_or("");
                    
                    let component_status_str = match component_status {
                        "healthy" => component_status.green(),
                        "unhealthy" => component_status.red(),
                        _ => component_status.yellow(),
                    };
                    
                    println!("  - {}: {} ({})", name, component_status_str, component_message);
                }
            }
        },
        SystemCommands::GetConfig => {
            println!("获取系统配置...");
            let result = client.get_system_config().await?;
            print_json_result(&result, "系统配置");
        },
        SystemCommands::UpdateConfig { file } => {
            println!("更新系统配置 ({})...", file.display());
            let result = client.update_system_config(file).await?;
            print_json_result(&result, "系统配置更新结果");
        },
    }
    
    Ok(())
}

// 美化打印JSON结果
fn print_json_result(result: &Value, title: &str) {
    println!("\n{}", title.bold().blue());
    println!("{}", "=".repeat(title.len()).blue());
    
    let formatted = serde_json::to_string_pretty(result).unwrap_or_else(|_| result.to_string());
    println!("{}", formatted);
}
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 设置日志
    env_logger::init();
    
    // 创建tokio运行时并执行应用
    tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()?
        .block_on(app::run())
}
```

命令行接口的优势：

1. **完整的工作流操作**：支持工作流和任务的全生命周期管理
2. **结构化命令**：使用子命令和参数提供清晰的操作模式
3. **美化输出**：使用彩色和格式化输出增强可读性
4. **文件输入支持**：JSON文件作为复杂输入的载体
5. **错误处理**：提供清晰的错误信息和状态码
6. **令牌认证**：支持环境变量和命令行参数传递认证信息
7. **可脚本化**：便于集成到自动化脚本和CI/CD流程

## 15. 部署与扩展设计

### 15.1 容器化部署

实现Docker容器部署配置：

```dockerfile
# 构建阶段
FROM rust:1.70-slim as builder

WORKDIR /usr/src/app

# 安装构建依赖
RUN apt-get update && apt-get install -y \
    pkg-config \
    libssl-dev \
    && rm -rf /var/lib/apt/lists/*

# 复制Cargo配置文件
COPY Cargo.toml Cargo.lock ./

# 创建空的lib.rs以缓存依赖
RUN mkdir -p src && \
    echo "fn main() {println!(\"placeholder\")}" > src/main.rs && \
    echo "//! Placeholder" > src/lib.rs && \
    cargo build --release && \
    rm -rf src

# 复制源代码
COPY src ./src
COPY config ./config
COPY migrations ./migrations

# 强制重新构建
RUN touch src/main.rs src/lib.rs

# 构建最终二进制文件
RUN cargo build --release

# 运行阶段
FROM debian:12-slim

# 安装运行时依赖
RUN apt-get update && apt-get install -y \
    ca-certificates \
    libssl3 \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /usr/local/bin

# 从构建阶段复制二进制文件
COPY --from=builder /usr/src/app/target/release/workflow-engine .
COPY --from=builder /usr/src/app/config ./config

# 创建工作目录
RUN mkdir -p /data

# 设置环境变量
ENV RUST_LOG=info
ENV CONFIG_FILE=/usr/local/bin/config/default.yaml
ENV DATA_DIR=/data

# 创建非root用户
RUN groupadd -r workflow && useradd -r -g workflow workflow
RUN chown -R workflow:workflow /data

# 切换到非root用户
USER workflow

# 暴露端口
EXPOSE 8080 9091

# 设置健康检查
HEALTHCHECK --interval=30s --timeout=10s --start-period=10s --retries=3 \
    CMD curl -f http://localhost:8080/api/v1/system/health || exit 1

# 启动命令
ENTRYPOINT ["workflow-engine"]
CMD ["server", "--config", "${CONFIG_FILE}"]
```

### 15.2 Kubernetes部署

为分布式部署创建Kubernetes配置：

```yaml
---
# 命名空间
apiVersion: v1
kind: Namespace
metadata:
  name: workflow-system

---
# 配置映射
apiVersion: v1
kind: ConfigMap
metadata:
  name: workflow-config
  namespace: workflow-system
data:
  config.yaml: 
    server:
      host: "0.0.0.0"
      port: 8080
    
    database:
      type: "postgres"
      url: "postgres://postgres:${POSTGRES_PASSWORD}@postgres:5432/workflow"
      pool_size: 10
      max_lifetime: 1800
    
    messaging:
      type: "kafka"
      brokers: "kafka:9092"
      topic_prefix: "workflow"
      consumer_group: "workflow-engine"
    
    tracing:
      enabled: true
      exporter_type: "jaeger"
      jaeger_endpoint: "http://jaeger:14268/api/traces"
      service_name: "workflow-engine"
      service_version: "1.0.0"
      sampling_type: "probability"
      sampling_probability: 0.1
    
    metrics:
      enabled: true
      exporter_type: "prometheus"
      prometheus_port: 9091
    
    cluster:
      node_id: "${NODE_ID}"
      lease_duration_seconds: 30
      heartbeat_interval_seconds: 10
      node_auto_discovery: true
      min_nodes: 1
    
    scheduler:
      poll_interval_ms: 100
      max_concurrent_workflows: 1000
      max_concurrent_tasks_per_node: 200
      default_task_timeout_seconds: 300
    
    storage:
      data_dir: "/data"
      history_retention_days: 30
    
    security:
      jwt_secret: "${JWT_SECRET}"
      admin_token: "${ADMIN_TOKEN}"
      enable_rbac: true
    
    logging:
      level: "info"
      format: "json"

---
# 密钥
apiVersion: v1
kind: Secret
metadata:
  name: workflow-secrets
  namespace: workflow-system
type: Opaque
data:
  postgres_password: cGFzc3dvcmQ=  # 'password' base64编码
  jwt_secret: c2VjcmV0LWtleS1mb3ItandoLXRva2Vucy12ZXJ5LXNlY3VyZQ==
  admin_token: YWRtaW4tdG9rZW4tc3VwZXItc2VjcmV0

---
# 持久卷声明
apiVersion: v1
kind: PersistentVolumeClaim
metadata:
  name: workflow-data
  namespace: workflow-system
spec:
  accessModes:
    - ReadWriteOnce
  resources:
    requests:
      storage: 20Gi
  storageClassName: standard

---
# StatefulSet
apiVersion: apps/v1
kind: StatefulSet
metadata:
  name: workflow-engine
  namespace: workflow-system
spec:
  selector:
    matchLabels:
      app: workflow-engine
  serviceName: "workflow-engine"
  replicas: 3
  podManagementPolicy: Parallel
  updateStrategy:
    type: RollingUpdate
  template:
    metadata:
      labels:
        app: workflow-engine
      annotations:
        prometheus.io/scrape: "true"
        prometheus.io/path: "/metrics"
        prometheus.io/port: "9091"
    spec:
      terminationGracePeriodSeconds: 60
      securityContext:
        runAsUser: 1000
        runAsGroup: 1000
        fsGroup: 1000
      containers:
        - name: workflow-engine
          image: workflow-engine:latest
          imagePullPolicy: IfNotPresent
          ports:
            - containerPort: 8080
              name: http
            - containerPort: 9091
              name: metrics
          env:
            - name: RUST_LOG
              value: "info"
            - name: CONFIG_FILE
              value: "/config/config.yaml"
            - name: DATA_DIR
              value: "/data"
            - name: NODE_ID
              valueFrom:
                fieldRef:
                  fieldPath: metadata.name
            - name: POSTGRES_PASSWORD
              valueFrom:
                secretKeyRef:
                  name: workflow-secrets
                  key: postgres_password
            - name: JWT_SECRET
              valueFrom:
                secretKeyRef:
                  name: workflow-secrets
                  key: jwt_secret
            - name: ADMIN_TOKEN
              valueFrom:
                secretKeyRef:
                  name: workflow-secrets
                  key: admin_token
          resources:
            requests:
              cpu: 200m
              memory: 512Mi
            limits:
              cpu: 1000m
              memory: 2Gi
          volumeMounts:
            - name: config-volume
              mountPath: /config
            - name: data
              mountPath: /data
          livenessProbe:
            httpGet:
              path: /api/v1/system/health
              port: 8080
            initialDelaySeconds: 30
            periodSeconds: 30
            timeoutSeconds: 10
            failureThreshold: 3
          readinessProbe:
            httpGet:
              path: /api/v1/system/health
              port: 8080
            initialDelaySeconds: 10
            periodSeconds: 10
            timeoutSeconds: 5
            failureThreshold: 2
      volumes:
        - name: config-volume
          configMap:
            name: workflow-config
  volumeClaimTemplates:
    - metadata:
        name: data
      spec:
        accessModes: [ "ReadWriteOnce" ]
        storageClassName: "standard"
        resources:
          requests:
            storage: 20Gi

---
# 服务
apiVersion: v1
kind: Service
metadata:
  name: workflow-engine
  namespace: workflow-system
  labels:
    app: workflow-engine
spec:
  type: ClusterIP
  ports:
    - port: 8080
      targetPort: 8080
      protocol: TCP
      name: http
    - port: 9091
      targetPort: 9091
      protocol: TCP
      name: metrics
  selector:
    app: workflow-engine

---
# 水平Pod自动缩放
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: workflow-engine
  namespace: workflow-system
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: StatefulSet
    name: workflow-engine
  minReplicas: 3
  maxReplicas: 10
  metrics:
    - type: Resource
      resource:
        name: cpu
        target:
          type: Utilization
          averageUtilization: 70
    - type: Resource
      resource:
        name: memory
        target:
          type: Utilization
          averageUtilization: 75

---
# 入口
apiVersion: networking.k8s.io/v1
kind: Ingress
metadata:
  name: workflow-engine
  namespace: workflow-system
  annotations:
    kubernetes.io/ingress.class: "nginx"
    nginx.ingress.kubernetes.io/ssl-redirect: "true"
    nginx.ingress.kubernetes.io/proxy-body-size: "50m"
    nginx.ingress.kubernetes.io/proxy-read-timeout: "3600"
    nginx.ingress.kubernetes.io/proxy-send-timeout: "3600"
    cert-manager.io/cluster-issuer: "letsencrypt-prod"
spec:
  tls:
    - hosts:
        - workflow.example.com
      secretName: workflow-tls
  rules:
    - host: workflow.example.com
      http:
        paths:
          - path: /
            pathType: Prefix
            backend:
              service:
                name: workflow-engine
                port:
                  number: 8080

---
# 网络策略
apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: workflow-engine
  namespace: workflow-system
spec:
  podSelector:
    matchLabels:
      app: workflow-engine
  policyTypes:
    - Ingress
    - Egress
  ingress:
    - from:
        - podSelector:
            matchLabels:
              app: nginx-ingress
      ports:
        - protocol: TCP
          port: 8080
    - from:
        - namespaceSelector:
            matchLabels:
              name: monitoring
      ports:
        - protocol: TCP
          port: 9091
    - from:
        - podSelector:
            matchLabels:
              app: workflow-engine
  egress:
    - to:
        - podSelector:
            matchLabels:
              app: postgres
      ports:
        - protocol: TCP
          port: 5432
    - to:
        - podSelector:
            matchLabels:
              app: kafka
      ports:
        - protocol: TCP
          port: 9092
    - to:
        - podSelector:
            matchLabels:
              app: jaeger
      ports:
        - protocol: TCP
          port: 14268
    - to:
        - podSelector:
            matchLabels:
              app: workflow-engine
```

### 15.3 扩展与高可用设计

实现集群节点管理，确保高可用性：

```rust
pub struct ClusterManager {
    node_id: String,
    coordinator: Arc<dyn ClusterCoordinator>,
    lease_manager: Arc<LeaseManager>,
    node_registry: Arc<RwLock<HashMap<String, NodeInfo>>>,
    state: Arc<AtomicU8>,
    metrics_collector: Arc<MetricsCollector>,
    config: ClusterConfig,
}

impl ClusterManager {
    pub fn new(
        node_id: String,
        coordinator: Arc<dyn ClusterCoordinator>,
        metrics_collector: Arc<MetricsCollector>,
        config: ClusterConfig,
    ) -> Self {
        let lease_manager = Arc::new(LeaseManager::new(
            node_id.clone(),
            coordinator.clone(),
            config.lease_duration_seconds,
        ));
        
        Self {
            node_id,
            coordinator,
            lease_manager,
            node_registry: Arc::new(RwLock::new(HashMap::new())),
            state: Arc::new(AtomicU8::new(ClusterState::Starting as u8)),
            metrics_collector,
            config,
        }
    }
    
    // 启动集群管理器
    pub async fn start(&self) -> Result<(), ClusterError> {
        // 注册节点
        self.register_node().await?;
        
        // 启动心跳处理
        self.start_heartbeat_task();
        
        // 启动节点发现任务
        self.start_node_discovery_task();
        
        // 设置状态为运行中
        self.state.store(ClusterState::Running as u8, Ordering::SeqCst);
        
        log::info!("集群管理器已启动，节点ID: {}", self.node_id);
        
        Ok(())
    }
    
    // 注册节点
    async fn register_node(&self) -> Result<(), ClusterError> {
        // 创建节点信息
        let node_info = NodeInfo {
            id: self.node_id.clone(),
            host: gethostname::gethostname().to_string_lossy().to_string(),
            ip: self.get_local_ip()?,
            port: self.config.port,
            status: NodeStatus::Active,
            capabilities: self.config.capabilities.clone(),
            started_at: chrono::Utc::now(),
            last_heartbeat: chrono::Utc::now(),
            metadata: self.config.metadata.clone(),
        };
        
        // 注册到协调器
        self.coordinator.register_node(&node_info).await?;
        
        // 更新本地注册表
        {
            let mut registry = self.node_registry.write().await;
            registry.insert(self.node_id.clone(), node_info);
        }
        
        Ok(())
    }
    
    // 启动心跳任务
    fn start_heartbeat_task(&self) {
        let node_id = self.node_id.clone();
        let lease_manager = self.lease_manager.clone();
        let heartbeat_interval = Duration::from_secs(self.config.heartbeat_interval_seconds);
        let metrics_collector = self.metrics_collector.clone();
        let state = self.state.clone();
        
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(heartbeat_interval);
            
            loop {
                interval.tick().await;
                
                // 检查是否正在运行
                if state.load(Ordering::SeqCst) != ClusterState::Running as u8 {
                    break;
                }
                
                // 更新租约
                match lease_manager.renew_lease().await {
                    Ok(_) => {
                        // 记录成功的心跳
                        let mut labels = HashMap::new();
                        labels.insert("node_id".to_string(), node_id.clone());
                        
                        if let Err(e) = metrics_collector.increment_counter(
                            "cluster_heartbeat_success_total",
                            "Total number of successful cluster heartbeats",
                            labels,
                            1
                        ) {
                            log::warn!("记录集群心跳指标失败: {}", e);
                        }
                    },
                    Err(e) => {
                        log::error!("节点心跳更新失败: {}", e);
                        
                        // 记录失败的心跳
                        let mut labels = HashMap::new();
                        labels.insert("node_id".to_string(), node_id.clone());
                        labels.insert("error".to_string(), e.to_string());
                        
                        if let Err(e) = metrics_collector.increment_counter(
                            "cluster_heartbeat_failure_total",
                            "Total number of failed cluster heartbeats",
                            labels,
                            1
                        ) {
                            log::warn!("记录集群心跳指标失败: {}", e);
                        }
                    }
                }
            }
        });
    }
    
    // 启动节点发现任务
    fn start_node_discovery_task(&self) {
        let coordinator = self.coordinator.clone();
        let node_registry = self.node_registry.clone();
        let discovery_interval = Duration::from_secs(self.config.discovery_interval_seconds);
        let metrics_collector = self.metrics_collector.clone();
        let state = self.state.clone();
        
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(discovery_interval);
            
            loop {
                interval.tick().await;
                
                // 检查是否正在运行
                if state.load(Ordering::SeqCst) != ClusterState::Running as u8 {
                    break;
                }
                
                // 获取所有节点信息
                match coordinator.get_all_nodes().await {
                    Ok(nodes) => {
                        // 更新本地注册表
                        let mut registry = node_registry.write().await;
                        registry.clear();
                        
                        for node in nodes {
                            registry.insert(node.id.clone(), node);
                        }
                        
                        // 记录节点数量指标
                        let active_nodes = registry.values()
                            .filter(|n| n.status == NodeStatus::Active)
                            .count();
                            
                        if let Err(e) = metrics_collector.set_gauge(
                            "cluster_active_nodes",
                            "Number of active nodes in the cluster",
                            HashMap::new(),
                            active_nodes as f64
                        ) {
                            log::warn!("记录集群节点指标失败: {}", e);
                        }
                    },
                    Err(e) => {
                        log::error!("获取集群节点信息失败: {}", e);
                    }
                }
            }
        });
    }
    
    // 获取所有活动节点
    pub async fn get_active_nodes(&self) -> Vec<NodeInfo> {
        let registry = self.node_registry.read().await;
        
        registry.values()
            .filter(|n| n.status == NodeStatus::Active)
            .cloned()
            .collect()
    }
    
    // 获取节点数量
    pub async fn get_node_count(&self) -> usize {
        let registry = self.node_registry.read().await;
        
        registry.values()
            .filter(|n| n.status == NodeStatus::Active)
            .count()
    }
    
    // 检查节点是否可用
    pub async fn is_node_available(&self, node_id: &str) -> bool {
        let registry = self.node_registry.read().await;
        
        registry.get(node_id)
            .map(|n| n.status == NodeStatus::Active)
            .unwrap_or(false)
    }
    
    // 获取本地IP地址
    fn get_local_ip(&self) -> Result<String, ClusterError> {
        use std::net::UdpSocket;
        
        // 此方法用于获取可路由的本地IP地址
        let socket = UdpSocket::bind("0.0.0.0:0")
            .map_err(|e| ClusterError::SystemError(format!("无法绑定UDP套接字: {}", e)))?;
            
        // 连接到公共DNS服务器（不会真正发送数据）
        socket.connect("8.8.8.8:80")
            .map_err(|e| ClusterError::SystemError(format!("无法连接套接字: {}", e)))?;
            
        let addr = socket.local_addr()
            .map_err(|e| ClusterError::SystemError(format!("无法获取本地地址: {}", e)))?;
            
        Ok(addr.ip().to_string())
    }
    
// 关闭集群管理器
pub async fn shutdown(&self) -> Result<(), ClusterError> {
    // 设置状态为关闭中
    self.state.store(ClusterState::Stopping as u8, Ordering::SeqCst);
    
    // 更新节点状态为非活动
    let mut node_info = {
        let registry = self.node_registry.read().await;
        registry.get(&self.node_id).cloned()
    };
    
    if let Some(mut info) = node_info.take() {
        info.status = NodeStatus::Inactive;
        
        // 更新协调器中的节点信息
        if let Err(e) = self.coordinator.update_node(&info).await {
            log::warn!("关闭时更新节点状态失败: {}", e);
        }
    }
    
    // 释放租约
    if let Err(e) = self.lease_manager.release_lease().await {
        log::warn!("释放节点租约失败: {}", e);
    }
    
    // 设置状态为已停止
    self.state.store(ClusterState::Stopped as u8, Ordering::SeqCst);
    
    log::info!("集群管理器已关闭，节点ID: {}", self.node_id);
    
    Ok(())
}

// 获取当前角色
pub async fn get_current_role(&self) -> NodeRole {
    // 检查当前节点是否是领导者
    if self.lease_manager.is_leader().await {
        return NodeRole::Leader;
    }
    
    // 否则为跟随者
    NodeRole::Follower
}

// 获取领导者节点ID
pub async fn get_leader_id(&self) -> Option<String> {
    self.lease_manager.get_leader_id().await
}

// 检查集群健康状态
pub async fn check_health(&self) -> ClusterHealth {
    // 获取所有节点数量
    let registry = self.node_registry.read().await;
    let total_nodes = registry.len();
    let active_nodes = registry.values()
        .filter(|n| n.status == NodeStatus::Active)
        .count();
    
    // 获取领导者节点
    let leader_id = self.lease_manager.get_leader_id().await;
    
    // 确定健康状态
    let status = if active_nodes >= self.config.min_nodes {
        if leader_id.is_some() {
            HealthStatus::Healthy
        } else {
            HealthStatus::Degraded
        }
    } else {
        HealthStatus::Unhealthy
    };
    
    ClusterHealth {
        status,
        total_nodes,
        active_nodes,
        leader_id,
        self_id: self.node_id.clone(),
        self_role: if let Some(leader) = &leader_id {
            if leader == &self.node_id {
                NodeRole::Leader
            } else {
                NodeRole::Follower
            }
        } else {
            NodeRole::Unknown
        },
    }
}
}

// 租约管理器
pub struct LeaseManager {
    node_id: String,
    coordinator: Arc<dyn ClusterCoordinator>,
    lease_duration: u64,
    is_leader: AtomicBool,
}

impl LeaseManager {
    pub fn new(
        node_id: String,
        coordinator: Arc<dyn ClusterCoordinator>,
        lease_duration_seconds: u64,
    ) -> Self {
        Self {
            node_id,
            coordinator,
            lease_duration: lease_duration_seconds,
            is_leader: AtomicBool::new(false),
        }
    }
    
    // 更新租约
    pub async fn renew_lease(&self) -> Result<(), ClusterError> {
        // 尝试获取或更新租约
        let lease_result = self.coordinator.renew_lease(&self.node_id, self.lease_duration).await?;
        
        // 更新领导者状态
        self.is_leader.store(lease_result.is_leader, Ordering::SeqCst);
        
        Ok(())
    }
    
    // 释放租约
    pub async fn release_lease(&self) -> Result<(), ClusterError> {
        // 如果是领导者，释放领导权
        if self.is_leader.load(Ordering::SeqCst) {
            self.coordinator.release_leadership(&self.node_id).await?;
            self.is_leader.store(false, Ordering::SeqCst);
        }
        
        // 释放节点租约
        self.coordinator.release_lease(&self.node_id).await?;
        
        Ok(())
    }
    
    // 检查是否是领导者
    pub async fn is_leader(&self) -> bool {
        self.is_leader.load(Ordering::SeqCst)
    }
    
    // 获取领导者ID
    pub async fn get_leader_id(&self) -> Option<String> {
        self.coordinator.get_leader_id().await.ok()
    }
}

// 集群协调器接口
#[async_trait]
pub trait ClusterCoordinator: Send + Sync {
    // 注册节点
    async fn register_node(&self, node: &NodeInfo) -> Result<(), ClusterError>;
    
    // 更新节点
    async fn update_node(&self, node: &NodeInfo) -> Result<(), ClusterError>;
    
    // 获取所有节点
    async fn get_all_nodes(&self) -> Result<Vec<NodeInfo>, ClusterError>;
    
    // 获取节点信息
    async fn get_node(&self, node_id: &str) -> Result<NodeInfo, ClusterError>;
    
    // 更新节点租约
    async fn renew_lease(&self, node_id: &str, duration_seconds: u64) -> Result<LeaseResult, ClusterError>;
    
    // 释放节点租约
    async fn release_lease(&self, node_id: &str) -> Result<(), ClusterError>;
    
    // 获取领导者ID
    async fn get_leader_id(&self) -> Result<String, ClusterError>;
    
    // 释放领导权
    async fn release_leadership(&self, node_id: &str) -> Result<(), ClusterError>;
}

// Redis集群协调器实现
pub struct RedisCoordinator {
    client: redis::Client,
    namespace: String,
}

impl RedisCoordinator {
    pub fn new(redis_url: &str, namespace: &str) -> Result<Self, ClusterError> {
        let client = redis::Client::open(redis_url)
            .map_err(|e| ClusterError::ConnectionError(format!("Redis连接失败: {}", e)))?;
            
        Ok(Self {
            client,
            namespace: namespace.to_string(),
        })
    }
    
    // 构建节点键
    fn node_key(&self, node_id: &str) -> String {
        format!("{}:nodes:{}", self.namespace, node_id)
    }
    
    // 构建租约键
    fn lease_key(&self, node_id: &str) -> String {
        format!("{}:leases:{}", self.namespace, node_id)
    }
    
    // 构建领导者键
    fn leader_key(&self) -> String {
        format!("{}:leader", self.namespace)
    }
    
    // 构建节点列表键
    fn nodes_list_key(&self) -> String {
        format!("{}:nodes", self.namespace)
    }
}

#[async_trait]
impl ClusterCoordinator for RedisCoordinator {
    async fn register_node(&self, node: &NodeInfo) -> Result<(), ClusterError> {
        let mut conn = self.client.get_async_connection().await
            .map_err(|e| ClusterError::ConnectionError(format!("Redis连接失败: {}", e)))?;
            
        // 序列化节点信息
        let node_data = serde_json::to_string(node)
            .map_err(|e| ClusterError::SerializationError(format!("节点序列化失败: {}", e)))?;
            
        // 使用管道执行多个命令
        redis::pipe()
            // 设置节点信息
            .set(self.node_key(&node.id), &node_data)
            // 添加到节点列表
            .sadd(self.nodes_list_key(), &node.id)
            .query_async(&mut conn).await
            .map_err(|e| ClusterError::OperationError(format!("注册节点失败: {}", e)))?;
            
        Ok(())
    }
    
    async fn update_node(&self, node: &NodeInfo) -> Result<(), ClusterError> {
        let mut conn = self.client.get_async_connection().await
            .map_err(|e| ClusterError::ConnectionError(format!("Redis连接失败: {}", e)))?;
            
        // 序列化节点信息
        let node_data = serde_json::to_string(node)
            .map_err(|e| ClusterError::SerializationError(format!("节点序列化失败: {}", e)))?;
            
        // 更新节点信息
        conn.set(self.node_key(&node.id), node_data).await
            .map_err(|e| ClusterError::OperationError(format!("更新节点失败: {}", e)))?;
            
        Ok(())
    }
    
    async fn get_all_nodes(&self) -> Result<Vec<NodeInfo>, ClusterError> {
        let mut conn = self.client.get_async_connection().await
            .map_err(|e| ClusterError::ConnectionError(format!("Redis连接失败: {}", e)))?;
            
        // 获取所有节点ID
        let node_ids: Vec<String> = conn.smembers(self.nodes_list_key()).await
            .map_err(|e| ClusterError::OperationError(format!("获取节点列表失败: {}", e)))?;
            
        if node_ids.is_empty() {
            return Ok(Vec::new());
        }
        
        // 批量获取节点信息
        let mut pipeline = redis::pipe();
        for node_id in &node_ids {
            pipeline.get(self.node_key(node_id));
        }
        
        let node_data: Vec<Option<String>> = pipeline.query_async(&mut conn).await
            .map_err(|e| ClusterError::OperationError(format!("获取节点数据失败: {}", e)))?;
            
        // 反序列化节点信息
        let mut nodes = Vec::new();
        for data in node_data.into_iter().flatten() {
            match serde_json::from_str::<NodeInfo>(&data) {
                Ok(node) => nodes.push(node),
                Err(e) => log::warn!("节点数据反序列化失败: {}", e),
            }
        }
        
        Ok(nodes)
    }
    
    async fn get_node(&self, node_id: &str) -> Result<NodeInfo, ClusterError> {
        let mut conn = self.client.get_async_connection().await
            .map_err(|e| ClusterError::ConnectionError(format!("Redis连接失败: {}", e)))?;
            
        // 获取节点数据
        let node_data: Option<String> = conn.get(self.node_key(node_id)).await
            .map_err(|e| ClusterError::OperationError(format!("获取节点数据失败: {}", e)))?;
            
        match node_data {
            Some(data) => {
                // 反序列化节点信息
                serde_json::from_str(&data)
                    .map_err(|e| ClusterError::DeserializationError(format!("节点反序列化失败: {}", e)))
            },
            None => Err(ClusterError::NotFoundError(format!("节点 {} 不存在", node_id))),
        }
    }
    
    async fn renew_lease(&self, node_id: &str, duration_seconds: u64) -> Result<LeaseResult, ClusterError> {
        let mut conn = self.client.get_async_connection().await
            .map_err(|e| ClusterError::ConnectionError(format!("Redis连接失败: {}", e)))?;
            
        // 更新节点租约
        let lease_key = self.lease_key(node_id);
        let lease_set: bool = conn.set_ex(lease_key, node_id, duration_seconds as usize).await
            .map_err(|e| ClusterError::OperationError(format!("更新租约失败: {}", e)))?;
            
        if !lease_set {
            return Err(ClusterError::OperationError("设置租约失败".to_string()));
        }
        
        // 检查领导者状态
        let leader_key = self.leader_key();
        let current_leader: Option<String> = conn.get(&leader_key).await
            .map_err(|e| ClusterError::OperationError(format!("获取领导者信息失败: {}", e)))?;
            
        let is_leader = match current_leader {
            Some(leader) if leader == node_id => true,
            Some(_) => false,
            None => {
                // 尝试成为领导者
                let set_leader: bool = redis::cmd("SET")
                    .arg(&leader_key)
                    .arg(node_id)
                    .arg("NX")
                    .arg("EX")
                    .arg(duration_seconds as usize)
                    .query_async(&mut conn).await
                    .map_err(|e| ClusterError::OperationError(format!("设置领导者失败: {}", e)))?;
                    
                if set_leader {
                    log::info!("节点 {} 成为领导者", node_id);
                    true
                } else {
                    false
                }
            }
        };
        
        // 如果是领导者，刷新领导者租约
        if is_leader {
            conn.expire(leader_key, duration_seconds as usize).await
                .map_err(|e| ClusterError::OperationError(format!("更新领导者租约失败: {}", e)))?;
        }
        
        // 更新节点的最后心跳时间
        if let Ok(mut node) = self.get_node(node_id).await {
            node.last_heartbeat = chrono::Utc::now();
            self.update_node(&node).await?;
        }
        
        Ok(LeaseResult { is_leader })
    }
    
    async fn release_lease(&self, node_id: &str) -> Result<(), ClusterError> {
        let mut conn = self.client.get_async_connection().await
            .map_err(|e| ClusterError::ConnectionError(format!("Redis连接失败: {}", e)))?;
            
        // 删除租约
        conn.del(self.lease_key(node_id)).await
            .map_err(|e| ClusterError::OperationError(format!("释放租约失败: {}", e)))?;
            
        Ok(())
    }
    
    async fn get_leader_id(&self) -> Result<String, ClusterError> {
        let mut conn = self.client.get_async_connection().await
            .map_err(|e| ClusterError::ConnectionError(format!("Redis连接失败: {}", e)))?;
            
        // 获取领导者ID
        let leader_id: Option<String> = conn.get(self.leader_key()).await
            .map_err(|e| ClusterError::OperationError(format!("获取领导者信息失败: {}", e)))?;
            
        match leader_id {
            Some(id) => Ok(id),
            None => Err(ClusterError::NotFoundError("当前没有领导者".to_string())),
        }
    }
    
    async fn release_leadership(&self, node_id: &str) -> Result<(), ClusterError> {
        let mut conn = self.client.get_async_connection().await
            .map_err(|e| ClusterError::ConnectionError(format!("Redis连接失败: {}", e)))?;
            
        // 获取当前领导者
        let current_leader: Option<String> = conn.get(self.leader_key()).await
            .map_err(|e| ClusterError::OperationError(format!("获取领导者信息失败: {}", e)))?;
            
        // 只有当前领导者才能释放领导权
        match current_leader {
            Some(leader) if leader == node_id => {
                // 删除领导者键
                conn.del(self.leader_key()).await
                    .map_err(|e| ClusterError::OperationError(format!("释放领导权失败: {}", e)))?;
                
                log::info!("节点 {} 释放了领导权", node_id);
                Ok(())
            },
            Some(leader) => Err(ClusterError::AuthorizationError(
                format!("节点 {} 不是当前领导者 (当前领导者: {})", node_id, leader)
            )),
            None => Ok(()),
        }
    }
}

// 租约结果
#[derive(Debug)]
pub struct LeaseResult {
    pub is_leader: bool,
}

// 节点信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NodeInfo {
    pub id: String,
    pub host: String,
    pub ip: String,
    pub port: u16,
    pub status: NodeStatus,
    pub capabilities: HashMap<String, String>,
    pub started_at: chrono::DateTime<chrono::Utc>,
    pub last_heartbeat: chrono::DateTime<chrono::Utc>,
    pub metadata: HashMap<String, String>,
}

// 节点状态
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum NodeStatus {
    Active,
    Inactive,
    Starting,
    Stopping,
    Failed,
}

// 节点角色
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum NodeRole {
    Leader,
    Follower,
    Unknown,
}

// 集群状态
#[derive(Debug, Clone)]
pub enum ClusterState {
    Starting = 1,
    Running = 2,
    Stopping = 3,
    Stopped = 4,
}

// 健康状态
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum HealthStatus {
    Healthy,
    Degraded,
    Unhealthy,
}

// 集群健康
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ClusterHealth {
    pub status: HealthStatus,
    pub total_nodes: usize,
    pub active_nodes: usize,
    pub leader_id: Option<String>,
    pub self_id: String,
    pub self_role: NodeRole,
}

// 集群配置
#[derive(Debug, Clone)]
pub struct ClusterConfig {
    pub node_id: String,
    pub port: u16,
    pub lease_duration_seconds: u64,
    pub heartbeat_interval_seconds: u64,
    pub discovery_interval_seconds: u64,
    pub min_nodes: usize,
    pub capabilities: HashMap<String, String>,
    pub metadata: HashMap<String, String>,
}

// 集群错误
#[derive(Debug, thiserror::Error)]
pub enum ClusterError {
    #[error("连接错误: {0}")]
    ConnectionError(String),
    
    #[error("操作错误: {0}")]
    OperationError(String),
    
    #[error("序列化错误: {0}")]
    SerializationError(String),
    
    #[error("反序列化错误: {0}")]
    DeserializationError(String),
    
    #[error("未找到: {0}")]
    NotFoundError(String),
    
    #[error("系统错误: {0}")]
    SystemError(String),
    
    #[error("授权错误: {0}")]
    AuthorizationError(String),
}
```

## 16. 总结与展望

### 16.1 系统整体架构回顾

分布式工作流执行引擎的整体架构设计如下：

1. **核心层**
   - 工作流模型与定义
   - 任务调度与执行
   - 状态管理与持久化
   - 事件驱动架构

2. **服务层**
   - 工作流管理服务
   - 任务管理服务
   - 事件服务
   - 系统管理服务

3. **通信与集成层**
   - REST API接口
   - WebSocket实时接口
   - 命令行工具
   - 事件总线

4. **基础设施层**
   - 分布式协调
   - 高可用集群
   - 数据存储
   - 消息队列

5. **可观测性层**
   - 分布式追踪
   - 结构化日志
   - 指标收集
   - 监控告警

6. **安全与治理层**
   - 身份验证与授权
   - 数据加密
   - 审计日志
   - 合规管理

### 16.2 主要特性与优势

本系统设计的主要特性和优势包括：

1. **稳定可靠**
   - 分布式高可用架构
   - 完善的错误处理与恢复机制
   - 数据一致性保证
   - 全面的可观测性

2. **灵活扩展**
   - 模块化设计
   - 插件式扩展点
   - 自定义工作流定义
   - 多种集成方式

3. **高性能**
   - 异步处理模型
   - 高效的任务调度
   - 多级缓存优化
   - 批量处理能力

4. **丰富功能**
   - 复杂工作流支持
   - 人工干预能力
   - 超时与重试策略
   - 事件驱动集成

5. **易于运维**
   - 容器化部署
   - Kubernetes支持
   - 完整的监控与告警
   - 自动化扩缩容

6. **安全合规**
   - 细粒度的访问控制
   - 敏感数据保护
   - 详细的审计跟踪
   - 数据隔离机制

### 16.3 未来发展方向

系统未来的发展方向包括：

1. **增强AI能力**
   - 工作流自动优化
   - 异常预测与处理
   - 智能资源分配
   - 工作流推荐系统

2. **低代码集成**
   - 可视化工作流设计器
   - 拖拽式业务逻辑定义
   - 模板市场
   - 无代码调试能力

3. **边缘计算支持**
   - 边缘节点工作流执行
   - 离线工作模式
   - 边缘-云协同执行
   - 低带宽优化

4. **跨组织协作**
   - 多租户完全隔离
   - 跨组织工作流定义
   - 联邦身份管理
   - 分布式数据共享

5. **高级分析能力**
   - 工作流趋势分析
   - 业务价值衡量
   - 预测性洞察
   - 流程挖掘

6. **行业特化解决方案**
   - 金融行业合规工作流
   - 医疗健康数据处理
   - 制造业供应链优化
   - 政府流程数字化

通过持续创新和迭代，这个分布式工作流执行引擎将不断满足企业对于自动化、可靠性和高效性的需求，并适应未来技术发展和业务变革的挑战。
