# Rust工作流架构设计：数据流、执行流与控制流的融合

## 目录

- [Rust工作流架构设计：数据流、执行流与控制流的融合](#rust工作流架构设计数据流执行流与控制流的融合)
  - [目录](#目录)
  - [1. 架构设计论证过程](#1-架构设计论证过程)
    - [1.1 工作流基本需求分析](#11-工作流基本需求分析)
    - [1.2 Rust类型系统的优势](#12-rust类型系统的优势)
    - [1.3 形式逻辑推理](#13-形式逻辑推理)
  - [2. 详细设计](#2-详细设计)
    - [2.1 核心抽象层](#21-核心抽象层)
    - [2.2 工作流构建器 - 连接三种流](#22-工作流构建器---连接三种流)
    - [2.3 分布式和容错特性实现](#23-分布式和容错特性实现)
    - [2.4 兼容企业业务流程与IoT设计领域](#24-兼容企业业务流程与iot设计领域)
  - [3. 完整实现示例](#3-完整实现示例)
  - [4. 分布式工作流执行引擎](#4-分布式工作流执行引擎)
  - [5. 企业级工作流与IoT集成示例](#5-企业级工作流与iot集成示例)
  - [6. 实现Redis存储适配器](#6-实现redis存储适配器)
  - [7. Redis分布式锁服务实现](#7-redis分布式锁服务实现)
  - [8. 兼容企业业务流程与IoT的高级适配器](#8-兼容企业业务流程与iot的高级适配器)
  - [9. 总结与架构评估](#9-总结与架构评估)

## 1. 架构设计论证过程

### 1.1 工作流基本需求分析

工作流系统需要处理三个层面的语义：

1. **数据流**：关注数据如何在系统中传递和转换
2. **执行流**：关注任务的执行顺序和依赖关系
3. **控制流**：关注业务逻辑决策和流程控制

同时需要考虑分布式系统特性，并能够适配企业业务流程和IoT设计领域。

### 1.2 Rust类型系统的优势

Rust的类型系统提供了多种特性，可以帮助我们设计这样的工作流架构：

1. **代数数据类型**：使用enum和struct定义复杂的状态和数据结构
2. **特质系统(Traits)**：定义行为接口，支持多态性
3. **泛型**：实现可重用组件
4. **所有权模型**：保证内存安全和并发安全
5. **错误处理机制**：Result和Option类型支持错误传播
6. **生命周期**：管理引用的有效性

### 1.3 形式逻辑推理

从形式逻辑角度，我们可以将工作流系统建模为：

- 工作流是一个有向图 G = (V, E)，其中V是任务节点，E是依赖边
- 数据流可以表示为在边E上传递的类型化数据D
- 执行流可以表示为节点V的执行顺序
- 控制流可以表示为节点V中的决策逻辑

这种模型可以使用Rust的类型系统来实现：

- 使用泛型参数表示数据类型
- 使用trait bounds表示节点的能力要求
- 使用枚举表示控制流分支

## 2. 详细设计

### 2.1 核心抽象层

```rust
/// 任务状态枚举
pub enum TaskState {
    NotStarted,
    Running,
    Completed,
    Failed { error: String },
    Canceled,
}

/// 工作流事件
pub enum WorkflowEvent<T> {
    TaskStarted { task_id: String },
    TaskCompleted { task_id: String, result: T },
    TaskFailed { task_id: String, error: String },
    WorkflowCompleted,
    WorkflowFailed,
}

/// 定义任务特质 - 执行流的基本单元
pub trait Task {
    type Input;
    type Output;
    type Error;

    /// 执行任务
    async fn execute(&self, input: Self::Input) -> Result<Self::Output, Self::Error>;
    
    /// 获取任务状态
    fn state(&self) -> TaskState;
    
    /// 取消任务
    async fn cancel(&self) -> Result<(), Self::Error>;
    
    /// 恢复任务
    async fn recover(&self) -> Result<(), Self::Error>;
}

/// 定义工作流特质 - 控制流的协调者
pub trait Workflow {
    type Input;
    type Output;
    type Error;
    
    /// 启动工作流
    async fn start(&self, input: Self::Input) -> Result<(), Self::Error>;
    
    /// 获取工作流状态
    fn status(&self) -> WorkflowStatus;
    
    /// 暂停工作流
    async fn pause(&self) -> Result<(), Self::Error>;
    
    /// 恢复工作流
    async fn resume(&self) -> Result<(), Self::Error>;
    
    /// 取消工作流
    async fn cancel(&self) -> Result<(), Self::Error>;
    
    /// 等待工作流完成
    async fn wait_for_completion(&self) -> Result<Self::Output, Self::Error>;
    
    /// 注册事件监听器
    fn register_listener<L: WorkflowListener>(&mut self, listener: L);
}

/// 数据转换特质 - 数据流的核心
pub trait DataTransformer<I, O, E> {
    /// 将一种数据类型转换为另一种
    fn transform(&self, input: I) -> Result<O, E>;
}
```

### 2.2 工作流构建器 - 连接三种流

```rust
/// 工作流构建器 - 用于构建复杂工作流
pub struct WorkflowBuilder<T> {
    tasks: HashMap<String, Box<dyn Task<Output = T>>>,
    dependencies: HashMap<String, Vec<String>>,
    error_handlers: HashMap<String, Box<dyn Fn(String) -> BoxFuture<'static, Result<(), Error>>>>,
}

impl<T: 'static> WorkflowBuilder<T> {
    pub fn new() -> Self {
        Self {
            tasks: HashMap::new(),
            dependencies: HashMap::new(),
            error_handlers: HashMap::new(),
        }
    }
    
    /// 添加任务到工作流
    pub fn add_task<TaskT>(&mut self, id: String, task: TaskT) -> &mut Self 
    where
        TaskT: Task<Output = T> + 'static,
    {
        self.tasks.insert(id, Box::new(task));
        self
    }
    
    /// 添加任务依赖关系
    pub fn add_dependency(&mut self, task_id: String, depends_on: String) -> &mut Self {
        self.dependencies
            .entry(task_id)
            .or_insert_with(Vec::new)
            .push(depends_on);
        self
    }
    
    /// 添加错误处理器
    pub fn add_error_handler<F>(&mut self, task_id: String, handler: F) -> &mut Self
    where
        F: Fn(String) -> BoxFuture<'static, Result<(), Error>> + 'static,
    {
        self.error_handlers.insert(task_id, Box::new(handler));
        self
    }
    
    /// 构建工作流
    pub fn build(self) -> impl Workflow<Input = (), Output = HashMap<String, T>, Error = Error> {
        // 实现工作流构建逻辑
        WorkflowImpl {
            tasks: self.tasks,
            dependencies: self.dependencies,
            error_handlers: self.error_handlers,
            // 其他必要状态...
        }
    }
}

struct WorkflowImpl<T> {
    tasks: HashMap<String, Box<dyn Task<Output = T>>>,
    dependencies: HashMap<String, Vec<String>>,
    error_handlers: HashMap<String, Box<dyn Fn(String) -> BoxFuture<'static, Result<(), Error>>>>,
    // 其他状态...
}
```

### 2.3 分布式和容错特性实现

```rust
/// 分布式任务执行器
pub struct DistributedTaskExecutor<T> {
    connection_pool: ConnectionPool,
    task_registry: Arc<RwLock<HashMap<String, BoxedTask<T>>>>,
    retry_policy: RetryPolicy,
}

impl<T: Send + Sync + 'static> DistributedTaskExecutor<T> {
    pub fn new(connection_url: &str, retry_policy: RetryPolicy) -> Self {
        // 初始化分布式执行器
        Self {
            connection_pool: ConnectionPool::new(connection_url),
            task_registry: Arc::new(RwLock::new(HashMap::new())),
            retry_policy,
        }
    }
    
    /// 执行任务，支持重试和容错
    pub async fn execute_task(&self, task_id: &str, input: T) -> Result<T, Error> {
        let mut retries = 0;
        let max_retries = self.retry_policy.max_retries;
        
        loop {
            match self.try_execute_task(task_id, input.clone()).await {
                Ok(result) => return Ok(result),
                Err(err) => {
                    if retries >= max_retries || !self.retry_policy.should_retry(&err) {
                        return Err(err);
                    }
                    
                    let delay = self.retry_policy.delay_for_retry(retries);
                    tokio::time::sleep(delay).await;
                    retries += 1;
                    // 日志记录重试
                }
            }
        }
    }
    
    async fn try_execute_task(&self, task_id: &str, input: T) -> Result<T, Error> {
        // 从注册表获取任务
        let task = {
            let registry = self.task_registry.read().await;
            registry.get(task_id).cloned().ok_or(Error::TaskNotFound)
        }?;
        
        // 获取分布式锁避免重复执行
        let _lock = self.connection_pool.acquire_lock(task_id).await?;
        
        // 执行任务并记录状态到分布式存储
        let result = task.execute(input).await?;
        self.connection_pool.store_task_result(task_id, &result).await?;
        
        Ok(result)
    }
}

/// 重试策略
pub struct RetryPolicy {
    max_retries: usize,
    base_delay: Duration,
    max_delay: Duration,
    retry_on: Vec<ErrorKind>,
}

impl RetryPolicy {
    /// 计算重试延迟（指数退避算法）
    pub fn delay_for_retry(&self, retry_count: usize) -> Duration {
        let exponential_delay = self.base_delay.mul_f64(2.0f64.powi(retry_count as i32));
        min(exponential_delay, self.max_delay)
    }
    
    /// 判断是否应该重试
    pub fn should_retry(&self, error: &Error) -> bool {
        self.retry_on.contains(&error.kind())
    }
}
```

### 2.4 兼容企业业务流程与IoT设计领域

为了兼容两个不同领域，我们设计了可扩展的适配器模式：

```rust
/// 业务流程适配器特质
pub trait BusinessProcessAdapter {
    type Input;
    type Output;
    type Error;
    
    /// 将业务流程转换为工作流任务
    fn adapt_to_workflow(&self) -> Box<dyn Task<Input = Self::Input, Output = Self::Output, Error = Self::Error>>;
    
    /// 从工作流结果更新业务状态
    fn update_business_state(&self, result: Self::Output) -> Result<(), Self::Error>;
}

/// IoT设备适配器特质
pub trait IoTDeviceAdapter {
    type DeviceData;
    type Command;
    type Error;
    
    /// 获取设备数据
    async fn get_device_data(&self) -> Result<Self::DeviceData, Self::Error>;
    
    /// 发送命令到设备
    async fn send_command(&self, command: Self::Command) -> Result<(), Self::Error>;
    
    /// 将设备转换为工作流任务
    fn as_workflow_task(&self) -> Box<dyn Task<Input = Option<Self::Command>, Output = Self::DeviceData, Error = Self::Error>>;
}

/// 业务流程示例实现
pub struct OrderProcessingAdapter {
    order_id: String,
    db_connection: DbConnection,
}

impl BusinessProcessAdapter for OrderProcessingAdapter {
    type Input = OrderData;
    type Output = OrderStatus;
    type Error = Error;
    
    fn adapt_to_workflow(&self) -> Box<dyn Task<Input = Self::Input, Output = Self::Output, Error = Self::Error>> {
        Box::new(OrderProcessingTask {
            order_id: self.order_id.clone(),
            db_connection: self.db_connection.clone(),
        })
    }
    
    fn update_business_state(&self, result: Self::Output) -> Result<(), Self::Error> {
        self.db_connection.update_order_status(&self.order_id, result)
    }
}

/// IoT设备示例实现
pub struct TemperatureSensorAdapter {
    device_id: String,
    mqtt_client: MqttClient,
}

impl IoTDeviceAdapter for TemperatureSensorAdapter {
    type DeviceData = Temperature;
    type Command = SensorCommand;
    type Error = Error;
    
    async fn get_device_data(&self) -> Result<Self::DeviceData, Self::Error> {
        self.mqtt_client.request_data(&self.device_id).await
    }
    
    async fn send_command(&self, command: Self::Command) -> Result<(), Self::Error> {
        self.mqtt_client.publish_command(&self.device_id, command).await
    }
    
    fn as_workflow_task(&self) -> Box<dyn Task<Input = Option<Self::Command>, Output = Self::DeviceData, Error = Self::Error>> {
        Box::new(TemperatureSensorTask {
            device_id: self.device_id.clone(),
            mqtt_client: self.mqtt_client.clone(),
        })
    }
}
```

## 3. 完整实现示例

下面是一个完整的工作流实现示例，展示了如何整合上述所有设计：

```rust
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{RwLock, Mutex};
use tokio::time;
use futures::{Future, StreamExt};
use serde::{Serialize, Deserialize};
use thiserror::Error;

// 错误定义
#[derive(Error, Debug)]
pub enum WorkflowError {
    #[error("任务执行失败: {0}")]
    TaskExecutionError(String),
    
    #[error("任务不存在: {0}")]
    TaskNotFound(String),
    
    #[error("工作流已取消")]
    WorkflowCanceled,
    
    #[error("分布式锁获取失败: {0}")]
    LockAcquisitionFailed(String),
    
    #[error("数据转换失败: {0}")]
    DataTransformationError(String),
    
    #[error("IoT设备通信错误: {0}")]
    IoTCommunicationError(String),
    
    #[error("数据库错误: {0}")]
    DatabaseError(String),
}

// 工作流状态
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WorkflowStatus {
    NotStarted,
    Running,
    Paused,
    Completed,
    Failed,
    Canceled,
}

// 实现Task特质的具体任务
struct SimpleTask<I, O, E> {
    id: String,
    state: Arc<RwLock<TaskState>>,
    handler: Box<dyn Fn(I) -> impl Future<Output = Result<O, E>> + Send + Sync>,
}

impl<I: Send + 'static, O: Send + 'static, E: Into<WorkflowError> + Send + 'static> Task for SimpleTask<I, O, E> {
    type Input = I;
    type Output = O;
    type Error = WorkflowError;
    
    async fn execute(&self, input: Self::Input) -> Result<Self::Output, Self::Error> {
        let mut state = self.state.write().await;
        *state = TaskState::Running;
        drop(state);
        
        let handler = &self.handler;
        match handler(input).await {
            Ok(output) => {
                let mut state = self.state.write().await;
                *state = TaskState::Completed;
                Ok(output)
            },
            Err(e) => {
                let mut state = self.state.write().await;
                *state = TaskState::Failed { error: format!("{:?}", e) };
                Err(e.into())
            }
        }
    }
    
    fn state(&self) -> TaskState {
        futures::executor::block_on(async {
            self.state.read().await.clone()
        })
    }
    
    async fn cancel(&self) -> Result<(), Self::Error> {
        let mut state = self.state.write().await;
        *state = TaskState::Canceled;
        Ok(())
    }
    
    async fn recover(&self) -> Result<(), Self::Error> {
        let mut state = self.state.write().await;
        if let TaskState::Failed { .. } = *state {
            *state = TaskState::NotStarted;
            Ok(())
        } else {
            Err(WorkflowError::TaskExecutionError("任务未处于失败状态，无法恢复".to_string()))
        }
    }
}

// 一个真实的工作流实现
struct WorkflowExecutor<Input, Output> {
    id: String,
    tasks: HashMap<String, Box<dyn Task<Input = Input, Output = Output, Error = WorkflowError>>>,
    dependencies: HashMap<String, Vec<String>>,
    status: Arc<RwLock<WorkflowStatus>>,
    results: Arc<RwLock<HashMap<String, Output>>>,
    error_handlers: HashMap<String, Box<dyn Fn(String) -> tokio::task::JoinHandle<Result<(), WorkflowError>>>>,
    cancel_flag: Arc<RwLock<bool>>,
    listeners: Vec<Box<dyn Fn(WorkflowEvent<Output>) + Send + Sync>>,
}

impl<Input: Clone + Send + 'static, Output: Clone + Send + 'static> Workflow for WorkflowExecutor<Input, Output> {
    type Input = Input;
    type Output = HashMap<String, Output>;
    type Error = WorkflowError;
    
    async fn start(&self, input: Self::Input) -> Result<(), Self::Error> {
        let mut status = self.status.write().await;
        *status = WorkflowStatus::Running;
        drop(status);
        
        // 构建任务依赖图
        let graph = self.build_dependency_graph();
        
        // 找出所有没有依赖的起始任务
        let start_tasks: Vec<String> = graph.iter()
            .filter(|(_, deps)| deps.is_empty())
            .map(|(id, _)| id.clone())
            .collect();
        
        // 启动任务执行
        let mut handles = vec![];
        for task_id in start_tasks {
            let handle = self.execute_task_with_dependencies(task_id, input.clone(), graph.clone()).await?;
            handles.push(handle);
        }
        
        // 等待所有任务完成
        for handle in handles {
            handle.await.map_err(|e| WorkflowError::TaskExecutionError(format!("任务执行失败: {:?}", e)))?;
        }
        
        // 更新工作流状态
        let mut status = self.status.write().await;
        if *status != WorkflowStatus::Canceled {
            *status = WorkflowStatus::Completed;
        }
        
        // 触发工作流完成事件
        for listener in &self.listeners {
            listener(WorkflowEvent::WorkflowCompleted);
        }
        
        Ok(())
    }
    
    fn status(&self) -> WorkflowStatus {
        futures::executor::block_on(async {
            self.status.read().await.clone()
        })
    }
    
    async fn pause(&self) -> Result<(), Self::Error> {
        let mut status = self.status.write().await;
        if *status == WorkflowStatus::Running {
            *status = WorkflowStatus::Paused;
            Ok(())
        } else {
            Err(WorkflowError::TaskExecutionError("工作流不在运行状态，无法暂停".to_string()))
        }
    }
    
    async fn resume(&self) -> Result<(), Self::Error> {
        let mut status = self.status.write().await;
        if *status == WorkflowStatus::Paused {
            *status = WorkflowStatus::Running;
            Ok(())
        } else {
            Err(WorkflowError::TaskExecutionError("工作流不在暂停状态，无法恢复".to_string()))
        }
    }
    
    async fn cancel(&self) -> Result<(), Self::Error> {
        let mut cancel_flag = self.cancel_flag.write().await;
        *cancel_flag = true;
        drop(cancel_flag);
        
        let mut status = self.status.write().await;
        *status = WorkflowStatus::Canceled;
        
        // 取消所有正在执行的任务
        for (id, task) in &self.tasks {
            task.cancel().await?;
        }
        
        Ok(())
    }
    
    async fn wait_for_completion(&self) -> Result<Self::Output, Self::Error> {
        loop {
            let status = self.status.read().await.clone();
            match status {
                WorkflowStatus::Completed => {
                    return Ok(self.results.read().await.clone());
                },
                WorkflowStatus::Failed => {
                    return Err(WorkflowError::TaskExecutionError("工作流执行失败".to_string()));
                },
                WorkflowStatus::Canceled => {
                    return Err(WorkflowError::WorkflowCanceled);
                },
                _ => {
                    // 等待一段时间后再检查
                    drop(status);
                    time::sleep(Duration::from_millis(100)).await;
                }
            }
        }
    }
    
    fn register_listener<L: Fn(WorkflowEvent<Output>) + Send + Sync + 'static>(&mut self, listener: L) {
        self.listeners.push(Box::new(listener));
    }
}

impl<Input: Clone + Send + 'static, Output: Clone + Send + 'static> WorkflowExecutor<Input, Output> {
    // 构建任务依赖图
    fn build_dependency_graph(&self) -> HashMap<String, Vec<String>> {
        self.dependencies.clone()
    }
    
    // 执行单个任务及其依赖
    async fn execute_task_with_dependencies(
        &self, 
        task_id: String, 
        input: Input,
        graph: HashMap<String, Vec<String>>
    ) -> Result<tokio::task::JoinHandle<Result<(), WorkflowError>>, WorkflowError> {
        let task = self.tasks.get(&task_id)
            .ok_or_else(|| WorkflowError::TaskNotFound(task_id.clone()))?;
        
        let task_id_clone = task_id.clone();
        let input_clone = input.clone();
        let results = self.results.clone();
        let cancel_flag = self.cancel_flag.clone();
        let error_handlers = self.error_handlers.clone();
        let listeners = self.listeners.clone();
        
        // 启动异步任务
        let handle = tokio::spawn(async move {
            // 检查是否取消
            if *cancel_flag.read().await {
                return Err(WorkflowError::WorkflowCanceled);
            }
            
            // 通知任务开始
            for listener in &listeners {
                listener(WorkflowEvent::TaskStarted { task_id: task_id_clone.clone() });
            }
            
            // 执行任务
            match task.execute(input_clone).await {
                Ok(output) => {
                    // 存储结果
                    results.write().await.insert(task_id_clone.clone(), output.clone());
                    
                    // 通知任务完成
                    for listener in &listeners {
                        listener(WorkflowEvent::TaskCompleted { 
                            task_id: task_id_clone.clone(), 
                            result: output 
                        });
                    }
                    
                    Ok(())
                },
                Err(err) => {
                    // 尝试错误恢复
                    if let Some(handler) = error_handlers.get(&task_id_clone) {
                        let _recovery_handle = handler(task_id_clone.clone());
                    }
                    
                    // 通知任务失败
                    for listener in &listeners {
                        listener(WorkflowEvent::TaskFailed { 
                            task_id: task_id_clone.clone(), 
                            error: format!("{:?}", err) 
                        });
                    }
                    
                    Err(err)
                }
            }
        });
        
        Ok(handle)
    }
}

// 一个企业业务流程与IoT设备集成的示例
#[derive(Debug, Clone, Serialize, Deserialize)]
struct SensorReading {
    device_id: String,
    temperature: f32,
    humidity: f32,
    timestamp: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct AlertConfig {
    high_temp_threshold: f32,
    low_temp_threshold: f32,
    high_humidity_threshold: f32,
    low_humidity_threshold: f32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct AlertNotification {
    alert_id: String,
    device_id: String,
    alert_type: String,
    message: String,
    timestamp: u64,
}

struct SensorDataCollectorTask {
    device_id: String,
    mqtt_client: Arc<MqttClient>,
    state: Arc<RwLock<TaskState>>,
}

struct AlertProcessorTask {
    alert_config: AlertConfig,
    state: Arc<RwLock<TaskState>>,
}

struct NotificationSenderTask {
    notification_service: Arc<NotificationService>,
    state: Arc<RwLock<TaskState>>,
}

// 模拟MQTT客户端
struct MqttClient {
    broker_url: String,
}

impl MqttClient {
    async fn get_latest_reading(&self, device_id: &str) -> Result<SensorReading, WorkflowError> {
        // 模拟从MQTT获取数据
        Ok(SensorReading {
            device_id: device_id.to_string(),
            temperature: 22.5,
            humidity: 45.0,
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
        })
    }
}

// 模拟通知服务
struct NotificationService {
    api_url: String,
}

impl NotificationService {
    async fn send_notification(&self, notification: AlertNotification) -> Result<(), WorkflowError> {
        // 模拟发送通知
        println!("发送通知: {:?}", notification);
        Ok(())
    }
}

// 实现IoT传感器任务
impl Task for SensorDataCollectorTask {
    type Input = ();
    type Output = SensorReading;
    type Error = WorkflowError;
    
    async fn execute(&self, _: Self::Input) -> Result<Self::Output, Self::Error> {
        let mut state = self.state.write().await;
        *state = TaskState::Running;
        drop(state);
        
        match self.mqtt_client.get_latest_reading(&self.device_id).await {
            Ok(reading) => {
                let mut state = self.state.write().await;
                *state = TaskState::Completed;
                Ok(reading)
            },
            Err(e) => {
                let mut state = self.state.write().await;
                *state = TaskState::Failed { error: format!("{:?}", e) };
                Err(e)
            }
        }
    }
    
    fn state(&self) -> TaskState {
        futures::executor::block_on(async {
            self.state.read().await.clone()
        })
    }
    
    async fn cancel(&self) -> Result<(), Self::Error> {
        let mut state = self.state.write().await;
        *state = TaskState::Canceled;
        Ok(())
    }
    
    async fn recover(&self) -> Result<(), Self::Error> {
        let mut state = self.state.write().await;
        if let TaskState::Failed { .. } = *state {
            *state = TaskState::NotStarted;
            Ok(())
        } else {
            Err(WorkflowError::TaskExecutionError("任务未处于失败状态，无法恢复".to_string()))
        }
    }
}

// 实现告警处理任务
impl Task for AlertProcessorTask {
    type Input = SensorReading;
    type Output = Option<AlertNotification>;
    type Error = WorkflowError;
    
    async fn execute(&self, input: Self::Input) -> Result<Self::Output, Self::Error> {
        let mut state = self.state.write().await;
        *state = TaskState::Running;
        drop(state);
        
        // 检查是否需要生成告警
        let alert = if input.temperature > self.alert_config.high_temp_threshold {
            Some(AlertNotification {
                alert_id: uuid::Uuid::new_v4().to_string(),
                device_id: input.device_id.clone(),
                alert_type: "HIGH_TEMPERATURE".to_string(),
                message: format!("温度过高: {}", input.temperature),
                timestamp: input.timestamp,
            })
        } else if input.temperature < self.alert_config.low_temp_threshold {
            Some(AlertNotification {
                alert_id: uuid::Uuid::new_v4().to_string(),
                device_id: input.device_id.clone(),
                alert_type: "LOW_TEMPERATURE".to_string(),
                message: format!("温度过低: {}", input.temperature),
                timestamp: input.timestamp,
            })
        } else if input.humidity > self.alert_config.high_humidity_threshold {
            Some(AlertNotification {
# Rust工作流架构设计：数据流、执行流与控制流的融合（续）

## 3. 完整实现示例（续）

```rust
                alert_id: uuid::Uuid::new_v4().to_string(),
                device_id: input.device_id.clone(),
                alert_type: "HIGH_HUMIDITY".to_string(),
                message: format!("湿度过高: {}", input.humidity),
                timestamp: input.timestamp,
            })
        } else if input.humidity < self.alert_config.low_humidity_threshold {
            Some(AlertNotification {
                alert_id: uuid::Uuid::new_v4().to_string(),
                device_id: input.device_id.clone(),
                alert_type: "LOW_HUMIDITY".to_string(),
                message: format!("湿度过低: {}", input.humidity),
                timestamp: input.timestamp,
            })
        } else {
            None
        };
        
        let mut state = self.state.write().await;
        *state = TaskState::Completed;
        Ok(alert)
    }
    
    fn state(&self) -> TaskState {
        futures::executor::block_on(async {
            self.state.read().await.clone()
        })
    }
    
    async fn cancel(&self) -> Result<(), Self::Error> {
        let mut state = self.state.write().await;
        *state = TaskState::Canceled;
        Ok(())
    }
    
    async fn recover(&self) -> Result<(), Self::Error> {
        let mut state = self.state.write().await;
        if let TaskState::Failed { .. } = *state {
            *state = TaskState::NotStarted;
            Ok(())
        } else {
            Err(WorkflowError::TaskExecutionError("任务未处于失败状态，无法恢复".to_string()))
        }
    }
}

// 实现通知发送任务
impl Task for NotificationSenderTask {
    type Input = Option<AlertNotification>;
    type Output = bool;
    type Error = WorkflowError;
    
    async fn execute(&self, input: Self::Input) -> Result<Self::Output, Self::Error> {
        let mut state = self.state.write().await;
        *state = TaskState::Running;
        drop(state);
        
        // 如果有告警，则发送
        if let Some(alert) = input {
            match self.notification_service.send_notification(alert).await {
                Ok(_) => {
                    let mut state = self.state.write().await;
                    *state = TaskState::Completed;
                    Ok(true)
                },
                Err(e) => {
                    let mut state = self.state.write().await;
                    *state = TaskState::Failed { error: format!("{:?}", e) };
                    Err(e)
                }
            }
        } else {
            // 没有告警需要发送
            let mut state = self.state.write().await;
            *state = TaskState::Completed;
            Ok(false)
        }
    }
    
    fn state(&self) -> TaskState {
        futures::executor::block_on(async {
            self.state.read().await.clone()
        })
    }
    
    async fn cancel(&self) -> Result<(), Self::Error> {
        let mut state = self.state.write().await;
        *state = TaskState::Canceled;
        Ok(())
    }
    
    async fn recover(&self) -> Result<(), Self::Error> {
        let mut state = self.state.write().await;
        if let TaskState::Failed { .. } = *state {
            *state = TaskState::NotStarted;
            Ok(())
        } else {
            Err(WorkflowError::TaskExecutionError("任务未处于失败状态，无法恢复".to_string()))
        }
    }
}

// 数据转换任务
struct DataTransformerTask<I, O> {
    transformer: Box<dyn Fn(I) -> Result<O, WorkflowError> + Send + Sync>,
    state: Arc<RwLock<TaskState>>,
}

impl<I: Send + 'static, O: Send + 'static> Task for DataTransformerTask<I, O> {
    type Input = I;
    type Output = O;
    type Error = WorkflowError;
    
    async fn execute(&self, input: Self::Input) -> Result<Self::Output, Self::Error> {
        let mut state = self.state.write().await;
        *state = TaskState::Running;
        drop(state);
        
        match (self.transformer)(input) {
            Ok(output) => {
                let mut state = self.state.write().await;
                *state = TaskState::Completed;
                Ok(output)
            },
            Err(e) => {
                let mut state = self.state.write().await;
                *state = TaskState::Failed { error: format!("{:?}", e) };
                Err(e)
            }
        }
    }
    
    fn state(&self) -> TaskState {
        futures::executor::block_on(async {
            self.state.read().await.clone()
        })
    }
    
    async fn cancel(&self) -> Result<(), Self::Error> {
        let mut state = self.state.write().await;
        *state = TaskState::Canceled;
        Ok(())
    }
    
    async fn recover(&self) -> Result<(), Self::Error> {
        let mut state = self.state.write().await;
        if let TaskState::Failed { .. } = *state {
            *state = TaskState::NotStarted;
            Ok(())
        } else {
            Err(WorkflowError::TaskExecutionError("任务未处于失败状态，无法恢复".to_string()))
        }
    }
}
```

## 4. 分布式工作流执行引擎

下面是一个分布式工作流执行引擎的实现，它能够在分布式环境中协调任务执行并提供故障恢复能力：

```rust
/// 分布式工作流执行引擎
pub struct DistributedWorkflowEngine {
    // 存储引擎，用于持久化工作流状态
    storage: Arc<dyn WorkflowStorage>,
    // 分布式锁服务
    lock_service: Arc<dyn LockService>,
    // 集群节点管理
    cluster_manager: Arc<dyn ClusterManager>,
    // 健康检查服务
    health_checker: Arc<dyn HealthChecker>,
}

/// 工作流存储接口
#[async_trait]
pub trait WorkflowStorage: Send + Sync {
    // 保存工作流定义
    async fn save_workflow_definition(&self, workflow: WorkflowDefinition) -> Result<(), WorkflowError>;
    
    // 获取工作流定义
    async fn get_workflow_definition(&self, workflow_id: &str) -> Result<WorkflowDefinition, WorkflowError>;
    
    // 保存工作流状态
    async fn save_workflow_state(&self, workflow_id: &str, state: WorkflowState) -> Result<(), WorkflowError>;
    
    // 获取工作流状态
    async fn get_workflow_state(&self, workflow_id: &str) -> Result<WorkflowState, WorkflowError>;
    
    // 保存任务结果
    async fn save_task_result(&self, workflow_id: &str, task_id: &str, result: TaskResult) -> Result<(), WorkflowError>;
    
    // 获取任务结果
    async fn get_task_result(&self, workflow_id: &str, task_id: &str) -> Result<TaskResult, WorkflowError>;
    
    // 列出所有待执行任务
    async fn list_pending_tasks(&self) -> Result<Vec<PendingTask>, WorkflowError>;
}

/// 分布式锁服务接口
#[async_trait]
pub trait LockService: Send + Sync {
    // 获取锁
    async fn acquire_lock(&self, resource_id: &str, ttl: Duration) -> Result<Lock, WorkflowError>;
    
    // 续期锁
    async fn renew_lock(&self, lock: &Lock) -> Result<(), WorkflowError>;
    
    // 释放锁
    async fn release_lock(&self, lock: &Lock) -> Result<(), WorkflowError>;
}

/// 集群管理接口
#[async_trait]
pub trait ClusterManager: Send + Sync {
    // 注册节点
    async fn register_node(&self, node_id: &str, capabilities: NodeCapabilities) -> Result<(), WorkflowError>;
    
    // 注销节点
    async fn unregister_node(&self, node_id: &str) -> Result<(), WorkflowError>;
    
    // 获取活跃节点列表
    async fn get_active_nodes(&self) -> Result<Vec<NodeInfo>, WorkflowError>;
    
    // 分配任务到节点
    async fn assign_task(&self, task: PendingTask) -> Result<String, WorkflowError>;
}

/// 健康检查接口
#[async_trait]
pub trait HealthChecker: Send + Sync {
    // 检查节点健康状态
    async fn check_node_health(&self, node_id: &str) -> Result<bool, WorkflowError>;
    
    // 执行任务健康检查
    async fn check_task_health(&self, workflow_id: &str, task_id: &str) -> Result<TaskHealthStatus, WorkflowError>;
    
    // 恢复失败的任务
    async fn recover_failed_task(&self, workflow_id: &str, task_id: &str) -> Result<(), WorkflowError>;
}

/// 分布式工作流引擎实现
impl DistributedWorkflowEngine {
    pub fn new(
        storage: Arc<dyn WorkflowStorage>,
        lock_service: Arc<dyn LockService>,
        cluster_manager: Arc<dyn ClusterManager>,
        health_checker: Arc<dyn HealthChecker>,
    ) -> Self {
        Self {
            storage,
            lock_service,
            cluster_manager,
            health_checker,
        }
    }
    
    /// 启动工作流引擎
    pub async fn start(&self, node_id: String, capabilities: NodeCapabilities) -> Result<(), WorkflowError> {
        // 注册当前节点
        self.cluster_manager.register_node(&node_id, capabilities).await?;
        
        // 启动任务调度器
        self.start_task_scheduler(node_id.clone()).await?;
        
        // 启动健康检查服务
        self.start_health_check_service(node_id).await?;
        
        Ok(())
    }
    
    /// 部署工作流定义
    pub async fn deploy_workflow(&self, definition: WorkflowDefinition) -> Result<String, WorkflowError> {
        // 生成唯一ID
        let workflow_id = uuid::Uuid::new_v4().to_string();
        
        // 保存工作流定义
        let mut def = definition;
        def.id = workflow_id.clone();
        self.storage.save_workflow_definition(def).await?;
        
        // 初始化工作流状态
        let initial_state = WorkflowState {
            id: workflow_id.clone(),
            status: WorkflowStatus::NotStarted,
            start_time: None,
            end_time: None,
            error: None,
        };
        self.storage.save_workflow_state(&workflow_id, initial_state).await?;
        
        Ok(workflow_id)
    }
    
    /// 执行工作流
    pub async fn execute_workflow(&self, workflow_id: String, input: serde_json::Value) -> Result<String, WorkflowError> {
        // 获取工作流定义
        let definition = self.storage.get_workflow_definition(&workflow_id).await?;
        
        // 获取工作流锁，确保同一工作流不会并发执行
        let lock = self.lock_service.acquire_lock(&format!("workflow:{}", workflow_id), Duration::from_secs(60)).await?;
        
        // 更新工作流状态为运行中
        let mut state = self.storage.get_workflow_state(&workflow_id).await?;
        state.status = WorkflowStatus::Running;
        state.start_time = Some(chrono::Utc::now().timestamp());
        self.storage.save_workflow_state(&workflow_id, state).await?;
        
        // 创建工作流执行上下文
        let context = WorkflowContext {
            workflow_id: workflow_id.clone(),
            execution_id: uuid::Uuid::new_v4().to_string(),
            input,
        };
        
        // 调度起始任务
        let start_tasks = definition.get_start_tasks();
        for task_def in start_tasks {
            let pending_task = PendingTask {
                workflow_id: workflow_id.clone(),
                task_id: task_def.id.clone(),
                task_type: task_def.task_type.clone(),
                dependencies: vec![],
                state: TaskState::NotStarted,
                retry_count: 0,
                max_retries: task_def.max_retries,
                input: context.input.clone(),
            };
            
            // 将任务保存到存储，准备执行
            self.storage.save_task_result(&workflow_id, &task_def.id, TaskResult {
                task_id: task_def.id.clone(),
                state: TaskState::NotStarted,
                result: None,
                error: None,
                start_time: None,
                end_time: None,
            }).await?;
        }
        
        // 释放工作流锁
        self.lock_service.release_lock(&lock).await?;
        
        Ok(context.execution_id)
    }
    
    /// 启动任务调度器
    async fn start_task_scheduler(&self, node_id: String) -> Result<(), WorkflowError> {
        // 创建调度器任务
        let storage = self.storage.clone();
        let lock_service = self.lock_service.clone();
        let cluster_manager = self.cluster_manager.clone();
        
        tokio::spawn(async move {
            loop {
                // 获取待执行任务
                match storage.list_pending_tasks().await {
                    Ok(tasks) => {
                        for task in tasks {
                            // 为任务获取锁，避免多节点重复执行
                            let lock_key = format!("task:{}:{}", task.workflow_id, task.task_id);
                            if let Ok(lock) = lock_service.acquire_lock(&lock_key, Duration::from_secs(60)).await {
                                // 检查任务是否已分配给其他节点
                                if let Ok(assigned_node) = cluster_manager.assign_task(task.clone()).await {
                                    if assigned_node == node_id {
                                        // 任务分配给当前节点，执行它
                                        let task_clone = task.clone();
                                        let storage_clone = storage.clone();
                                        let lock_service_clone = lock_service.clone();
                                        let lock_clone = lock.clone();
                                        
                                        tokio::spawn(async move {
                                            // 执行任务
                                            let result = execute_task(task_clone).await;
                                            
                                            // 保存任务结果
                                            match result {
                                                Ok(output) => {
                                                    storage_clone.save_task_result(
                                                        &task_clone.workflow_id, 
                                                        &task_clone.task_id, 
                                                        TaskResult {
                                                            task_id: task_clone.task_id.clone(),
                                                            state: TaskState::Completed,
                                                            result: Some(output),
                                                            error: None,
                                                            start_time: Some(chrono::Utc::now().timestamp()),
                                                            end_time: Some(chrono::Utc::now().timestamp()),
                                                        }
                                                    ).await.ok();
                                                },
                                                Err(err) => {
                                                    storage_clone.save_task_result(
                                                        &task_clone.workflow_id, 
                                                        &task_clone.task_id, 
                                                        TaskResult {
                                                            task_id: task_clone.task_id.clone(),
                                                            state: TaskState::Failed { error: format!("{:?}", err) },
                                                            result: None,
                                                            error: Some(format!("{:?}", err)),
                                                            start_time: Some(chrono::Utc::now().timestamp()),
                                                            end_time: Some(chrono::Utc::now().timestamp()),
                                                        }
                                                    ).await.ok();
                                                }
                                            }
                                            
                                            // 释放任务锁
                                            lock_service_clone.release_lock(&lock_clone).await.ok();
                                        });
                                    }
                                }
                            }
                        }
                    },
                    Err(e) => {
                        eprintln!("获取待执行任务失败: {:?}", e);
                    }
                }
                
                // 睡眠一段时间后再次检查
                tokio::time::sleep(Duration::from_millis(500)).await;
            }
        });
        
        Ok(())
    }
    
    /// 启动健康检查服务
    async fn start_health_check_service(&self, node_id: String) -> Result<(), WorkflowError> {
        let health_checker = self.health_checker.clone();
        let storage = self.storage.clone();
        
        tokio::spawn(async move {
            loop {
                // 获取所有进行中的任务
                if let Ok(tasks) = storage.list_pending_tasks().await {
                    for task in tasks {
                        // 检查任务健康状态
                        if let Ok(status) = health_checker.check_task_health(&task.workflow_id, &task.task_id).await {
                            if status == TaskHealthStatus::Failed || status == TaskHealthStatus::Stalled {
                                // 尝试恢复失败的任务
                                health_checker.recover_failed_task(&task.workflow_id, &task.task_id).await.ok();
                            }
                        }
                    }
                }
                
                // 睡眠后再次检查
                tokio::time::sleep(Duration::from_secs(30)).await;
            }
        });
        
        Ok(())
    }
}

// 任务执行函数
async fn execute_task(task: PendingTask) -> Result<serde_json::Value, WorkflowError> {
    // 根据任务类型执行相应的逻辑
    match task.task_type.as_str() {
        "http_request" => {
            // 执行HTTP请求任务
            execute_http_request_task(&task).await
        },
        "data_transformation" => {
            // 执行数据转换任务
            execute_data_transformation_task(&task).await
        },
        "iot_command" => {
            // 执行IoT命令任务
            execute_iot_command_task(&task).await
        },
        "database_operation" => {
            // 执行数据库操作任务
            execute_database_operation_task(&task).await
        },
        _ => {
            Err(WorkflowError::TaskExecutionError(format!("未知任务类型: {}", task.task_type)))
        }
    }
}

// 各种任务执行函数的实现
async fn execute_http_request_task(task: &PendingTask) -> Result<serde_json::Value, WorkflowError> {
    // 实现HTTP请求任务的逻辑
    // ...
    Ok(serde_json::json!({"status": "success"}))
}

async fn execute_data_transformation_task(task: &PendingTask) -> Result<serde_json::Value, WorkflowError> {
    // 实现数据转换任务的逻辑
    // ...
    Ok(serde_json::json!({"transformed": true}))
}

async fn execute_iot_command_task(task: &PendingTask) -> Result<serde_json::Value, WorkflowError> {
    // 实现IoT命令任务的逻辑
    // ...
    Ok(serde_json::json!({"command_sent": true}))
}

async fn execute_database_operation_task(task: &PendingTask) -> Result<serde_json::Value, WorkflowError> {
    // 实现数据库操作任务的逻辑
    // ...
    Ok(serde_json::json!({"rows_affected": 5}))
}
```

## 5. 企业级工作流与IoT集成示例

下面的示例展示了如何使用上述架构来构建一个企业级的工作流系统，同时集成IoT设备：

```rust
/// 工厂温度监控与自动调节工作流示例
async fn main() -> Result<(), WorkflowError> {
    // 初始化工作流引擎
    let storage = Arc::new(RedisWorkflowStorage::new("redis://localhost")?);
    let lock_service = Arc::new(RedisLockService::new("redis://localhost")?);
    let cluster_manager = Arc::new(EtcdClusterManager::new(&["http://localhost:2379"])?);
    let health_checker = Arc::new(DefaultHealthChecker::new());
    
    let engine = DistributedWorkflowEngine::new(
        storage.clone(),
        lock_service.clone(),
        cluster_manager.clone(),
        health_checker.clone(),
    );
    
    // 构建工厂温度监控与调节工作流
    let workflow_definition = WorkflowDefinition {
        id: String::new(), // 将由引擎生成
        name: "工厂温度监控与自动调节".to_string(),
        description: "监控工厂温度，根据温度自动调节空调系统".to_string(),
        version: "1.0".to_string(),
        tasks: vec![
            // 1. 从多个传感器收集温度数据
            TaskDefinition {
                id: "collect_temperature_data".to_string(),
                name: "收集温度数据".to_string(),
                task_type: "iot_sensor_reading".to_string(),
                max_retries: 3,
                timeout: Duration::from_secs(30),
                parameters: serde_json::json!({
                    "sensor_ids": ["temp_sensor_1", "temp_sensor_2", "temp_sensor_3", "temp_sensor_4"],
                    "reading_type": "temperature"
                }),
                depends_on: vec![],
            },
            
            // 2. 分析温度数据
            TaskDefinition {
                id: "analyze_temperature_data".to_string(),
                name: "分析温度数据".to_string(),
                task_type: "data_transformation".to_string(),
                max_retries: 1,
                timeout: Duration::from_secs(10),
                parameters: serde_json::json!({
                    "operation": "average",
                    "threshold_high": 28.0,
                    "threshold_low": 22.0,
                }),
                depends_on: vec!["collect_temperature_data".to_string()],
            },
            
            // 3. 决策：是否需要调节空调
            TaskDefinition {
                id: "temperature_decision".to_string(),
                name: "温度决策".to_string(),
                task_type: "decision".to_string(),
                max_retries: 1,
                timeout: Duration::from_secs(5),
                parameters: serde_json::json!({
                    "conditions": [
                        {
                            "condition": "$.average_temperature > $.threshold_high",
                            "next_task": "activate_cooling"
                        },
                        {
                            "condition": "$.average_temperature < $.threshold_low",
                            "next_task": "activate_heating"
                        },
                        {
                            "condition": "true",
                            "next_task": "no_action_needed"
                        }
                    ]
                }),
                depends_on: vec!["analyze_temperature_data".to_string()],
            },
            
            // 4a. 启动制冷
            TaskDefinition {
                id: "activate_cooling".to_string(),
                name: "启动制冷".to_string(),
                task_type: "iot_command".to_string(),
                max_retries: 3,
                timeout: Duration::from_secs(60),
                parameters: serde_json::json!({
                    "device_id": "hvac_controller",
                    "command": "set_mode",
                    "parameters": {
                        "mode": "cooling",
                        "temperature": 22.0
                    }
                }),
                depends_on: vec!["temperature_decision".to_string()],
            },
            
            // 4b. 启动加热
            TaskDefinition {
                id: "activate_heating".to_string(),
                name: "启动加热".to_string(),
                task_type: "iot_command".to_string(),
                max_retries: 3,
                timeout: Duration::from_secs(60),
                parameters: serde_json::json!({
                    "device_id": "hvac_controller",
                    "command": "set_mode",
                    "parameters": {
                        "mode": "heating",
                        "temperature": 24.0
                    }
                }),
                depends_on: vec!["temperature_decision".to_string()],
            },
            
            // 4c. 无需操作
            TaskDefinition {
                id: "no_action_needed".to_string(),
                name: "无需操作".to_string(),
                task_type: "noop".to_string(),
                max_retries: 0,
                timeout: Duration::from_secs(5),
                parameters: serde_json::json!({}),
                depends_on: vec!["temperature_decision".to_string()],
            },
            
            // 5. 记录操作到数据库
            TaskDefinition {
                id: "record_operation".to_string(),
                name: "记录操作".to_string(),
                task_type: "database_operation".to_string(),
                max_retries: 3,
                timeout: Duration::from_secs(30),
                parameters: serde_json::json!({
                    "operation": "insert",
                    "table": "temperature_control_logs",
                    "data": {
                        "timestamp": "${now()}",
                        "average_temperature": "${output.analyze_temperature_data.average_temperature}",
                        "action_taken": "${current_task}"
                    }
                }),
                depends_on: vec!["activate_cooling".to_string(), "activate_heating".to_string(), "no_action_needed".to_string()],
            },
            
            // 6. 发送通知
            TaskDefinition {
                id: "send_notification".to_string(),
                name: "发送通知".to_string(),
                task_type: "notification".to_string(),
                max_retries: 3,
                timeout: Duration::from_secs(30),
                parameters: serde_json::json!({
                    "channel": "slack",
                    "recipients": ["#factory-monitoring"],
                    "message": "工厂温度监控: ${output.analyze_temperature_data.average_temperature}°C, 操作: ${current_task}"
                }),
                depends_on: vec!["record_operation".to_string()],
            }
        ]
    };

    // 部署工作流
    let workflow_id = engine.deploy_workflow(workflow_definition).await?;
    println!("工作流已部署，ID: {}", workflow_id);
    
    // 启动工作流引擎
    engine.start("node-1".to_string(), NodeCapabilities {
        cpu: 4,
        memory: 8192,
        supported_task_types: vec![
            "iot_sensor_reading".to_string(),
            "data_transformation".to_string(),
            "decision".to_string(),
            "iot_command".to_string(),
            "database_operation".to_string(),
            "notification".to_string(),
            "noop".to_string(),
        ],
    }).await?;
    
    // 每10分钟执行一次工作流
    loop {
        let execution_id = engine.execute_workflow(workflow_id.clone(), serde_json::json!({})).await?;
        println!("工作流执行已启动，执行ID: {}", execution_id);
        
        // 等待10分钟
        tokio::time::sleep(Duration::from_secs(600)).await;
    }
}
```

## 6. 实现Redis存储适配器

```rust
/// Redis工作流存储实现
struct RedisWorkflowStorage {
    client: redis::Client,
}

impl RedisWorkflowStorage {
    fn new(redis_url: &str) -> Result<Self, WorkflowError> {
        let client = redis::Client::open(redis_url)
            .map_err(|e| WorkflowError::DatabaseError(format!("Redis连接失败: {}", e)))?;
        Ok(Self { client })
    }
}

#[async_trait]
impl WorkflowStorage for RedisWorkflowStorage {
    async fn save_workflow_definition(&self, workflow: WorkflowDefinition) -> Result<(), WorkflowError> {
        let mut conn = self.client.get_async_connection().await
            .map_err(|e| WorkflowError::DatabaseError(format!("获取Redis连接失败: {}", e)))?;
        
        let json = serde_json::to_string(&workflow)
            .map_err(|e| WorkflowError::DataTransformationError(format!("序列化工作流定义失败: {}", e)))?;
        
        redis::cmd("SET")
            .arg(format!("workflow:definition:{}", workflow.id))
            .arg(json)
            .query_async(&mut conn)
            .await
            .map_err(|e| WorkflowError::DatabaseError(format!("保存工作流定义失败: {}", e)))?;
        
        Ok(())
    }
    
    async fn get_workflow_definition(&self, workflow_id: &str) -> Result<WorkflowDefinition, WorkflowError> {
        let mut conn = self.client.get_async_connection().await
            .map_err(|e| WorkflowError::DatabaseError(format!("获取Redis连接失败: {}", e)))?;
        
        let json: String = redis::cmd("GET")
            .arg(format!("workflow:definition:{}", workflow_id))
            .query_async(&mut conn)
            .await
            .map_err(|e| WorkflowError::DatabaseError(format!("获取工作流定义失败: {}", e)))?;
        
        let definition: WorkflowDefinition = serde_json::from_str(&json)
            .map_err(|e| WorkflowError::DataTransformationError(format!("反序列化工作流定义失败: {}", e)))?;
        
        Ok(definition)
    }
    
    async fn save_workflow_state(&self, workflow_id: &str, state: WorkflowState) -> Result<(), WorkflowError> {
        let mut conn = self.client.get_async_connection().await
            .map_err(|e| WorkflowError::DatabaseError(format!("获取Redis连接失败: {}", e)))?;
        
        let json = serde_json::to_string(&state)
            .map_err(|e| WorkflowError::DataTransformationError(format!("序列化工作流状态失败: {}", e)))?;
        
        redis::cmd("SET")
            .arg(format!("workflow:state:{}", workflow_id))
            .arg(json)
            .query_async(&mut conn)
            .await
            .map_err(|e| WorkflowError::DatabaseError(format!("保存工作流状态失败: {}", e)))?;
        
        Ok(())
    }
    
    async fn get_workflow_state(&self, workflow_id: &str) -> Result<WorkflowState, WorkflowError> {
        let mut conn = self.client.get_async_connection().await
            .map_err(|e| WorkflowError::DatabaseError(format!("获取Redis连接失败: {}", e)))?;
        
        let json: String = redis::cmd("GET")
            .arg(format!("workflow:state:{}", workflow_id))
            .query_async(&mut conn)
            .await
            .map_err(|e| WorkflowError::DatabaseError(format!("获取工作流状态失败: {}", e)))?;
        
        let state: WorkflowState = serde_json::from_str(&json)
            .map_err(|e| WorkflowError::DataTransformationError(format!("反序列化工作流状态失败: {}", e)))?;
        
        Ok(state)
    }
    
    async fn save_task_result(&self, workflow_id: &str, task_id: &str, result: TaskResult) -> Result<(), WorkflowError> {
        let mut conn = self.client.get_async_connection().await
            .map_err(|e| WorkflowError::DatabaseError(format!("获取Redis连接失败: {}", e)))?;
        
        let json = serde_json::to_string(&result)
            .map_err(|e| WorkflowError::DataTransformationError(format!("序列化任务结果失败: {}", e)))?;
        
        redis::cmd("SET")
            .arg(format!("workflow:task:{}:{}", workflow_id, task_id))
            .arg(json)
            .query_async(&mut conn)
            .await
            .map_err(|e| WorkflowError::DatabaseError(format!("保存任务结果失败: {}", e)))?;
        
        // 如果任务完成，将触发依赖任务
        if let TaskState::Completed = result.state {
            self.trigger_dependent_tasks(workflow_id, task_id).await?;
        }
        
        Ok(())
    }
    
    async fn get_task_result(&self, workflow_id: &str, task_id: &str) -> Result<TaskResult, WorkflowError> {
        let mut conn = self.client.get_async_connection().await
            .map_err(|e| WorkflowError::DatabaseError(format!("获取Redis连接失败: {}", e)))?;
        
        let json: String = redis::cmd("GET")
            .arg(format!("workflow:task:{}:{}", workflow_id, task_id))
            .query_async(&mut conn)
            .await
            .map_err(|e| WorkflowError::DatabaseError(format!("获取任务结果失败: {}", e)))?;
        
        let result: TaskResult = serde_json::from_str(&json)
            .map_err(|e| WorkflowError::DataTransformationError(format!("反序列化任务结果失败: {}", e)))?;
        
        Ok(result)
    }
    
    async fn list_pending_tasks(&self) -> Result<Vec<PendingTask>, WorkflowError> {
        let mut conn = self.client.get_async_connection().await
            .map_err(|e| WorkflowError::DatabaseError(format!("获取Redis连接失败: {}", e)))?;
        
        let task_keys: Vec<String> = redis::cmd("KEYS")
            .arg("workflow:pending_task:*")
            .query_async(&mut conn)
            .await
            .map_err(|e| WorkflowError::DatabaseError(format!("获取待执行任务列表失败: {}", e)))?;
        
        let mut pending_tasks = Vec::new();
        
        for key in task_keys {
            let json: String = redis::cmd("GET")
                .arg(&key)
                .query_async(&mut conn)
                .await
                .map_err(|e| WorkflowError::DatabaseError(format!("获取待执行任务失败: {}", e)))?;
            
            let task: PendingTask = serde_json::from_str(&json)
                .map_err(|e| WorkflowError::DataTransformationError(format!("反序列化待执行任务失败: {}", e)))?;
            
            pending_tasks.push(task);
        }
        
        Ok(pending_tasks)
    }
}

impl RedisWorkflowStorage {
    // 触发依赖任务
    async fn trigger_dependent_tasks(&self, workflow_id: &str, completed_task_id: &str) -> Result<(), WorkflowError> {
        // 获取工作流定义
        let definition = self.get_workflow_definition(workflow_id).await?;
        
        // 找出依赖于已完成任务的所有任务
        let dependent_tasks: Vec<TaskDefinition> = definition.tasks.into_iter()
            .filter(|task| task.depends_on.contains(&completed_task_id.to_string()))
            .collect();
        
        for task in dependent_tasks {
            // 检查任务的所有依赖是否已完成
            let mut all_dependencies_completed = true;
            
            for dep_id in &task.depends_on {
                if let Ok(dep_result) = self.get_task_result(workflow_id, dep_id).await {
                    if !matches!(dep_result.state, TaskState::Completed) {
                        all_dependencies_completed = false;
                        break;
                    }
                } else {
                    all_dependencies_completed = false;
                    break;
                }
            }
            
            // 如果所有依赖都已完成，将任务加入待执行队列
            if all_dependencies_completed {
                // 收集所有依赖任务的输出结果
                let mut dependency_results = serde_json::Map::new();
                for dep_id in &task.depends_on {
                    if let Ok(dep_result) = self.get_task_result(workflow_id, dep_id).await {
                        if let Some(result) = dep_result.result {
                            dependency_results.insert(dep_id.clone(), result);
                        }
                    }
                }
                
                // 创建待执行任务
                let pending_task = PendingTask {
                    workflow_id: workflow_id.to_string(),
                    task_id: task.id.clone(),
                    task_type: task.task_type.clone(),
                    dependencies: task.depends_on.clone(),
                    state: TaskState::NotStarted,
                    retry_count: 0,
                    max_retries: task.max_retries,
                    input: serde_json::json!({
                        "task": task.parameters,
                        "dependencies": dependency_results
                    }),
                };
                
                // 保存待执行任务
                let mut conn = self.client.get_async_connection().await
                    .map_err(|e| WorkflowError::DatabaseError(format!("获取Redis连接失败: {}", e)))?;
                
                let json = serde_json::to_string(&pending_task)
                    .map_err(|e| WorkflowError::DataTransformationError(format!("序列化待执行任务失败: {}", e)))?;
                
                redis::cmd("SET")
                    .arg(format!("workflow:pending_task:{}:{}", workflow_id, task.id))
                    .arg(json)
                    .query_async(&mut conn)
                    .await
                    .map_err(|e| WorkflowError::DatabaseError(format!("保存待执行任务失败: {}", e)))?;
            }
        }
        
        Ok(())
    }
}
```

## 7. Redis分布式锁服务实现

```rust
/// Redis分布式锁实现
pub struct RedisLockService {
    client: redis::Client,
}

pub struct Lock {
    resource_id: String,
    token: String,
    ttl: Duration,
    created_at: Instant,
}

impl RedisLockService {
    pub fn new(redis_url: &str) -> Result<Self, WorkflowError> {
        let client = redis::Client::open(redis_url)
            .map_err(|e| WorkflowError::DatabaseError(format!("Redis连接失败: {}", e)))?;
        Ok(Self { client })
    }
}

#[async_trait]
impl LockService for RedisLockService {
    async fn acquire_lock(&self, resource_id: &str, ttl: Duration) -> Result<Lock, WorkflowError> {
        let mut conn = self.client.get_async_connection().await
            .map_err(|e| WorkflowError::DatabaseError(format!("获取Redis连接失败: {}", e)))?;
        
        // 生成随机令牌
        let token = uuid::Uuid::new_v4().to_string();
        
        // 尝试获取锁，使用Lua脚本确保原子性
        let script = r"
            if redis.call('EXISTS', KEYS[1]) == 0 then
                redis.call('SET', KEYS[1], ARGV[1], 'PX', ARGV[2])
                return 1
            else
                return 0
            end
        ";
        
        let result: i32 = redis::Script::new(script)
            .key(format!("lock:{}", resource_id))
            .arg(&token)
            .arg(ttl.as_millis().to_string())
            .invoke_async(&mut conn)
            .await
            .map_err(|e| WorkflowError::LockAcquisitionFailed(format!("获取锁失败: {}", e)))?;
        
        if result == 1 {
            Ok(Lock {
                resource_id: resource_id.to_string(),
                token,
                ttl,
                created_at: Instant::now(),
            })
        } else {
            Err(WorkflowError::LockAcquisitionFailed(format!("资源已被锁定: {}", resource_id)))
        }
    }
    
    async fn renew_lock(&self, lock: &Lock) -> Result<(), WorkflowError> {
        let mut conn = self.client.get_async_connection().await
            .map_err(|e| WorkflowError::DatabaseError(format!("获取Redis连接失败: {}", e)))?;
        
        // 续期锁，使用Lua脚本确保只有锁的拥有者才能续期
        let script = r"
            if redis.call('GET', KEYS[1]) == ARGV[1] then
                redis.call('PEXPIRE', KEYS[1], ARGV[2])
                return 1
            else
                return 0
            end
        ";
        
        let result: i32 = redis::Script::new(script)
            .key(format!("lock:{}", lock.resource_id))
            .arg(&lock.token)
            .arg(lock.ttl.as_millis().to_string())
            .invoke_async(&mut conn)
            .await
            .map_err(|e| WorkflowError::DatabaseError(format!("续期锁失败: {}", e)))?;
        
        if result == 1 {
            Ok(())
        } else {
            Err(WorkflowError::LockAcquisitionFailed(format!("锁已不存在或已被其他进程获取: {}", lock.resource_id)))
        }
    }
    
    async fn release_lock(&self, lock: &Lock) -> Result<(), WorkflowError> {
        let mut conn = self.client.get_async_connection().await
            .map_err(|e| WorkflowError::DatabaseError(format!("获取Redis连接失败: {}", e)))?;
        
        // 释放锁，使用Lua脚本确保只有锁的拥有者才能释放
        let script = r"
            if redis.call('GET', KEYS[1]) == ARGV[1] then
                redis.call('DEL', KEYS[1])
                return 1
            else
                return 0
            end
        ";
        
        let result: i32 = redis::Script::new(script)
            .key(format!("lock:{}", lock.resource_id))
            .arg(&lock.token)
            .invoke_async(&mut conn)
            .await
            .map_err(|e| WorkflowError::DatabaseError(format!("释放锁失败: {}", e)))?;
        
        if result == 1 {
            Ok(())
        } else {
            Err(WorkflowError::LockAcquisitionFailed(format!("锁已不存在或已被其他进程获取: {}", lock.resource_id)))
        }
    }
}
```

## 8. 兼容企业业务流程与IoT的高级适配器

```rust
/// 企业业务流程适配器
pub struct EnterpriseBusinessAdapter<T: Serialize + DeserializeOwned> {
    service_client: Arc<dyn EnterpriseServiceClient<T>>,
    process_id: String,
    process_config: ProcessConfig,
}

#[async_trait]
pub trait EnterpriseServiceClient<T>: Send + Sync {
    async fn start_process(&self, process_id: &str, input: &serde_json::Value) -> Result<String, WorkflowError>;
    async fn get_process_status(&self, process_id: &str, instance_id: &str) -> Result<ProcessStatus, WorkflowError>;
    async fn get_process_result(&self, process_id: &str, instance_id: &str) -> Result<T, WorkflowError>;
    async fn cancel_process(&self, process_id: &str, instance_id: &str) -> Result<(), WorkflowError>;
}

impl<T: Serialize + DeserializeOwned + Send + Sync + 'static> EnterpriseBusinessAdapter<T> {
    pub fn new(service_client: Arc<dyn EnterpriseServiceClient<T>>, process_id: &str, process_config: ProcessConfig) -> Self {
        Self {
            service_client,
            process_id: process_id.to_string(),
            process_config,
        }
    }
    
    /// 将企业流程包装为工作流任务
    pub fn as_task(&self) -> impl Task<Input = serde_json::Value, Output = T, Error = WorkflowError> {
        EnterpriseProcessTask {
            service_client: self.service_client.clone(),
            process_id: self.process_id.clone(),
            process_config: self.process_config.clone(),
            state: Arc::new(RwLock::new(TaskState::NotStarted)),
            instance_id: Arc::new(RwLock::new(None)),
        }
    }
}

struct EnterpriseProcessTask<T: Serialize + DeserializeOwned + Send + Sync> {
    service_client: Arc<dyn EnterpriseServiceClient<T>>,
    process_id: String,
    process_config: ProcessConfig,
    state: Arc<RwLock<TaskState>>,
    instance_id: Arc<RwLock<Option<String>>>,
}

#[async_trait]
impl<T: Serialize + DeserializeOwned + Send + Sync + 'static> Task for EnterpriseProcessTask<T> {
    type Input = serde_json::Value;
    type Output = T;
    type Error = WorkflowError;
    
    async fn execute(&self, input: Self::Input) -> Result<Self::Output, Self::Error> {
        let mut state = self.state.write().await;
        *state = TaskState::Running;
        drop(state);
        
        // 启动企业流程
        let instance_id = self.service_client.start_process(&self.process_id, &input).await?;
        
        // 保存实例ID
        let mut instance_id_guard = self.instance_id.write().await;
        *instance_id_guard = Some(instance_id.clone());
        drop(instance_id_guard);
        
        // 等待流程完成
        let mut retry_count = 0;
        let max_retries = self.process_config.max_status_check_retries;
        let check_interval = self.process_config.status_check_interval;
        
        loop {
            tokio::time::sleep(check_interval).await;
            
            let status = self.service_client.get_process_status(&self.process_id, &instance_id).await?;
            
            match status {
                ProcessStatus::Completed => {
                    // 获取流程结果
                    let result = self.service_client.get_process_result(&self.process_id, &instance_id).await?;
                    
                    let mut state = self.state.write().await;
                    *state = TaskState::Completed;
                    
                    return Ok(result);
                },
                ProcessStatus::Failed(error) => {
                    let mut state = self.state.write().await;
                    *state = TaskState::Failed { error: error.clone() };
                    
                    return Err(WorkflowError::TaskExecutionError(format!("企业流程执行失败: {}", error)));
                },
                ProcessStatus::Running | ProcessStatus::Pending => {
                    retry_count += 1;
                    
                    if retry_count > max_retries {
                        let mut state = self.state.write().await;
                        *state = TaskState::Failed { error: "企业流程执行超时".to_string() };
                        
                        return Err(WorkflowError::TaskExecutionError("企业流程执行超时".to_string()));
                    }
                },
                ProcessStatus::Canceled => {
                    let mut state = self.state.write().await;
                    *state = TaskState::Canceled;
                    
                    return Err(WorkflowError::WorkflowCanceled);
                }
            }
        }
    }
    
    fn state(&self) -> TaskState {
        futures::executor::block_on(async {
            self.state.read().await.clone()
        })
    }
    
    async fn cancel(&self) -> Result<(), Self::Error> {
        let instance_id_guard = self.instance_id.read().await;
        
        if let Some(instance_id) = &*instance_id_guard {
            self.service_client.cancel_process(&self.process_id, instance_id).await?;
        }
        
        let mut state = self.state.write().await;
        *state = TaskState::Canceled;
        
        Ok(())
    }
    
    async fn recover(&self) -> Result<(), Self::Error> {
        let mut state = self.state.write().await;
        if let TaskState::Failed { .. } = *state {
            *state = TaskState::NotStarted;
            Ok(())
        } else {
            Err(WorkflowError::TaskExecutionError("任务未处于失败状态，无法恢复".to_string()))
        }
    }
}

/// IoT设备适配器
pub struct IoTDeviceAdapter {
    mqtt_client: Arc<MqttClient>,
    device_id: String,
    command_topic: String,
    response_topic: String,
    timeout: Duration,
}

impl IoTDeviceAdapter {
    pub fn new(
        mqtt_client: Arc<MqttClient>,
        device_id: &str,
        command_topic: &str,
        response_topic: &str,
        timeout: Duration,
    ) -> Self {
        Self {
            mqtt_client,
            device_id: device_id.to_string(),
            command_topic: command_topic.to_string(),
            response_topic: response_topic.to_string(),
            timeout,
        }
    }
    
    /// 将IoT设备操作包装为工作流任务
    pub fn as_command_task<T: Serialize + DeserializeOwned + Send + Sync + 'static>(
        &self,
        command_type: &str,
    ) -> impl Task<Input = serde_json::Value, Output = serde_json::Value, Error = WorkflowError> {
        IoTCommandTask {
            mqtt_client: self.mqtt_client.clone(),
            device_id: self.device_id.clone(),
            command_topic: self.command_topic.clone(),
            response_topic: self.response_topic.clone(),
            command_type: command_type.to_string(),
            timeout: self.timeout,
            state: Arc::new(RwLock::new(TaskState::NotStarted)),
        }
    }
    
    /// 将IoT数据收集包装为工作流任务
    pub fn as_sensor_task<T: Serialize + DeserializeOwned + Send + Sync + 'static>(
        &self
    ) -> impl Task<Input = (), Output = serde_json::Value, Error = WorkflowError> {
        IoTSensorTask {
            mqtt_client: self.mqtt_client.clone(),
            device_id: self.device_id.clone(),
            response_topic: self.response_topic.clone(),
            timeout: self.timeout,
            state: Arc::new(RwLock::new(TaskState::NotStarted)),
        }
    }
}

struct IoTCommandTask {
    mqtt_client: Arc<MqttClient>,
    device_id: String,
    command_topic: String,
    response_topic: String,
    command_type: String,
    timeout: Duration,
    state: Arc<RwLock<TaskState>>,
}

#[async_trait]
impl Task for IoTCommandTask {
    type Input = serde_json::Value;
    type Output = serde_json::Value;
    type Error = WorkflowError;
    
    async fn execute(&self, input: Self::Input) -> Result<Self::Output, Self::Error> {
        let mut state = self.state.write().await;
        *state = TaskState::Running;
        drop(state);
        
        // 构建命令消息
        let command = serde_json::json!({
            "device_id": self.device_id,
            "command_type": self.command_type,
            "parameters": input,
            "timestamp": chrono::Utc::now().timestamp(),
            "request_id": uuid::Uuid::new_v4().to_string(),
        });
        
        // 发送命令
        let request_id = command["request_id"].as_str().unwrap();
        let response_future = self.mqtt_client.request_response(
            &self.command_topic,
            &self.response_topic,
            request_id,
            &command,
        );
        
        // 等待响应，带超时
        match tokio::time::timeout(self.timeout, response_future).await {
            Ok(Ok(response)) => {
                let mut state = self.state.write().await;
                *state = TaskState::Completed;
                Ok(response)
            },
            Ok(Err(e)) => {
                let mut state = self.state.write().await;
                *state = TaskState::Failed { error: format!("{:?}", e) };
                Err(e)
            },
            Err(_) => {
                let mut state = self.state.write().await;
                *state = TaskState::Failed { error: "命令执行超时".to_string() };
                Err(WorkflowError::IoTCommunicationError("命令执行超时".to_string()))
            },
        }
    }
    
    fn state(&self) -> TaskState {
        futures::executor::block_on(async {
            self.state.read().await.clone()
        })
    }
    
    async fn cancel(&self) -> Result<(), Self::Error> {
        let mut state = self.state.write().await;
        *state = TaskState::Canceled;
        
        // 可以在这里添加取消命令的逻辑
        
        Ok(())
    }
    
    async fn recover(&self) -> Result<(), Self::Error> {
        let mut state = self.state.write().await;
        if let TaskState::Failed { .. } = *state {
            *state = TaskState::NotStarted;
            Ok(())
        } else {
            Err(WorkflowError::TaskExecutionError("任务未处于失败状态，无法恢复".to_string()))
        }
    }
}
```

## 9. 总结与架构评估

通过上述实现，我们构建了一个完整的工作流架构，它具有以下特性：

1. **三层语义处理**：
   - **数据流**：通过`DataTransformer`特质和类型化的输入/输出处理数据转换
   - **执行流**：通过`Task`特质和任务依赖关系管理执行顺序
   - **控制流**：通过`Workflow`特质和决策任务控制业务逻辑

2. **分布式系统特性**：
   - **容错性**：通过重试策略和错误处理机制实现
   - **健壮性**：使用分布式锁和健康检查保证系统稳定性
   - **可自动恢复**：任务失败时自动重试和恢复机制

3. **企业业务流程与IoT设计领域的集成**：
   - 提供了企业业务流程适配器，将业务流程系统集成到工作流中
   - 提供了IoT设备适配器，将设备操作和数据收集集成到工作流中

此架构的优势在于：

1. **类型安全**：利用Rust的类型系统确保数据流的正确性
2. **可扩展性**：通过特质（trait）系统支持自定义组件
3. **高性能**：Rust的零成本抽象和内存安全保证高效执行
4. **易于维护**：清晰的架构分层便于维护和扩展
5. **可靠性**：完善的错误处理和恢复机制提高系统可靠性

这个架构适用于各种复杂的场景，从企业业务流程自动化到IoT设备控制系统，都能胜任。
通过组合不同的适配器和任务类型，可以构建出适应不同领域需求的工作流系统。
