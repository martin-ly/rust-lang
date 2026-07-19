# Rust 类型设计准则：工作流与算法系统

## 目录

- [Rust 类型设计准则：工作流与算法系统](#rust-类型设计准则工作流与算法系统)
  - [目录](#目录)
  - [1. 同步、异步、并发与并行](#1-同步异步并发与并行)
    - [1.1 统一执行模型](#11-统一执行模型)
    - [1.2 状态管理通道](#12-状态管理通道)
  - [2. 通用性、可组合性与可监测性](#2-通用性可组合性与可监测性)
    - [2.1 可组合工作流管道](#21-可组合工作流管道)
    - [2.2 自定义性能监控框架](#22-自定义性能监控框架)
  - [3. 分布式系统控制与错误处理](#3-分布式系统控制与错误处理)
    - [3.1 状态机与恢复点](#31-状态机与恢复点)
    - [3.2 容错重试与熔断](#32-容错重试与熔断)
  - [4. 工作流与算法集成](#4-工作流与算法集成)
    - [4.1 工作流内置调度器](#41-工作流内置调度器)
    - [4.2 算法与工作流集成器](#42-算法与工作流集成器)
  - [5. 总结：工作流与算法设计准则](#5-总结工作流与算法设计准则)
    - [5.1 同步、异步与并行模式](#51-同步异步与并行模式)
    - [5.2 组合性与可监测性](#52-组合性与可监测性)
    - [5.3 分布式控制与错误处理](#53-分布式控制与错误处理)
    - [5.4 算法与工作流集成](#54-算法与工作流集成)

本文提出的设计准则着重考虑工作流和算法系统的同步/异步特性、
并发/并行处理能力、通用性、组合性、可监测性、
可持续性和分布式系统的弹性，不依赖外部开源组件。

## 1. 同步、异步、并发与并行

### 1.1 统一执行模型

```rust
// 推荐：统一执行模型
use std::future::Future;
use std::pin::Pin;
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

// 任务特征 - 统一同步和异步执行
pub trait Task {
    type Output;
    
    // 同步执行
    fn execute(&self) -> Self::Output;
    
    // 异步执行接口
    fn execute_async(&self) -> Pin<Box<dyn Future<Output = Self::Output> + Send + '_>> {
        // 默认实现：在异步上下文中执行同步操作
        let task = self.clone();
        Box::pin(async move {
            // 创建线程以避免阻塞异步运行时
            let handle = thread::spawn(move || task.execute());
            
            // 等待线程完成并获取结果
            // 在实际项目中，应该使用更高效的方法，例如 tokio::task::spawn_blocking
            handle.join().expect("Thread panicked")
        })
    }
    
    // 提供克隆功能以支持移动到新线程或任务
    fn clone(&self) -> Box<dyn Task<Output = Self::Output> + Send + Sync>;
}

// 任务结果 - 支持同步和异步访问
pub struct TaskResult<T> {
    value: Arc<Mutex<Option<T>>>,
    completed: Arc<Mutex<bool>>,
}

impl<T: Clone> TaskResult<T> {
    pub fn new() -> Self {
        Self {
            value: Arc::new(Mutex::new(None)),
            completed: Arc::new(Mutex::new(false)),
        }
    }
    
    // 设置结果
    pub fn set(&self, value: T) {
        let mut val = self.value.lock().unwrap();
        *val = Some(value);
        
        let mut completed = self.completed.lock().unwrap();
        *completed = true;
    }
    
    // 同步获取结果（阻塞）
    pub fn get(&self) -> Option<T> {
        let val = self.value.lock().unwrap();
        val.clone()
    }
    
    // 同步等待结果
    pub fn wait(&self, timeout_ms: u64) -> Option<T> {
        let start = std::time::Instant::now();
        
        while start.elapsed().as_millis() < timeout_ms as u128 {
            {
                let completed = self.completed.lock().unwrap();
                if *completed {
                    return self.get();
                }
            }
            
            // 短暂休眠以减少 CPU 使用
            thread::sleep(Duration::from_millis(10));
        }
        
        // 超时返回 None
        None
    }
    
    // 异步等待结果
    pub async fn wait_async(&self) -> T {
        loop {
            {
                let completed = self.completed.lock().unwrap();
                if *completed {
                    return self.get().unwrap();
                }
            }
            
            // 异步休眠以避免阻塞
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    }
}

// 任务执行器 - 支持不同执行模式
pub struct Executor {
    thread_pool: Option<Arc<ThreadPool>>,
}

impl Executor {
    pub fn new() -> Self {
        Self {
            thread_pool: None,
        }
    }
    
    // 配置线程池
    pub fn with_thread_pool(mut self, num_threads: usize) -> Self {
        self.thread_pool = Some(Arc::new(ThreadPool::new(num_threads)));
        self
    }
    
    // 同步执行
    pub fn execute<T: 'static + Send + Sync>(&self, task: Box<dyn Task<Output = T> + Send + Sync>) -> T {
        task.execute()
    }
    
    // 异步执行
    pub async fn execute_async<T: 'static + Send + Sync>(&self, task: Box<dyn Task<Output = T> + Send + Sync>) -> T {
        task.execute_async().await
    }
    
    // 后台执行（并发）
    pub fn execute_background<T: 'static + Send + Sync>(&self, task: Box<dyn Task<Output = T> + Send + Sync>) -> TaskResult<T> {
        let result = TaskResult::new();
        let result_clone = result.clone();
        
        if let Some(pool) = &self.thread_pool {
            // 使用线程池
            let pool = pool.clone();
            thread::spawn(move || {
                pool.execute(move || {
                    let output = task.execute();
                    result_clone.set(output);
                });
            });
        } else {
            // 创建新线程
            thread::spawn(move || {
                let output = task.execute();
                result_clone.set(output);
            });
        }
        
        result
    }
    
    // 批量执行（并行）
    pub fn execute_batch<T: 'static + Send + Sync>(
        &self,
        tasks: Vec<Box<dyn Task<Output = T> + Send + Sync>>,
    ) -> Vec<T> {
        // 创建线程处理每个任务
        let handles: Vec<_> = tasks
            .into_iter()
            .map(|task| {
                thread::spawn(move || {
                    task.execute()
                })
            })
            .collect();
        
        // 收集结果
        handles
            .into_iter()
            .map(|handle| handle.join().expect("Thread panicked"))
            .collect()
    }
    
    // 异步批量执行
    pub async fn execute_batch_async<T: 'static + Send + Sync>(
        &self,
        tasks: Vec<Box<dyn Task<Output = T> + Send + Sync>>,
    ) -> Vec<T> {
        // 创建 futures
        let futures: Vec<_> = tasks
            .into_iter()
            .map(|task| task.execute_async())
            .collect();
        
        // 并行执行所有 futures
        futures::future::join_all(futures).await
    }
}

// 简单的线程池实现
struct ThreadPool {
    workers: Vec<Worker>,
    sender: Option<std::sync::mpsc::Sender<Message>>,
}

type Job = Box<dyn FnOnce() + Send + 'static>;

enum Message {
    NewJob(Job),
    Terminate,
}

impl ThreadPool {
    fn new(size: usize) -> Self {
        assert!(size > 0);

        let (sender, receiver) = std::sync::mpsc::channel();
        let receiver = Arc::new(Mutex::new(receiver));

        let mut workers = Vec::with_capacity(size);

        for id in 0..size {
            workers.push(Worker::new(id, Arc::clone(&receiver)));
        }

        Self {
            workers,
            sender: Some(sender),
        }
    }

    fn execute<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'static,
    {
        let job = Box::new(f);
        self.sender.as_ref().unwrap().send(Message::NewJob(job)).unwrap();
    }
}

impl Drop for ThreadPool {
    fn drop(&mut self) {
        // 发送终止消息给所有工作线程
        for _ in &self.workers {
            self.sender.as_ref().unwrap().send(Message::Terminate).unwrap();
        }

        // 等待所有工作线程完成
        for worker in &mut self.workers {
            if let Some(thread) = worker.thread.take() {
                thread.join().unwrap();
            }
        }
    }
}

struct Worker {
    id: usize,
    thread: Option<thread::JoinHandle<()>>,
}

impl Worker {
    fn new(id: usize, receiver: Arc<Mutex<std::sync::mpsc::Receiver<Message>>>) -> Self {
        let thread = thread::spawn(move || loop {
            let message = receiver.lock().unwrap().recv().unwrap();

            match message {
                Message::NewJob(job) => {
                    job();
                }
                Message::Terminate => {
                    break;
                }
            }
        });

        Self {
            id,
            thread: Some(thread),
        }
    }
}

impl<T: Clone> Clone for TaskResult<T> {
    fn clone(&self) -> Self {
        Self {
            value: Arc::clone(&self.value),
            completed: Arc::clone(&self.completed),
        }
    }
}

// 示例：具体任务实现
struct DataProcessingTask {
    data: Vec<u32>,
}

impl DataProcessingTask {
    fn new(data: Vec<u32>) -> Self {
        Self { data }
    }
}

impl Task for DataProcessingTask {
    type Output = u32;
    
    fn execute(&self) -> Self::Output {
        println!("Processing data of size {}", self.data.len());
        
        // 模拟计算密集型任务
        thread::sleep(Duration::from_millis(100));
        
        self.data.iter().sum()
    }
    
    fn clone(&self) -> Box<dyn Task<Output = Self::Output> + Send + Sync> {
        Box::new(Self {
            data: self.data.clone(),
        })
    }
}

// 使用统一执行模型示例
async fn execution_model_example() {
    // 创建执行器
    let executor = Executor::new().with_thread_pool(4);
    
    // 创建任务
    let task = Box::new(DataProcessingTask::new(vec![1, 2, 3, 4, 5]));
    
    // 1. 同步执行
    let result1 = executor.execute(task.clone());
    println!("Sync result: {}", result1);
    
    // 2. 异步执行
    let result2 = executor.execute_async(task.clone()).await;
    println!("Async result: {}", result2);
    
    // 3. 后台执行
    let background_result = executor.execute_background(task.clone());
    
    // 做一些其他工作
    println!("Doing other work while background task is running...");
    
    // 等待结果
    if let Some(result3) = background_result.wait(2000) {
        println!("Background result: {}", result3);
    } else {
        println!("Background task timed out");
    }
    
    // 4. 批量执行
    let tasks = vec![
        Box::new(DataProcessingTask::new(vec![1, 2, 3])),
        Box::new(DataProcessingTask::new(vec![4, 5, 6])),
        Box::new(DataProcessingTask::new(vec![7, 8, 9])),
    ];
    
    let batch_results = executor.execute_batch(tasks);
    println!("Batch results: {:?}", batch_results);
    
    // 5. 异步批量执行
    let async_tasks = vec![
        Box::new(DataProcessingTask::new(vec![10, 20, 30])),
        Box::new(DataProcessingTask::new(vec![40, 50, 60])),
        Box::new(DataProcessingTask::new(vec![70, 80, 90])),
    ];
    
    let async_batch_results = executor.execute_batch_async(async_tasks).await;
    println!("Async batch results: {:?}", async_batch_results);
}
```

**准则**：设计统一的任务执行框架，支持同步、异步、并发和并行处理模式，使开发者能够根据任务特性选择最合适的执行方式。

### 1.2 状态管理通道

```rust
// 推荐：状态管理通道
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

// 任务状态
#[derive(Debug, Clone, PartialEq)]
pub enum TaskState {
    Queued,
    Running,
    Paused,
    Completed,
    Failed(String),
}

// 任务事件
#[derive(Debug, Clone)]
pub enum TaskEvent {
    StateChanged(TaskState),
    ProgressUpdate(f32),
    LogMessage(String),
    ResultProduced(Arc<dyn std::any::Any + Send + Sync>),
}

// 任务控制命令
#[derive(Debug, Clone)]
pub enum TaskCommand {
    Start,
    Pause,
    Resume,
    Cancel,
    SetParameter(String, Arc<dyn std::any::Any + Send + Sync>),
}

// 状态管理通道
pub struct StateChannel {
    event_senders: Vec<Arc<Mutex<Vec<Box<dyn Fn(TaskEvent) + Send + Sync>>>>>,
    command_receiver: Arc<Mutex<Vec<TaskCommand>>>,
}

impl StateChannel {
    pub fn new() -> Self {
        Self {
            event_senders: Vec::new(),
            command_receiver: Arc::new(Mutex::new(Vec::new())),
        }
    }
    
    // 发送事件
    pub fn send_event(&self, event: TaskEvent) {
        for sender in &self.event_senders {
            let callbacks = sender.lock().unwrap();
            for callback in callbacks.iter() {
                callback(event.clone());
            }
        }
    }
    
    // 接收命令
    pub fn receive_commands(&self) -> Vec<TaskCommand> {
        let mut commands = self.command_receiver.lock().unwrap();
        let result = commands.clone();
        commands.clear();
        result
    }
    
    // 发送命令
    pub fn send_command(&self, command: TaskCommand) {
        let mut commands = self.command_receiver.lock().unwrap();
        commands.push(command);
    }
    
    // 订阅事件
    pub fn subscribe<F>(&mut self, callback: F) -> usize
    where
        F: Fn(TaskEvent) + Send + Sync + 'static,
    {
        let callbacks = Arc::new(Mutex::new(vec![Box::new(callback) as Box<dyn Fn(TaskEvent) + Send + Sync>]));
        self.event_senders.push(callbacks);
        self.event_senders.len() - 1
    }
    
    // 取消订阅
    pub fn unsubscribe(&mut self, id: usize) -> bool {
        if id < self.event_senders.len() {
            self.event_senders.remove(id);
            true
        } else {
            false
        }
    }
}

// 可响应状态的工作流
pub struct StatefulWorkflow {
    name: String,
    state: TaskState,
    channel: Arc<StateChannel>,
    progress: f32,
}

impl StatefulWorkflow {
    pub fn new(name: impl Into<String>) -> Self {
        let slf = Self {
            name: name.into(),
            state: TaskState::Queued,
            channel: Arc::new(StateChannel::new()),
            progress: 0.0,
        };
        
        // 初始状态通知
        slf.update_state(TaskState::Queued);
        
        slf
    }
    
    // 获取状态通道
    pub fn channel(&self) -> Arc<StateChannel> {
        self.channel.clone()
    }
    
    // 更新状态
    fn update_state(&self, state: TaskState) {
        self.channel.send_event(TaskEvent::StateChanged(state.clone()));
    }
    
    // 更新进度
    fn update_progress(&self, progress: f32) {
        self.channel.send_event(TaskEvent::ProgressUpdate(progress));
    }
    
    // 记录日志
    fn log(&self, message: impl Into<String>) {
        self.channel.send_event(TaskEvent::LogMessage(message.into()));
    }
    
    // 提供结果
    fn provide_result<T: Send + Sync + 'static>(&self, result: T) {
        self.channel.send_event(TaskEvent::ResultProduced(Arc::new(result)));
    }
    
    // 执行工作流
    pub fn execute(&mut self) {
        // 更新状态为运行中
        self.state = TaskState::Running;
        self.update_state(self.state.clone());
        
        self.log(format!("Starting workflow '{}'", self.name));
        
        // 模拟长时间运行的任务
        for i in 0..10 {
            // 检查命令
            let commands = self.channel.receive_commands();
            for cmd in commands {
                match cmd {
                    TaskCommand::Pause => {
                        self.state = TaskState::Paused;
                        self.update_state(self.state.clone());
                        self.log("Workflow paused");
                        
                        // 等待恢复命令
                        loop {
                            thread::sleep(Duration::from_millis(100));
                            let commands = self.channel.receive_commands();
                            if commands.iter().any(|cmd| matches!(cmd, TaskCommand::Resume)) {
                                self.state = TaskState::Running;
                                self.update_state(self.state.clone());
                                self.log("Workflow resumed");
                                break;
                            }
                            if commands.iter().any(|cmd| matches!(cmd, TaskCommand::Cancel)) {
                                self.state = TaskState::Failed("Cancelled by user".into());
                                self.update_state(self.state.clone());
                                self.log("Workflow cancelled");
                                return;
                            }
                        }
                    }
                    TaskCommand::Cancel => {
                        self.state = TaskState::Failed("Cancelled by user".into());
                        self.update_state(self.state.clone());
                        self.log("Workflow cancelled");
                        return;
                    }
                    _ => {}
                }
            }
            
            // 执行工作
            thread::sleep(Duration::from_millis(200));
            
            // 更新进度
            self.progress = (i + 1) as f32 / 10.0;
            self.update_progress(self.progress);
            self.log(format!("Step {} completed", i + 1));
        }
        
        // 完成
        self.state = TaskState::Completed;
        self.update_state(self.state.clone());
        self.log(format!("Workflow '{}' completed", self.name));
        
        // 提供结果
        self.provide_result(format!("Result of workflow '{}'", self.name));
    }
}

// 工作流管理器
pub struct WorkflowManager {
    workflows: Vec<(String, Arc<Mutex<StatefulWorkflow>>)>,
}

impl WorkflowManager {
    pub fn new() -> Self {
        Self {
            workflows: Vec::new(),
        }
    }
    
    // 创建工作流
    pub fn create_workflow(&mut self, name: impl Into<String>) -> Arc<Mutex<StatefulWorkflow>> {
        let name_str = name.into();
        let workflow = Arc::new(Mutex::new(StatefulWorkflow::new(name_str.clone())));
        
        self.workflows.push((name_str, workflow.clone()));
        
        workflow
    }
    
    // 启动工作流
    pub fn start_workflow(&self, name: &str) -> Result<(), String> {
        let workflow = self.find_workflow(name)?;
        
        let workflow_clone = workflow.clone();
        thread::spawn(move || {
            let mut workflow = workflow_clone.lock().unwrap();
            workflow.execute();
        });
        
        Ok(())
    }
    
    // 暂停工作流
    pub fn pause_workflow(&self, name: &str) -> Result<(), String> {
        let workflow = self.find_workflow(name)?;
        
        let channel = {
            let wf = workflow.lock().unwrap();
            wf.channel()
        };
        
        channel.send_command(TaskCommand::Pause);
        
        Ok(())
    }
    
    // 恢复工作流
    pub fn resume_workflow(&self, name: &str) -> Result<(), String> {
        let workflow = self.find_workflow(name)?;
        
        let channel = {
            let wf = workflow.lock().unwrap();
            wf.channel()
        };
        
        channel.send_command(TaskCommand::Resume);
        
        Ok(())
    }
    
    // 取消工作流
    pub fn cancel_workflow(&self, name: &str) -> Result<(), String> {
        let workflow = self.find_workflow(name)?;
        
        let channel = {
            let wf = workflow.lock().unwrap();
            wf.channel()
        };
        
        channel.send_command(TaskCommand::Cancel);
        
        Ok(())
    }
    
    // 查找工作流
    fn find_workflow(&self, name: &str) -> Result<Arc<Mutex<StatefulWorkflow>>, String> {
        for (wf_name, workflow) in &self.workflows {
            if wf_name == name {
                return Ok(workflow.clone());
            }
        }
        
        Err(format!("Workflow '{}' not found", name))
    }
}

// 使用状态管理通道示例
fn state_channel_example() {
    // 创建工作流管理器
    let mut manager = WorkflowManager::new();
    
    // 创建工作流
    let workflow = manager.create_workflow("data-processing");
    
    // 添加状态监听器
    {
        let mut wf = workflow.lock().unwrap();
        let channel = wf.channel();
        
        // 创建一个新的状态通道副本
        let mut state_channel = StateChannel::new();
        
        // 订阅事件
        state_channel.subscribe(|event| {
            match event {
                TaskEvent::StateChanged(state) => {
                    println!("State changed: {:?}", state);
                }
                TaskEvent::ProgressUpdate(progress) => {
                    println!("Progress: {:.1}%", progress * 100.0);
                }
                TaskEvent::LogMessage(message) => {
                    println!("Log: {}", message);
                }
                TaskEvent::ResultProduced(result) => {
                    println!("Result produced");
                    // 处理结果...
                }
            }
        });
    }
    
    // 启动工作流
    manager.start_workflow("data-processing").unwrap();
    
    // 等待一段时间后暂停
    thread::sleep(Duration::from_millis(500));
    println!("Pausing workflow...");
    manager.pause_workflow("data-processing").unwrap();
    
    // 等待一段时间后恢复
    thread::sleep(Duration::from_millis(1000));
    println!("Resuming workflow...");
    manager.resume_workflow("data-processing").unwrap();
    
    // 等待工作流完成
    thread::sleep(Duration::from_secs(5));
}
```

**准则**：设计基于状态通道的任务协调机制，支持状态传递、事件通知和命令控制，为同步和异步代码提供统一的通信手段。

## 2. 通用性、可组合性与可监测性

### 2.1 可组合工作流管道

```rust
// 推荐：可组合工作流管道
use std::collections::HashMap;
use std::fmt;
use std::sync::{Arc, Mutex};
use std::time::Instant;

// 工作单元特征
pub trait WorkUnit<I, O, E> {
    // 处理单个输入并产生输出或错误
    fn process(&self, input: I) -> Result<O, E>;
    
    // 工作单元名称
    fn name(&self) -> &str;
    
    // 克隆工作单元
    fn box_clone(&self) -> Box<dyn WorkUnit<I, O, E> + Send + Sync>;
}

impl<I, O, E> Clone for Box<dyn WorkUnit<I, O, E> + Send + Sync>
where
    I: 'static,
    O: 'static,
    E: 'static,
{
    fn clone(&self) -> Self {
        self.box_clone()
    }
}

// 工作管道 - 用于组合多个工作单元
pub struct Pipeline<I, O, E>
where
    I: Clone + 'static,
    O: 'static,
    E: fmt::Debug + 'static,
{
    name: String,
    stages: Vec<Box<dyn WorkUnit<I, O, E> + Send + Sync>>,
    metrics: Arc<Mutex<PipelineMetrics>>,
}

// 管道性能指标
#[derive(Default, Clone)]
pub struct PipelineMetrics {
    processed_count: usize,
    success_count: usize,
    error_count: usize,
    stage_metrics: HashMap<String, StageMetrics>,
}

// 阶段性能指标
#[derive(Default, Clone)]
pub struct StageMetrics {
    calls: usize,
    success_count: usize,
    error_count: usize,
    total_duration: std::time::Duration,
    min_duration: Option<std::time::Duration>,
    max_duration: Option<std::time::Duration>,
}

impl<I, O, E> Pipeline<I, O, E>
where
    I: Clone + 'static,
    O: 'static,
    E: fmt::Debug + 'static,
{
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            stages: Vec::new(),
            metrics: Arc::new(Mutex::new(PipelineMetrics::default())),
        }
    }
    
    // 添加处理阶段
    pub fn add_stage(&mut self, stage: Box<dyn WorkUnit<I, O, E> + Send + Sync>) -> &mut Self {
        // 初始化阶段指标
        {
            let mut metrics = self.metrics.lock().unwrap();
            metrics.stage_metrics.insert(
                stage.name().to_string(),
                StageMetrics::default(),
            );
        }
        
        self.stages.push(stage);
        self
    }
    
    // 处理输入
    pub fn process(&self, input: I) -> Result<Vec<O>, E> {
        let mut results = Vec::new();
        let mut overall_success = true;
        
        // 更新已处理计数
        {
            let mut metrics = self.metrics.lock().unwrap();
            metrics.processed_count += 1;
        }
        
        // 依次执行每个阶段
        for stage in &self.stages {
            let stage_name = stage.name().to_string();
            let start_time = Instant::now();
            
            match stage.process(input.clone()) {
                Ok(output) => {
                    let elapsed = start_time.elapsed();
                    
                    // 更新阶段指标
                    {
                        let mut metrics = self.metrics.lock().unwrap();
                        let stage_metrics = metrics.stage_metrics.get_mut(&stage_name).unwrap();
                        stage_metrics.calls += 1;
                        stage_metrics.success_count += 1;
                        stage_metrics.total_duration += elapsed;
                        
                        if let Some(min) = stage_metrics.min_duration {
                            if elapsed < min {
                                stage_metrics.min_duration = Some(elapsed);
                            }
                        } else {
                            stage_metrics.min_duration = Some(elapsed);
                        }
                        
                        if let Some(max) = stage_metrics.max_duration {
                            if elapsed > max {
                                stage_metrics.max_duration = Some(elapsed);
                            }
                        } else {
                            stage_metrics.max_duration = Some(elapsed);
                        }
                    }
                    
                    results.push(output);
                }
                Err(e) => {
                    let elapsed = start_time.elapsed();
                    
                    // 更新阶段指标
                    {
                        let mut metrics = self.metrics.lock().unwrap();
                        let stage_metrics = metrics.stage_metrics.get_mut(&stage_name).unwrap();
                        stage_metrics.calls += 1;
                        stage_metrics.error_count += 1;
                        stage_metrics.total_duration += elapsed;
                    }
                    
                    overall_success = false;
                    
                    // 更新管道整体指标
                    {
                        let mut metrics = self.metrics.lock().unwrap();
                        metrics.error_count += 1;
                    }
                    
                    // 返回错误
                    return Err(e);
                }
            }
        }
        
        // 更新成功计数
        if overall_success {
            let mut metrics = self.metrics.lock().unwrap();
            metrics.success_count += 1;
        }
        
        Ok(results)
    }
    
    // 批量处理输入
    pub fn process_batch(&self, inputs: Vec<I>) -> Vec<Result<Vec<O>, E>> {
        inputs.into_iter().map(|input| self.process(input)).collect()
    }
    
    // 获取性能指标
    pub fn get_metrics(&self) -> PipelineMetrics {
        let metrics = self.metrics.lock().unwrap();
        metrics.clone()
    }
    
    // 重置性能指标
    pub fn reset_metrics(&self) {
        let mut metrics = self.metrics.lock().unwrap();
        *metrics = PipelineMetrics::default();
        
        // 重新初始化阶段指标
        for stage in &self.stages {
            metrics.stage_metrics.insert(
                stage.name().to_string(),
                StageMetrics::default(),
            );
        }
    }
    
    // 获取管道名称
    pub fn name(&self) -> &str {
        &self.name
    }
    
    // 获取阶段数量
    pub fn stage_count(&self) -> usize {
        self.stages.len()
    }
    
    // 创建管道的克隆
    pub fn clone(&self) -> Self {
        Self {
            name: self.name.clone(),
            stages: self.stages.clone(),
            metrics: Arc::new(Mutex::new(PipelineMetrics::default())),
        }
    }
}

// 函数式工作单元 - 从函数创建工作单元
pub struct FnWorkUnit<I, O, E, F>
where
    F: Fn(I) -> Result<O, E> + Send + Sync + Clone,
{
    name: String,
    func: F,
    _phantom: std::marker::PhantomData<(I, O, E)>,
}

impl<I, O, E, F> FnWorkUnit<I, O, E, F>
where
    F: Fn(I) -> Result<O, E> + Send + Sync + Clone,
{
    pub fn new(name: impl Into<String>, func: F) -> Self {
        Self {
            name: name.into(),
            func,
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<I, O, E, F> WorkUnit<I, O, E> for FnWorkUnit<I, O, E, F>
where
    I: 'static,
    O: 'static,
    E: 'static,
    F: Fn(I) -> Result<O, E> + Send + Sync + Clone + 'static,
{
    fn process(&self, input: I) -> Result<O, E> {
        (self.func)(input)
    }
    
    fn name(&self) -> &str {
        &self.name
    }
    
    fn box_clone(&self) -> Box<dyn WorkUnit<I, O, E> + Send + Sync> {
        Box::new(Self {
            name: self.name.clone(),
            func: self.func.clone(),
            _phantom: std::marker::PhantomData,
        })
    }
}

// 条件工作单元 - 根据条件选择不同的处理路径
pub struct ConditionalWorkUnit<I, O, E>
where
    I: Clone + 'static,
    O: 'static,
    E: 'static,
{
    name: String,
    condition: Box<dyn Fn(&I) -> bool + Send + Sync>,
    if_branch: Box<dyn WorkUnit<I, O, E> + Send + Sync>,
    else_branch: Box<dyn WorkUnit<I, O, E> + Send + Sync>,
}

impl<I, O, E> ConditionalWorkUnit<I, O, E>
where
    I: Clone + 'static,
    O: 'static,
    E: 'static,
{
    pub fn new(
        name: impl Into<String>,
        condition: impl Fn(&I) -> bool + Send + Sync + 'static,
        if_branch: Box<dyn WorkUnit<I, O, E> + Send + Sync>,
        else_branch: Box<dyn WorkUnit<I, O, E> + Send + Sync>,
    ) -> Self {
        Self {
            name: name.into(),
            condition: Box::new(condition),
            if_branch,
            else_branch,
        }
    }
}

impl<I, O, E> WorkUnit<I, O, E> for ConditionalWorkUnit<I, O, E>
where
    I: Clone + 'static,
    O: 'static,
    E: 'static,
{
    fn process(&self, input: I) -> Result<O, E> {
        if (self.condition)(&input) {
            self.if_branch.process(input)
        } else {
            self.else_branch.process(input)
        }
    }
    
    fn name(&self) -> &str {
        &self.name
    }
    
    fn box_clone(&self) -> Box<dyn WorkUnit<I, O, E> + Send + Sync> {
        Box::new(Self {
            name: self.name.clone(),
            condition: self.condition.clone(),
            if_branch: self.if_branch.clone(),
            else_branch: self.else_branch.clone(),
        })
    }
}

impl<F> Clone for Box<dyn Fn(&F) -> bool + Send + Sync>
where
    F: 'static,
{
    fn clone(&self) -> Self {
        let cloned: Box<dyn Fn(&F) -> bool + Send + Sync> = Box::new(move |input| self(input));
        cloned
    }
}

// 重试工作单元 - 在失败时自动重试
pub struct RetryWorkUnit<I, O, E>
where
    I: Clone + 'static,
    O: 'static,
    E: fmt::Debug + 'static,
{
    name: String,
    inner: Box<dyn WorkUnit<I, O, E> + Send + Sync>,
    max_attempts: usize,
}

impl<I, O, E> RetryWorkUnit<I, O, E>
where
    I: Clone + 'static,
    O: 'static,
    E: fmt::Debug + 'static,
{
    pub fn new(
        name: impl Into<String>,
        inner: Box<dyn WorkUnit<I, O, E> + Send + Sync>,
        max_attempts: usize,
    ) -> Self {
        Self {
            name: name.into(),
            inner,
            max_attempts,
        }
    }
}

impl<I, O, E> WorkUnit<I, O, E> for RetryWorkUnit<I, O, E>
where
    I: Clone + 'static,
    O: 'static,
    E: fmt::Debug + 'static,
{
    fn process(&self, input: I) -> Result<O, E> {
        let mut last_error = None;
        
        for attempt in 1..=self.max_attempts {
            match self.inner.process(input.clone()) {
                Ok(output) => return Ok(output),
                Err(e) => {
                    println!("Attempt {} failed: {:?}", attempt, e);
                    last_error = Some(e);
                    
                    if attempt < self.max_attempts {
                        // 简单的指数退避
                        let delay = std::time::Duration::from_millis(100 * (1 << (attempt - 1)));
                        std::thread::sleep(delay);
                    }
                }
            }
        }
        
        Err(last_error.unwrap())
    }
    
    fn name(&self) -> &str {
        &self.name
    }
    
    fn box_clone(&self) -> Box<dyn WorkUnit<I, O, E> + Send + Sync> {
        Box::new(Self {
            name: self.name.clone(),
            inner: self.inner.clone(),
            max_attempts: self.max_attempts,
        })
    }
}

// 组合工作流 - 将多个管道组合成一个复杂工作流
pub struct CompositeWorkflow<I, M, O, E>
where
    I: Clone + 'static,
    M: Clone + 'static,
    O: 'static,
    E: fmt::Debug + 'static,
{
    name: String,
    first_pipeline: Pipeline<I, M, E>,
    second_pipeline: Pipeline<M, O, E>,
    metrics: Arc<Mutex<WorkflowMetrics>>,
}

// 工作流性能指标
#[derive(Default, Clone)]
pub struct WorkflowMetrics {
    total_processed: usize,
    successful: usize,
    failed: usize,
    total_time: std::time::Duration,
}

impl<I, M, O, E> CompositeWorkflow<I, M, O, E>
where
    I: Clone + 'static,
    M: Clone + 'static,
    O: 'static,
    E: fmt::Debug + 'static,
{
    pub fn new(
        name: impl Into<String>,
        first_pipeline: Pipeline<I, M, E>,
        second_pipeline: Pipeline<M, O, E>,
    ) -> Self {
        Self {
            name: name.into(),
            first_pipeline,
            second_pipeline,
            metrics: Arc::new(Mutex::new(WorkflowMetrics::default())),
        }
    }
    
    // 处理输入
    pub fn process(&self, input: I) -> Result<Vec<O>, E> {
        let start_time = Instant::now();
        let mut overall_success = true;
        
        // 更新计数
        {
            let mut metrics = self.metrics.lock().unwrap();
            metrics.total_processed += 1;
        }
        
        // 执行第一个管道
        let intermediate_results = match self.first_pipeline.process(input) {
            Ok(results) => results,
            Err(e) => {
                // 更新指标
                {
                    let mut metrics = self.metrics.lock().unwrap();
                    metrics.failed += 1;
                    metrics.total_time += start_time.elapsed();
                }
                
                return Err(e);
            }
        };
        
        // 收集最终结果
        let mut final_results = Vec::new();
        
        // 将中间结果送入第二个管道
        for intermediate in intermediate_results {
            match self.second_pipeline.process(intermediate) {
                Ok(outputs) => {
                    final_results.extend(outputs);
                }
                Err(e) => {
                    overall_success = false;
                    
                    // 更新指标
                    {
                        let mut metrics = self.metrics.lock().unwrap();
                        metrics.failed += 1;
                        metrics.total_time += start_time.elapsed();
                    }
                    
                    return Err(e);
                }
            }
        }
        
        // 更新指标
        {
            let mut metrics = self.metrics.lock().unwrap();
            if overall_success {
                metrics.successful += 1;
            }
            metrics.total_time += start_time.elapsed();
        }
        
        Ok(final_results)
    }
    
    // 获取性能指标
    pub fn get_metrics(&self) -> WorkflowMetrics {
        let metrics = self.metrics.lock().unwrap();
        metrics.clone()
    }
    
    // 获取工作流名称
    pub fn name(&self) -> &str {
        &self.name
    }
}

// 示例工作单元实现
struct ValidationUnit;

impl WorkUnit<String, String, String> for ValidationUnit {
    fn process(&self, input: String) -> Result<String, String> {
        if input.is_empty() {
            Err("Input cannot be empty".into())
        } else {
            Ok(input)
        }
    }
    
    fn name(&self) -> &str {
        "validator"
    }
    
    fn box_clone(&self) -> Box<dyn WorkUnit<String, String, String> + Send + Sync> {
        Box::new(ValidationUnit)
    }
}

// 使用可组合工作流示例
fn composable_pipeline_example() {
    // 创建第一个管道 - 数据验证和预处理
    let mut preprocessing = Pipeline::<String, String, String>::new("preprocessing");
    
    // 添加验证阶段
    preprocessing.add_stage(Box::new(ValidationUnit));
    
    // 添加清理阶段（使用函数式工作单元）
    preprocessing.add_stage(Box::new(FnWorkUnit::new("cleaner", |input: String| {
        // 移除多余空格
        let cleaned = input.trim().to_string();
        Ok(cleaned)
    })));
    
    // 添加转换阶段
    preprocessing.add_stage(Box::new(FnWorkUnit::new("transformer", |input: String| {
        // 转换为大写
        Ok(input.to_uppercase())
    })));
    
    // 创建第二个管道 - 数据分析
    let mut analysis = Pipeline::<String, u32, String>::new("analysis");
    
    // 添加分词阶段
    analysis.add_stage(Box::new(FnWorkUnit::new("tokenizer", |input: String| {
        // 分词并计数
        let tokens: Vec<&str> = input.split_whitespace().collect();
        Ok(tokens.len() as u32)
    })));
    
    // 添加一个有条件的工作单元
    let condition_unit = ConditionalWorkUnit::new(
        "length_check",
        |&count: &u32| count > 5,
        // 如果词数 > 5
        Box::new(FnWorkUnit::new("complex_analyzer", |count: u32| {
            Ok(count * 2) // 复杂分析
        })),
        // 如果词数 <= 5
        Box::new(FnWorkUnit::new("simple_analyzer", |count: u32| {
            Ok(count) // 简单分析
        })),
    );
    
    analysis.add_stage(Box::new(condition_unit));
    
    // 添加重试工作单元
    let retry_unit = RetryWorkUnit::new(
        "final_analysis_with_retry",
        Box::new(FnWorkUnit::new("final_analysis", |count: u32| {
            // 模拟随机失败
            if rand::random::<f32>() < 0.3 {
                Err(format!("Random failure processing count: {}", count))
            } else {
                Ok(count + 10)
            }
        })),
        3, // 最大尝试次数
    );
    
    analysis.add_stage(Box::new(retry_unit));
    
    // 创建组合工作流
    let workflow = CompositeWorkflow::new(
        "text_analysis_workflow",
        preprocessing,
        analysis,
    );
    
    // 处理样本数据
    let inputs = vec![
        "Hello world".to_string(),
        "This is a longer sentence with more words".to_string(),
        "".to_string(), // 应该导致验证错误
        "Short".to_string(),
    ];
    
    // 处理每个输入
    for (i, input) in inputs.iter().enumerate() {
        println!("Processing input {}: '{}'", i, input);
        
        match workflow.process(input.clone()) {
            Ok(results) => {
                println!("Success! Results: {:?}", results);
            }
            Err(e) => {
                println!("Error: {}", e);
            }
        }
        
        println!("---");
    }
    
    // 显示性能指标
    let workflow_metrics = workflow.get_metrics();
    println!("Workflow metrics:");
    println!("  Total processed: {}", workflow_metrics.total_processed);
    println!("  Successful: {}", workflow_metrics.successful);
    println!("  Failed: {}", workflow_metrics.failed);
    println!("  Total time: {:?}", workflow_metrics.total_time);
}
```

**准则**：设计可组合的工作流管道架构，支持工作单元组合、条件处理和错误处理机制，构建灵活而可监测的数据处理流程。

### 2.2 自定义性能监控框架

```rust
// 推荐：自定义性能监控框架
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

// 性能计数器类型
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum MetricType {
    Counter,    // 累加计数
    Gauge,      // 可变值
    Histogram,  // 值分布
}

// 性能数据点
#[derive(Debug, Clone)]
pub struct DataPoint {
    value: f64,
    timestamp: Instant,
}

impl DataPoint {
    pub fn new(value: f64) -> Self {
        Self {
            value,
            timestamp: Instant::now(),
        }
    }
}

// 性能指标
#[derive(Debug, Clone)]
pub struct Metric {
    name: String,
    metric_type: MetricType,
    description: String,
    data_points: Vec<DataPoint>,
    labels: HashMap<String, String>,
}

impl Metric {
    pub fn new(name: impl Into<String>, metric_type: MetricType, description: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            metric_type,
            description: description.into(),
            data_points: Vec::new(),
            labels: HashMap::new(),
        }
    }
    
    // 添加标签
    pub fn with_label(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.labels.insert(key.into(), value.into());
        self
    }
    
    // 添加数据点
    pub fn add_datapoint(&mut self, value: f64) {
        self.data_points.push(DataPoint::new(value));
        
        // 对于 Histogram 类型，我们保留最近的 1000 个数据点
        if self.metric_type == MetricType::Histogram && self.data_points.len() > 1000 {
            self.data_points.remove(0);
        }
    }
    
    // 获取最新值
    pub fn latest_value(&self) -> Option<f64> {
        self.data_points.last().map(|dp| dp.value)
    }
    
    // 获取计数器类型的总和
    pub fn sum(&self) -> f64 {
        self.data_points.iter().map(|dp| dp.value).sum()
    }
    
    // 获取 Histogram 分位数
    pub fn percentile(&self, percentile: f64) -> Option<f64> {
        if self.data_points.is_empty() {
            return None;
        }
        
        // 收集所有值
        let mut values: Vec<f64> = self.data_points.iter().map(|dp| dp.value).collect();
        values.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
        
        let index = (percentile * values.len() as f64).floor() as usize;
        let index = index.min(values.len() - 1);
        
        Some(values[index])
    }
}

// 指标注册表
pub struct MetricsRegistry {
    metrics: Arc<Mutex<HashMap<String, Metric>>>,
}

impl MetricsRegistry {
    pub fn new() -> Self {
        Self {
            metrics: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    // 注册新指标
    pub fn register(&self, metric: Metric) -> Result<(), String> {
        let name = metric.name.clone();
        let mut metrics = self.metrics.lock().unwrap();
        
        if metrics.contains_key(&name) {
            return Err(format!("Metric with name '{}' already exists", name));
        }
        
        metrics.insert(name, metric);
        Ok(())
    }
    
    // 记录计数器增量
    pub fn increment_counter(&self, name: &str, value: f64) -> Result<(), String> {
        let mut metrics = self.metrics.lock().unwrap();
        
        let metric = metrics.get_mut(name).ok_or_else(|| format!("Metric '{}' not found", name))?;
        
        if metric.metric_type != MetricType::Counter {
            return Err(format!("Metric '{}' is not a counter", name));
        }
        
        // 对于计数器，添加增量值
        let current = metric.latest_value().unwrap_or(0.0);
        metric.add_datapoint(current + value);
        
        Ok(())
    }
    
    // 设置仪表值
    pub fn set_gauge(&self, name: &str, value: f64) -> Result<(), String> {
        let mut metrics = self.metrics.lock().unwrap();
        
        let metric = metrics.get_mut(name).ok_or_else(|| format!("Metric '{}' not found", name))?;
        
        if metric.metric_type != MetricType::Gauge {
            return Err(format!("Metric '{}' is not a gauge", name));
        }
        
        // 对于仪表，直接设置新值
        metric.add_datapoint(value);
        
        Ok(())
    }
    
    // 记录直方图观测值
    pub fn observe_histogram(&self, name: &str, value: f64) -> Result<(), String> {
        let mut metrics = self.metrics.lock().unwrap();
        
        let metric = metrics.get_mut(name).ok_or_else(|| format!("Metric '{}' not found", name))?;
        
        if metric.metric_type != MetricType::Histogram {
            return Err(format!("Metric '{}' is not a histogram", name));
        }
        
        // 对于直方图，添加观测值
        metric.add_datapoint(value);
        
        Ok(())
    }
    
    // 获取指标
    pub fn get_metric(&self, name: &str) -> Option<Metric> {
        let metrics = self.metrics.lock().unwrap();
        metrics.get(name).cloned()
    }
    
    // 获取所有指标
    pub fn get_all_metrics(&self) -> Vec<Metric> {
        let metrics = self.metrics.lock().unwrap();
        metrics.values().cloned().collect()
    }
}

// 性能计时器 - 用于测量代码段执行时间
pub struct Timer {
    registry: Arc<MetricsRegistry>,
    metric_name: String,
    start_time: Instant,
}

impl Timer {
    pub fn new(registry: Arc<MetricsRegistry>, metric_name: impl Into<String>) -> Self {
        Self {
            registry,
            metric_name: metric_name.into(),
            start_time: Instant::now(),
        }
    }
    
    // 停止计时并记录
    pub fn stop(self) -> Result<Duration, String> {
        let elapsed = self.start_time.elapsed();
        
        self.registry.observe_histogram(&self.metric_name, elapsed.as_secs_f64())?;
        
        Ok(elapsed)
    }
}

// 性能指标导出器接口
pub trait MetricsExporter {
    fn export(&self, metrics: &[Metric]) -> Result<(), String>;
}

// 简单的控制台导出器
pub struct ConsoleExporter {
    prefix: String,
}

impl ConsoleExporter {
    pub fn new(prefix: impl Into<String>) -> Self {
        Self {
            prefix: prefix.into(),
        }
    }
}

impl MetricsExporter for ConsoleExporter {
    fn export(&self, metrics: &[Metric]) -> Result<(), String> {
        println!("{}--- Metrics Report ---", self.prefix);
        
        for metric in metrics {
            println!("{}Name: {}", self.prefix, metric.name);
            println!("{}Type: {:?}", self.prefix, metric.metric_type);
            println!("{}Description: {}", self.prefix, metric.description);
            
            if !metric.labels.is_empty() {
                println!("{}Labels:", self.prefix);
                for (k, v) in &metric.labels {
                    println!("{}  {}: {}", self.prefix, k, v);
                }
            }
            
            match metric.metric_type {
                MetricType::Counter => {
                    println!("{}Value: {}", self.prefix, metric.sum());
                }
                MetricType::Gauge => {
                    if let Some(value) = metric.latest_value() {
                        println!("{}Value: {}", self.prefix, value);
                    } else {
                        println!("{}Value: None", self.prefix);
                    }
                }
                MetricType::Histogram => {
                    println!("{}Observations: {}", self.prefix, metric.data_points.len());
                    
                    if !metric.data_points.is_empty() {
                        println!("{}Percentiles:", self.prefix);
                        for p in &[0.5, 0.9, 0.95, 0.99] {
                            if let Some(value) = metric.percentile(*p) {
                                println!("{}  p{}: {}", self.prefix, p * 100.0, value);
                            }
                        }
                    }
                }
            }
            
            println!("{}---", self.prefix);
        }
        
        Ok(())
    }
}

// 指标收集器 - 定期收集和导出指标
pub struct MetricsCollector {
    registry: Arc<MetricsRegistry>,
    exporters: Vec<Box<dyn MetricsExporter + Send + Sync>>,
    collection_interval: Duration,
    shutdown_signal: Arc<Mutex<bool>>,
    collector_thread: Option<thread::JoinHandle<()>>,
}

impl MetricsCollector {
    pub fn new(registry: Arc<MetricsRegistry>) -> Self {
        Self {
            registry,
            exporters: Vec::new(),
            collection_interval: Duration::from_secs(60),
            shutdown_signal: Arc::new(Mutex::new(false)),
            collector_thread: None,
        }
    }
    
    // 添加导出器
    pub fn add_exporter<E: MetricsExporter + Send + Sync + 'static>(&mut self, exporter: E) -> &mut Self {
        self.exporters.push(Box::new(exporter));
        self
    }
    
    // 设置收集间隔
    pub fn with_interval(mut self, interval: Duration) -> Self {
        self.collection_interval = interval;
        self
    }
    
    // 启动收集器
    pub fn start(&mut self) {
        if self.collector_thread.is_some() {
            return; // 已经在运行
        }
        
        // 重置关闭信号
        {
            let mut shutdown = self.shutdown_signal.lock().unwrap();
            *shutdown = false;
        }
        
        let registry = self.registry.clone();
        let exporters = self.exporters.clone();
        let interval = self.collection_interval;
        let shutdown_signal = self.shutdown_signal.clone();
        
        // 启动收集线程
        let handle = thread::spawn(move || {
            loop {
                // 检查是否应该关闭
                {
                    let shutdown = shutdown_signal.lock().unwrap();
                    if *shutdown {
                        break;
                    }
                }
                
                // 收集所有指标
                let metrics = registry.get_all_metrics();
                
                // 导出指标
                for exporter in &exporters {
                    if let Err(e) = exporter.export(&metrics) {
                        eprintln!("Failed to export metrics: {}", e);
                    }
                }
                
                // 等待下一个收集间隔
                thread::sleep(interval);
            }
        });
        
        self.collector_thread = Some(handle);
    }
    
    // 停止收集器
    pub fn stop(&mut self) {
        // 设置关闭信号
        {
            let mut shutdown = self.shutdown_signal.lock().unwrap();
            *shutdown = true;
        }
        
        // 等待收集线程结束
        if let Some(handle) = self.collector_thread.take() {
            let _ = handle.join();
        }
    }
}

// 使用自定义性能监控框架示例
fn custom_metrics_example() {
    // 创建指标注册表
    let registry = Arc::new(MetricsRegistry::new());
    
    // 注册一些指标
    registry.register(Metric::new(
        "request_count",
        MetricType::Counter,
        "Total number of requests",
    ).with_label("service", "api")).unwrap();
    
    registry.register(Metric::new(
        "active_connections",
        MetricType::Gauge,
        "Current number of active connections",
    ).with_label("service", "api")).unwrap();
    
    registry.register(Metric::new(
        "request_duration_seconds",
        MetricType::Histogram,
        "Request duration in seconds",
    ).with_label("service", "api")).unwrap();
    
    // 创建指标收集器
    let mut collector = MetricsCollector::new(registry.clone());
    
    // 添加控制台导出器
    collector.add_exporter(ConsoleExporter::new("  "))
             .with_interval(Duration::from_secs(3));
    
    // 启动收集器
    collector.start();
    
    // 模拟一些应用活动
    for i in 0..10 {
        // 记录请求
        registry.increment_counter("request_count", 1.0).unwrap();
        
        // 更新活动连接
        let connections = 5.0 + (i as f64 * 1.5).sin() * 3.0;
        registry.set_gauge("active_connections", connections).unwrap();
        
        // 测量请求持续时间
        let timer = Timer::new(registry.clone(), "request_duration_seconds");
        
        // 模拟请求处理
        thread::sleep(Duration::from_millis(100 + (rand::random::<u64>() % 150)));
        
        // 停止计时器并记录持续时间
        let duration = timer.stop().unwrap();
        println!("Request {} took {:?}", i, duration);
        
        // 短暂休眠
        thread::sleep(Duration::from_millis(500));
    }
    
    // 运行一段时间后停止收集器
    thread::sleep(Duration::from_secs(5));
    collector.stop();
    
    // 手动导出最终指标
    let exporter = ConsoleExporter::new("");
    let metrics = registry.get_all_metrics();
    exporter.export(&metrics).unwrap();
}
```

**准则**：设计轻量级自定义性能监控框架，支持多种指标类型和导出格式，为工作流和算法提供细粒度的性能分析能力。

## 3. 分布式系统控制与错误处理

### 3.1 状态机与恢复点

```rust
// 推荐：状态机与恢复点模式
use std::collections::HashMap;
use std::fmt;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

// 状态机事件
#[derive(Debug, Clone)]
pub enum Event<TData> {
    Start,
    Transition(String),  // 带有转换原因的转换事件
    Data(TData),         // 数据事件
    Error(String),       // 错误事件
    Complete,
}

// 处理器结果
#[derive(Debug, Clone)]
pub enum ProcessResult<TState, TData> {
    // 转换到新状态
    Transition(TState),
    
    // 保持当前状态
    Continue,
    
    // 生成数据
    Data(TData),
    
    // 出错
    Error(String),
    
    // 完成处理
    Complete,
}

// 状态处理器特征
pub trait StateProcessor<TState, TData> {
    // 处理事件并返回结果
    fn process(&self, event: Event<TData>) -> ProcessResult<TState, TData>;
    
    // 生成检查点数据
    fn checkpoint(&self) -> Option<Vec<u8>> {
        None
    }
    
    // 从检查点恢复
    fn restore(&mut self, _data: &[u8]) -> Result<(), String> {
        Ok(())
    }
}

// 状态机定义
pub struct StateMachine<TState, TData>
where
    TState: Clone + Eq + std::hash::Hash + fmt::Debug,
    TData: Clone,
{
    name: String,
    current_state: TState,
    processors: HashMap<TState, Box<dyn StateProcessor<TState, TData> + Send + Sync>>,
    event_log: Vec<(Instant, TState, Event<TData>)>,
    state_history: Vec<(Instant, TState)>,
    checkpoints: HashMap<TState, Vec<u8>>,
    transition_handlers: Vec<Box<dyn Fn(&TState, &TState) + Send + Sync>>,
}

impl<TState, TData> StateMachine<TState, TData>
where
    TState: Clone + Eq + std::hash::Hash + fmt::Debug,
    TData: Clone,
{
    pub fn new(name: impl Into<String>, initial_state: TState) -> Self {
        let now = Instant::now();
        Self {
            name: name.into(),
            current_state: initial_state.clone(),
            processors: HashMap::new(),
            event_log: Vec::new(),
            state_history: vec![(now, initial_state)],
            checkpoints: HashMap::new(),
            transition_handlers: Vec::new(),
        }
    }
    
    // 注册状态处理器
    pub fn register_processor(
        &mut self,
        state: TState,
        processor: impl StateProcessor<TState, TData> + Send + Sync + 'static,
    ) -> &mut Self {
        self.processors.insert(state, Box::new(processor));
        self
    }
    
    // 注册转换处理器
    pub fn on_transition<F>(&mut self, handler: F) -> &mut Self
    where
        F: Fn(&TState, &TState) + Send + Sync + 'static,
    {
        self.transition_handlers.push(Box::new(handler));
        self
    }
    
    // 发送事件
    pub fn send(&mut self, event: Event<TData>) -> Result<Vec<TData>, String> {
        let start_time = Instant::now();
        let mut collected_data = Vec::new();
        
        // 记录事件
        self.event_log.push((start_time, self.current_state.clone(), event.clone()));
        
        // 获取当前状态的处理器
        let processor = self.processors.get(&self.current_state)
            .ok_or_else(|| format!("No processor registered for state {:?}", self.current_state))?;
        
        // 处理事件
        match processor.process(event) {
            ProcessResult::Transition(next_state) => {
                // 创建当前状态的检查点
                if let Some(checkpoint_data) = processor.checkpoint() {
                    self.checkpoints.insert(self.current_state.clone(), checkpoint_data);
                }
                
                // 记录状态转换
                let previous_state = self.current_state.clone();
                self.current_state = next_state.clone();
                self.state_history.push((Instant::now(), next_state));
                
                // 调用转换处理器
                for handler in &self.transition_handlers {
                    handler(&previous_state, &self.current_state);
                }
                
                // 尝试恢复检查点（如果有）
                if let Some(next_processor) = self.processors.get_mut(&self.current_state) {
                    if let Some(checkpoint_data) = self.checkpoints.get(&self.current_state) {
                        if let Err(e) = next_processor.restore(checkpoint_data) {
                            return Err(format!("Failed to restore checkpoint: {}", e));
                        }
                    }
                }
            }
            ProcessResult::Continue => {
                // 保持当前状态
            }
            ProcessResult::Data(data) => {
                // 收集数据
                collected_data.push(data);
            }
            ProcessResult::Error(message) => {
                return Err(message);
            }
            ProcessResult::Complete => {
                // 处理完成，不需要额外操作
            }
        }
        
        Ok(collected_data)
    }
    
    // 获取当前状态
    pub fn current_state(&self) -> &TState {
        &self.current_state
    }
    
    // 获取状态历史
    pub fn state_history(&self) -> &[(Instant, TState)] {
        &self.state_history
    }
    
    // 获取事件历史
    pub fn event_log(&self) -> &[(Instant, TState, Event<TData>)] {
        &self.event_log
    }
    
    // 创建检查点
    pub fn create_checkpoint(&mut self) -> Result<(), String> {
        let processor = self.processors.get(&self.current_state)
            .ok_or_else(|| format!("No processor registered for state {:?}", self.current_state))?;
            
        if let Some(checkpoint_data) = processor.checkpoint() {
            self.checkpoints.insert(self.current_state.clone(), checkpoint_data);
            Ok(())
        } else {
            Err(format!("Processor for state {:?} does not support checkpointing", self.current_state))
        }
    }
    
    // 恢复到特定状态
    pub fn restore_to_state(&mut self, state: TState) -> Result<(), String> {
        if !self.processors.contains_key(&state) {
            return Err(format!("No processor registered for state {:?}", state));
        }
        
        let checkpoint_data = self.checkpoints.get(&state)
            .ok_or_else(|| format!("No checkpoint available for state {:?}", state))?;
            
        let processor = self.processors.get_mut(&state)
            .ok_or_else(|| format!("No processor registered for state {:?}", state))?;
            
        processor.restore(checkpoint_data)?;
        
        // 更新当前状态
        self.current_state = state.clone();
        self.state_history.push((Instant::now(), state));
        
        Ok(())
    }
}

// 持久化状态机
pub struct PersistentStateMachine<TState, TData>
where
    TState: Clone + Eq + std::hash::Hash + fmt::Debug + serde::Serialize + for<'de> serde::Deserialize<'de>,
    TData: Clone,
{
    state_machine: Arc<Mutex<StateMachine<TState, TData>>>,
    storage_path: String,
}

impl<TState, TData> PersistentStateMachine<TState, TData>
where
    TState: Clone + Eq + std::hash::Hash + fmt::Debug + serde::Serialize + for<'de> serde::Deserialize<'de> + 'static,
    TData: Clone + 'static,
{
    pub fn new(
        name: impl Into<String>,
        initial_state: TState,
        storage_path: impl Into<String>,
    ) -> Self {
        Self {
            state_machine: Arc::new(Mutex::new(StateMachine::new(name, initial_state))),
            storage_path: storage_path.into(),
        }
    }
    
    // 注册状态处理器
    pub fn register_processor(
        &mut self,
        state: TState,
        processor: impl StateProcessor<TState, TData> + Send + Sync + 'static,
    ) -> &mut Self {
        let mut sm = self.state_machine.lock().unwrap();
        sm.register_processor(state, processor);
        self
    }
    
    // 注册转换处理器
    pub fn on_transition<F>(&mut self, handler: F) -> &mut Self
    where
        F: Fn(&TState, &TState) + Send + Sync + 'static,
    {
        let mut sm = self.state_machine.lock().unwrap();
        sm.on_transition(handler);
        self
    }
    
    // 发送事件
    pub fn send(&self, event: Event<TData>) -> Result<Vec<TData>, String> {
        let mut sm = self.state_machine.lock().unwrap();
        let result = sm.send(event);
        
        // 保存状态机状态
        self.save()?;
        
        result
    }
    
    // 保存状态机状态
    fn save(&self) -> Result<(), String> {
        let sm = self.state_machine.lock().unwrap();
        
        // 序列化当前状态
        let state_data = serde_json::to_vec(&sm.current_state)
            .map_err(|e| format!("Failed to serialize state: {}", e))?;
            
        // 写入状态文件
        std::fs::write(format!("{}/current_state.json", self.storage_path), &state_data)
            .map_err(|e| format!("Failed to write state file: {}", e))?;
            
        // 保存检查点
        for (state, checkpoint_data) in &sm.checkpoints {
            let state_name = format!("{:?}", state);
            let file_name = format!("{}/checkpoint_{}.bin", self.storage_path, state_name);
            std::fs::write(&file_name, checkpoint_data)
                .map_err(|e| format!("Failed to write checkpoint file {}: {}", file_name, e))?;
        }
        
        Ok(())
    }
    
    // 从存储中加载状态机
    pub fn load() -> Result<Self, String> {
        // 实际实现会加载状态文件和检查点
        todo!("实现状态机加载功能")
    }
    
    // 获取当前状态
    pub fn current_state(&self) -> TState {
        let sm = self.state_machine.lock().unwrap();
        sm.current_state().clone()
    }
}

// 示例状态定义
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
enum ProcessState {
    Initialized,
    Loading,
    Processing,
    Error,
    Completed,
}

// 示例状态处理器
struct InitializedProcessor {
    counter: usize,
}

impl InitializedProcessor {
    fn new() -> Self {
        Self { counter: 0 }
    }
}

impl StateProcessor<ProcessState, String> for InitializedProcessor {
    fn process(&self, event: Event<String>) -> ProcessResult<ProcessState, String> {
        match event {
            Event::Start => {
                println!("Starting process from initialized state");
                ProcessResult::Transition(ProcessState::Loading)
            }
            Event::Error(msg) => {
                println!("Error in initialized state: {}", msg);
                ProcessResult::Transition(ProcessState::Error)
            }
            _ => ProcessResult::Continue,
        }
    }
    
    fn checkpoint(&self) -> Option<Vec<u8>> {
        // 序列化处理器状态
        let data = format!("counter:{}", self.counter).into_bytes();
        Some(data)
    }
    
    fn restore(&mut self, data: &[u8]) -> Result<(), String> {
        // 反序列化处理器状态
        let data_str = String::from_utf8_lossy(data);
        
        if let Some(value) = data_str.strip_prefix("counter:") {
            self.counter = value.parse().map_err(|_| "Invalid counter value".to_string())?;
            Ok(())
        } else {
            Err("Invalid checkpoint data format".to_string())
        }
    }
}

// 加载状态处理器
struct LoadingProcessor {
    progress: f32,
    loaded_items: Vec<String>,
}

impl LoadingProcessor {
    fn new() -> Self {
        Self { 
            progress: 0.0,
            loaded_items: Vec::new(),
        }
    }
}

impl StateProcessor<ProcessState, String> for LoadingProcessor {
    fn process(&self, event: Event<String>) -> ProcessResult<ProcessState, String> {
        match event {
            Event::Data(item) => {
                println!("Loading data: {}", item);
                
                // 模拟加载完成条件
                if self.loaded_items.len() >= 5 {
                    println!("Loading complete");
                    ProcessResult::Transition(ProcessState::Processing)
                } else {
                    ProcessResult::Continue
                }
            }
            Event::Error(msg) => {
                println!("Error during loading: {}", msg);
                ProcessResult::Transition(ProcessState::Error)
            }
            _ => ProcessResult::Continue,
        }
    }
    
    fn checkpoint(&self) -> Option<Vec<u8>> {
        // 序列化加载进度和数据
        let mut data = format!("progress:{}\n", self.progress).into_bytes();
        
        for item in &self.loaded_items {
            let item_data = format!("item:{}\n", item).into_bytes();
            data.extend_from_slice(&item_data);
        }
        
        Some(data)
    }
    
    fn restore(&mut self, data: &[u8]) -> Result<(), String> {
        // 反序列化加载进度和数据
        let data_str = String::from_utf8_lossy(data);
        let lines: Vec<&str> = data_str.lines().collect();
        
        self.loaded_items.clear();
        
        for line in lines {
            if let Some(value) = line.strip_prefix("progress:") {
                self.progress = value.parse().map_err(|_| "Invalid progress value".to_string())?;
            } else if let Some(value) = line.strip_prefix("item:") {
                self.loaded_items.push(value.to_string());
            }
        }
        
        Ok(())
    }
}

// 使用状态机和恢复点示例
fn stateful_processing_example() {
    // 创建文件系统目录
    let storage_path = "./state_machine_storage";
    std::fs::create_dir_all(storage_path).expect("Failed to create storage directory");
    
    // 创建状态机
    let mut state_machine = PersistentStateMachine::new(
        "data_processing",
        ProcessState::Initialized,
        storage_path,
    );
    
    // 注册状态处理器
    state_machine.register_processor(ProcessState::Initialized, InitializedProcessor::new());
    state_machine.register_processor(ProcessState::Loading, LoadingProcessor::new());
    
    // 注册转换处理器
    state_machine.on_transition(|from, to| {
        println!("State transition: {:?} -> {:?}", from, to);
    });
    
    // 启动处理
    println!("Starting state machine...");
    state_machine.send(Event::Start).expect("Failed to start");
    
    // 加载数据
    for i in 1..=6 {
        println!("Sending data item {}...", i);
        state_machine.send(Event::Data(format!("Item {}", i))).expect("Failed to process data");
    }
    
    // 获取当前状态
    let current_state = state_machine.current_state();
    println!("Current state: {:?}", current_state);
}
```

**准则**：设计基于状态机的工作流处理系统，支持事件处理、状态转换、检查点和恢复功能，提高分布式系统的可靠性和可恢复性。

### 3.2 容错重试与熔断

```rust
// 推荐：容错重试与熔断模式
use std::collections::{HashMap, VecDeque};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

// 错误类型
#[derive(Debug, Clone)]
pub enum RetryableError {
    Transient(String),    // 临时错误，可以重试
    Permanent(String),    // 永久错误，不应重试
}

impl RetryableError {
    pub fn is_transient(&self) -> bool {
        matches!(self, RetryableError::Transient(_))
    }
    
    pub fn message(&self) -> &str {
        match self {
            RetryableError::Transient(msg) => msg,
            RetryableError::Permanent(msg) => msg,
        }
    }
}

// 重试策略
pub trait RetryStrategy: Send + Sync {
    // 决定是否应该重试
    fn should_retry(&self, attempt: usize, error: &RetryableError) -> bool;
    
    // 计算下一次重试的延迟
    fn next_delay(&self, attempt: usize) -> Duration;
}

// 固定间隔重试策略
pub struct FixedIntervalRetry {
    max_attempts: usize,
    delay: Duration,
}

impl FixedIntervalRetry {
    pub fn new(max_attempts: usize, delay: Duration) -> Self {
        Self { max_attempts, delay }
    }
}

impl RetryStrategy for FixedIntervalRetry {
    fn should_retry(&self, attempt: usize, error: &RetryableError) -> bool {
        attempt < self.max_attempts && error.is_transient()
    }
    
    fn next_delay(&self, _attempt: usize) -> Duration {
        self.delay
    }
}

// 指数退避重试策略
pub struct ExponentialBackoffRetry {
    max_attempts: usize,
    initial_delay: Duration,
    max_delay: Duration,
    multiplier: f64,
    jitter: bool,
}

impl ExponentialBackoffRetry {
    pub fn new(max_attempts: usize, initial_delay: Duration) -> Self {
        Self {
            max_attempts,
            initial_delay,
            max_delay: Duration::from_secs(60),
            multiplier: 2.0,
            jitter: true,
        }
    }
    
    pub fn with_max_delay(mut self, max_delay: Duration) -> Self {
        self.max_delay = max_delay;
        self
    }
    
    pub fn with_multiplier(mut self, multiplier: f64) -> Self {
        self.multiplier = multiplier;
        self
    }
    
    pub fn with_jitter(mut self, jitter: bool) -> Self {
        self.jitter = jitter;
        self
    }
}

impl RetryStrategy for ExponentialBackoffRetry {
    fn should_retry(&self, attempt: usize, error: &RetryableError) -> bool {
        attempt < self.max_attempts && error.is_transient()
    }
    
    fn next_delay(&self, attempt: usize) -> Duration {
        // 计算基础延迟
        let base_delay_millis = self.initial_delay.as_millis() as f64 * self.multiplier.powi(attempt as i32);
        let base_delay_millis = base_delay_millis.min(self.max_delay.as_millis() as f64);
        
        // 添加抖动（如果启用）
        let delay_millis = if self.jitter {
            // 添加 -25% 到 +25% 的随机抖动
            let jitter_factor = 0.75 + (rand::random::<f64>() * 0.5);
            (base_delay_millis * jitter_factor) as u64
        } else {
            base_delay_millis as u64
        };
        
        Duration::from_millis(delay_millis)
    }
}

// 重试执行器
pub struct RetryExecutor<S: RetryStrategy> {
    strategy: S,
    metrics: Arc<Mutex<RetryMetrics>>,
}

// 重试指标
#[derive(Default, Clone)]
pub struct RetryMetrics {
    attempt_counts: HashMap<String, usize>,
    success_counts: HashMap<String, usize>,
    failure_counts: HashMap<String, usize>,
}

impl<S: RetryStrategy> RetryExecutor<S> {
    pub fn new(strategy: S) -> Self {
        Self {
            strategy,
            metrics: Arc::new(Mutex::new(RetryMetrics::default())),
        }
    }
    
    // 执行可重试操作
    pub fn execute<F, T>(&self, operation_name: &str, mut operation: F) -> Result<T, RetryableError>
    where
        F: FnMut() -> Result<T, RetryableError>,
    {
        let mut attempt = 0;
        let operation_name = operation_name.to_string();
        
        loop {
            attempt += 1;
            
            // 更新尝试计数
            {
                let mut metrics = self.metrics.lock().unwrap();
                *metrics.attempt_counts.entry(operation_name.clone()).or_insert(0) += 1;
            }
            
            // 执行操作
            match operation() {
                Ok(result) => {
                    // 更新成功计数
                    {
                        let mut metrics = self.metrics.lock().unwrap();
                        *metrics.success_counts.entry(operation_name).or_insert(0) += 1;
                    }
                    
                    return Ok(result);
                }
                Err(error) => {
                    // 检查是否应该重试
                    if self.strategy.should_retry(attempt, &error) {
                        let delay = self.strategy.next_delay(attempt);
                        
                        println!(
                            "Operation '{}' failed with transient error (attempt {}/{}), retrying after {:?}: {}",
                            operation_name, attempt, self.get_max_attempts(), delay, error.message()
                        );
                        
                        // 等待延迟时间
                        std::thread::sleep(delay);
                    } else {
                        // 更新失败计数
                        {
                            let mut metrics = self.metrics.lock().unwrap();
                            *metrics.failure_counts.entry(operation_name).or_insert(0) += 1;
                        }
                        
                        println!(
                            "Operation '{}' failed with error after {} attempts: {}",
                            operation_name, attempt, error.message()
                        );
                        
                        return Err(error);
                    }
                }
            }
        }
    }
    
    // 获取最大尝试次数
    fn get_max_attempts(&self) -> usize {
        // 注：这个方法需要根据具体的策略类型来实现
        // 这里我们假设所有策略都有 max_attempts 属性
        0 // 占位，实际实现会根据策略返回正确的值
    }
    
    // 获取指标
    pub fn get_metrics(&self) -> RetryMetrics {
        let metrics = self.metrics.lock().unwrap();
        metrics.clone()
    }
}

// 断路器状态
#[derive(Debug, Clone, PartialEq)]
enum CircuitState {
    Closed,                 // 正常，允许所有请求
    Open(Instant),          // 断开，拒绝所有请求
    HalfOpen,               // 半开，允许有限请求以测试服务
}

// 断路器
pub struct CircuitBreaker {
    name: String,
    state: Arc<Mutex<CircuitState>>,
    failure_threshold: usize,
    reset_timeout: Duration,
    recent_failures: Arc<Mutex<VecDeque<Instant>>>,
    half_open_allowed: Arc<Mutex<usize>>,
    max_half_open_allowed: usize,
}

impl CircuitBreaker {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            state: Arc::new(Mutex::new(CircuitState::Closed)),
            failure_threshold: 5,
            reset_timeout: Duration::from_secs(30),
            recent_failures: Arc::new(Mutex::new(VecDeque::new())),
            half_open_allowed: Arc::new(Mutex::new(0)),
            max_half_open_allowed: 3,
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
    
    pub fn with_half_open_limit(mut self, limit: usize) -> Self {
        self.max_half_open_allowed = limit;
        self
    }
    
    // 执行受断路器保护的操作
    pub fn execute<F, T, E>(&self, operation: F) -> Result<T, E>
    where
        F: FnOnce() -> Result<T, E>,
        E: std::fmt::Debug,
    {
        // 检查断路器状态
        let can_execute = self.allow_request();
        
        if !can_execute {
            // 断路器开路，返回错误
            return Err(std::mem::zeroed()); // 注：实际代码应返回合适的错误
        }
        
        // 执行操作
        match operation() {
            Ok(result) => {
                // 操作成功，记录成功
                self.record_success();
                Ok(result)
            }
            Err(error) => {
                // 操作失败，记录失败
                self.record_failure();
                Err(error)
            }
        }
    }
    
    // 检查是否允许请求
    fn allow_request(&self) -> bool {
        let state = self.state.lock().unwrap().clone();
        
        match state {
            CircuitState::Closed => true,
            CircuitState::Open(opened_at) => {
                // 检查是否应该进入半开状态
                if opened_at.elapsed() >= self.reset_timeout {
                    // 转换到半开状态
                    let mut state = self.state.lock().unwrap();
                    *state = CircuitState::HalfOpen;
                    
                    // 重置半开状态计数器
                    let mut allowed = self.half_open_allowed.lock().unwrap();
                    *allowed = self.max_half_open_allowed;
                    
                    true
                } else {
                    false
                }
            }
            CircuitState::HalfOpen => {
                // 检查是否还有剩余的半开状态请求计数
                let mut allowed = self.half_open_allowed.lock().unwrap();
                if *allowed > 0 {
                    *allowed -= 1;
                    true
                } else {
                    false
                }
            }
        }
    }
    
    // 记录成功
    fn record_success(&self) {
        let current_state = self.state.lock().unwrap().clone();
        
        if current_state == CircuitState::HalfOpen {
            // 在半开状态下成功，重置断路器
            let mut state = self.state.lock().unwrap();
            *state = CircuitState::Closed;
            
            // 清除失败记录
            let mut failures = self.recent_failures.lock().unwrap();
            failures.clear();
            
            println!("Circuit breaker '{}' reset to closed state after successful test request", self.name);
        }
    }
    
    // 记录失败
    fn record_failure(&self) {
        let current_state = self.state.lock().unwrap().clone();
        
        match current_state {
            CircuitState::Closed => {
                // 添加失败记录
                let now = Instant::now();
                
                {
                    let mut failures = self.recent_failures.lock().unwrap();
                    failures.push_back(now);
                    
                    // 移除过期的失败记录（超过1分钟）
                    while let Some(front) = failures.front() {
                        if front.elapsed() > Duration::from_secs(60) {
                            failures.pop_front();
                        } else {
                            break;
                        }
                    }
                    
                    // 如果失败次数超过阈值，断开断路器
                    if failures.len() >= self.failure_threshold {
                        let mut state = self.state.lock().unwrap();
                        *state = CircuitState::Open(now);
                        
                        println!(
                            "Circuit breaker '{}' tripped open after {} failures",
                            self.name, failures.len()
                        );
                    }
                }
            }
            CircuitState::HalfOpen => {
                // 在半开状态下失败，回到断开状态
                let now = Instant::now();
                let mut state = self.state.lock().unwrap();
                *state = CircuitState::Open(now);
                
                println!(
                    "Circuit breaker '{}' returning to open state after failed test request",
                    self.name
                );
            }
            _ => {}
        }
    }
    
    // 获取当前状态
    pub fn state(&self) -> String {
        let state = self.state.lock().unwrap().clone();
        
        match state {
            CircuitState::Closed => "Closed".to_string(),
            CircuitState::Open(opened_at) => {
                format!("Open (for {:?})", opened_at.elapsed())
            }
            CircuitState::HalfOpen => {
                let allowed = self.half_open_allowed.lock().unwrap();
                format!("Half-Open ({} test requests remaining)", *allowed)
            }
        }
    }
    
    // 获取失败计数
    pub fn failure_count(&self) -> usize {
        let failures = self.recent_failures.lock().unwrap();
        failures.len()
    }
    
    // 手动重置断路器
    pub fn reset(&self) {
        let mut state = self.state.lock().unwrap();
        *state = CircuitState::Closed;
        
        let mut failures = self.recent_failures.lock().unwrap();
        failures.clear();
        
        println!("Circuit breaker '{}' manually reset to closed state", self.name);
    }
}

// 幂等操作记录器
pub struct IdempotencyTracker {
    processed_operations: Arc<Mutex<HashMap<String, (Instant, Option<Vec<u8>>)>>>,
    ttl: Duration,
}

impl IdempotencyTracker {
    pub fn new(ttl: Duration) -> Self {
        Self {
            processed_operations: Arc::new(Mutex::new(HashMap::new())),
            ttl,
        }
    }
    
    // 检查操作是否已处理
    pub fn has_processed(&self, operation_id: &str) -> Option<Vec<u8>> {
        let mut operations = self.processed_operations.lock().unwrap();
        
        // 清理过期记录
        self.cleanup(&mut operations);
        
        // 检查是否存在记录
        if let Some((_, result)) = operations.get(operation_id) {
            result.clone()
        } else {
            None
        }
    }
    
    // 标记操作为已处理
    pub fn mark_processed(&self, operation_id: &str, result: Option<Vec<u8>>) {
        let mut operations = self.processed_operations.lock().unwrap();
        operations.insert(operation_id.to_string(), (Instant::now(), result));
    }
    
    // 清理过期记录
    fn cleanup(&self, operations: &mut HashMap<String, (Instant, Option<Vec<u8>>)>) {
        operations.retain(|_, (timestamp, _)| timestamp.elapsed() < self.ttl);
    }
    
    // 获取已处理操作数量
    pub fn processed_count(&self) -> usize {
        let operations = self.processed_operations.lock().unwrap();
        operations.len()
    }
}

// 综合使用模式：断路器、重试和幂等性
struct NetworkService {
    retry_executor: RetryExecutor<ExponentialBackoffRetry>,
    circuit_breaker: CircuitBreaker,
    idempotency_tracker: IdempotencyTracker,
}

impl NetworkService {
    fn new() -> Self {
        // 设置指数退避重试
        let retry_strategy = ExponentialBackoffRetry::new(
            3,                                     // 最大重试次数
            Duration::from_millis(100),           // 初始延迟
        )
        .with_max_delay(Duration::from_secs(2))   // 最大延迟
        .with_jitter(true);                       // 启用抖动
        
        Self {
            retry_executor: RetryExecutor::new(retry_strategy),
            circuit_breaker: CircuitBreaker::new("network-service")
                .with_failure_threshold(3)
                .with_reset_timeout(Duration::from_secs(10)),
            idempotency_tracker: IdempotencyTracker::new(Duration::from_secs(300)), // 5分钟TTL
        }
    }
    
    // 发送请求
    fn send_request(&self, request_id: &str, data: &str) -> Result<String, String> {
        // 检查请求是否已处理（幂等性检查）
        if let Some(result_bytes) = self.idempotency_tracker.has_processed(request_id) {
            if let Some(bytes) = result_bytes {
                return Ok(String::from_utf8_lossy(&bytes).to_string());
            } else {
                return Err("Previous request failed".to_string());
            }
        }
        
        // 使用断路器和重试执行请求
        let request_id = request_id.to_string();
        let data = data.to_string();
        
        let result = self.circuit_breaker.execute(|| {
            self.retry_executor.execute("send_http_request", || {
                // 模拟网络请求
                self.simulate_network_request(&data)
            })
        });
        
        match result {
            Ok(response) => {
                // 记录成功的操作
                self.idempotency_tracker.mark_processed(&request_id, Some(response.as_bytes().to_vec()));
                Ok(response)
            }
            Err(e) => {
                // 记录失败的操作
                self.idempotency_tracker.mark_processed(&request_id, None);
                Err(format!("Request failed: {:?}", e))
            }
        }
    }
    
    // 模拟网络请求
    fn simulate_network_request(&self, data: &str) -> Result<String, RetryableError> {
        // 模拟网络延迟
        std::thread::sleep(Duration::from_millis(50));
        
        // 模拟随机错误
        let random_value = rand::random::<f32>();
        
        if random_value < 0.3 {
            // 30% 概率出现临时错误
            Err(RetryableError::Transient("Temporary network error".to_string()))
        } else if random_value < 0.4 {
            // 10% 概率出现永久错误
            Err(RetryableError::Permanent("Permanent error: Invalid data".to_string()))
        } else {
            // 60% 概率成功
            Ok(format!("Response for: {}", data))
        }
    }
    
    // 获取断路器状态
    fn circuit_state(&self) -> String {
        self.circuit_breaker.state()
    }
    
    // 获取已处理请求数
    fn processed_count(&self) -> usize {
        self.idempotency_tracker.processed_count()
    }
    
    // 获取重试指标
    fn retry_metrics(&self) -> RetryMetrics {
        self.retry_executor.get_metrics()
    }
}

// 使用容错模式示例
fn fault_tolerance_example() {
    // 创建网络服务
    let service = NetworkService::new();
    
    // 发送多个请求
    for i in 1..=10 {
        let request_id = format!("req-{}", i);
        let data = format!("data-{}", i);
        
        println!("\nSending request {} with id '{}'", i, request_id);
        println!("Circuit state: {}", service.circuit_state());
        
        match service.send_request(&request_id, &data) {
            Ok(response) => {
                println!("Request successful: {}", response);
            }
            Err(e) => {
                println!("Request failed: {}", e);
            }
        }
        
        // 短暂休眠
        std::thread::sleep(Duration::from_millis(200));
    }
    
    // 打印指标
    println!("\nCircuit state: {}", service.circuit_state());
    println!("Processed requests: {}", service.processed_count());
    
    let metrics = service.retry_metrics();
    println!("Retry metrics:");
    for (op, attempts) in metrics.attempt_counts {
        let successes = metrics.success_counts.get(&op).cloned().unwrap_or(0);
        let failures = metrics.failure_counts.get(&op).cloned().unwrap_or(0);
        
        println!("  {}: {} attempts, {} successes, {} failures",
                 op, attempts, successes, failures);
    }
    
    // 等待断路器重置
    if service.circuit_state().starts_with("Open") {
        println!("\nWaiting for circuit breaker to reset...");
        std::thread::sleep(Duration::from_secs(15));
        println!("Circuit state after wait: {}", service.circuit_state());
    }
    
    // 尝试重新发送上一个请求（验证幂等性）
    let last_request_id = "req-10";
    println!("\nResending last request with id '{}'", last_request_id);
    
    match service.send_request(last_request_id, "resent-data") {
        Ok(response) => {
            println!("Request successful: {}", response);
        }
        Err(e) => {
            println!("Request failed: {}", e);
        }
    }
}
```

**准则**：设计综合容错机制，结合重试策略、断路器和幂等性处理，确保分布式系统在面对网络或服务故障时能够可靠运行。

## 4. 工作流与算法集成

### 4.1 工作流内置调度器

```rust
// 推荐：工作流内置调度器
use std::collections::{HashMap, VecDeque};
use std::future::Future;
use std::pin::Pin;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

// 任务标识符
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TaskId(String);

impl TaskId {
    pub fn new(id: impl Into<String>) -> Self {
        Self(id.into())
    }
    
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

// 任务优先级
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Priority {
    Low = 0,
    Normal = 1,
    High = 2,
    Critical = 3,
}

// 任务状态
#[derive(Debug, Clone, PartialEq)]
pub enum TaskStatus {
    Pending,
    Running,
    Completed,
    Failed(String),
    Canceled,
}

// 任务描述
#[derive(Debug, Clone)]
pub struct TaskDescriptor {
    id: TaskId,
    name: String,
    dependencies: Vec<TaskId>,
    priority: Priority,
    max_retries: usize,
    retry_delay: Duration,
}

impl TaskDescriptor {
    pub fn new(id: impl Into<String>, name: impl Into<String>) -> Self {
        Self {
            id: TaskId::new(id),
            name: name.into(),
            dependencies: Vec::new(),
            priority: Priority::Normal,
            max_retries: 0,
            retry_delay: Duration::from_millis(100),
        }
    }
    
    pub fn with_dependency(mut self, dependency: impl Into<TaskId>) -> Self {
        self.dependencies.push(dependency.into());
        self
    }
    
    pub fn with_priority(mut self, priority: Priority) -> Self {
        self.priority = priority;
        self
    }
    
    pub fn with_retry(mut self, max_retries: usize, delay: Duration) -> Self {
        self.max_retries = max_retries;
        self.retry_delay = delay;
        self
    }
}

// 任务定义
pub struct Task<T> {
    descriptor: TaskDescriptor,
    action: Box<dyn FnOnce() -> T + Send + 'static>,
}

impl<T: Send + 'static> Task<T> {
    pub fn new(
        descriptor: TaskDescriptor,
        action: impl FnOnce() -> T + Send + 'static,
    ) -> Self {
        Self {
            descriptor,
            action: Box::new(action),
        }
    }
}

// 异步任务定义
pub struct AsyncTask<T> {
    descriptor: TaskDescriptor,
    action: Box<dyn FnOnce() -> Pin<Box<dyn Future<Output = T> + Send>> + Send + 'static>,
}

impl<T: Send + 'static> AsyncTask<T> {
    pub fn new<F, Fut>(
        descriptor: TaskDescriptor,
        action: F,
    ) -> Self
    where
        F: FnOnce() -> Fut + Send + 'static,
        Fut: Future<Output = T> + Send + 'static,
    {
        Self {
            descriptor,
            action: Box::new(move || Box::pin(action()) as Pin<Box<dyn Future<Output = T> + Send>>),
        }
    }
}

// 任务结果
pub struct TaskResult<T> {
    id: TaskId,
    status: TaskStatus,
    result: Option<T>,
    start_time: Option<Instant>,
    end_time: Option<Instant>,
    retry_count: usize,
}

impl<T> TaskResult<T> {
    fn new(id: TaskId) -> Self {
        Self {
            id,
            status: TaskStatus::Pending,
            result: None,
            start_time: None,
            end_time: None,
            retry_count: 0,
        }
    }
    
    pub fn status(&self) -> &TaskStatus {
        &self.status
    }
    
    pub fn result(&self) -> Option<&T> {
        self.result.as_ref()
    }
    
    pub fn duration(&self) -> Option<Duration> {
        match (self.start_time, self.end_time) {
            (Some(start), Some(end)) => Some(end.duration_since(start)),
            _ => None,
        }
    }
}

// 工作流调度器
pub struct WorkflowScheduler<T: Send + 'static> {
    tasks: HashMap<TaskId, TaskDescriptor>,
    results: HashMap<TaskId, Arc<Mutex<TaskResult<T>>>>,
    pending: VecDeque<TaskId>,
    running: HashMap<TaskId, std::thread::JoinHandle<()>>,
    max_concurrent: usize,
}

impl<T: Send + 'static> WorkflowScheduler<T> {
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            tasks: HashMap::new(),
            results: HashMap::new(),
            pending: VecDeque::new(),
            running: HashMap::new(),
            max_concurrent,
        }
    }
    
    // 注册同步任务
    pub fn register_task(&mut self, task: Task<T>) -> Arc<Mutex<TaskResult<T>>> {
        let descriptor = task.descriptor.clone();
        let id = descriptor.id.clone();
        
        // 创建结果对象
        let result = Arc::new(Mutex::new(TaskResult::new(id.clone())));
        
        // 存储任务和结果
        self.tasks.insert(id.clone(), descriptor);
        self.results.insert(id.clone(), result.clone());
        
        // 将任务放入待处理队列
        self.pending.push_back(id);
        
        result
    }
    
    // 执行工作流
    pub fn execute(&mut self) {
        // 计算初始的可执行任务
        self.update_executable_tasks();
        
        // 循环直到所有任务完成
        while !self.pending.is_empty() || !self.running.is_empty() {
            // 启动新任务（如果可能）
            self.start_pending_tasks();
            
            // 检查运行中的任务
            self.check_running_tasks();
            
            // 短暂暂停，避免忙等
            std::thread::sleep(Duration::from_millis(10));
        }
    }
    
    // 异步执行工作流
    pub async fn execute_async(&mut self) {
        // 计算初始的可执行任务
        self.update_executable_tasks();
        
        // 循环直到所有任务完成
        while !self.pending.is_empty() || !self.running.is_empty() {
            // 启动新任务（如果可能）
            self.start_pending_tasks();
            
            // 检查运行中的任务
            self.check_running_tasks();
            
            // 异步暂停，避免忙等
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    }
    
    // 更新可执行任务列表
    fn update_executable_tasks(&mut self) {
        // 按优先级排序
        self.pending.make_contiguous().sort_by(|a, b| {
            let priority_a = self.tasks[a].priority;
            let priority_b = self.tasks[b].priority;
            priority_b.cmp(&priority_a) // 高优先级排在前面
        });
        
        // 过滤掉依赖未满足的任务
        let mut i = 0;
        while i < self.pending.len() {
            let id = &self.pending[i];
            let descriptor = &self.tasks[id];
            
            let all_deps_satisfied = descriptor.dependencies.iter().all(|dep_id| {
                if let Some(result) = self.results.get(dep_id) {
                    let result = result.lock().unwrap();
                    matches!(result.status, TaskStatus::Completed)
                } else {
                    false
                }
            });
            
            if all_deps_satisfied {
                i += 1;
            } else {
                // 将不满足依赖的任务移到队列末尾
                let id = self.pending.remove(i).unwrap();
                self.pending.push_back(id);
            }
        }
    }
    
    // 启动待处理任务
    fn start_pending_tasks(&mut self) {
        while self.running.len() < self.max_concurrent && !self.pending.is_empty() {
            // 选择下一个要执行的任务
            if let Some(task_id) = self.pending.pop_front() {
                let descriptor = self.tasks[&task_id].clone();
                let result_arc = self.results[&task_id].clone();
                
                // 更新任务状态
                {
                    let mut result = result_arc.lock().unwrap();
                    result.status = TaskStatus::Running;
                    result.start_time = Some(Instant::now());
                }
                
                // 启动任务线程
                let handle = std::thread::spawn(move || {
                    // 执行任务
                    // 注意：这里我们假设任务是同步的，实际实现应该处理 Task<T> 对象
                    
                    // 更新结果
                    let mut result = result_arc.lock().unwrap();
                    result.status = TaskStatus::Completed;
                    result.end_time = Some(Instant::now());
                });
                
                // 存储线程句柄
                self.running.insert(task_id, handle);
            }
        }
    }
    
    // 检查运行中的任务
    fn check_running_tasks(&mut self) {
        // 收集已完成的任务
        let finished: Vec<TaskId> = self.running.iter()
            .filter(|(_, handle)| handle.is_finished())
            .map(|(id, _)| id.clone())
            .collect();
        
        // 处理已完成的任务
        for id in finished {
            if let Some(handle) = self.running.remove(&id) {
                // 我们不需要做任何事情，因为任务已经更新了它的结果
                drop(handle);
            }
            
            // 更新可执行任务列表
            self.update_executable_tasks();
        }
    }
    
    // 获取任务结果
    pub fn get_result(&self, id: &TaskId) -> Option<Arc<Mutex<TaskResult<T>>>> {
        self.results.get(id).cloned()
    }
    
    // 获取所有结果
    pub fn get_all_results(&self) -> HashMap<TaskId, Arc<Mutex<TaskResult<T>>>> {
        self.results.clone()
    }
    
    // 取消任务
    pub fn cancel_task(&mut self, id: &TaskId) -> Result<(), String> {
        // 检查任务是否存在
        if !self.tasks.contains_key(id) {
            return Err(format!("Task {} not found", id.as_str()));
        }
        
        // 如果任务在待处理队列中，直接移除
        let mut i = 0;
        while i < self.pending.len() {
            if &self.pending[i] == id {
                self.pending.remove(i);
                
                // 更新任务状态
                if let Some(result_arc) = self.results.get(id) {
                    let mut result = result_arc.lock().unwrap();
                    result.status = TaskStatus::Canceled;
                }
                
                return Ok(());
            }
            i += 1;
        }
        
        // 如果任务正在运行，我们无法直接取消它
        // 实际实现可能需要一种机制来通知任务取消
        if self.running.contains_key(id) {
            return Err(format!("Cannot cancel running task {}", id.as_str()));
        }
        
        Ok(())
    }
}

// 工作流构建器
pub struct WorkflowBuilder<T: Send + 'static> {
    tasks: Vec<Task<T>>,
    max_concurrent: usize,
}

impl<T: Send + 'static> WorkflowBuilder<T> {
    pub fn new() -> Self {
        Self {
            tasks: Vec::new(),
            max_concurrent: 4, // 默认并发数
        }
    }
    
    pub fn add_task(&mut self, task: Task<T>) -> &mut Self {
        self.tasks.push(task);
        self
    }
    
    pub fn with_max_concurrent(&mut self, max: usize) -> &mut Self {
        self.max_concurrent = max;
        self
    }
    
    pub fn build(self) -> WorkflowScheduler<T> {
        let mut scheduler = WorkflowScheduler::new(self.max_concurrent);
        
        for task in self.tasks {
            scheduler.register_task(task);
        }
        
        scheduler
    }
}

// 使用工作流调度器示例
fn workflow_scheduler_example() {
    // 创建工作流构建器
    let mut builder = WorkflowBuilder::<String>::new();
    
    // 添加一些任务
    builder.add_task(Task::new(
        TaskDescriptor::new("task1", "Data Fetching")
            .with_priority(Priority::High),
        || {
            println!("Fetching data...");
            std::thread::sleep(Duration::from_millis(500));
            "Data fetched".to_string()
        }
    ));
    
    builder.add_task(Task::new(
        TaskDescriptor::new("task2", "Data Processing")
            .with_dependency(TaskId::new("task1"))
            .with_retry(2, Duration::from_millis(200)),
        || {
            println!("Processing data...");
            std::thread::sleep(Duration::from_millis(300));
            "Data processed".to_string()
        }
    ));
    
    builder.add_task(Task::new(
        TaskDescriptor::new("task3", "Report Generation")
            .with_dependency(TaskId::new("task2")),
        || {
            println!("Generating report...");
            std::thread::sleep(Duration::from_millis(200));
            "Report generated".to_string()
        }
    ));
    
    // 设置最大并发数
    builder.with_max_concurrent(2);
    
    // 构建工作流
    let mut workflow = builder.build();
    
    // 执行工作流
    println!("Starting workflow execution...");
    workflow.execute();
    
    // 获取所有结果
    let results = workflow.get_all_results();
    
    println!("Workflow execution completed. Results:");
    for (id, result_arc) in results {
        let result = result_arc.lock().unwrap();
        
        println!("Task {}: {:?}", id.as_str(), result.status());
        
        if let Some(value) = result.result() {
            println!("  Result: {}", value);
        }
        
        if let Some(duration) = result.duration() {
            println!("  Duration: {:?}", duration);
        }
        
        println!();
    }
}
```

**准则**：设计工作流内置调度器，管理任务依赖关系、优先级和执行顺序，提供统一的任务执行和监控接口。

### 4.2 算法与工作流集成器

```rust
// 推荐：算法与工作流集成器
use std::collections::HashMap;
use std::marker::PhantomData;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

// 算法接口
pub trait Algorithm<Input, Output, Error> {
    // 算法名称
    fn name(&self) -> &str;
    
    // 执行算法
    fn execute(&self, input: Input) -> Result<Output, Error>;
    
    // 估计执行时间
    fn estimate_execution_time(&self, input: &Input) -> Duration {
        // 默认实现返回一个保守估计
        Duration::from_secs(1)
    }
    
    // 估计内存使用量（字节）
    fn estimate_memory_usage(&self, input: &Input) -> usize {
        // 默认实现返回一个保守估计
        1024 * 1024 // 1MB
    }
    
    // 算法复杂度
    fn complexity(&self) -> &str {
        "Unknown"
    }
}

// 算法包装器 - 用于计算和记录性能指标
pub struct InstrumentedAlgorithm<A, I, O, E>
where
    A: Algorithm<I, O, E>,
{
    inner: A,
    execution_times: Arc<Mutex<Vec<Duration>>>,
    error_count: Arc<Mutex<usize>>,
    _phantom: PhantomData<(I, O, E)>,
}

impl<A, I, O, E> InstrumentedAlgorithm<A, I, O, E>
where
    A: Algorithm<I, O, E>,
{
    pub fn new(algorithm: A) -> Self {
        Self {
            inner: algorithm,
            execution_times: Arc::new(Mutex::new(Vec::new())),
            error_count: Arc::new(Mutex::new(0)),
            _phantom: PhantomData,
        }
    }
    
    // 获取平均执行时间
    pub fn average_execution_time(&self) -> Option<Duration> {
        let times = self.execution_times.lock().unwrap();
        
        if times.is_empty() {
            return None;
        }
        
        let total = times.iter().sum::<Duration>();
        Some(total / times.len() as u32)
    }
    
    // 获取最长执行时间
    pub fn max_execution_time(&self) -> Option<Duration> {
        let times = self.execution_times.lock().unwrap();
        times.iter().max().cloned()
    }
    
    // 获取错误计数
    pub fn error_count(&self) -> usize {
        let count = self.error_count.lock().unwrap();
        *count
    }
    
    // 获取执行计数
    pub fn execution_count(&self) -> usize {
        let times = self.execution_times.lock().unwrap();
        times.len()
    }
}

impl<A, I, O, E> Algorithm<I, O, E> for InstrumentedAlgorithm<A, I, O, E>
where
    A: Algorithm<I, O, E>,
{
    fn name(&self) -> &str {
        self.inner.name()
    }
    
    fn execute(&self, input: I) -> Result<O, E> {
        let start_time = Instant::now();
        
        let result = self.inner.execute(input);
        
        let elapsed = start_time.elapsed();
        
        // 记录执行时间
        let mut times = self.execution_times.lock().unwrap();
        times.push(elapsed);
        
        // 记录错误（如果有）
        if result.is_err() {
            let mut count = self.error_count.lock().unwrap();
            *count += 1;
        }
        
        result
    }
    
    fn estimate_execution_time(&self, input: &I) -> Duration {
        self.inner.estimate_execution_time(input)
    }
    
    fn estimate_memory_usage(&self, input: &I) -> usize {
        self.inner.estimate_memory_usage(input)
    }
    
    fn complexity(&self) -> &str {
        self.inner.complexity()
    }
}

// 分段算法 - 把大型任务分解为小块
pub struct ChunkedAlgorithm<A, I, O, E>
where
    A: Algorithm<I, O, E>,
{
    inner: A,
    chunk_size: usize,
    _phantom: PhantomData<(I, O, E)>,
}

impl<A, I, O, E> ChunkedAlgorithm<A, I, O, E>
where
    A: Algorithm<I, O, E>,
    I: Clone,
{
    pub fn new(algorithm: A, chunk_size: usize) -> Self {
        Self {
            inner: algorithm,
            chunk_size,
            _phantom: PhantomData,
        }
    }
    
    // 分块处理数据
    pub fn process_chunks<Iter, Combiner>(
        &self,
        items: Iter,
        combiner: Combiner,
    ) -> Result<O, E>
    where
        Iter: IntoIterator<Item = I>,
        Combiner: FnMut(Vec<O>) -> Result<O, E>,
    {
        let iterator = items.into_iter();
        let mut results = Vec::new();
        let mut current_chunk = Vec::with_capacity(self.chunk_size);
        
        for item in iterator {
            current_chunk.push(item);
            
            if current_chunk.len() >= self.chunk_size {
                // 处理当前块
                for chunk_item in current_chunk.drain(..) {
                    results.push(self.inner.execute(chunk_item)?);
                }
            }
        }
        
        // 处理剩余的项
        for chunk_item in current_chunk {
            results.push(self.inner.execute(chunk_item)?);
        }
        
        // 合并结果
        combiner(results)
    }
}

impl<A, I, O, E> Algorithm<I, O, E> for ChunkedAlgorithm<A, I, O, E>
where
    A: Algorithm<I, O, E>,
    I: Clone,
{
    fn name(&self) -> &str {
        self.inner.name()
    }
    
    fn execute(&self, input: I) -> Result<O, E> {
        self.inner.execute(input)
    }
    
    fn estimate_execution_time(&self, input: &I) -> Duration {
        self.inner.estimate_execution_time(input)
    }
    
    fn estimate_memory_usage(&self, input: &I) -> usize {
        self.inner.estimate_memory_usage(input)
    }
    
    fn complexity(&self) -> &str {
        self.inner.complexity()
    }
}

// 自适应算法 - 根据输入特性选择最佳实现
pub struct AdaptiveAlgorithm<I, O, E> {
    name: String,
    implementations: Vec<Box<dyn Algorithm<I, O, E> + Send + Sync>>,
    selector: Box<dyn Fn(&I) -> usize + Send + Sync>,
}

impl<I, O, E> AdaptiveAlgorithm<I, O, E> {
    pub fn new(
        name: impl Into<String>,
        selector: impl Fn(&I) -> usize + Send + Sync + 'static,
    ) -> Self {
        Self {
            name: name.into(),
            implementations: Vec::new(),
            selector: Box::new(selector),
        }
    }
    
    // 添加算法实现
    pub fn add_implementation(
        &mut self,
        implementation: impl Algorithm<I, O, E> + Send + Sync + 'static,
    ) -> &mut Self {
        self.implementations.push(Box::new(implementation));
        self
    }
    
    // 获取实现数量
    pub fn implementation_count(&self) -> usize {
        self.implementations.len()
    }
}

impl<I, O, E> Algorithm<I, O, E> for AdaptiveAlgorithm<I, O, E> {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn execute(&self, input: I) -> Result<O, E> {
        // 选择最佳实现
        let input_ref = &input;
        let index = (self.selector)(input_ref);
        
        // 检查索引是否有效
        if index >= self.implementations.len() {
            // 在实际应用中，这应该返回适当的错误
            // 这里为简化示例，我们使用第一个实现
            return self.implementations[0].execute(input);
        }
        
        // 执行选定的实现
        self.implementations[index].execute(input)
    }
    
    fn estimate_execution_time(&self, input: &I) -> Duration {
        // 获取选择器建议的实现
        let index = (self.selector)(input);
        let index = index.min(self.implementations.len() - 1);
        
        self.implementations[index].estimate_execution_time(input)
    }
    
    fn estimate_memory_usage(&self, input: &I) -> usize {
        // 获取选择器建议的实现
        let index = (self.selector)(input);
        let index = index.min(self.implementations.len() - 1);
        
        self.implementations[index].estimate_memory_usage(input)
    }
    
    fn complexity(&self) -> &str {
        "Adaptive" // 复杂度取决于选择的实现
    }
}

// 工作流与算法集成器
pub struct AlgorithmWorkflow<I, O, E> {
    stages: Vec<AlgorithmStage<I, O, E>>,
    metrics: Arc<Mutex<WorkflowMetrics>>,
    name: String,
}

// 算法阶段
pub struct AlgorithmStage<I, O, E> {
    algorithm: Box<dyn Algorithm<I, O, E> + Send + Sync>,
    name: String,
    next_stages: Vec<usize>, // 索引到下一个阶段
}

// 工作流指标
#[derive(Default, Clone)]
pub struct WorkflowMetrics {
    stage_execution_times: HashMap<String, Vec<Duration>>,
    stage_error_counts: HashMap<String, usize>,
    total_executions: usize,
    successful_executions: usize,
}

impl<I: 'static, O: 'static, E: 'static> AlgorithmWorkflow<I, O, E> {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            stages: Vec::new(),
            metrics: Arc::new(Mutex::new(WorkflowMetrics::default())),
            name: name.into(),
        }
    }
    
    // 添加算法阶段
    pub fn add_stage(
        &mut self,
        name: impl Into<String>,
        algorithm: impl Algorithm<I, O, E> + Send + Sync + 'static,
    ) -> usize {
        let stage = AlgorithmStage {
            algorithm: Box::new(algorithm),
            name: name.into(),
            next_stages: Vec::new(),
        };
        
        let index = self.stages.len();
        self.stages.push(stage);
        
        // 初始化阶段指标
        {
            let mut metrics = self.metrics.lock().unwrap();
            metrics.stage_execution_times.insert(self.stages[index].name.clone(), Vec::new());
            metrics.stage_error_counts.insert(self.stages[index].name.clone(), 0);
        }
        
        index
    }
    
    // 添加阶段之间的连接
    pub fn connect_stages(&mut self, from_index: usize, to_index: usize) -> Result<(), String> {
        if from_index >= self.stages.len() || to_index >= self.stages.len() {
            return Err("Invalid stage index".to_string());
        }
        
        self.stages[from_index].next_stages.push(to_index);
        Ok(())
    }
    
    // 执行工作流
    pub fn execute(&self, input: I) -> Result<HashMap<String, O>, E> {
        let start_time = Instant::now();
        
        // 更新执行计数
        {
            let mut metrics = self.metrics.lock().unwrap();
            metrics.total_executions += 1;
        }
        
        // 跟踪哪些阶段已执行
        let mut executed_stages = HashMap::new();
        
        // 从第一个阶段开始
        if self.stages.is_empty() {
            return Ok(HashMap::new());
        }
        
        // 创建入口阶段的队列
        let mut stage_queue = vec![0]; // 从索引 0 开始
        
        // 处理所有阶段
        while !stage_queue.is_empty() {
            let stage_index = stage_queue.remove(0);
            let stage = &self.stages[stage_index];
            
            // 执行当前阶段
            let stage_start = Instant::now();
            let result = stage.algorithm.execute(input.clone());
            let stage_elapsed = stage_start.elapsed();
            
            // 更新阶段指标
            {
                let mut metrics = self.metrics.lock().unwrap();
                metrics.stage_execution_times
                    .get_mut(&stage.name)
                    .unwrap()
                    .push(stage_elapsed);
            }
            
            match result {
                Ok(output) => {
                    // 存储结果
                    executed_stages.insert(stage.name.clone(), output);
                    
                    // 将下一个阶段添加到队列
                    for &next_index in &stage.next_stages {
                        if !stage_queue.contains(&next_index) {
                            stage_queue.push(next_index);
                        }
                    }
                }
                Err(e) => {
                    // 更新错误计数
                    {
                        let mut metrics = self.metrics.lock().unwrap();
                        *metrics.stage_error_counts.get_mut(&stage.name).unwrap() += 1;
                    }
                    
                    return Err(e);
                }
            }
        }
        
        // 更新成功执行计数
        {
            let mut metrics = self.metrics.lock().unwrap();
            metrics.successful_executions += 1;
        }
        
        Ok(executed_stages)
    }
    
    // 获取工作流指标
    pub fn get_metrics(&self) -> WorkflowMetrics {
        let metrics = self.metrics.lock().unwrap();
        metrics.clone()
    }
    
    // 获取工作流名称
    pub fn name(&self) -> &str {
        &self.name
    }
    
    // 重置指标
    pub fn reset_metrics(&self) {
        let mut metrics = self.metrics.lock().unwrap();
        *metrics = WorkflowMetrics::default();
        
        // 重新初始化阶段指标
        for stage in &self.stages {
            metrics.stage_execution_times.insert(stage.name.clone(), Vec::new());
            metrics.stage_error_counts.insert(stage.name.clone(), 0);
        }
    }
}

// 示例算法实现
struct SortingAlgorithm {
    name: String,
}

impl SortingAlgorithm {
    fn new(name: impl Into<String>) -> Self {
        Self { name: name.into() }
    }
}

impl Algorithm<Vec<i32>, Vec<i32>, String> for SortingAlgorithm {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn execute(&self, mut input: Vec<i32>) -> Result<Vec<i32>, String> {
        println!("Executing sorting algorithm '{}'", self.name);
        
        if self.name == "quick_sort" {
            // 快速排序实现
            if input.is_empty() {
                return Ok(Vec::new());
            }
            
            // 简化版快速排序
            let pivot = input[0];
            let mut left = Vec::new();
            let mut right = Vec::new();
            
            for &item in &input[1..] {
                if item <= pivot {
                    left.push(item);
                } else {
                    right.push(item);
                }
            }
            
            // 递归排序
            match self.execute(left) {
                Ok(mut sorted_left) => {
                    sorted_left.push(pivot);
                    
                    match self.execute(right) {
                        Ok(sorted_right) => {
                            sorted_left.extend(sorted_right);
                            Ok(sorted_left)
                        }
                        Err(e) => Err(e),
                    }
                }
                Err(e) => Err(e),
            }
        } else {
            // 默认使用标准库排序
            input.sort();
            Ok(input)
        }
    }
    
    fn estimate_execution_time(&self, input: &Vec<i32>) -> Duration {
        // 简单估计：O(n log n)
        let n = input.len();
        if n <= 1 {
            Duration::from_micros(1)
        } else {
            let estimated_ns = (n as f64 * (n as f64).log2()) as u64;
            Duration::from_nanos(estimated_ns * 100) // 缩放因子
        }
    }
    
    fn estimate_memory_usage(&self, input: &Vec<i32>) -> usize {
        // 内存估计：输入大小 + 临时存储
        let element_size = std::mem::size_of::<i32>();
        input.len() * element_size * 2
    }
    
    fn complexity(&self) -> &str {
        "O(n log n)"
    }
}

// 使用算法与工作流集成器示例
fn algorithm_workflow_example() {
    // 创建算法
    let quick_sort = SortingAlgorithm::new("quick_sort");
    let merge_sort = SortingAlgorithm::new("merge_sort");
    
    // 创建一个自适应排序算法
    let mut adaptive_sort = AdaptiveAlgorithm::new("adaptive_sort", |input: &Vec<i32>| {
        // 根据输入大小选择算法：
        // - 小数组使用快速排序 (索引 0)
        // - 大数组使用归并排序 (索引 1)
        if input.len() < 1000 { 0 } else { 1 }
    });
    
    adaptive_sort.add_implementation(quick_sort);
    adaptive_sort.add_implementation(merge_sort);
    
    // 对自适应算法进行计时
    let instrumented_sort = InstrumentedAlgorithm::new(adaptive_sort);
    
    // 创建工作流
    let mut workflow = AlgorithmWorkflow::<Vec<i32>, Vec<i32>, String>::new("data_processing");
    
    // 添加阶段
    let sort_stage = workflow.add_stage("sorting", instrumented_sort);
    let filter_stage = workflow.add_stage("filtering", 
        FnWorkUnit::new("filter_even", |input: Vec<i32>| {
            println!("Filtering even numbers");
            Ok(input.into_iter().filter(|&x| x % 2 == 0).collect())
        })
    );
    
    // 连接阶段
    workflow.connect_stages(sort_stage, filter_stage).unwrap();
    
    // 准备输入数据
    let input_data: Vec<i32> = (0..100).rev().collect();
    
    // 执行工作流
    println!("Executing workflow '{}'", workflow.name());
    match workflow.execute(input_data) {
        Ok(results) => {
            for (stage_name, result) in results {
                println!("Result from stage '{}': {:?}", stage_name, result);
            }
        }
        Err(e) => {
            println!("Workflow execution failed: {}", e);
        }
    }
    
    // 打印指标
    let metrics = workflow.get_metrics();
    println!("\nWorkflow metrics:");
    println!("  Total executions: {}", metrics.total_executions);
    println!("  Successful executions: {}", metrics.successful_executions);
    
    for (stage, times) in metrics.stage_execution_times {
        if !times.is_empty() {
            let total: Duration = times.iter().sum();
            let avg = total / times.len() as u32;
            let error_count = metrics.stage_error_counts.get(&stage).unwrap_or(&0);
            
            println!("  Stage '{}': {} executions, avg time {:?}, {} errors", 
                     stage, times.len(), avg, error_count);
        }
    }
}

// 函数式工作单元 - 从函数创建算法
pub struct FnWorkUnit<I, O, E, F>
where
    F: Fn(I) -> Result<O, E> + Send + Sync,
{
    name: String,
    func: F,
    _phantom: PhantomData<(I, O, E)>,
}

impl<I, O, E, F> FnWorkUnit<I, O, E, F>
where
    F: Fn(I) -> Result<O, E> + Send + Sync,
{
    pub fn new(name: impl Into<String>, func: F) -> Self {
        Self {
            name: name.into(),
            func,
            _phantom: PhantomData,
        }
    }
}

impl<I, O, E, F> Algorithm<I, O, E> for FnWorkUnit<I, O, E, F>
where
    F: Fn(I) -> Result<O, E> + Send + Sync,
{
    fn name(&self) -> &str {
        &self.name
    }
    
    fn execute(&self, input: I) -> Result<O, E> {
        (self.func)(input)
    }
}
```

**准则**：设计算法与工作流集成器，将各种算法封装为可组合的工作单元，支持多路径工作流和自适应算法选择。

## 5. 总结：工作流与算法设计准则

### 5.1 同步、异步与并行模式

1. **统一执行模型**：设计支持同步、异步、并发和并行处理的统一任务执行模型，使开发者能够根据任务特性选择合适的执行方式。

2. **状态透明传递**：实现基于状态通道的通信机制，在同步和异步代码之间安全传递状态和命令，支持进度跟踪和任务控制。

3. **资源适应性**：根据系统资源状态自动调整任务执行策略，在负载高峰期降低并发度，在资源充足时提高处理能力。

4. **回压机制**：在工作流各环节实现回压支持，防止快速生产者压垮慢速消费者，确保系统稳定运行。

### 5.2 组合性与可监测性

1. **模块化设计**：将工作流拆分为可独立测试和重用的模块，通过清晰的接口实现灵活组合。

2. **声明式配置**：支持通过声明式方式定义工作流，使复杂流程更易于理解和维护。

3. **内置监测**：在工作流组件中集成性能和健康监测功能，收集细粒度指标，实现问题早期发现和根因分析。

4. **结构化日志**：实现结构化的上下文日志记录，关联工作流执行的各个环节，便于追踪和调试。

### 5.3 分布式控制与错误处理

1. **状态机模式**：采用显式状态机设计模式，确保工作流状态变化可追踪、可恢复，支持检查点和回滚。

2. **弹性重试**：实现智能重试策略，区分临时和永久错误，采用退避算法避免重试风暴。

3. **断路保护**：在面向外部系统的接口处实现断路器模式，防止级联故障，保护系统核心功能。

4. **幂等设计**：确保关键操作具有幂等性，支持安全重试和操作恢复，避免重复处理导致的数据不一致。

### 5.4 算法与工作流集成

1. **算法抽象**：设计通用算法接口，统一不同算法的调用方式，支持运行时切换和组合。

2. **自适应选择**：实现上下文感知的算法选择机制，根据输入特性、资源状态自动选择最优算法。

3. **分解与并行**：支持大型任务的自动分解和并行处理，平衡负载并充分利用可用资源。

4. **进度反馈**：为长时间运行的算法提供进度反馈机制，使外部系统能够监控执行状态。

通过遵循这些设计准则，可以构建既灵活又高效的工作流和算法系统，不依赖外部组件也能实现强大的功能、可靠的错误处理和优秀的性能特性。
