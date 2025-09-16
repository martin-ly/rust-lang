//! # 工作流引擎核心实现 / Workflow Engine Core Implementation
//!
//! 本模块提供了工作流引擎的完整实现，包括事件处理、状态管理和性能优化。
//! This module provides the complete implementation of the workflow engine, including event processing, state management, and performance optimization.

use crate::error::*;
use crate::types::*;
use serde_json::Value;
use std::collections::HashMap;
use std::sync::{Arc, Mutex, RwLock};
use std::time::Instant;
use tokio::sync::mpsc;
use tokio::time::Duration;

/// 工作流引擎 / Workflow Engine
///
/// 核心工作流执行引擎，负责管理工作流定义、实例和事件处理。
/// Core workflow execution engine responsible for managing workflow definitions, instances, and event processing.
pub struct WorkflowEngine {
    /// 工作流定义存储 / Workflow Definition Storage
    workflows: Arc<RwLock<HashMap<String, WorkflowDefinition>>>,
    /// 工作流实例存储 / Workflow Instance Storage
    instances: Arc<RwLock<HashMap<String, WorkflowInstance>>>,
    /// 事件发送器 / Event Sender
    event_sender: mpsc::Sender<WorkflowEvent>,
    /// 事件接收器 / Event Receiver
    event_receiver: Option<mpsc::Receiver<WorkflowEvent>>,
    /// 性能监控器 / Performance Monitor
    performance_monitor: Arc<PerformanceMonitor>,
    /// 配置选项 / Configuration Options
    config: EngineConfig,
}

/// 引擎配置 / Engine Configuration
#[derive(Debug, Clone)]
pub struct EngineConfig {
    /// 最大并发实例数 / Maximum Concurrent Instances
    pub max_concurrent_instances: usize,
    /// 事件队列大小 / Event Queue Size
    pub event_queue_size: usize,
    /// 超时设置 / Timeout Settings
    pub default_timeout: Duration,
    /// 性能监控启用 / Performance Monitoring Enabled
    pub enable_performance_monitoring: bool,
    /// 持久化启用 / Persistence Enabled
    pub enable_persistence: bool,
}

impl Default for EngineConfig {
    fn default() -> Self {
        Self {
            max_concurrent_instances: 1000,
            event_queue_size: 10000,
            default_timeout: Duration::from_secs(300), // 5 minutes
            enable_performance_monitoring: true,
            enable_persistence: false,
        }
    }
}

impl WorkflowEngine {
    /// 创建新的工作流引擎 / Create New Workflow Engine
    pub fn new() -> Self {
        Self::with_config(EngineConfig::default())
    }

    /// 使用配置创建工作流引擎 / Create Workflow Engine with Configuration
    pub fn with_config(config: EngineConfig) -> Self {
        let (event_sender, event_receiver) = mpsc::channel(config.event_queue_size);
        let performance_monitor = Arc::new(PerformanceMonitor::new());

        Self {
            workflows: Arc::new(RwLock::new(HashMap::new())),
            instances: Arc::new(RwLock::new(HashMap::new())),
            event_sender,
            event_receiver: Some(event_receiver),
            performance_monitor,
            config,
        }
    }

    /// 注册工作流定义 / Register Workflow Definition
    pub async fn register_workflow(
        &self,
        name: String,
        definition: WorkflowDefinition,
    ) -> Result<(), WorkflowError> {
        let start_time = Instant::now();

        // 验证工作流定义 / Validate workflow definition
        if let Err(e) = definition.validate() {
            return Err(WorkflowError::ValidationError(e.to_string()));
        }

        // 检查循环依赖 / Check for circular dependencies
        if crate::types::utils::has_cycles(&definition) {
            return Err(WorkflowError::ValidationError(
                "Circular dependency detected".to_string(),
            ));
        }

        // 存储工作流定义 / Store workflow definition
        {
            let mut workflows = self.workflows.write().unwrap();
            workflows.insert(name.clone(), definition);
        }

        // 记录性能指标 / Record performance metrics
        if self.config.enable_performance_monitoring {
            self.performance_monitor.record_operation(
                "register_workflow",
                start_time.elapsed(),
                Some(name),
            );
        }

        Ok(())
    }

    /// 启动工作流实例 / Start Workflow Instance
    pub async fn start_workflow(
        &self,
        name: &str,
        initial_data: WorkflowData,
    ) -> Result<String, WorkflowError> {
        let start_time = Instant::now();

        // 检查工作流定义是否存在 / Check if workflow definition exists
        let _definition = {
            let workflows = self.workflows.read().unwrap();
            workflows
                .get(name)
                .ok_or_else(|| WorkflowError::WorkflowNotFound(name.to_string()))?
                .clone()
        };

        // 检查并发实例数限制 / Check concurrent instance limit
        {
            let instances = self.instances.read().unwrap();
            if instances.len() >= self.config.max_concurrent_instances {
                return Err(WorkflowError::ResourceLimitExceeded(
                    "Maximum concurrent instances reached".to_string(),
                ));
            }
        }

        // 创建实例ID / Create instance ID
        let instance_id = crate::types::utils::generate_instance_id();

        // 创建工作流实例 / Create workflow instance
        let instance = WorkflowInstance::new(instance_id.clone(), name.to_string(), initial_data);

        // 存储实例 / Store instance
        {
            let mut instances = self.instances.write().unwrap();
            instances.insert(instance_id.clone(), instance);
        }

        // 发送启动事件 / Send start event
        let event = WorkflowEvent::Start {
            instance_id: instance_id.clone(),
            workflow_name: name.to_string(),
        };

        self.event_sender
            .send(event)
            .await
            .map_err(|_| WorkflowError::EventChannelClosed)?;

        // 记录性能指标 / Record performance metrics
        if self.config.enable_performance_monitoring {
            self.performance_monitor.record_operation(
                "start_workflow",
                start_time.elapsed(),
                Some(instance_id.clone()),
            );
        }

        Ok(instance_id)
    }

    /// 获取工作流实例状态 / Get Workflow Instance State
    pub async fn get_workflow_state(&self, instance_id: &str) -> Result<String, WorkflowError> {
        let instances = self.instances.read().unwrap();
        let instance = instances
            .get(instance_id)
            .ok_or_else(|| WorkflowError::InstanceNotFound(instance_id.to_string()))?;

        Ok(instance.current_state.clone())
    }

    /// 处理工作流事件 / Handle Workflow Events
    pub async fn process_events(&mut self) -> Result<(), WorkflowError> {
        while let Some(receiver) = &mut self.event_receiver {
            if let Some(event) = receiver.recv().await {
                let start_time = Instant::now();

                match event {
                    WorkflowEvent::Start {
                        instance_id,
                        workflow_name,
                    } => {
                        self.handle_start_event(instance_id, workflow_name).await?;
                    }
                    WorkflowEvent::StateTransition {
                        instance_id,
                        from_state,
                        to_state,
                        data,
                    } => {
                        self.handle_state_transition_event(instance_id, from_state, to_state, data)
                            .await?;
                    }
                    WorkflowEvent::Complete {
                        instance_id,
                        result,
                    } => {
                        self.handle_complete_event(instance_id, result).await?;
                    }
                    WorkflowEvent::Error { instance_id, error } => {
                        self.handle_error_event(instance_id, error).await?;
                    }
                    WorkflowEvent::Timeout { instance_id, state } => {
                        self.handle_timeout_event(instance_id, state).await?;
                    }
                }

                // 记录事件处理性能 / Record event processing performance
                if self.config.enable_performance_monitoring {
                    self.performance_monitor.record_operation(
                        "process_event",
                        start_time.elapsed(),
                        None,
                    );
                }
            } else {
                break;
            }
        }

        Ok(())
    }

    /// 处理启动事件 / Handle Start Event
    async fn handle_start_event(
        &self,
        instance_id: String,
        workflow_name: String,
    ) -> Result<(), WorkflowError> {
        // 获取工作流定义 / Get workflow definition
        let definition = {
            let workflows = self.workflows.read().unwrap();
            workflows
                .get(&workflow_name)
                .ok_or_else(|| WorkflowError::WorkflowNotFound(workflow_name.clone()))?
                .clone()
        };

        // 更新实例状态 / Update instance state
        {
            let mut instances = self.instances.write().unwrap();
            if let Some(instance) = instances.get_mut(&instance_id) {
                instance.current_state = definition.initial_state.clone();
                instance.updated_at = Instant::now();
            }
        }

        // 发送状态转换事件 / Send state transition event
        let event = WorkflowEvent::StateTransition {
            instance_id: instance_id.clone(),
            from_state: "initial".to_string(),
            to_state: definition.initial_state,
            data: None,
        };

        self.event_sender
            .send(event)
            .await
            .map_err(|_| WorkflowError::EventChannelClosed)?;

        Ok(())
    }

    /// 处理状态转换事件 / Handle State Transition Event
    async fn handle_state_transition_event(
        &self,
        instance_id: String,
        _from_state: String,
        to_state: String,
        data: Option<Value>,
    ) -> Result<(), WorkflowError> {
        // 更新实例状态 / Update instance state
        {
            let mut instances = self.instances.write().unwrap();
            if let Some(instance) = instances.get_mut(&instance_id) {
                instance.transition(to_state.clone(), data);
            }
        }

        // 检查是否为最终状态 / Check if final state
        let is_final = {
            let workflows = self.workflows.read().unwrap();
            if let Some(definition) = workflows.get(&instance_id) {
                definition.final_states.contains(&to_state)
            } else {
                false
            }
        };

        if is_final {
            // 发送完成事件 / Send complete event
            let event = WorkflowEvent::Complete {
                instance_id: instance_id.clone(),
                result: serde_json::json!({"status": "completed", "final_state": to_state}),
            };

            self.event_sender
                .send(event)
                .await
                .map_err(|_| WorkflowError::EventChannelClosed)?;
        }

        Ok(())
    }

    /// 处理完成事件 / Handle Complete Event
    async fn handle_complete_event(
        &self,
        instance_id: String,
        result: Value,
    ) -> Result<(), WorkflowError> {
        // 更新实例状态 / Update instance state
        {
            let mut instances = self.instances.write().unwrap();
            if let Some(instance) = instances.get_mut(&instance_id) {
                instance.complete(result);
            }
        }

        Ok(())
    }

    /// 处理错误事件 / Handle Error Event
    async fn handle_error_event(
        &self,
        instance_id: String,
        error: String,
    ) -> Result<(), WorkflowError> {
        // 更新实例状态 / Update instance state
        {
            let mut instances = self.instances.write().unwrap();
            if let Some(instance) = instances.get_mut(&instance_id) {
                instance.mark_error(error);
            }
        }

        Ok(())
    }

    /// 处理超时事件 / Handle Timeout Event
    async fn handle_timeout_event(
        &self,
        instance_id: String,
        state: String,
    ) -> Result<(), WorkflowError> {
        // 更新实例状态 / Update instance state
        {
            let mut instances = self.instances.write().unwrap();
            if let Some(instance) = instances.get_mut(&instance_id) {
                instance.mark_error(format!("Timeout in state: {}", state));
            }
        }

        Ok(())
    }

    /// 获取工作流实例 / Get Workflow Instance
    pub fn get_instance(&self, instance_id: &str) -> Option<WorkflowInstance> {
        let instances = self.instances.read().unwrap();
        instances.get(instance_id).cloned()
    }

    /// 获取所有实例 / Get All Instances
    pub fn get_all_instances(&self) -> Vec<WorkflowInstance> {
        let instances = self.instances.read().unwrap();
        instances.values().cloned().collect()
    }

    /// 获取性能统计 / Get Performance Statistics
    pub fn get_performance_stats(&self) -> PerformanceStats {
        self.performance_monitor.get_stats()
    }

    /// 清理完成的实例 / Clean Up Completed Instances
    pub async fn cleanup_completed_instances(&self) -> Result<usize, WorkflowError> {
        let mut instances = self.instances.write().unwrap();
        let initial_count = instances.len();

        instances.retain(|_, instance| {
            matches!(
                instance.status,
                WorkflowStatus::Running | WorkflowStatus::Paused
            )
        });

        let removed_count = initial_count - instances.len();
        Ok(removed_count)
    }
}

/// 性能监控器 / Performance Monitor
///
/// 监控工作流引擎的性能指标。
/// Monitor performance metrics of the workflow engine.
pub struct PerformanceMonitor {
    /// 操作统计 / Operation Statistics
    operations: Arc<Mutex<HashMap<String, OperationStats>>>,
    /// 总体统计 / Overall Statistics
    overall_stats: Arc<Mutex<OverallStats>>,
}

/// 操作统计 / Operation Statistics
#[derive(Debug, Clone)]
pub struct OperationStats {
    /// 调用次数 / Call Count
    pub call_count: u64,
    /// 总执行时间 / Total Execution Time
    pub total_time: Duration,
    /// 平均执行时间 / Average Execution Time
    pub avg_time: Duration,
    /// 最小执行时间 / Minimum Execution Time
    pub min_time: Duration,
    /// 最大执行时间 / Maximum Execution Time
    pub max_time: Duration,
    /// 最后调用时间 / Last Call Time
    pub last_call: Option<Instant>,
}

impl OperationStats {
    /// 创建新的操作统计 / Create New Operation Statistics
    pub fn new() -> Self {
        Self {
            call_count: 0,
            total_time: Duration::ZERO,
            avg_time: Duration::ZERO,
            min_time: Duration::MAX,
            max_time: Duration::ZERO,
            last_call: None,
        }
    }

    /// 更新统计信息 / Update Statistics
    pub fn update(&mut self, execution_time: Duration) {
        self.call_count += 1;
        self.total_time += execution_time;
        self.avg_time = self.total_time / self.call_count as u32;
        self.min_time = self.min_time.min(execution_time);
        self.max_time = self.max_time.max(execution_time);
        self.last_call = Some(Instant::now());
    }
}

/// 总体统计 / Overall Statistics
#[derive(Debug, Clone)]
pub struct OverallStats {
    /// 总操作次数 / Total Operations
    pub total_operations: u64,
    /// 总执行时间 / Total Execution Time
    pub total_execution_time: Duration,
    /// 平均响应时间 / Average Response Time
    pub avg_response_time: Duration,
    /// 启动时间 / Start Time
    pub start_time: Instant,
    /// 最后活动时间 / Last Activity Time
    pub last_activity: Option<Instant>,
}

impl OverallStats {
    /// 创建新的总体统计 / Create New Overall Statistics
    pub fn new() -> Self {
        Self {
            total_operations: 0,
            total_execution_time: Duration::ZERO,
            avg_response_time: Duration::ZERO,
            start_time: Instant::now(),
            last_activity: None,
        }
    }

    /// 更新统计信息 / Update Statistics
    pub fn update(&mut self, execution_time: Duration) {
        self.total_operations += 1;
        self.total_execution_time += execution_time;
        self.avg_response_time = self.total_execution_time / self.total_operations as u32;
        self.last_activity = Some(Instant::now());
    }
}

impl PerformanceMonitor {
    /// 创建新的性能监控器 / Create New Performance Monitor
    pub fn new() -> Self {
        Self {
            operations: Arc::new(Mutex::new(HashMap::new())),
            overall_stats: Arc::new(Mutex::new(OverallStats::new())),
        }
    }

    /// 记录操作 / Record Operation
    pub fn record_operation(
        &self,
        operation_name: &str,
        execution_time: Duration,
        _context: Option<String>,
    ) {
        // 更新操作统计 / Update operation statistics
        {
            let mut operations = self.operations.lock().unwrap();
            let stats = operations
                .entry(operation_name.to_string())
                .or_insert_with(OperationStats::new);
            stats.update(execution_time);
        }

        // 更新总体统计 / Update overall statistics
        {
            let mut overall_stats = self.overall_stats.lock().unwrap();
            overall_stats.update(execution_time);
        }
    }

    /// 获取统计信息 / Get Statistics
    pub fn get_stats(&self) -> PerformanceStats {
        let operations = self.operations.lock().unwrap();
        let overall_stats = self.overall_stats.lock().unwrap();

        PerformanceStats {
            operations: operations.clone(),
            overall: overall_stats.clone(),
        }
    }
}

/// 性能统计 / Performance Statistics
#[derive(Debug, Clone)]
pub struct PerformanceStats {
    /// 操作统计 / Operation Statistics
    pub operations: HashMap<String, OperationStats>,
    /// 总体统计 / Overall Statistics
    pub overall: OverallStats,
}

/// 工作流引擎构建器 / Workflow Engine Builder
///
/// 提供流式API来配置和创建工作流引擎。
/// Provides fluent API to configure and create workflow engines.
pub struct WorkflowEngineBuilder {
    config: EngineConfig,
}

impl WorkflowEngineBuilder {
    /// 创建新的构建器 / Create New Builder
    pub fn new() -> Self {
        Self {
            config: EngineConfig::default(),
        }
    }

    /// 设置最大并发实例数 / Set Maximum Concurrent Instances
    pub fn max_concurrent_instances(mut self, max: usize) -> Self {
        self.config.max_concurrent_instances = max;
        self
    }

    /// 设置事件队列大小 / Set Event Queue Size
    pub fn event_queue_size(mut self, size: usize) -> Self {
        self.config.event_queue_size = size;
        self
    }

    /// 设置默认超时 / Set Default Timeout
    pub fn default_timeout(mut self, timeout: Duration) -> Self {
        self.config.default_timeout = timeout;
        self
    }

    /// 启用性能监控 / Enable Performance Monitoring
    pub fn enable_performance_monitoring(mut self, enable: bool) -> Self {
        self.config.enable_performance_monitoring = enable;
        self
    }

    /// 启用持久化 / Enable Persistence
    pub fn enable_persistence(mut self, enable: bool) -> Self {
        self.config.enable_persistence = enable;
        self
    }

    /// 构建工作流引擎 / Build Workflow Engine
    pub fn build(self) -> WorkflowEngine {
        WorkflowEngine::with_config(self.config)
    }
}

/// 工作流引擎管理器 / Workflow Engine Manager
///
/// 管理多个工作流引擎实例。
/// Manage multiple workflow engine instances.
pub struct WorkflowEngineManager {
    /// 引擎实例 / Engine Instances
    engines: Arc<RwLock<HashMap<String, Arc<WorkflowEngine>>>>,
}

impl WorkflowEngineManager {
    /// 创建新的管理器 / Create New Manager
    pub fn new() -> Self {
        Self {
            engines: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 添加引擎 / Add Engine
    pub fn add_engine(&self, name: String, engine: WorkflowEngine) {
        let mut engines = self.engines.write().unwrap();
        engines.insert(name, Arc::new(engine));
    }

    /// 获取引擎 / Get Engine
    pub fn get_engine(&self, name: &str) -> Option<Arc<WorkflowEngine>> {
        let engines = self.engines.read().unwrap();
        engines.get(name).cloned()
    }

    /// 移除引擎 / Remove Engine
    pub fn remove_engine(&self, name: &str) -> Option<Arc<WorkflowEngine>> {
        let mut engines = self.engines.write().unwrap();
        engines.remove(name)
    }

    /// 获取所有引擎名称 / Get All Engine Names
    pub fn get_engine_names(&self) -> Vec<String> {
        let engines = self.engines.read().unwrap();
        engines.keys().cloned().collect()
    }
}
