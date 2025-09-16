//! # 工作流状态管理模块 / Workflow State Management Module
//!
//! 本模块提供了完整的工作流状态管理功能，基于状态机理论和分布式协调理论。
//! This module provides complete workflow state management functionality based on state machine theory and distributed coordination theory.

use crate::types::*;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::collections::HashMap;
use std::sync::{Arc, Mutex, RwLock};
use std::time::{Duration, Instant};

mod timestamp_serde {
    use super::*;

    pub fn serialize<S>(instant: &Instant, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_u64(instant.elapsed().as_nanos() as u64)
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<Instant, D::Error>
    where
        D: Deserializer<'de>,
    {
        let nanos = u64::deserialize(deserializer)?;
        Ok(Instant::now() - Duration::from_nanos(nanos))
    }

    pub fn serialize_option<S>(instant: &Option<Instant>, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match instant {
            Some(inst) => serialize(inst, serializer),
            None => serializer.serialize_none(),
        }
    }

    pub fn deserialize_option<'de, D>(deserializer: D) -> Result<Option<Instant>, D::Error>
    where
        D: Deserializer<'de>,
    {
        let nanos = Option::<u64>::deserialize(deserializer)?;
        match nanos {
            Some(n) => Ok(Some(Instant::now() - Duration::from_nanos(n))),
            None => Ok(None),
        }
    }
}

/// 状态管理器 / State Manager
///
/// 负责管理工作流实例的状态转换和生命周期。
/// Responsible for managing state transitions and lifecycle of workflow instances.
pub struct StateManager {
    /// 状态定义存储 / State Definition Storage
    states: Arc<RwLock<HashMap<String, StateDefinition>>>,
    /// 实例状态存储 / Instance State Storage
    instance_states: Arc<RwLock<HashMap<String, InstanceState>>>,
    /// 状态转换历史 / State Transition History
    transition_history: Arc<Mutex<Vec<StateTransitionRecord>>>,
    /// 状态监听器 / State Listeners
    listeners: Arc<Mutex<HashMap<String, Vec<StateListener>>>>,
    /// 配置选项 / Configuration Options
    config: StateManagerConfig,
}

/// 状态管理器配置 / State Manager Configuration
#[derive(Debug, Clone)]
pub struct StateManagerConfig {
    /// 最大状态数 / Maximum States
    pub max_states: usize,
    /// 状态超时时间 / State Timeout
    pub state_timeout: Duration,
    /// 是否启用状态验证 / Enable State Validation
    pub enable_validation: bool,
    /// 是否启用状态持久化 / Enable State Persistence
    pub enable_persistence: bool,
    /// 状态清理间隔 / State Cleanup Interval
    pub cleanup_interval: Duration,
}

impl Default for StateManagerConfig {
    fn default() -> Self {
        Self {
            max_states: 1000,
            state_timeout: Duration::from_secs(3600), // 1 hour
            enable_validation: true,
            enable_persistence: false,
            cleanup_interval: Duration::from_secs(300), // 5 minutes
        }
    }
}

/// 状态定义 / State Definition
///
/// 定义工作流状态的结构和行为。
/// Defines the structure and behavior of workflow states.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StateDefinition {
    /// 状态名称 / State Name
    pub name: String,
    /// 状态描述 / State Description
    pub description: Option<String>,
    /// 状态类型 / State Type
    pub state_type: StateType,
    /// 进入动作 / Entry Actions
    pub entry_actions: Vec<String>,
    /// 退出动作 / Exit Actions
    pub exit_actions: Vec<String>,
    /// 状态超时 / State Timeout
    pub timeout: Option<Duration>,
    /// 重试策略 / Retry Strategy
    pub retry_strategy: Option<RetryStrategy>,
    /// 状态元数据 / State Metadata
    pub metadata: HashMap<String, serde_json::Value>,
}

/// 状态类型 / State Type
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum StateType {
    /// 初始状态 / Initial State
    Initial,
    /// 中间状态 / Intermediate State
    Intermediate,
    /// 最终状态 / Final State
    Final,
    /// 错误状态 / Error State
    Error,
    /// 暂停状态 / Paused State
    Paused,
}

/// 重试策略 / Retry Strategy
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RetryStrategy {
    /// 最大重试次数 / Maximum Retry Count
    pub max_retries: usize,
    /// 重试延迟 / Retry Delay
    pub retry_delay: Duration,
    /// 退避策略 / Backoff Strategy
    pub backoff_strategy: BackoffStrategy,
}

/// 退避策略 / Backoff Strategy
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum BackoffStrategy {
    /// 固定延迟 / Fixed Delay
    Fixed(Duration),
    /// 指数退避 / Exponential Backoff
    Exponential {
        base_delay: Duration,
        max_delay: Duration,
    },
    /// 线性退避 / Linear Backoff
    Linear {
        base_delay: Duration,
        increment: Duration,
    },
}

/// 实例状态 / Instance State
///
/// 工作流实例的当前状态信息。
/// Current state information of workflow instances.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InstanceState {
    /// 实例ID / Instance ID
    pub instance_id: String,
    /// 当前状态 / Current State
    pub current_state: String,
    /// 状态数据 / State Data
    pub state_data: HashMap<String, serde_json::Value>,
    /// 状态进入时间 / State Entry Time
    #[serde(with = "timestamp_serde")]
    pub entry_time: Instant,
    /// 状态超时时间 / State Timeout Time
    #[serde(
        serialize_with = "timestamp_serde::serialize_option",
        deserialize_with = "timestamp_serde::deserialize_option"
    )]
    pub timeout_time: Option<Instant>,
    /// 重试计数 / Retry Count
    pub retry_count: usize,
    /// 状态历史 / State History
    pub history: Vec<StateHistoryEntry>,
    /// 状态锁 / State Lock
    pub is_locked: bool,
    /// 锁定时间 / Lock Time
    #[serde(
        serialize_with = "timestamp_serde::serialize_option",
        deserialize_with = "timestamp_serde::deserialize_option"
    )]
    pub lock_time: Option<Instant>,
}

/// 状态历史条目 / State History Entry
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StateHistoryEntry {
    /// 状态名称 / State Name
    pub state_name: String,
    /// 进入时间 / Entry Time
    #[serde(with = "timestamp_serde")]
    pub entry_time: Instant,
    /// 退出时间 / Exit Time
    #[serde(
        serialize_with = "timestamp_serde::serialize_option",
        deserialize_with = "timestamp_serde::deserialize_option"
    )]
    pub exit_time: Option<Instant>,
    /// 停留时长 / Duration
    pub duration: Option<Duration>,
    /// 状态数据 / State Data
    pub state_data: HashMap<String, serde_json::Value>,
    /// 转换原因 / Transition Reason
    pub transition_reason: Option<String>,
}

/// 状态监听器 / State Listener
///
/// 监听状态变化事件的回调函数。
/// Callback function for listening to state change events.
pub type StateListener = Box<dyn Fn(StateChangeEvent) + Send + Sync>;

/// 状态变化事件 / State Change Event
#[derive(Debug, Clone)]
pub struct StateChangeEvent {
    /// 实例ID / Instance ID
    pub instance_id: String,
    /// 源状态 / Source State
    pub from_state: String,
    /// 目标状态 / Target State
    pub to_state: String,
    /// 变化时间 / Change Time
    pub change_time: Instant,
    /// 变化原因 / Change Reason
    pub reason: Option<String>,
    /// 状态数据 / State Data
    pub state_data: HashMap<String, serde_json::Value>,
}

impl StateManager {
    /// 创建新的状态管理器 / Create New State Manager
    pub fn new() -> Self {
        Self::with_config(StateManagerConfig::default())
    }

    /// 使用配置创建状态管理器 / Create State Manager with Configuration
    pub fn with_config(config: StateManagerConfig) -> Self {
        Self {
            states: Arc::new(RwLock::new(HashMap::new())),
            instance_states: Arc::new(RwLock::new(HashMap::new())),
            transition_history: Arc::new(Mutex::new(Vec::new())),
            listeners: Arc::new(Mutex::new(HashMap::new())),
            config,
        }
    }

    /// 注册状态定义 / Register State Definition
    pub fn register_state(&self, definition: StateDefinition) -> Result<(), StateError> {
        // 验证状态定义 / Validate state definition
        self.validate_state_definition(&definition)?;

        // 检查状态数量限制 / Check state count limit
        {
            let states = self.states.read().unwrap();
            if states.len() >= self.config.max_states {
                return Err(StateError::StateLimitExceeded(self.config.max_states));
            }
        }

        // 存储状态定义 / Store state definition
        {
            let mut states = self.states.write().unwrap();
            states.insert(definition.name.clone(), definition);
        }

        Ok(())
    }

    /// 创建实例状态 / Create Instance State
    pub fn create_instance_state(
        &self,
        instance_id: String,
        initial_state: String,
    ) -> Result<(), StateError> {
        // 验证初始状态是否存在 / Validate if initial state exists
        {
            let states = self.states.read().unwrap();
            if !states.contains_key(&initial_state) {
                return Err(StateError::StateNotFound(initial_state));
            }
        }

        // 创建实例状态 / Create instance state
        let instance_state = InstanceState {
            instance_id: instance_id.clone(),
            current_state: initial_state,
            state_data: HashMap::new(),
            entry_time: Instant::now(),
            timeout_time: None,
            retry_count: 0,
            history: Vec::new(),
            is_locked: false,
            lock_time: None,
        };

        // 存储实例状态 / Store instance state
        {
            let mut instance_states = self.instance_states.write().unwrap();
            instance_states.insert(instance_id, instance_state);
        }

        Ok(())
    }

    /// 执行状态转换 / Execute State Transition
    pub fn transition_state(
        &self,
        instance_id: &str,
        to_state: String,
        transition_data: Option<HashMap<String, serde_json::Value>>,
        reason: Option<String>,
    ) -> Result<(), StateError> {
        // 获取实例状态 / Get instance state
        let mut instance_states = self.instance_states.write().unwrap();
        let instance_state = instance_states
            .get_mut(instance_id)
            .ok_or_else(|| StateError::InstanceNotFound(instance_id.to_string()))?;

        // 检查状态锁 / Check state lock
        if instance_state.is_locked {
            return Err(StateError::StateLocked(instance_id.to_string()));
        }

        // 验证目标状态 / Validate target state
        let states = self.states.read().unwrap();
        if !states.contains_key(&to_state) {
            return Err(StateError::StateNotFound(to_state));
        }

        // 记录历史 / Record history
        let from_state = instance_state.current_state.clone();
        let entry_time = instance_state.entry_time;
        let exit_time = Instant::now();
        let duration = exit_time.duration_since(entry_time);

        let history_entry = StateHistoryEntry {
            state_name: from_state.clone(),
            entry_time,
            exit_time: Some(exit_time),
            duration: Some(duration),
            state_data: instance_state.state_data.clone(),
            transition_reason: reason.clone(),
        };

        instance_state.history.push(history_entry);

        // 执行退出动作 / Execute exit actions
        self.execute_exit_actions(&from_state, instance_id)?;

        // 更新状态 / Update state
        instance_state.current_state = to_state.clone();
        instance_state.entry_time = Instant::now();
        instance_state.retry_count = 0;

        // 设置超时时间 / Set timeout time
        let states = self.states.read().unwrap();
        if let Some(state_def) = states.get(&to_state) {
            if let Some(timeout) = state_def.timeout {
                instance_state.timeout_time = Some(Instant::now() + timeout);
            }
        }

        // 更新状态数据 / Update state data
        if let Some(data) = transition_data {
            instance_state.state_data.extend(data);
        }

        // 执行进入动作 / Execute entry actions
        self.execute_entry_actions(&to_state, instance_id)?;

        // 通知监听器 / Notify listeners
        self.notify_listeners(StateChangeEvent {
            instance_id: instance_id.to_string(),
            from_state: from_state.clone(),
            to_state: to_state.clone(),
            change_time: Instant::now(),
            reason,
            state_data: instance_state.state_data.clone(),
        });

        // 记录转换历史 / Record transition history
        {
            let mut history = self.transition_history.lock().unwrap();
            history.push(StateTransitionRecord {
                from_state,
                to_state,
                timestamp: Instant::now(),
                data: Some(serde_json::to_value(&instance_state.state_data).unwrap_or_default()),
            });
        }

        Ok(())
    }

    /// 获取实例状态 / Get Instance State
    pub fn get_instance_state(&self, instance_id: &str) -> Option<InstanceState> {
        let instance_states = self.instance_states.read().unwrap();
        instance_states.get(instance_id).cloned()
    }

    /// 锁定实例状态 / Lock Instance State
    pub fn lock_instance_state(&self, instance_id: &str) -> Result<(), StateError> {
        let mut instance_states = self.instance_states.write().unwrap();
        if let Some(instance_state) = instance_states.get_mut(instance_id) {
            if instance_state.is_locked {
                return Err(StateError::StateLocked(instance_id.to_string()));
            }
            instance_state.is_locked = true;
            instance_state.lock_time = Some(Instant::now());
            Ok(())
        } else {
            Err(StateError::InstanceNotFound(instance_id.to_string()))
        }
    }

    /// 解锁实例状态 / Unlock Instance State
    pub fn unlock_instance_state(&self, instance_id: &str) -> Result<(), StateError> {
        let mut instance_states = self.instance_states.write().unwrap();
        if let Some(instance_state) = instance_states.get_mut(instance_id) {
            instance_state.is_locked = false;
            instance_state.lock_time = None;
            Ok(())
        } else {
            Err(StateError::InstanceNotFound(instance_id.to_string()))
        }
    }

    /// 添加状态监听器 / Add State Listener
    pub fn add_listener(&self, event_type: String, listener: StateListener) {
        let mut listeners = self.listeners.lock().unwrap();
        listeners
            .entry(event_type)
            .or_insert_with(Vec::new)
            .push(listener);
    }

    /// 清理过期状态 / Cleanup Expired States
    pub fn cleanup_expired_states(&self) -> Result<usize, StateError> {
        let now = Instant::now();
        let mut cleaned_count = 0;

        {
            let mut instance_states = self.instance_states.write().unwrap();
            let expired_instances: Vec<String> = instance_states
                .iter()
                .filter_map(|(instance_id, state)| {
                    if let Some(timeout_time) = state.timeout_time {
                        if now > timeout_time {
                            Some(instance_id.clone())
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                })
                .collect();

            for instance_id in expired_instances {
                instance_states.remove(&instance_id);
                cleaned_count += 1;
            }
        }

        Ok(cleaned_count)
    }

    /// 验证状态定义 / Validate State Definition
    fn validate_state_definition(&self, definition: &StateDefinition) -> Result<(), StateError> {
        // 检查状态名称 / Check state name
        if definition.name.is_empty() {
            return Err(StateError::InvalidStateName(
                "State name cannot be empty".to_string(),
            ));
        }

        // 检查状态名称格式 / Check state name format
        if !crate::types::utils::validate_state_name(&definition.name) {
            return Err(StateError::InvalidStateName(format!(
                "Invalid state name: {}",
                definition.name
            )));
        }

        // 检查超时时间 / Check timeout duration
        if let Some(timeout) = definition.timeout {
            if timeout.is_zero() {
                return Err(StateError::InvalidTimeout(
                    "Timeout cannot be zero".to_string(),
                ));
            }
        }

        // 检查重试策略 / Check retry strategy
        if let Some(retry_strategy) = &definition.retry_strategy {
            if retry_strategy.max_retries == 0 {
                return Err(StateError::InvalidRetryStrategy(
                    "Max retries cannot be zero".to_string(),
                ));
            }
            if retry_strategy.retry_delay.is_zero() {
                return Err(StateError::InvalidRetryStrategy(
                    "Retry delay cannot be zero".to_string(),
                ));
            }
        }

        Ok(())
    }

    /// 执行进入动作 / Execute Entry Actions
    fn execute_entry_actions(&self, state_name: &str, instance_id: &str) -> Result<(), StateError> {
        // 获取状态定义 / Get state definition
        let states = self.states.read().unwrap();
        let state_def = states
            .get(state_name)
            .ok_or_else(|| StateError::StateNotFound(state_name.to_string()))?;

        // 执行进入动作 / Execute entry actions
        for action in &state_def.entry_actions {
            // 这里可以实现具体的动作执行逻辑
            // Here you can implement specific action execution logic
            println!(
                "执行进入动作 / Executing entry action: {} for instance: {}",
                action, instance_id
            );
        }

        Ok(())
    }

    /// 执行退出动作 / Execute Exit Actions
    fn execute_exit_actions(&self, state_name: &str, instance_id: &str) -> Result<(), StateError> {
        // 获取状态定义 / Get state definition
        let states = self.states.read().unwrap();
        let state_def = states
            .get(state_name)
            .ok_or_else(|| StateError::StateNotFound(state_name.to_string()))?;

        // 执行退出动作 / Execute exit actions
        for action in &state_def.exit_actions {
            // 这里可以实现具体的动作执行逻辑
            // Here you can implement specific action execution logic
            println!(
                "执行退出动作 / Executing exit action: {} for instance: {}",
                action, instance_id
            );
        }

        Ok(())
    }

    /// 通知监听器 / Notify Listeners
    fn notify_listeners(&self, event: StateChangeEvent) {
        let listeners = self.listeners.lock().unwrap();
        if let Some(state_listeners) = listeners.get("state_change") {
            for listener in state_listeners {
                listener(event.clone());
            }
        }
    }
}

/// 状态错误类型 / State Error Types
#[derive(Debug, thiserror::Error)]
pub enum StateError {
    #[error("状态未找到 / State not found: {0}")]
    StateNotFound(String),

    #[error("实例未找到 / Instance not found: {0}")]
    InstanceNotFound(String),

    #[error("状态已锁定 / State is locked: {0}")]
    StateLocked(String),

    #[error("状态数量超限 / State limit exceeded: {0}")]
    StateLimitExceeded(usize),

    #[error("无效的状态名称 / Invalid state name: {0}")]
    InvalidStateName(String),

    #[error("无效的超时设置 / Invalid timeout: {0}")]
    InvalidTimeout(String),

    #[error("无效的重试策略 / Invalid retry strategy: {0}")]
    InvalidRetryStrategy(String),

    #[error("状态转换失败 / State transition failed: {0}")]
    TransitionFailed(String),
}

/// 状态机实现 / State Machine Implementation
///
/// 基于状态机理论的具体实现。
/// Concrete implementation based on state machine theory.
pub struct StateMachineImpl {
    /// 状态管理器 / State Manager
    state_manager: Arc<StateManager>,
    /// 状态机配置 / State Machine Configuration
    config: StateMachineConfig,
}

/// 状态机配置 / State Machine Configuration
#[derive(Debug, Clone)]
pub struct StateMachineConfig {
    /// 是否启用自动转换 / Enable Auto Transition
    pub enable_auto_transition: bool,
    /// 是否启用状态验证 / Enable State Validation
    pub enable_state_validation: bool,
    /// 是否启用状态持久化 / Enable State Persistence
    pub enable_state_persistence: bool,
    /// 状态转换超时 / State Transition Timeout
    pub transition_timeout: Duration,
}

impl Default for StateMachineConfig {
    fn default() -> Self {
        Self {
            enable_auto_transition: true,
            enable_state_validation: true,
            enable_state_persistence: false,
            transition_timeout: Duration::from_secs(30),
        }
    }
}

impl StateMachineImpl {
    /// 创建新的状态机 / Create New State Machine
    pub fn new(state_manager: Arc<StateManager>) -> Self {
        Self::with_config(state_manager, StateMachineConfig::default())
    }

    /// 使用配置创建状态机 / Create State Machine with Configuration
    pub fn with_config(state_manager: Arc<StateManager>, config: StateMachineConfig) -> Self {
        Self {
            state_manager,
            config,
        }
    }

    /// 处理状态事件 / Handle State Event
    pub async fn handle_event(
        &self,
        instance_id: &str,
        event: StateEvent,
    ) -> Result<(), StateError> {
        match event {
            StateEvent::Transition {
                to_state,
                data,
                reason,
            } => {
                self.transition_state(instance_id, to_state, data, reason)
                    .await
            }
            StateEvent::Lock => self.state_manager.lock_instance_state(instance_id),
            StateEvent::Unlock => self.state_manager.unlock_instance_state(instance_id),
            StateEvent::Timeout => self.handle_timeout(instance_id).await,
        }
    }

    /// 异步状态转换 / Async State Transition
    async fn transition_state(
        &self,
        instance_id: &str,
        to_state: String,
        data: Option<HashMap<String, serde_json::Value>>,
        reason: Option<String>,
    ) -> Result<(), StateError> {
        // 验证状态转换 / Validate state transition
        if self.config.enable_state_validation {
            self.validate_transition(instance_id, &to_state)?;
        }

        // 执行状态转换 / Execute state transition
        self.state_manager
            .transition_state(instance_id, to_state, data, reason)
    }

    /// 处理超时事件 / Handle Timeout Event
    async fn handle_timeout(&self, instance_id: &str) -> Result<(), StateError> {
        // 获取实例状态 / Get instance state
        let instance_state = self
            .state_manager
            .get_instance_state(instance_id)
            .ok_or_else(|| StateError::InstanceNotFound(instance_id.to_string()))?;

        // 检查是否超时 / Check if timeout
        if let Some(timeout_time) = instance_state.timeout_time {
            if Instant::now() > timeout_time {
                // 执行超时处理逻辑 / Execute timeout handling logic
                println!("实例超时 / Instance timeout: {}", instance_id);
                return Ok(());
            }
        }

        Ok(())
    }

    /// 验证状态转换 / Validate State Transition
    fn validate_transition(&self, instance_id: &str, _to_state: &str) -> Result<(), StateError> {
        // 获取当前状态 / Get current state
        let instance_state = self
            .state_manager
            .get_instance_state(instance_id)
            .ok_or_else(|| StateError::InstanceNotFound(instance_id.to_string()))?;

        // 检查状态锁 / Check state lock
        if instance_state.is_locked {
            return Err(StateError::StateLocked(instance_id.to_string()));
        }

        // 这里可以添加更多的验证逻辑
        // Here you can add more validation logic

        Ok(())
    }
}

/// 状态事件 / State Event
#[derive(Debug, Clone)]
pub enum StateEvent {
    /// 状态转换 / State Transition
    Transition {
        /// 目标状态 / Target State
        to_state: String,
        /// 转换数据 / Transition Data
        data: Option<HashMap<String, serde_json::Value>>,
        /// 转换原因 / Transition Reason
        reason: Option<String>,
    },
    /// 锁定状态 / Lock State
    Lock,
    /// 解锁状态 / Unlock State
    Unlock,
    /// 超时事件 / Timeout Event
    Timeout,
}

/// 状态机特征实现 / State Machine Trait Implementation
impl crate::types::state_machine::StateMachine for StateMachineImpl {
    type State = String;
    type Event = StateEvent;
    type Action = String;

    fn transition(&self, _state: &Self::State, event: &Self::Event) -> Option<Self::State> {
        // 这里实现具体的状态转换逻辑
        // Here implement specific state transition logic
        match event {
            StateEvent::Transition { to_state, .. } => Some(to_state.clone()),
            _ => None,
        }
    }

    fn execute_action(&self, state: &Self::State) -> Option<Self::Action> {
        // 这里实现具体的动作执行逻辑
        // Here implement specific action execution logic
        Some(format!("Execute action for state: {}", state))
    }

    fn initial_state(&self) -> Self::State {
        "initial".to_string()
    }

    fn is_final_state(&self, state: &Self::State) -> bool {
        // 检查是否为最终状态 / Check if it's a final state
        state == "completed" || state == "error" || state == "cancelled"
    }
}
