//! # 工作流系统核心类型定义 / Workflow System Core Type Definitions
//!
//! 本模块定义了工作流系统的核心数据类型和结构。
//! This module defines the core data types and structures for the workflow system.

use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::collections::HashMap;
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
}

/// 工作流定义 / Workflow Definition
///
/// 描述工作流的结构、状态和转换规则。
/// Describes the structure, states, and transition rules of a workflow.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkflowDefinition {
    /// 工作流名称 / Workflow Name
    pub name: String,
    /// 工作流描述 / Workflow Description
    pub description: Option<String>,
    /// 工作流版本 / Workflow Version
    pub version: String,
    /// 状态列表 / State List
    pub states: Vec<String>,
    /// 转换规则 / Transition Rules
    pub transitions: Vec<StateTransition>,
    /// 初始状态 / Initial State
    pub initial_state: String,
    /// 最终状态列表 / Final States
    pub final_states: Vec<String>,
    /// 元数据 / Metadata
    pub metadata: HashMap<String, serde_json::Value>,
}

impl WorkflowDefinition {
    /// 创建新的工作流定义 / Create New Workflow Definition
    pub fn new(name: String) -> Self {
        Self {
            name,
            description: None,
            version: "1.0.0".to_string(),
            states: Vec::new(),
            transitions: Vec::new(),
            initial_state: "initial".to_string(),
            final_states: Vec::new(),
            metadata: HashMap::new(),
        }
    }

    /// 添加状态 / Add State
    pub fn add_state(&mut self, state: String) {
        if !self.states.contains(&state) {
            self.states.push(state);
        }
    }

    /// 添加转换规则 / Add Transition Rule
    pub fn add_transition(&mut self, from: String, to: String, condition: Option<String>) {
        let transition = StateTransition {
            from_state: from,
            to_state: to,
            condition,
            actions: Vec::new(),
            timeout: None,
        };
        self.transitions.push(transition);
    }

    /// 验证工作流定义 / Validate Workflow Definition
    pub fn validate(&self) -> Result<(), WorkflowValidationError> {
        // 检查初始状态是否存在 / Check if initial state exists
        if !self.states.contains(&self.initial_state) {
            return Err(WorkflowValidationError::InvalidInitialState);
        }

        // 检查最终状态是否都存在 / Check if all final states exist
        for final_state in &self.final_states {
            if !self.states.contains(final_state) {
                return Err(WorkflowValidationError::InvalidFinalState(
                    final_state.clone(),
                ));
            }
        }

        // 检查转换规则的有效性 / Check validity of transition rules
        for transition in &self.transitions {
            if !self.states.contains(&transition.from_state) {
                return Err(WorkflowValidationError::InvalidTransitionFrom(
                    transition.from_state.clone(),
                ));
            }
            if !self.states.contains(&transition.to_state) {
                return Err(WorkflowValidationError::InvalidTransitionTo(
                    transition.to_state.clone(),
                ));
            }
        }

        Ok(())
    }
}

/// 状态转换 / State Transition
///
/// 定义从一个状态到另一个状态的转换规则。
/// Defines transition rules from one state to another.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StateTransition {
    /// 源状态 / Source State
    pub from_state: String,
    /// 目标状态 / Target State
    pub to_state: String,
    /// 转换条件 / Transition Condition
    pub condition: Option<String>,
    /// 转换动作 / Transition Actions
    pub actions: Vec<String>,
    /// 超时设置 / Timeout Setting
    pub timeout: Option<Duration>,
}

/// 工作流数据 / Workflow Data
///
/// 工作流执行过程中携带的数据。
/// Data carried during workflow execution.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkflowData {
    /// 数据内容 / Data Content
    pub content: serde_json::Value,
    /// 数据版本 / Data Version
    pub version: String,
    /// 创建时间 / Creation Time
    #[serde(with = "timestamp_serde")]
    pub created_at: Instant,
    /// 最后更新时间 / Last Update Time
    #[serde(with = "timestamp_serde")]
    pub updated_at: Instant,
    /// 元数据 / Metadata
    pub metadata: HashMap<String, serde_json::Value>,
}

impl WorkflowData {
    /// 创建新的工作流数据 / Create New Workflow Data
    pub fn new(content: serde_json::Value) -> Self {
        let now = Instant::now();
        Self {
            content,
            version: "1.0.0".to_string(),
            created_at: now,
            updated_at: now,
            metadata: HashMap::new(),
        }
    }

    /// 更新数据内容 / Update Data Content
    pub fn update(&mut self, new_content: serde_json::Value) {
        self.content = new_content;
        self.updated_at = Instant::now();
    }

    /// 添加元数据 / Add Metadata
    pub fn add_metadata(&mut self, key: String, value: serde_json::Value) {
        self.metadata.insert(key, value);
        self.updated_at = Instant::now();
    }
}

/// 工作流事件 / Workflow Event
///
/// 工作流系统中传递的事件类型。
/// Event types transmitted in the workflow system.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum WorkflowEvent {
    /// 启动事件 / Start Event
    Start {
        /// 实例ID / Instance ID
        instance_id: String,
        /// 工作流名称 / Workflow Name
        workflow_name: String,
    },
    /// 状态转换事件 / State Transition Event
    StateTransition {
        /// 实例ID / Instance ID
        instance_id: String,
        /// 源状态 / Source State
        from_state: String,
        /// 目标状态 / Target State
        to_state: String,
        /// 转换数据 / Transition Data
        data: Option<serde_json::Value>,
    },
    /// 完成事件 / Complete Event
    Complete {
        /// 实例ID / Instance ID
        instance_id: String,
        /// 结果数据 / Result Data
        result: serde_json::Value,
    },
    /// 错误事件 / Error Event
    Error {
        /// 实例ID / Instance ID
        instance_id: String,
        /// 错误信息 / Error Message
        error: String,
    },
    /// 超时事件 / Timeout Event
    Timeout {
        /// 实例ID / Instance ID
        instance_id: String,
        /// 超时状态 / Timeout State
        state: String,
    },
}

/// 工作流实例 / Workflow Instance
///
/// 工作流的具体执行实例。
/// Specific execution instance of a workflow.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkflowInstance {
    /// 实例ID / Instance ID
    pub id: String,
    /// 工作流名称 / Workflow Name
    pub workflow_name: String,
    /// 当前状态 / Current State
    pub current_state: String,
    /// 工作流数据 / Workflow Data
    pub data: WorkflowData,
    /// 执行历史 / Execution History
    pub history: Vec<StateTransitionRecord>,
    /// 创建时间 / Creation Time
    #[serde(with = "timestamp_serde")]
    pub created_at: Instant,
    /// 最后更新时间 / Last Update Time
    #[serde(with = "timestamp_serde")]
    pub updated_at: Instant,
    /// 状态 / Status
    pub status: WorkflowStatus,
}

impl WorkflowInstance {
    /// 创建新的工作流实例 / Create New Workflow Instance
    pub fn new(id: String, workflow_name: String, initial_data: WorkflowData) -> Self {
        let now = Instant::now();
        Self {
            id,
            workflow_name,
            current_state: "initial".to_string(),
            data: initial_data,
            history: Vec::new(),
            created_at: now,
            updated_at: now,
            status: WorkflowStatus::Running,
        }
    }

    /// 执行状态转换 / Execute State Transition
    pub fn transition(&mut self, to_state: String, transition_data: Option<serde_json::Value>) {
        let record = StateTransitionRecord {
            from_state: self.current_state.clone(),
            to_state: to_state.clone(),
            timestamp: Instant::now(),
            data: transition_data,
        };

        self.history.push(record);
        self.current_state = to_state;
        self.updated_at = Instant::now();
    }

    /// 完成工作流 / Complete Workflow
    pub fn complete(&mut self, result: serde_json::Value) {
        self.status = WorkflowStatus::Completed;
        self.data.update(result);
        self.updated_at = Instant::now();
    }

    /// 标记为错误 / Mark as Error
    pub fn mark_error(&mut self, error_message: String) {
        self.status = WorkflowStatus::Error;
        self.data.add_metadata(
            "error".to_string(),
            serde_json::Value::String(error_message),
        );
        self.updated_at = Instant::now();
    }
}

/// 状态转换记录 / State Transition Record
///
/// 记录工作流实例的状态转换历史。
/// Records state transition history of workflow instances.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StateTransitionRecord {
    /// 源状态 / Source State
    pub from_state: String,
    /// 目标状态 / Target State
    pub to_state: String,
    /// 时间戳 / Timestamp
    #[serde(with = "timestamp_serde")]
    pub timestamp: Instant,
    /// 转换数据 / Transition Data
    pub data: Option<serde_json::Value>,
}

/// 工作流状态 / Workflow Status
///
/// 工作流实例的执行状态。
/// Execution status of workflow instances.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum WorkflowStatus {
    /// 运行中 / Running
    Running,
    /// 暂停 / Paused
    Paused,
    /// 已完成 / Completed
    Completed,
    /// 错误 / Error
    Error,
    /// 已取消 / Cancelled
    Cancelled,
}

/// 工作流验证错误 / Workflow Validation Error
///
/// 工作流定义验证过程中的错误类型。
/// Error types during workflow definition validation.
#[derive(Debug, thiserror::Error)]
pub enum WorkflowValidationError {
    #[error("无效的初始状态 / Invalid initial state")]
    InvalidInitialState,

    #[error("无效的最终状态 / Invalid final state: {0}")]
    InvalidFinalState(String),

    #[error("无效的转换源状态 / Invalid transition from state: {0}")]
    InvalidTransitionFrom(String),

    #[error("无效的转换目标状态 / Invalid transition to state: {0}")]
    InvalidTransitionTo(String),

    #[error("循环依赖检测 / Circular dependency detected")]
    CircularDependency,

    #[error("缺少必需的状态 / Missing required states")]
    MissingRequiredStates,
}

/// 进程代数类型 / Process Algebra Types
///
/// 基于进程代数理论的数据类型。
/// Data types based on process algebra theory.
pub mod process_algebra {
    // use super::*;

    /// 顺序进程 / Sequential Process
    #[derive(Debug, Clone)]
    pub struct SequentialProcess<P1, P2> {
        pub first: P1,
        pub second: P2,
    }

    /// 并行进程 / Parallel Process
    #[derive(Debug, Clone)]
    pub struct ParallelProcess<P1, P2> {
        pub left: P1,
        pub right: P2,
    }

    /// 选择进程 / Choice Process
    #[derive(Debug, Clone)]
    pub struct ChoiceProcess<P1, P2> {
        pub option1: P1,
        pub option2: P2,
    }

    /// 进程代数特征 / Process Algebra Trait
    pub trait ProcessAlgebra {
        /// 顺序组合 / Sequential Composition
        fn seq<T>(self, other: T) -> SequentialProcess<Self, T>
        where
            T: ProcessAlgebra,
            Self: Sized;

        /// 并行组合 / Parallel Composition
        fn par<T>(self, other: T) -> ParallelProcess<Self, T>
        where
            T: ProcessAlgebra,
            Self: Sized;

        /// 选择操作 / Choice Operation
        fn choice<T>(self, other: T) -> ChoiceProcess<Self, T>
        where
            T: ProcessAlgebra,
            Self: Sized;
    }
}

/// 状态机类型 / State Machine Types
///
/// 基于状态机理论的数据类型。
/// Data types based on state machine theory.
pub mod state_machine {
    // use super::*;

    /// 状态机特征 / State Machine Trait
    pub trait StateMachine {
        /// 状态类型 / State Type
        type State;
        /// 事件类型 / Event Type
        type Event;
        /// 动作类型 / Action Type
        type Action;

        /// 状态转换函数 / State Transition Function
        fn transition(&self, state: &Self::State, event: &Self::Event) -> Option<Self::State>;

        /// 动作执行函数 / Action Execution Function
        fn execute_action(&self, state: &Self::State) -> Option<Self::Action>;

        /// 获取初始状态 / Get Initial State
        fn initial_state(&self) -> Self::State;

        /// 检查是否为最终状态 / Check if Final State
        fn is_final_state(&self, state: &Self::State) -> bool;
    }
}

/// 工具函数 / Utility Functions
///
/// 工作流系统相关的工具函数。
/// Utility functions related to workflow systems.
pub mod utils {
    use super::*;
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    /// 生成实例ID / Generate Instance ID
    pub fn generate_instance_id() -> String {
        let mut hasher = DefaultHasher::new();
        Instant::now().hash(&mut hasher);
        format!("wf_{:x}", hasher.finish())
    }

    /// 验证状态名称 / Validate State Name
    pub fn validate_state_name(name: &str) -> bool {
        !name.is_empty()
            && name
                .chars()
                .all(|c| c.is_alphanumeric() || c == '_' || c == '-')
    }

    /// 计算工作流复杂度 / Calculate Workflow Complexity
    pub fn calculate_complexity(definition: &WorkflowDefinition) -> f64 {
        let state_count = definition.states.len() as f64;
        let transition_count = definition.transitions.len() as f64;

        // 复杂度 = 状态数 * 转换数 / 2 (简化公式)
        // Complexity = state_count * transition_count / 2 (simplified formula)
        state_count * transition_count / 2.0
    }

    /// 检查工作流是否有循环 / Check if Workflow Has Cycles
    pub fn has_cycles(definition: &WorkflowDefinition) -> bool {
        // 使用深度优先搜索检测循环
        // Use depth-first search to detect cycles
        let mut visited = std::collections::HashSet::new();
        let mut rec_stack = std::collections::HashSet::new();

        fn dfs(
            state: &str,
            definition: &WorkflowDefinition,
            visited: &mut std::collections::HashSet<String>,
            rec_stack: &mut std::collections::HashSet<String>,
        ) -> bool {
            visited.insert(state.to_string());
            rec_stack.insert(state.to_string());

            for transition in &definition.transitions {
                if transition.from_state == state {
                    let next_state = &transition.to_state;
                    if !visited.contains(next_state) {
                        if dfs(next_state, definition, visited, rec_stack) {
                            return true;
                        }
                    } else if rec_stack.contains(next_state) {
                        return true;
                    }
                }
            }

            rec_stack.remove(state);
            false
        }

        for state in &definition.states {
            if !visited.contains(state) {
                if dfs(state, definition, &mut visited, &mut rec_stack) {
                    return true;
                }
            }
        }

        false
    }
}
