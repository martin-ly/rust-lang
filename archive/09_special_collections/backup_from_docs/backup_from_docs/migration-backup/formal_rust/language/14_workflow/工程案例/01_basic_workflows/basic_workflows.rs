//! 基础工作流案例
//! 
//! 本模块演示工作流系统的基础实现，包括状态机、管道、事件驱动等模式。
//! 
//! 理论映射：
//! - 工作流: W = (T, E, S, I, O, Δ, Φ)
//! - 工作流实例: W_i = (W, s_0, t, σ)
//! - 任务依赖: depends(t_i, t_j) ≡ (t_j, t_i) ∈ E
//! - 工作流组合: W_1 ⊕ W_2 = (T_1 ∪ T_2, E_1 ∪ E_2 ∪ E_bridge, S_1 × S_2, ...)

use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};
use serde::{Deserialize, Serialize};
use tokio::time::{sleep, Duration};
use chrono::{DateTime, Utc};

/// 工作流状态
/// 
/// 理论映射：S (状态空间)
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum WorkflowState {
    Created,
    Running,
    Paused,
    Completed,
    Failed,
    Cancelled,
}

/// 任务状态
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum TaskStatus {
    Pending,
    Running,
    Completed,
    Failed,
    Cancelled,
}

/// 任务定义
/// 
/// 理论映射：T (任务集合)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Task {
    pub id: String,
    pub name: String,
    pub description: String,
    pub status: TaskStatus,
    pub dependencies: Vec<String>,
    pub input: serde_json::Value,
    pub output: Option<serde_json::Value>,
    pub created_at: DateTime<Utc>,
    pub started_at: Option<DateTime<Utc>>,
    pub completed_at: Option<DateTime<Utc>>,
}

impl Task {
    pub fn new(id: String, name: String, description: String) -> Self {
        Self {
            id,
            name,
            description,
            status: TaskStatus::Pending,
            dependencies: Vec::new(),
            input: serde_json::Value::Null,
            output: None,
            created_at: Utc::now(),
            started_at: None,
            completed_at: None,
        }
    }
    
    pub fn add_dependency(&mut self, task_id: String) {
        self.dependencies.push(task_id);
    }
    
    pub fn can_execute(&self, completed_tasks: &HashSet<String>) -> bool {
        self.dependencies.iter().all(|dep| completed_tasks.contains(dep))
    }
    
    pub async fn execute(&mut self) -> Result<serde_json::Value, String> {
        self.status = TaskStatus::Running;
        self.started_at = Some(Utc::now());
        
        // 模拟任务执行
        sleep(Duration::from_millis(100)).await;
        
        // 模拟执行结果
        let result = serde_json::json!({
            "task_id": self.id,
            "result": "success",
            "timestamp": Utc::now()
        });
        
        self.output = Some(result.clone());
        self.status = TaskStatus::Completed;
        self.completed_at = Some(Utc::now());
        
        Ok(result)
    }
}

/// 工作流定义
/// 
/// 理论映射：W = (T, E, S, I, O, Δ, Φ)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Workflow {
    pub id: String,
    pub name: String,
    pub description: String,
    pub tasks: HashMap<String, Task>,
    pub state: WorkflowState,
    pub input: serde_json::Value,
    pub output: Option<serde_json::Value>,
    pub created_at: DateTime<Utc>,
    pub started_at: Option<DateTime<Utc>>,
    pub completed_at: Option<DateTime<Utc>>,
}

impl Workflow {
    pub fn new(id: String, name: String, description: String) -> Self {
        Self {
            id,
            name,
            description,
            tasks: HashMap::new(),
            state: WorkflowState::Created,
            input: serde_json::Value::Null,
            output: None,
            created_at: Utc::now(),
            started_at: None,
            completed_at: None,
        }
    }
    
    pub fn add_task(&mut self, task: Task) {
        self.tasks.insert(task.id.clone(), task);
    }
    
    pub fn add_dependency(&mut self, task_id: &str, dependency_id: &str) -> Result<(), String> {
        if let Some(task) = self.tasks.get_mut(task_id) {
            task.add_dependency(dependency_id.to_string());
            Ok(())
        } else {
            Err(format!("Task {} not found", task_id))
        }
    }
    
    pub fn get_ready_tasks(&self, completed_tasks: &HashSet<String>) -> Vec<String> {
        self.tasks
            .iter()
            .filter(|(_, task)| {
                task.status == TaskStatus::Pending && task.can_execute(completed_tasks)
            })
            .map(|(id, _)| id.clone())
            .collect()
    }
    
    pub fn is_completed(&self) -> bool {
        self.tasks.values().all(|task| task.status == TaskStatus::Completed)
    }
    
    pub fn is_failed(&self) -> bool {
        self.tasks.values().any(|task| task.status == TaskStatus::Failed)
    }
}

/// 工作流执行器
/// 
/// 理论映射：执行引擎
pub struct WorkflowExecutor {
    workflows: Arc<Mutex<HashMap<String, Workflow>>>,
    execution_history: Arc<Mutex<Vec<ExecutionRecord>>>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExecutionRecord {
    pub workflow_id: String,
    pub task_id: String,
    pub status: TaskStatus,
    pub timestamp: DateTime<Utc>,
    pub duration: Option<Duration>,
}

impl WorkflowExecutor {
    pub fn new() -> Self {
        Self {
            workflows: Arc::new(Mutex::new(HashMap::new())),
            execution_history: Arc::new(Mutex::new(Vec::new())),
        }
    }
    
    pub async fn register_workflow(&self, workflow: Workflow) {
        let mut workflows = self.workflows.lock().unwrap();
        workflows.insert(workflow.id.clone(), workflow);
    }
    
    pub async fn execute_workflow(&self, workflow_id: &str) -> Result<serde_json::Value, String> {
        let mut workflows = self.workflows.lock().unwrap();
        
        if let Some(workflow) = workflows.get_mut(workflow_id) {
            workflow.state = WorkflowState::Running;
            workflow.started_at = Some(Utc::now());
            
            let mut completed_tasks = HashSet::new();
            let mut execution_queue = Vec::new();
            
            // 初始化执行队列
            execution_queue.extend(workflow.get_ready_tasks(&completed_tasks));
            
            while !execution_queue.is_empty() {
                let task_id = execution_queue.remove(0);
                
                if let Some(task) = workflow.tasks.get_mut(&task_id) {
                    let start_time = Utc::now();
                    
                    // 执行任务
                    match task.execute().await {
                        Ok(result) => {
                            completed_tasks.insert(task_id.clone());
                            
                            // 记录执行历史
                            let record = ExecutionRecord {
                                workflow_id: workflow_id.to_string(),
                                task_id: task_id.clone(),
                                status: TaskStatus::Completed,
                                timestamp: Utc::now(),
                                duration: Some(Utc::now().signed_duration_since(start_time).to_std().unwrap()),
                            };
                            
                            let mut history = self.execution_history.lock().unwrap();
                            history.push(record);
                        }
                        Err(e) => {
                            workflow.state = WorkflowState::Failed;
                            return Err(format!("Task {} failed: {}", task_id, e));
                        }
                    }
                }
                
                // 更新执行队列
                execution_queue.extend(workflow.get_ready_tasks(&completed_tasks));
            }
            
            if workflow.is_completed() {
                workflow.state = WorkflowState::Completed;
                workflow.completed_at = Some(Utc::now());
                
                let result = serde_json::json!({
                    "workflow_id": workflow_id,
                    "status": "completed",
                    "completed_tasks": completed_tasks.len(),
                    "total_tasks": workflow.tasks.len(),
                    "completion_time": workflow.completed_at
                });
                
                workflow.output = Some(result.clone());
                Ok(result)
            } else {
                workflow.state = WorkflowState::Failed;
                Err("Workflow execution failed".to_string())
            }
        } else {
            Err(format!("Workflow {} not found", workflow_id))
        }
    }
    
    pub async fn get_execution_history(&self, workflow_id: &str) -> Vec<ExecutionRecord> {
        let history = self.execution_history.lock().unwrap();
        history
            .iter()
            .filter(|record| record.workflow_id == workflow_id)
            .cloned()
            .collect()
    }
}

/// 状态机工作流
/// 
/// 理论映射：SM = (Q, Σ, δ, q_0, F)
pub struct StateMachineWorkflow<S, E> {
    pub states: HashSet<S>,
    pub events: HashSet<E>,
    pub transitions: HashMap<(S, E), S>,
    pub current_state: S,
    pub initial_state: S,
    pub final_states: HashSet<S>,
}

impl<S, E> StateMachineWorkflow<S, E>
where
    S: Clone + Eq + Hash,
    E: Clone + Eq + Hash,
{
    pub fn new(initial_state: S) -> Self {
        let mut states = HashSet::new();
        states.insert(initial_state.clone());
        
        Self {
            states,
            events: HashSet::new(),
            transitions: HashMap::new(),
            current_state: initial_state.clone(),
            initial_state,
            final_states: HashSet::new(),
        }
    }
    
    pub fn add_state(&mut self, state: S) {
        self.states.insert(state);
    }
    
    pub fn add_event(&mut self, event: E) {
        self.events.insert(event);
    }
    
    pub fn add_transition(&mut self, from: S, event: E, to: S) {
        self.states.insert(from.clone());
        self.states.insert(to.clone());
        self.events.insert(event.clone());
        self.transitions.insert((from, event), to);
    }
    
    pub fn add_final_state(&mut self, state: S) {
        self.final_states.insert(state);
    }
    
    pub fn transition(&mut self, event: E) -> Result<S, String> {
        let key = (self.current_state.clone(), event);
        
        if let Some(new_state) = self.transitions.get(&key) {
            self.current_state = new_state.clone();
            Ok(new_state.clone())
        } else {
            Err("Invalid transition".to_string())
        }
    }
    
    pub fn is_final(&self) -> bool {
        self.final_states.contains(&self.current_state)
    }
    
    pub fn reset(&mut self) {
        self.current_state = self.initial_state.clone();
    }
}

/// 管道工作流
/// 
/// 理论映射：Pipeline(I, O) = ∀i : I. ∃o : O. process(i) = o
pub struct PipelineWorkflow<I, O, E> {
    pub stages: Vec<Box<dyn PipelineStage<I, O, E>>>,
    pub metrics: Arc<Mutex<PipelineMetrics>>,
}

pub trait PipelineStage<I, O, E> {
    fn process(&self, input: I) -> Result<O, E>;
    fn name(&self) -> &str;
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PipelineMetrics {
    pub total_executions: u64,
    pub successful_executions: u64,
    pub failed_executions: u64,
    pub average_execution_time: Duration,
}

impl<I, O, E> PipelineWorkflow<I, O, E> {
    pub fn new() -> Self {
        Self {
            stages: Vec::new(),
            metrics: Arc::new(Mutex::new(PipelineMetrics {
                total_executions: 0,
                successful_executions: 0,
                failed_executions: 0,
                average_execution_time: Duration::from_millis(0),
            })),
        }
    }
    
    pub fn add_stage(&mut self, stage: Box<dyn PipelineStage<I, O, E>>) {
        self.stages.push(stage);
    }
    
    pub fn process(&self, input: I) -> Result<O, E> {
        let start_time = std::time::Instant::now();
        
        let mut current_input = input;
        
        for stage in &self.stages {
            current_input = stage.process(current_input)?;
        }
        
        let execution_time = start_time.elapsed();
        
        // 更新指标
        let mut metrics = self.metrics.lock().unwrap();
        metrics.total_executions += 1;
        metrics.successful_executions += 1;
        metrics.average_execution_time = Duration::from_millis(
            (metrics.average_execution_time.as_millis() + execution_time.as_millis()) / 2
        );
        
        Ok(current_input)
    }
}

/// 事件驱动工作流
/// 
/// 理论映射：Event = (id, type, payload, timestamp)
pub struct EventDrivenWorkflow {
    pub event_handlers: HashMap<String, Box<dyn EventHandler>>,
    pub event_queue: Arc<Mutex<Vec<Event>>>,
    pub state: Arc<Mutex<serde_json::Value>>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Event {
    pub id: String,
    pub event_type: String,
    pub payload: serde_json::Value,
    pub timestamp: DateTime<Utc>,
}

pub trait EventHandler: Send + Sync {
    fn handle(&self, event: &Event, state: &mut serde_json::Value) -> Result<(), String>;
    fn event_type(&self) -> &str;
}

impl EventDrivenWorkflow {
    pub fn new() -> Self {
        Self {
            event_handlers: HashMap::new(),
            event_queue: Arc::new(Mutex::new(Vec::new())),
            state: Arc::new(Mutex::new(serde_json::Value::Null)),
        }
    }
    
    pub fn register_handler(&mut self, handler: Box<dyn EventHandler>) {
        let event_type = handler.event_type().to_string();
        self.event_handlers.insert(event_type, handler);
    }
    
    pub async fn publish_event(&self, event: Event) -> Result<(), String> {
        let mut queue = self.event_queue.lock().unwrap();
        queue.push(event);
        Ok(())
    }
    
    pub async fn process_events(&self) -> Result<(), String> {
        let mut queue = self.event_queue.lock().unwrap();
        let mut state = self.state.lock().unwrap();
        
        while let Some(event) = queue.pop() {
            if let Some(handler) = self.event_handlers.get(&event.event_type) {
                handler.handle(&event, &mut state)?;
            }
        }
        
        Ok(())
    }
}

/// 具体的事件处理器实现
pub struct OrderEventHandler;

impl EventHandler for OrderEventHandler {
    fn handle(&self, event: &Event, state: &mut serde_json::Value) -> Result<(), String> {
        match event.event_type.as_str() {
            "order.created" => {
                *state = serde_json::json!({
                    "order_id": event.payload["order_id"],
                    "status": "created",
                    "timestamp": event.timestamp
                });
            }
            "order.processed" => {
                if let Some(current_state) = state.as_object_mut() {
                    current_state.insert("status".to_string(), serde_json::Value::String("processed".to_string()));
                }
            }
            "order.completed" => {
                if let Some(current_state) = state.as_object_mut() {
                    current_state.insert("status".to_string(), serde_json::Value::String("completed".to_string()));
                }
            }
            _ => return Err(format!("Unknown event type: {}", event.event_type)),
        }
        
        Ok(())
    }
    
    fn event_type(&self) -> &str {
        "order"
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// 测试基础工作流
    #[tokio::test]
    async fn test_basic_workflow() {
        let mut workflow = Workflow::new(
            "test_workflow".to_string(),
            "Test Workflow".to_string(),
            "A test workflow".to_string(),
        );
        
        // 添加任务
        let mut task1 = Task::new(
            "task1".to_string(),
            "Task 1".to_string(),
            "First task".to_string(),
        );
        
        let mut task2 = Task::new(
            "task2".to_string(),
            "Task 2".to_string(),
            "Second task".to_string(),
        );
        
        task2.add_dependency("task1".to_string());
        
        workflow.add_task(task1);
        workflow.add_task(task2);
        
        // 测试任务依赖
        let completed_tasks = HashSet::new();
        let ready_tasks = workflow.get_ready_tasks(&completed_tasks);
        assert_eq!(ready_tasks.len(), 1);
        assert_eq!(ready_tasks[0], "task1");
        
        // 测试工作流执行
        let executor = WorkflowExecutor::new();
        executor.register_workflow(workflow).await;
        
        let result = executor.execute_workflow("test_workflow").await;
        assert!(result.is_ok());
    }

    /// 测试状态机工作流
    #[tokio::test]
    async fn test_state_machine_workflow() {
        let mut sm = StateMachineWorkflow::new("initial".to_string());
        
        sm.add_state("running".to_string());
        sm.add_state("completed".to_string());
        sm.add_event("start".to_string());
        sm.add_event("complete".to_string());
        
        sm.add_transition("initial".to_string(), "start".to_string(), "running".to_string());
        sm.add_transition("running".to_string(), "complete".to_string(), "completed".to_string());
        sm.add_final_state("completed".to_string());
        
        // 测试状态转换
        let new_state = sm.transition("start".to_string());
        assert!(new_state.is_ok());
        assert_eq!(new_state.unwrap(), "running");
        
        let final_state = sm.transition("complete".to_string());
        assert!(final_state.is_ok());
        assert_eq!(final_state.unwrap(), "completed");
        assert!(sm.is_final());
    }

    /// 测试管道工作流
    #[tokio::test]
    async fn test_pipeline_workflow() {
        struct TestStage;
        
        impl PipelineStage<String, String, String> for TestStage {
            fn process(&self, input: String) -> Result<String, String> {
                Ok(format!("processed_{}", input))
            }
            
            fn name(&self) -> &str {
                "test_stage"
            }
        }
        
        let mut pipeline = PipelineWorkflow::new();
        pipeline.add_stage(Box::new(TestStage));
        pipeline.add_stage(Box::new(TestStage));
        
        let result = pipeline.process("input".to_string());
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), "processed_processed_input");
    }

    /// 测试事件驱动工作流
    #[tokio::test]
    async fn test_event_driven_workflow() {
        let mut workflow = EventDrivenWorkflow::new();
        workflow.register_handler(Box::new(OrderEventHandler));
        
        let event = Event {
            id: "event1".to_string(),
            event_type: "order.created".to_string(),
            payload: serde_json::json!({"order_id": "123"}),
            timestamp: Utc::now(),
        };
        
        workflow.publish_event(event).await.unwrap();
        workflow.process_events().await.unwrap();
        
        let state = workflow.state.lock().unwrap();
        assert_eq!(state["status"], "created");
    }
}

/// 示例用法
pub async fn run_examples() {
    println!("=== 基础工作流案例 ===");
    
    // 1. 基础工作流示例
    println!("\n1. 基础工作流示例:");
    let mut workflow = Workflow::new(
        "order_processing".to_string(),
        "Order Processing Workflow".to_string(),
        "Process customer orders".to_string(),
    );
    
    // 创建任务
    let mut validate_order = Task::new(
        "validate_order".to_string(),
        "Validate Order".to_string(),
        "Validate customer order".to_string(),
    );
    
    let mut process_payment = Task::new(
        "process_payment".to_string(),
        "Process Payment".to_string(),
        "Process payment for order".to_string(),
    );
    
    let mut ship_order = Task::new(
        "ship_order".to_string(),
        "Ship Order".to_string(),
        "Ship the order to customer".to_string(),
    );
    
    // 添加依赖关系
    process_payment.add_dependency("validate_order".to_string());
    ship_order.add_dependency("process_payment".to_string());
    
    // 添加到工作流
    workflow.add_task(validate_order);
    workflow.add_task(process_payment);
    workflow.add_task(ship_order);
    
    // 执行工作流
    let executor = WorkflowExecutor::new();
    executor.register_workflow(workflow).await;
    
    match executor.execute_workflow("order_processing").await {
        Ok(result) => println!("  工作流执行成功: {:?}", result),
        Err(e) => println!("  工作流执行失败: {}", e),
    }
    
    // 2. 状态机工作流示例
    println!("\n2. 状态机工作流示例:");
    let mut order_sm = StateMachineWorkflow::new("created".to_string());
    
    order_sm.add_state("validated".to_string());
    order_sm.add_state("paid".to_string());
    order_sm.add_state("shipped".to_string());
    order_sm.add_state("delivered".to_string());
    
    order_sm.add_transition("created".to_string(), "validate".to_string(), "validated".to_string());
    order_sm.add_transition("validated".to_string(), "pay".to_string(), "paid".to_string());
    order_sm.add_transition("paid".to_string(), "ship".to_string(), "shipped".to_string());
    order_sm.add_transition("shipped".to_string(), "deliver".to_string(), "delivered".to_string());
    
    order_sm.add_final_state("delivered".to_string());
    
    // 执行状态转换
    println!("  初始状态: {:?}", order_sm.current_state);
    
    order_sm.transition("validate".to_string()).unwrap();
    println!("  验证后状态: {:?}", order_sm.current_state);
    
    order_sm.transition("pay".to_string()).unwrap();
    println!("  支付后状态: {:?}", order_sm.current_state);
    
    order_sm.transition("ship".to_string()).unwrap();
    println!("  发货后状态: {:?}", order_sm.current_state);
    
    order_sm.transition("deliver".to_string()).unwrap();
    println!("  交付后状态: {:?}", order_sm.current_state);
    println!("  是否完成: {}", order_sm.is_final());
    
    // 3. 管道工作流示例
    println!("\n3. 管道工作流示例:");
    struct DataValidationStage;
    struct DataTransformationStage;
    struct DataOutputStage;
    
    impl PipelineStage<String, String, String> for DataValidationStage {
        fn process(&self, input: String) -> Result<String, String> {
            if input.is_empty() {
                Err("Input cannot be empty".to_string())
            } else {
                Ok(format!("validated_{}", input))
            }
        }
        
        fn name(&self) -> &str {
            "validation"
        }
    }
    
    impl PipelineStage<String, String, String> for DataTransformationStage {
        fn process(&self, input: String) -> Result<String, String> {
            Ok(input.to_uppercase())
        }
        
        fn name(&self) -> &str {
            "transformation"
        }
    }
    
    impl PipelineStage<String, String, String> for DataOutputStage {
        fn process(&self, input: String) -> Result<String, String> {
            Ok(format!("output_{}", input))
        }
        
        fn name(&self) -> &str {
            "output"
        }
    }
    
    let mut pipeline = PipelineWorkflow::new();
    pipeline.add_stage(Box::new(DataValidationStage));
    pipeline.add_stage(Box::new(DataTransformationStage));
    pipeline.add_stage(Box::new(DataOutputStage));
    
    match pipeline.process("test data".to_string()) {
        Ok(result) => println!("  管道处理结果: {}", result),
        Err(e) => println!("  管道处理失败: {}", e),
    }
    
    // 4. 事件驱动工作流示例
    println!("\n4. 事件驱动工作流示例:");
    let mut event_workflow = EventDrivenWorkflow::new();
    event_workflow.register_handler(Box::new(OrderEventHandler));
    
    // 发布事件
    let events = vec![
        Event {
            id: "event1".to_string(),
            event_type: "order.created".to_string(),
            payload: serde_json::json!({"order_id": "12345"}),
            timestamp: Utc::now(),
        },
        Event {
            id: "event2".to_string(),
            event_type: "order.processed".to_string(),
            payload: serde_json::json!({"order_id": "12345"}),
            timestamp: Utc::now(),
        },
        Event {
            id: "event3".to_string(),
            event_type: "order.completed".to_string(),
            payload: serde_json::json!({"order_id": "12345"}),
            timestamp: Utc::now(),
        },
    ];
    
    for event in events {
        event_workflow.publish_event(event).await.unwrap();
    }
    
    event_workflow.process_events().await.unwrap();
    
    let state = event_workflow.state.lock().unwrap();
    println!("  最终状态: {:?}", state);
} 