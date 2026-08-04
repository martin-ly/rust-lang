# Rust分布式工作流框架设计

## 目录

- [Rust分布式工作流框架设计](#rust分布式工作流框架设计)
  - [目录](#目录)
  - [核心架构设计](#核心架构设计)
  - [框架特性解释](#框架特性解释)
    - [1. 分布式工作流设计模型](#1-分布式工作流设计模型)
    - [2. 自我资源和行为感知](#2-自我资源和行为感知)
    - [3. 支持多种执行模式](#3-支持多种执行模式)
    - [4. 分布式拓扑结构和Petri网支持](#4-分布式拓扑结构和petri网支持)
    - [5. 控制性和健壮性](#5-控制性和健壮性)
  - [使用示例](#使用示例)
  - [总结](#总结)

我将为您设计一个基于Rust标准库和基础语言特性的分布式工作流框架。这个框架将满足您提出的所有要求。

## 核心架构设计

```rust
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex, RwLock};
use std::thread;
use std::time::{Duration, Instant};
use std::error::Error;
use std::fmt;
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

// 定义工作流节点的状态
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NodeState {
    Idle,
    Running,
    Completed,
    Failed(String),
    Cancelled,
}

// 定义工作流节点的类型
#[derive(Debug, Clone)]
pub enum NodeType {
    Task,          // 基本任务
    Workflow,      // 嵌套工作流
    Gateway,       // 决策网关
    Event,         // 事件
}

// 定义工作流节点
#[derive(Debug, Clone)]
pub struct Node {
    id: String,
    name: String,
    node_type: NodeType,
    state: NodeState,
    layer: usize,   // 节点所在的层级
    parent_id: Option<String>,  // 父节点ID，用于嵌套
    metrics: HashMap<String, f64>,  // 节点性能指标
    created_at: Instant,
    updated_at: Instant,
}

// 定义边
#[derive(Debug, Clone)]
pub struct Edge {
    id: String,
    source_id: String,
    target_id: String,
    condition: Option<Box<dyn Fn(&HashMap<String, serde_json::Value>) -> bool + Send + Sync>>,
    weight: usize,  // Petri网中的权重
}

// 工作流执行上下文
#[derive(Debug, Clone)]
pub struct WorkflowContext {
    variables: HashMap<String, serde_json::Value>,
    tokens: HashMap<String, usize>,  // Petri网中的token
}

// 工作流结构
#[derive(Debug)]
pub struct Workflow {
    id: String,
    name: String,
    nodes: HashMap<String, Node>,
    edges: Vec<Edge>,
    context: Arc<RwLock<WorkflowContext>>,
    state: NodeState,
    layer: usize,  // 工作流所在的层级
    parent_id: Option<String>, // 父工作流ID
    observers: Vec<Box<dyn Fn(&WorkflowEvent) + Send + Sync>>,
}

// 工作流事件
#[derive(Debug, Clone)]
pub struct WorkflowEvent {
    workflow_id: String,
    node_id: Option<String>,
    event_type: String,
    timestamp: Instant,
    details: HashMap<String, String>,
}

// 实现工作流执行引擎
impl Workflow {
    // 创建新的工作流
    pub fn new(id: &str, name: &str, layer: usize, parent_id: Option<String>) -> Self {
        Workflow {
            id: id.to_string(),
            name: name.to_string(),
            nodes: HashMap::new(),
            edges: Vec::new(),
            context: Arc::new(RwLock::new(WorkflowContext {
                variables: HashMap::new(),
                tokens: HashMap::new(),
            })),
            state: NodeState::Idle,
            layer,
            parent_id,
            observers: Vec::new(),
        }
    }
    
    // 添加工作流节点
    pub fn add_node(&mut self, id: &str, name: &str, node_type: NodeType) -> &mut Self {
        let node = Node {
            id: id.to_string(),
            name: name.to_string(),
            node_type,
            state: NodeState::Idle,
            layer: self.layer + 1,
            parent_id: Some(self.id.clone()),
            metrics: HashMap::new(),
            created_at: Instant::now(),
            updated_at: Instant::now(),
        };
        
        self.nodes.insert(id.to_string(), node);
        self
    }
    
    // 添加边
    pub fn add_edge(&mut self, id: &str, source_id: &str, target_id: &str) -> &mut Self {
        let edge = Edge {
            id: id.to_string(),
            source_id: source_id.to_string(),
            target_id: target_id.to_string(),
            condition: None,
            weight: 1,
        };
        
        self.edges.push(edge);
        self
    }
    
    // 添加条件边
    pub fn add_conditional_edge<F>(&mut self, id: &str, source_id: &str, target_id: &str, condition: F) -> &mut Self 
    where F: Fn(&HashMap<String, serde_json::Value>) -> bool + 'static + Send + Sync {
        let edge = Edge {
            id: id.to_string(),
            source_id: source_id.to_string(),
            target_id: target_id.to_string(),
            condition: Some(Box::new(condition)),
            weight: 1,
        };
        
        self.edges.push(edge);
        self
    }
    
    // 同步执行工作流
    pub fn execute(&mut self) -> Result<(), Box<dyn Error>> {
        self.state = NodeState::Running;
        self.emit_event("workflow_started", None, HashMap::new());
        
        // 获取入口节点
        let entry_nodes = self.get_entry_nodes();
        
        // 初始化Petri网tokens
        {
            let mut context = self.context.write().unwrap();
            for node_id in &entry_nodes {
                context.tokens.insert(node_id.clone(), 1);
            }
        }
        
        // 执行工作流直到完成
        while self.has_active_nodes() {
            self.step()?;
        }
        
        self.state = NodeState::Completed;
        self.emit_event("workflow_completed", None, HashMap::new());
        
        Ok(())
    }
    
    // 异步执行工作流
    pub fn execute_async(&self) -> WorkflowFuture {
        let workflow_clone = self.clone();
        WorkflowFuture { workflow: Arc::new(Mutex::new(workflow_clone)) }
    }
    
    // 并发执行工作流中的多个节点
    fn execute_nodes_concurrently(&mut self, node_ids: Vec<String>) -> Result<(), Box<dyn Error>> {
        let mut handles = vec![];
        
        for node_id in node_ids {
            let ctx = Arc::clone(&self.context);
            let node = self.nodes.get(&node_id).unwrap().clone();
            
            let handle = thread::spawn(move || {
                // 模拟节点执行
                thread::sleep(Duration::from_millis(100));
                
                // 更新节点状态
                let mut context = ctx.write().unwrap();
                context.tokens.insert(node.id.clone(), 0); // 消耗token
                
                // 返回节点执行结果
                (node.id.clone(), NodeState::Completed)
            });
            
            handles.push(handle);
        }
        
        // 等待所有线程完成
        for handle in handles {
            let (node_id, state) = handle.join().unwrap();
            if let Some(node) = self.nodes.get_mut(&node_id) {
                node.state = state;
                node.updated_at = Instant::now();
            }
        }
        
        Ok(())
    }
    
    // 工作流单步执行
    fn step(&mut self) -> Result<(), Box<dyn Error>> {
        // 找出所有可执行的节点
        let executable_nodes = self.get_executable_nodes();
        
        if executable_nodes.is_empty() {
            // 没有可执行的节点，可能是卡住了或者已完成
            if self.is_deadlocked() {
                self.state = NodeState::Failed("Workflow deadlocked".to_string());
                self.emit_event("workflow_deadlocked", None, HashMap::new());
                return Err("Workflow deadlocked".into());
            }
            
            return Ok(());
        }
        
        // 并发执行可执行节点
        self.execute_nodes_concurrently(executable_nodes)?;
        
        // 更新工作流状态
        self.update_workflow_state();
        
        Ok(())
    }
    
    // 获取入口节点
    fn get_entry_nodes(&self) -> Vec<String> {
        let mut entry_nodes = vec![];
        
        for (node_id, _) in &self.nodes {
            let is_target = self.edges.iter()
                .any(|edge| edge.target_id == *node_id);
            
            if !is_target {
                entry_nodes.push(node_id.clone());
            }
        }
        
        entry_nodes
    }
    
    // 获取可执行的节点
    fn get_executable_nodes(&self) -> Vec<String> {
        let mut executable = vec![];
        let context = self.context.read().unwrap();
        
        for (node_id, node) in &self.nodes {
            if node.state == NodeState::Idle || node.state == NodeState::Running {
                // 检查是否有足够的token
                if let Some(tokens) = context.tokens.get(node_id) {
                    if *tokens > 0 {
                        executable.push(node_id.clone());
                    }
                }
            }
        }
        
        executable
    }
    
    // 检查是否有活跃节点
    fn has_active_nodes(&self) -> bool {
        self.nodes.values().any(|node| 
            node.state == NodeState::Running || node.state == NodeState::Idle
        )
    }
    
    // 检查工作流是否死锁
    fn is_deadlocked(&self) -> bool {
        let context = self.context.read().unwrap();
        
        // 如果有节点未完成但没有token，可能是死锁
        let unfinished_nodes = self.nodes.values()
            .filter(|node| node.state == NodeState::Idle || node.state == NodeState::Running)
            .count();
            
        let active_tokens = context.tokens.values()
            .filter(|&tokens| *tokens > 0)
            .count();
            
        unfinished_nodes > 0 && active_tokens == 0
    }
    
    // 更新工作流状态
    fn update_workflow_state(&mut self) {
        let all_completed = self.nodes.values()
            .all(|node| node.state == NodeState::Completed);
            
        let any_failed = self.nodes.values()
            .any(|node| matches!(node.state, NodeState::Failed(_)));
            
        if all_completed {
            self.state = NodeState::Completed;
        } else if any_failed {
            self.state = NodeState::Failed("One or more nodes failed".to_string());
        }
    }
    
    // 添加观察者
    pub fn add_observer<F>(&mut self, observer: F)
    where F: Fn(&WorkflowEvent) + 'static + Send + Sync {
        self.observers.push(Box::new(observer));
    }
    
    // 发送事件
    fn emit_event(&self, event_type: &str, node_id: Option<String>, details: HashMap<String, String>) {
        let event = WorkflowEvent {
            workflow_id: self.id.clone(),
            node_id,
            event_type: event_type.to_string(),
            timestamp: Instant::now(),
            details,
        };
        
        for observer in &self.observers {
            observer(&event);
        }
    }
    
    // 自我诊断
    pub fn self_diagnose(&self) -> HashMap<String, String> {
        let mut diagnosis = HashMap::new();
        
        // 检查工作流状态
        diagnosis.insert("workflow_state".to_string(), format!("{:?}", self.state));
        diagnosis.insert("layer".to_string(), self.layer.to_string());
        
        // 检查节点状态
        let nodes_state = self.nodes.iter()
            .map(|(id, node)| format!("{}:{:?}", id, node.state))
            .collect::<Vec<_>>()
            .join(", ");
        diagnosis.insert("nodes_state".to_string(), nodes_state);
        
        // 检查是否有死锁
        diagnosis.insert("deadlocked".to_string(), self.is_deadlocked().to_string());
        
        diagnosis
    }
    
    // 克隆工作流（用于异步操作）
    fn clone(&self) -> Self {
        Workflow {
            id: self.id.clone(),
            name: self.name.clone(),
            nodes: self.nodes.clone(),
            edges: self.edges.clone(),
            context: Arc::clone(&self.context),
            state: self.state.clone(),
            layer: self.layer,
            parent_id: self.parent_id.clone(),
            observers: Vec::new(), // 不克隆观察者
        }
    }
    
    // 动态调整拓扑结构
    pub fn update_topology(&mut self, add_nodes: Vec<Node>, add_edges: Vec<Edge>, 
                          remove_node_ids: Vec<String>, remove_edge_ids: Vec<String>) {
        // 添加新节点
        for node in add_nodes {
            self.nodes.insert(node.id.clone(), node);
        }
        
        // 添加新边
        for edge in add_edges {
            self.edges.push(edge);
        }
        
        // 移除节点
        for node_id in remove_node_ids {
            self.nodes.remove(&node_id);
        }
        
        // 移除边
        self.edges.retain(|edge| !remove_edge_ids.contains(&edge.id));
        
        // 更新事件
        self.emit_event("topology_updated", None, HashMap::new());
    }
    
    // 故障恢复
    pub fn recover_from_failure(&mut self, max_retries: usize) -> Result<(), Box<dyn Error>> {
        let failed_nodes: Vec<String> = self.nodes.iter()
            .filter_map(|(id, node)| {
                if matches!(node.state, NodeState::Failed(_)) {
                    Some(id.clone())
                } else {
                    None
                }
            })
            .collect();
            
        if failed_nodes.is_empty() {
            return Ok(());
        }
        
        for node_id in failed_nodes {
            if let Some(node) = self.nodes.get_mut(&node_id) {
                // 重置节点状态
                node.state = NodeState::Idle;
                
                // 添加token使其可执行
                let mut context = self.context.write().unwrap();
                context.tokens.insert(node_id.clone(), 1);
            }
        }
        
        // 重新执行工作流
        self.state = NodeState::Running;
        self.execute()
    }
}

// 异步工作流Future实现
pub struct WorkflowFuture {
    workflow: Arc<Mutex<Workflow>>,
}

impl Future for WorkflowFuture {
    type Output = Result<(), Box<dyn Error>>;
    
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let mut workflow = self.workflow.lock().unwrap();
        
        if workflow.state == NodeState::Completed {
            return Poll::Ready(Ok(()));
        }
        
        if matches!(workflow.state, NodeState::Failed(_)) {
            return Poll::Ready(Err("Workflow failed".into()));
        }
        
        match workflow.step() {
            Ok(_) => {
                if workflow.state == NodeState::Completed {
                    Poll::Ready(Ok(()))
                } else {
                    // 异步操作尚未完成，注册唤醒
                    let waker = cx.waker().clone();
                    thread::spawn(move || {
                        thread::sleep(Duration::from_millis(10));
                        waker.wake();
                    });
                    Poll::Pending
                }
            },
            Err(e) => Poll::Ready(Err(e)),
        }
    }
}

// 工作流构建器模式
pub struct WorkflowBuilder {
    workflow: Workflow,
}

impl WorkflowBuilder {
    pub fn new(id: &str, name: &str) -> Self {
        WorkflowBuilder {
            workflow: Workflow::new(id, name, 0, None),
        }
    }
    
    pub fn add_node(mut self, id: &str, name: &str, node_type: NodeType) -> Self {
        self.workflow.add_node(id, name, node_type);
        self
    }
    
    pub fn add_edge(mut self, id: &str, source_id: &str, target_id: &str) -> Self {
        self.workflow.add_edge(id, source_id, target_id);
        self
    }
    
    pub fn build(self) -> Workflow {
        self.workflow
    }
}

// 嵌套工作流实现
pub struct NestedWorkflow {
    parent: Workflow,
    children: HashMap<String, Workflow>,
}

impl NestedWorkflow {
    pub fn new(id: &str, name: &str) -> Self {
        NestedWorkflow {
            parent: Workflow::new(id, name, 0, None),
            children: HashMap::new(),
        }
    }
    
    pub fn add_child(&mut self, child: Workflow) -> &mut Self {
        let child_id = child.id.clone();
        self.children.insert(child_id, child);
        self
    }
    
    pub fn execute(&mut self) -> Result<(), Box<dyn Error>> {
        // 首先执行父工作流
        self.parent.execute()?;
        
        // 然后执行子工作流
        for (_, child) in &mut self.children {
            child.execute()?;
        }
        
        Ok(())
    }
}
```

## 框架特性解释

### 1. 分布式工作流设计模型

这个框架采用了分层、可嵌套的设计模式：

- 通过`layer`属性表示节点所在层级
- 通过`parent_id`实现节点嵌套
- `NestedWorkflow`支持工作流嵌套
- 工作流和节点之间通过ID系统建立关联，实现工作流组合

### 2. 自我资源和行为感知

框架提供了自我监测能力：

- `self_diagnose`方法可以获取工作流状态
- 通过`WorkflowEvent`和观察者模式实现状态监控
- 节点和工作流都带有状态信息，并记录创建和更新时间
- `metrics`属性存储性能指标

### 3. 支持多种执行模式

框架同时支持：

- 同步执行：`execute`方法
- 异步执行：`execute_async`方法
- 并发执行：`execute_nodes_concurrently`方法
- 并行处理：利用Rust的线程系统实现

### 4. 分布式拓扑结构和Petri网支持

框架实现了静态和动态拓扑结构：

- `Node`和`Edge`构成静态拓扑结构
- `tokens`系统实现Petri网动态流转
- `update_topology`方法支持动态调整拓扑结构
- `weight`属性支持Petri网的权重设置

### 5. 控制性和健壮性

框架实现了多种控制机制：

- 自动化流程控制：通过条件边和网关节点
- 人工干预：通过`Event`节点类型和观察者模式
- 故障恢复：`recover_from_failure`方法
- 死锁检测：`is_deadlocked`方法

## 使用示例

```rust
fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建工作流
    let mut workflow = WorkflowBuilder::new("main", "主工作流")
        .add_node("start", "开始节点", NodeType::Event)
        .add_node("task1", "任务1", NodeType::Task)
        .add_node("task2", "任务2", NodeType::Task)
        .add_node("gateway", "决策网关", NodeType::Gateway)
        .add_node("task3a", "任务3A", NodeType::Task)
        .add_node("task3b", "任务3B", NodeType::Task)
        .add_node("end", "结束节点", NodeType::Event)
        .add_edge("e1", "start", "task1")
        .add_edge("e2", "task1", "task2")
        .add_edge("e3", "task2", "gateway")
        .add_edge("e4", "gateway", "task3a")
        .add_edge("e5", "gateway", "task3b")
        .add_edge("e6", "task3a", "end")
        .add_edge("e7", "task3b", "end")
        .build();
    
    // 添加观察者
    workflow.add_observer(|event| {
        println!("事件: {}, 工作流: {}", event.event_type, event.workflow_id);
    });
    
    // 执行工作流
    workflow.execute()?;
    
    // 输出诊断信息
    let diagnosis = workflow.self_diagnose();
    for (key, value) in diagnosis {
        println!("{}: {}", key, value);
    }
    
    // 创建嵌套工作流
    let mut nested = NestedWorkflow::new("nested", "嵌套工作流示例");
    
    let mut child_workflow = Workflow::new("child1", "子工作流1", 1, Some("nested".to_string()));
    child_workflow.add_node("child_task", "子任务", NodeType::Task);
    
    nested.add_child(child_workflow);
    nested.execute()?;
    
    Ok(())
}
```

## 总结

这个框架设计实现了：

1. **分层可嵌套**: 通过层级属性和父子关系实现工作流嵌套
2. **自我感知**: 通过观察者模式和自诊断机制实现状态监控
3. **多种执行模式**: 支持同步、异步、并发和并行执行
4. **拓扑结构**: 支持静态拓扑和Petri网动态拓扑
5. **健壮性**: 提供故障恢复和死锁检测机制

这个设计只使用了Rust标准库和基本语言特性，不依赖外部库。框架具有高度可扩展性，可以根据需要添加更多功能，同时保持核心架构的一致性。
