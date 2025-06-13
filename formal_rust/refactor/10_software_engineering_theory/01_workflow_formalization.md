# 工作流理论形式化重构

## 目录

1. [理论基础](#1-理论基础)
2. [工作流五元组定义](#2-工作流五元组定义)
3. [Petri网工作流理论](#3-petri网工作流理论)
4. [过程代数工作流理论](#4-过程代数工作流理论)
5. [状态机工作流理论](#5-状态机工作流理论)
6. [工作流模式理论](#6-工作流模式理论)
7. [工作流验证理论](#7-工作流验证理论)
8. [核心定理证明](#8-核心定理证明)
9. [Rust实现](#9-rust实现)

## 1. 理论基础

### 1.1 工作流基础

**定义1.1 (工作流)**
工作流 $W = (A, T, D, R, C)$ 包含：
- $A$: 活动集合
- $T$: 转移关系集合
- $D$: 数据对象集合
- $R$: 资源集合
- $C$: 约束条件集合

**定义1.2 (活动)**
活动 $a \in A$ 是一个三元组 $(I, P, O)$ 包含：
- $I$: 输入条件集合
- $P$: 处理逻辑
- $O$: 输出结果集合

**定义1.3 (转移关系)**
转移关系 $t \in T$ 是一个四元组 $(a_1, a_2, g, f)$ 包含：
- $a_1, a_2 \in A$: 源活动和目标活动
- $g$: 转移条件
- $f$: 数据转换函数

### 1.2 工作流执行基础

**定义1.4 (工作流实例)**
工作流实例 $I = (W, S, E)$ 包含：
- $W$: 工作流定义
- $S$: 当前状态
- $E$: 执行历史

**定义1.5 (执行状态)**
执行状态 $S = (M, D, R)$ 包含：
- $M$: 活动标记
- $D$: 数据状态
- $R$: 资源分配

## 2. 工作流五元组定义

**定义2.1 (工作流系统)**
工作流系统 $WS = (M, E, S, V, C)$ 包含：

- **M (Model)**: 工作流模型 $M = (A, T, D, R, C)$
  - $A$: 活动定义
  - $T$: 转移定义
  - $D$: 数据定义
  - $R$: 资源定义
  - $C$: 约束定义

- **E (Engine)**: 执行引擎 $E = (S, P, C, M)$
  - $S$: 调度器
  - $P$: 处理器
  - $C$: 控制器
  - $M$: 监控器

- **S (State)**: 状态管理 $S = (I, T, P, H)$
  - $I$: 实例管理
  - $T$: 事务管理
  - $P$: 持久化
  - $H$: 历史记录

- **V (Validation)**: 验证系统 $V = (C, A, P, S)$
  - $C$: 正确性检查
  - $A$: 可达性分析
  - $P$: 性能分析
  - $S$: 安全性检查

- **C (Control)**: 控制系统 $C = (A, M, R, E)$
  - $A$: 访问控制
  - $M$: 监控管理
  - $R$: 资源管理
  - $E$: 异常处理

## 3. Petri网工作流理论

### 3.1 Petri网基础

**定义3.1 (Petri网)**
Petri网 $PN = (P, T, F, W, M_0)$ 包含：
- $P$: 库所集合
- $T$: 变迁集合
- $F \subseteq (P \times T) \cup (T \times P)$: 流关系
- $W: F \rightarrow \mathbb{N}^+$: 权重函数
- $M_0: P \rightarrow \mathbb{N}$: 初始标识

**定义3.2 (工作流Petri网)**
工作流Petri网 $WF-net = (PN, i, o)$ 满足：
- $\bullet i = \emptyset$ (唯一源库所)
- $o \bullet = \emptyset$ (唯一汇库所)
- 每个节点都在从 $i$ 到 $o$ 的路径上

### 3.2 Petri网性质

**定义3.3 (可达性)**
可达性 $\text{Reachable}: M \times M \rightarrow \text{Boolean}$ 定义为：
$$\text{Reachable}(M_1, M_2) = \exists \sigma: M_1[\sigma\rangle M_2$$

**定义3.4 (活性)**
活性 $\text{Live}: T \times M \rightarrow \text{Boolean}$ 定义为：
$$\text{Live}(t, M) = \forall M' \in \text{Reach}(M): \exists M'': M'[\sigma\rangle M'' \land t \in \sigma$$

**定义3.5 (有界性)**
有界性 $\text{Bounded}: P \times M \rightarrow \text{Boolean}$ 定义为：
$$\text{Bounded}(p, M) = \exists k \in \mathbb{N}: \forall M' \in \text{Reach}(M): M'(p) \leq k$$

## 4. 过程代数工作流理论

### 4.1 过程代数基础

**定义4.1 (过程代数)**
过程代数 $PA = (P, \Sigma, \rightarrow)$ 包含：
- $P$: 过程集合
- $\Sigma$: 动作集合
- $\rightarrow \subseteq P \times \Sigma \times P$: 转移关系

**定义4.2 (基本算子)**
过程代数基本算子：
- 顺序组合: $P \cdot Q$
- 选择组合: $P + Q$
- 并行组合: $P \parallel Q$
- 通信组合: $P | Q$

### 4.2 工作流过程代数

**定义4.3 (工作流过程)**
工作流过程 $WP = \text{Process}(A, T, D)$ 定义为：
$$WP = \text{Compose}(\text{Activities}(A), \text{Transitions}(T), \text{Data}(D))$$

**定义4.4 (过程组合)**
过程组合 $\text{Compose}: P \times P \times \text{Operator} \rightarrow P$ 定义为：
$$\text{Compose}(P_1, P_2, op) = P_1 \text{ op } P_2$$

## 5. 状态机工作流理论

### 5.1 状态机基础

**定义5.1 (状态机)**
状态机 $SM = (S, E, T, I, F)$ 包含：
- $S$: 状态集合
- $E$: 事件集合
- $T: S \times E \rightarrow S$: 转移函数
- $I \in S$: 初始状态
- $F \subseteq S$: 最终状态集合

**定义5.2 (工作流状态机)**
工作流状态机 $WSM = (SM, A, D, R)$ 包含：
- $SM$: 基础状态机
- $A$: 活动映射
- $D$: 数据映射
- $R$: 资源映射

### 5.2 状态机执行

**定义5.3 (状态机执行)**
状态机执行 $\text{Execute}: SM \times \text{Event} \rightarrow SM$ 定义为：
$$\text{Execute}(sm, e) = \text{Transition}(sm, e)$$

**定义5.4 (执行路径)**
执行路径 $\text{ExecutionPath}: SM \times [E] \rightarrow [S]$ 定义为：
$$\text{ExecutionPath}(sm, [e_1, e_2, \ldots, e_n]) = [s_0, s_1, \ldots, s_n]$$

## 6. 工作流模式理论

### 6.1 控制流模式

**定义6.1 (顺序模式)**
顺序模式 $\text{Sequential}: [A] \rightarrow W$ 定义为：
$$\text{Sequential}([a_1, a_2, \ldots, a_n]) = a_1 \rightarrow a_2 \rightarrow \ldots \rightarrow a_n$$

**定义6.2 (并行模式)**
并行模式 $\text{Parallel}: [A] \rightarrow W$ 定义为：
$$\text{Parallel}([a_1, a_2, \ldots, a_n]) = a_1 \parallel a_2 \parallel \ldots \parallel a_n$$

**定义6.3 (选择模式)**
选择模式 $\text{Choice}: [A] \times [C] \rightarrow W$ 定义为：
$$\text{Choice}([a_1, a_2, \ldots, a_n], [c_1, c_2, \ldots, c_n]) = c_1:a_1 + c_2:a_2 + \ldots + c_n:a_n$$

### 6.2 数据流模式

**定义6.4 (数据传递)**
数据传递 $\text{DataFlow}: A \times A \times D \rightarrow W$ 定义为：
$$\text{DataFlow}(a_1, a_2, d) = a_1 \xrightarrow{d} a_2$$

**定义6.5 (数据聚合)**
数据聚合 $\text{DataAggregation}: [D] \times A \rightarrow W$ 定义为：
$$\text{DataAggregation}([d_1, d_2, \ldots, d_n], a) = [d_1, d_2, \ldots, d_n] \rightarrow a$$

## 7. 工作流验证理论

### 7.1 正确性验证

**定义7.1 (工作流正确性)**
工作流正确性 $\text{Correct}: W \rightarrow \text{Boolean}$ 定义为：
$$\text{Correct}(W) = \text{Termination}(W) \land \text{Safety}(W) \land \text{Liveness}(W)$$

**定义7.2 (终止性)**
终止性 $\text{Termination}: W \rightarrow \text{Boolean}$ 定义为：
$$\text{Termination}(W) = \forall I \in \text{Instances}(W): \text{ReachesFinal}(I)$$

**定义7.3 (安全性)**
安全性 $\text{Safety}: W \rightarrow \text{Boolean}$ 定义为：
$$\text{Safety}(W) = \forall I \in \text{Instances}(W): \text{NoDeadlock}(I)$$

### 7.2 性能分析

**定义7.4 (工作流性能)**
工作流性能 $\text{Performance}: W \rightarrow \mathbb{R}$ 定义为：
$$\text{Performance}(W) = \text{Throughput}(W) \times \text{Efficiency}(W)$$

**定义7.5 (吞吐量)**
吞吐量 $\text{Throughput}: W \rightarrow \mathbb{R}$ 定义为：
$$\text{Throughput}(W) = \frac{\text{CompletedInstances}(W)}{\text{Time}(W)}$$

## 8. 核心定理证明

### 8.1 工作流正确性定理

**定理8.1 (工作流正确性)**
如果工作流 $W$ 满足Petri网的健全性条件，则 $W$ 是正确的。

**证明**:
设 $W$ 为满足健全性条件的工作流Petri网。

根据Petri网健全性定义：
1. **可达性**: 从初始状态可达最终状态
2. **活性**: 不存在死锁
3. **有界性**: 资源使用有限制

这意味着：
- 所有工作流实例都能正确完成
- 不会出现死锁或活锁
- 资源使用在合理范围内

因此工作流 $W$ 是正确的。$\square$

### 8.2 工作流终止性定理

**定理8.2 (工作流终止性)**
如果工作流 $W$ 是有限状态且无循环，则 $W$ 总是终止。

**证明**:
设 $W$ 为有限状态且无循环的工作流。

由于 $W$ 是有限状态的，状态空间是有限的。
由于 $W$ 无循环，每个执行路径都是有限的。

因此任何工作流实例都会在有限步内到达最终状态。

因此工作流 $W$ 总是终止。$\square$

### 8.3 工作流安全性定理

**定理8.3 (工作流安全性)**
如果工作流 $W$ 的所有活动都有明确的输入输出条件，则 $W$ 是安全的。

**证明**:
设 $W$ 为所有活动都有明确输入输出条件的工作流。

对于任意活动 $a \in A$：
- 输入条件 $I(a)$ 明确定义了执行前提
- 输出条件 $O(a)$ 明确定义了执行结果

这确保了：
1. 活动只在条件满足时执行
2. 活动执行后状态是确定的
3. 不会出现未定义的行为

因此工作流 $W$ 是安全的。$\square$

### 8.4 工作流活性定理

**定理8.4 (工作流活性)**
如果工作流 $W$ 的Petri网表示是活的，则 $W$ 是活的。

**证明**:
设 $W$ 为Petri网表示是活的工作流。

根据Petri网活性定义：
$$\forall t \in T, \forall M \in \text{Reach}(M_0): \exists M': M[\sigma\rangle M' \land t \in \sigma$$

这意味着：
1. 所有变迁都能在某个时刻被触发
2. 不存在永远无法执行的变迁
3. 工作流不会陷入死锁状态

因此工作流 $W$ 是活的。$\square$

### 8.5 工作流性能定理

**定理8.5 (工作流性能)**
如果工作流 $W$ 的并行度增加，则其吞吐量不会降低。

**证明**:
设 $W_1$ 为原始工作流，$W_2$ 为增加并行度后的工作流。

根据并行模式定义：
$$\text{Parallel}([a_1, a_2, \ldots, a_n]) = a_1 \parallel a_2 \parallel \ldots \parallel a_n$$

这意味着：
1. 多个活动可以同时执行
2. 总执行时间不会超过最长的串行路径
3. 资源利用率提高

因此增加并行度不会降低吞吐量。$\square$

## 9. Rust实现

### 9.1 工作流引擎实现

```rust
use std::collections::{HashMap, VecDeque};
use std::sync::{Arc, Mutex};

/// 活动状态
#[derive(Debug, Clone, PartialEq)]
pub enum ActivityState {
    Ready,
    Running,
    Completed,
    Failed,
}

/// 活动
#[derive(Debug, Clone)]
pub struct Activity {
    pub id: String,
    pub name: String,
    pub state: ActivityState,
    pub inputs: Vec<String>,
    pub outputs: Vec<String>,
    pub handler: Option<Box<dyn Fn() -> Result<(), String> + Send>>,
}

/// 转移条件
#[derive(Debug, Clone)]
pub struct Transition {
    pub from: String,
    pub to: String,
    pub condition: Option<Box<dyn Fn(&HashMap<String, String>) -> bool + Send>>,
    pub data_transform: Option<Box<dyn Fn(HashMap<String, String>) -> HashMap<String, String> + Send>>,
}

/// 工作流定义
pub struct Workflow {
    pub id: String,
    pub name: String,
    pub activities: HashMap<String, Activity>,
    pub transitions: Vec<Transition>,
    pub data_schema: HashMap<String, String>,
}

/// 工作流实例
pub struct WorkflowInstance {
    pub id: String,
    pub workflow: Workflow,
    pub current_state: HashMap<String, ActivityState>,
    pub data: HashMap<String, String>,
    pub history: VecDeque<String>,
}

/// 工作流引擎
pub struct WorkflowEngine {
    instances: Arc<Mutex<HashMap<String, WorkflowInstance>>>,
    workflows: Arc<Mutex<HashMap<String, Workflow>>>,
}

impl WorkflowEngine {
    pub fn new() -> Self {
        WorkflowEngine {
            instances: Arc::new(Mutex::new(HashMap::new())),
            workflows: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    /// 注册工作流
    pub fn register_workflow(&self, workflow: Workflow) -> Result<(), String> {
        let mut workflows = self.workflows.lock().unwrap();
        workflows.insert(workflow.id.clone(), workflow);
        Ok(())
    }
    
    /// 创建工作流实例
    pub fn create_instance(&self, workflow_id: &str, initial_data: HashMap<String, String>) -> Result<String, String> {
        let workflows = self.workflows.lock().unwrap();
        let workflow = workflows.get(workflow_id)
            .ok_or("Workflow not found")?;
        
        let instance_id = format!("{}_{}", workflow_id, uuid::Uuid::new_v4());
        let mut current_state = HashMap::new();
        
        // 初始化所有活动为Ready状态
        for (activity_id, _) in &workflow.activities {
            current_state.insert(activity_id.clone(), ActivityState::Ready);
        }
        
        let instance = WorkflowInstance {
            id: instance_id.clone(),
            workflow: workflow.clone(),
            current_state,
            data: initial_data,
            history: VecDeque::new(),
        };
        
        let mut instances = self.instances.lock().unwrap();
        instances.insert(instance_id.clone(), instance);
        
        Ok(instance_id)
    }
    
    /// 执行工作流实例
    pub fn execute_instance(&self, instance_id: &str) -> Result<(), String> {
        let mut instances = self.instances.lock().unwrap();
        let instance = instances.get_mut(instance_id)
            .ok_or("Instance not found")?;
        
        self.execute_workflow(instance)
    }
    
    /// 执行工作流
    fn execute_workflow(&self, instance: &mut WorkflowInstance) -> Result<(), String> {
        loop {
            let ready_activities = self.get_ready_activities(instance);
            
            if ready_activities.is_empty() {
                // 检查是否完成
                if self.is_completed(instance) {
                    break;
                } else {
                    return Err("Workflow stuck - no ready activities and not completed".to_string());
                }
            }
            
            // 执行就绪的活动
            for activity_id in ready_activities {
                self.execute_activity(instance, &activity_id)?;
            }
            
            // 处理转移
            self.process_transitions(instance)?;
        }
        
        Ok(())
    }
    
    /// 获取就绪的活动
    fn get_ready_activities(&self, instance: &WorkflowInstance) -> Vec<String> {
        let mut ready = Vec::new();
        
        for (activity_id, state) in &instance.current_state {
            if *state == ActivityState::Ready {
                ready.push(activity_id.clone());
            }
        }
        
        ready
    }
    
    /// 执行活动
    fn execute_activity(&self, instance: &mut WorkflowInstance, activity_id: &str) -> Result<(), String> {
        let activity = instance.workflow.activities.get(activity_id)
            .ok_or("Activity not found")?;
        
        // 更新状态为运行中
        instance.current_state.insert(activity_id.to_string(), ActivityState::Running);
        instance.history.push_back(format!("Started activity: {}", activity_id));
        
        // 执行活动处理器
        if let Some(handler) = &activity.handler {
            match handler() {
                Ok(_) => {
                    instance.current_state.insert(activity_id.to_string(), ActivityState::Completed);
                    instance.history.push_back(format!("Completed activity: {}", activity_id));
                },
                Err(e) => {
                    instance.current_state.insert(activity_id.to_string(), ActivityState::Failed);
                    instance.history.push_back(format!("Failed activity: {} - {}", activity_id, e));
                    return Err(e);
                }
            }
        } else {
            // 没有处理器，直接标记为完成
            instance.current_state.insert(activity_id.to_string(), ActivityState::Completed);
            instance.history.push_back(format!("Completed activity: {}", activity_id));
        }
        
        Ok(())
    }
    
    /// 处理转移
    fn process_transitions(&self, instance: &mut WorkflowInstance) -> Result<(), String> {
        for transition in &instance.workflow.transitions {
            let from_state = instance.current_state.get(&transition.from)
                .ok_or("Source activity not found")?;
            
            if *from_state == ActivityState::Completed {
                // 检查转移条件
                let can_transition = if let Some(condition) = &transition.condition {
                    condition(&instance.data)
                } else {
                    true
                };
                
                if can_transition {
                    // 执行数据转换
                    if let Some(transform) = &transition.data_transform {
                        instance.data = transform(instance.data.clone());
                    }
                    
                    // 更新目标活动状态为就绪
                    instance.current_state.insert(transition.to.clone(), ActivityState::Ready);
                    instance.history.push_back(format!("Transition: {} -> {}", transition.from, transition.to));
                }
            }
        }
        
        Ok(())
    }
    
    /// 检查是否完成
    fn is_completed(&self, instance: &WorkflowInstance) -> bool {
        // 检查是否所有活动都已完成或失败
        for state in instance.current_state.values() {
            if *state == ActivityState::Ready || *state == ActivityState::Running {
                return false;
            }
        }
        true
    }
    
    /// 获取实例状态
    pub fn get_instance_state(&self, instance_id: &str) -> Result<HashMap<String, ActivityState>, String> {
        let instances = self.instances.lock().unwrap();
        let instance = instances.get(instance_id)
            .ok_or("Instance not found")?;
        
        Ok(instance.current_state.clone())
    }
    
    /// 获取实例历史
    pub fn get_instance_history(&self, instance_id: &str) -> Result<Vec<String>, String> {
        let instances = self.instances.lock().unwrap();
        let instance = instances.get(instance_id)
            .ok_or("Instance not found")?;
        
        Ok(instance.history.iter().cloned().collect())
    }
}
```

### 9.2 Petri网工作流实现

```rust
use std::collections::{HashMap, HashSet};

/// Petri网库所
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Place {
    pub id: String,
    pub name: String,
    pub tokens: u32,
}

/// Petri网变迁
#[derive(Debug, Clone)]
pub struct Transition {
    pub id: String,
    pub name: String,
    pub input_places: HashMap<String, u32>,
    pub output_places: HashMap<String, u32>,
    pub enabled: bool,
}

/// Petri网
pub struct PetriNet {
    pub places: HashMap<String, Place>,
    pub transitions: HashMap<String, Transition>,
    pub initial_marking: HashMap<String, u32>,
}

/// 工作流Petri网
pub struct WorkflowPetriNet {
    pub petri_net: PetriNet,
    pub source_place: String,
    pub sink_place: String,
}

impl WorkflowPetriNet {
    pub fn new() -> Self {
        WorkflowPetriNet {
            petri_net: PetriNet {
                places: HashMap::new(),
                transitions: HashMap::new(),
                initial_marking: HashMap::new(),
            },
            source_place: "start".to_string(),
            sink_place: "end".to_string(),
        }
    }
    
    /// 添加库所
    pub fn add_place(&mut self, id: String, name: String, initial_tokens: u32) {
        let place = Place {
            id: id.clone(),
            name,
            tokens: initial_tokens,
        };
        self.petri_net.places.insert(id.clone(), place);
        self.petri_net.initial_marking.insert(id, initial_tokens);
    }
    
    /// 添加变迁
    pub fn add_transition(&mut self, id: String, name: String) {
        let transition = Transition {
            id: id.clone(),
            name,
            input_places: HashMap::new(),
            output_places: HashMap::new(),
            enabled: false,
        };
        self.petri_net.transitions.insert(id, transition);
    }
    
    /// 添加弧
    pub fn add_arc(&mut self, from: &str, to: &str, weight: u32) -> Result<(), String> {
        // 检查是从库所到变迁还是从变迁到库所
        if self.petri_net.places.contains_key(from) && self.petri_net.transitions.contains_key(to) {
            // 从库所到变迁
            let transition = self.petri_net.transitions.get_mut(to).unwrap();
            transition.input_places.insert(from.to_string(), weight);
        } else if self.petri_net.transitions.contains_key(from) && self.petri_net.places.contains_key(to) {
            // 从变迁到库所
            let transition = self.petri_net.transitions.get_mut(from).unwrap();
            transition.output_places.insert(to.to_string(), weight);
        } else {
            return Err("Invalid arc: must connect place to transition or transition to place".to_string());
        }
        
        Ok(())
    }
    
    /// 检查变迁是否可触发
    pub fn is_enabled(&self, transition_id: &str) -> bool {
        let transition = self.petri_net.transitions.get(transition_id)
            .expect("Transition not found");
        
        for (place_id, required_tokens) in &transition.input_places {
            let place = self.petri_net.places.get(place_id)
                .expect("Place not found");
            
            if place.tokens < *required_tokens {
                return false;
            }
        }
        
        true
    }
    
    /// 触发变迁
    pub fn fire_transition(&mut self, transition_id: &str) -> Result<(), String> {
        if !self.is_enabled(transition_id) {
            return Err("Transition is not enabled".to_string());
        }
        
        let transition = self.petri_net.transitions.get(transition_id)
            .expect("Transition not found");
        
        // 消耗输入库所的令牌
        for (place_id, tokens) in &transition.input_places {
            let place = self.petri_net.places.get_mut(place_id).unwrap();
            place.tokens -= tokens;
        }
        
        // 产生输出库所的令牌
        for (place_id, tokens) in &transition.output_places {
            let place = self.petri_net.places.get_mut(place_id).unwrap();
            place.tokens += tokens;
        }
        
        Ok(())
    }
    
    /// 检查是否可达最终状态
    pub fn can_reach_final(&self) -> bool {
        let mut reachable_markings = HashSet::new();
        let mut to_explore = vec![self.get_current_marking()];
        
        while let Some(marking) = to_explore.pop() {
            if marking.get(&self.sink_place) > Some(&0) {
                return true;
            }
            
            if reachable_markings.contains(&marking) {
                continue;
            }
            
            reachable_markings.insert(marking.clone());
            
            // 尝试所有可能的变迁
            for transition_id in self.petri_net.transitions.keys() {
                if self.is_enabled(transition_id) {
                    let mut new_marking = marking.clone();
                    // 模拟触发变迁
                    let transition = self.petri_net.transitions.get(transition_id).unwrap();
                    
                    for (place_id, tokens) in &transition.input_places {
                        *new_marking.get_mut(place_id).unwrap() -= tokens;
                    }
                    
                    for (place_id, tokens) in &transition.output_places {
                        *new_marking.get_mut(place_id).unwrap() += tokens;
                    }
                    
                    to_explore.push(new_marking);
                }
            }
        }
        
        false
    }
    
    /// 获取当前标识
    pub fn get_current_marking(&self) -> HashMap<String, u32> {
        let mut marking = HashMap::new();
        for (id, place) in &self.petri_net.places {
            marking.insert(id.clone(), place.tokens);
        }
        marking
    }
    
    /// 重置到初始标识
    pub fn reset(&mut self) {
        for (id, tokens) in &self.petri_net.initial_marking {
            if let Some(place) = self.petri_net.places.get_mut(id) {
                place.tokens = *tokens;
            }
        }
    }
}
```

### 9.3 状态机工作流实现

```rust
use std::collections::HashMap;

/// 工作流状态
#[derive(Debug, Clone, PartialEq)]
pub enum WorkflowState {
    Initial,
    Running,
    Completed,
    Failed,
    Suspended,
}

/// 工作流事件
#[derive(Debug, Clone)]
pub enum WorkflowEvent {
    Start,
    Complete,
    Fail,
    Suspend,
    Resume,
    Cancel,
}

/// 状态机工作流
pub struct StateMachineWorkflow {
    pub id: String,
    pub name: String,
    pub current_state: WorkflowState,
    pub transitions: HashMap<(WorkflowState, WorkflowEvent), WorkflowState>,
    pub activities: HashMap<String, Box<dyn Fn() -> Result<(), String> + Send>>,
    pub data: HashMap<String, String>,
}

impl StateMachineWorkflow {
    pub fn new(id: String, name: String) -> Self {
        let mut workflow = StateMachineWorkflow {
            id,
            name,
            current_state: WorkflowState::Initial,
            transitions: HashMap::new(),
            activities: HashMap::new(),
            data: HashMap::new(),
        };
        
        // 定义默认转移
        workflow.transitions.insert((WorkflowState::Initial, WorkflowEvent::Start), WorkflowState::Running);
        workflow.transitions.insert((WorkflowState::Running, WorkflowEvent::Complete), WorkflowState::Completed);
        workflow.transitions.insert((WorkflowState::Running, WorkflowEvent::Fail), WorkflowState::Failed);
        workflow.transitions.insert((WorkflowState::Running, WorkflowEvent::Suspend), WorkflowState::Suspended);
        workflow.transitions.insert((WorkflowState::Suspended, WorkflowEvent::Resume), WorkflowState::Running);
        workflow.transitions.insert((WorkflowState::Suspended, WorkflowEvent::Cancel), WorkflowState::Failed);
        
        workflow
    }
    
    /// 添加转移
    pub fn add_transition(&mut self, from: WorkflowState, event: WorkflowEvent, to: WorkflowState) {
        self.transitions.insert((from, event), to);
    }
    
    /// 添加活动
    pub fn add_activity<F>(&mut self, name: String, activity: F)
    where
        F: Fn() -> Result<(), String> + Send + 'static,
    {
        self.activities.insert(name, Box::new(activity));
    }
    
    /// 处理事件
    pub fn handle_event(&mut self, event: WorkflowEvent) -> Result<(), String> {
        let transition_key = (self.current_state.clone(), event.clone());
        
        if let Some(&new_state) = self.transitions.get(&transition_key) {
            self.current_state = new_state;
            
            // 执行状态相关的活动
            self.execute_state_activities(&event)?;
            
            Ok(())
        } else {
            Err(format!("Invalid transition: {:?} -> {:?}", self.current_state, event))
        }
    }
    
    /// 执行状态相关活动
    fn execute_state_activities(&mut self, event: &WorkflowEvent) -> Result<(), String> {
        match event {
            WorkflowEvent::Start => {
                // 执行启动活动
                if let Some(activity) = self.activities.get("start") {
                    activity()?;
                }
            },
            WorkflowEvent::Complete => {
                // 执行完成活动
                if let Some(activity) = self.activities.get("complete") {
                    activity()?;
                }
            },
            WorkflowEvent::Fail => {
                // 执行失败活动
                if let Some(activity) = self.activities.get("fail") {
                    activity()?;
                }
            },
            _ => {}
        }
        
        Ok(())
    }
    
    /// 获取当前状态
    pub fn get_current_state(&self) -> WorkflowState {
        self.current_state.clone()
    }
    
    /// 检查是否完成
    pub fn is_completed(&self) -> bool {
        self.current_state == WorkflowState::Completed
    }
    
    /// 检查是否失败
    pub fn is_failed(&self) -> bool {
        self.current_state == WorkflowState::Failed
    }
    
    /// 设置数据
    pub fn set_data(&mut self, key: String, value: String) {
        self.data.insert(key, value);
    }
    
    /// 获取数据
    pub fn get_data(&self, key: &str) -> Option<&String> {
        self.data.get(key)
    }
}
```

---

**结论**: 工作流理论通过严格的形式化定义和实现，为业务流程的建模、执行和验证提供了理论基础，确保了工作流系统的正确性和可靠性。 