# 工作流状态机形式化定义

> **模式类型**: 工作流编排
> **创建日期**: 2026-03-08
> **版本**: v1.0

---

## 1. 概念定义 (Def)

### Def WF1: 工作流状态机

工作流状态机是一种**业务流程建模机制**，通过状态转换描述业务流程的执行。

```
Workflow := (S, s₀, F, T, A)
  where:
    S = {s₁, s₂, ..., sₙ}     -- 状态集合
    s₀ ∈ S                     -- 初始状态
    F ⊆ S                      -- 终止状态集合
    T ⊆ S × Event × S          -- 状态转换关系
    A: S → Action              -- 状态动作映射
```

### Def WF2: 状态类型

```
StateType :=
  | Start        -- 开始状态
  | Task         -- 任务状态（执行动作）
  | Gateway      -- 网关（分支/合并）
    | Exclusive  -- 排他网关（XOR）
    | Parallel   -- 并行网关（AND）
    | Inclusive  -- 包容网关（OR）
  | Event        -- 事件状态
  | End          -- 结束状态
```

### Def WF3: 工作流实例

```
WorkflowInstance := (workflow_id, instance_id, current_state, context, history)
  where:
    history = [(timestamp, from_state, event, to_state)]
    context: Variables → Values  -- 流程变量上下文
```

---

## 2. 基本假设 (Axiom)

### Axiom WF1: 状态互斥性

```
∀t. instance.current_state 是唯一的
```

任一时刻，实例处于唯一状态。

### Axiom WF2: 终止可达性

```
∀s ∈ S. s →* F  （从任何状态可到达终止状态）
```

工作流设计必须保证终止性。

### Axiom WF3: 转换确定性

```
∀(s, e) ∈ S × Event. |{s' | (s, e, s') ∈ T}| ≤ 1
```

给定状态和事件，下一状态唯一（或不存在）。

---

## 3. 定理 (Theorem)

### Theorem WF1: 工作流活性

```
∀instance. ◇(instance.state ∈ F)
```

**证明概要**:

1. 根据 Axiom WF2，终止状态可达
2. 状态转换是有限的（或良基的）
3. 每次转换都向终止状态推进
4. 因此工作流必然终止

### Theorem WF2: 状态一致性

```
∀instance. history 中的状态转换形成有效路径
```

**证明概要**:

1. 初始状态为 s₀
2. 每次转换 (s, e, s') 必须满足 T
3. 因此历史记录是有效执行路径

---

## 4. Rust 实现示例

```rust
use std::collections::HashMap;
use async_trait::async_trait;

// 工作流定义
pub struct WorkflowDefinition {
    pub id: String,
    pub name: String,
    pub states: Vec<State>,
    pub transitions: Vec<Transition>,
    pub initial_state: String,
}

pub struct State {
    pub id: String,
    pub state_type: StateType,
    pub action: Option<Box<dyn StateAction>>,
}

pub enum StateType {
    Start,
    Task,
    ExclusiveGateway,
    ParallelGateway,
    Event,
    End,
}

pub struct Transition {
    pub id: String,
    pub from_state: String,
    pub to_state: String,
    pub event: String,
    pub condition: Option<Box<dyn TransitionCondition>>,
}

// 状态动作特质
#[async_trait]
pub trait StateAction: Send + Sync {
    async fn execute(&self, context: &mut WorkflowContext) -> Result<ActionResult, ActionError>;
}

// 工作流引擎
pub struct WorkflowEngine {
    definitions: HashMap<String, WorkflowDefinition>,
    instances: HashMap<String, WorkflowInstance>,
    storage: Box<dyn WorkflowStorage>,
}

impl WorkflowEngine {
    pub async fn start_workflow(
        &mut self,
        def_id: &str,
        variables: HashMap<String, Value>,
    ) -> Result<String, WorkflowError> {
        let def = self.definitions.get(def_id)
            .ok_or(WorkflowError::DefinitionNotFound)?;

        let instance_id = uuid::Uuid::new_v4().to_string();
        let instance = WorkflowInstance {
            id: instance_id.clone(),
            definition_id: def_id.to_string(),
            current_state: def.initial_state.clone(),
            variables,
            history: vec![],
            status: WorkflowStatus::Running,
        };

        self.storage.save_instance(&instance).await?;
        self.instances.insert(instance_id.clone(), instance);

        // 触发初始状态的动作
        self.execute_state(&instance_id).await?;

        Ok(instance_id)
    }

    pub async fn send_event(
        &mut self,
        instance_id: &str,
        event: &str,
    ) -> Result<(), WorkflowError> {
        let instance = self.instances.get_mut(instance_id)
            .ok_or(WorkflowError::InstanceNotFound)?;

        let def = self.definitions.get(&instance.definition_id)
            .ok_or(WorkflowError::DefinitionNotFound)?;

        // 查找匹配的转换
        let transition = def.transitions.iter()
            .find(|t| t.from_state == instance.current_state && t.event == event)
            .ok_or(WorkflowError::InvalidTransition)?;

        // 检查条件
        if let Some(condition) = &transition.condition {
            if !condition.evaluate(&instance.variables) {
                return Err(WorkflowError::ConditionNotMet);
            }
        }

        // 执行状态转换
        let from_state = instance.current_state.clone();
        instance.current_state = transition.to_state.clone();
        instance.history.push(TransitionRecord {
            timestamp: chrono::Utc::now(),
            from_state,
            to_state: transition.to_state.clone(),
            event: event.to_string(),
        });

        // 保存并执行新状态的动作
        self.storage.save_instance(instance).await?;
        self.execute_state(instance_id).await?;

        Ok(())
    }

    async fn execute_state(&self, instance_id: &str) -> Result<(), WorkflowError> {
        let instance = self.instances.get(instance_id)
            .ok_or(WorkflowError::InstanceNotFound)?;

        let def = self.definitions.get(&instance.definition_id)
            .ok_or(WorkflowError::DefinitionNotFound)?;

        let state = def.states.iter()
            .find(|s| s.id == instance.current_state)
            .ok_or(WorkflowError::StateNotFound)?;

        // 执行状态动作
        if let Some(action) = &state.action {
            let mut context = WorkflowContext {
                instance_id: instance_id.to_string(),
                variables: instance.variables.clone(),
            };

            match action.execute(&mut context).await {
                Ok(_) => {
                    // 更新变量
                    // ...
                }
                Err(e) => {
                    // 错误处理
                    return Err(WorkflowError::ActionFailed(e));
                }
            }
        }

        // 检查是否为结束状态
        if matches!(state.state_type, StateType::End) {
            let instance = self.instances.get(instance_id).unwrap();
            self.storage.update_status(instance_id, WorkflowStatus::Completed).await?;
        }

        Ok(())
    }
}

pub struct WorkflowInstance {
    pub id: String,
    pub definition_id: String,
    pub current_state: String,
    pub variables: HashMap<String, Value>,
    pub history: Vec<TransitionRecord>,
    pub status: WorkflowStatus,
}

pub struct TransitionRecord {
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub from_state: String,
    pub to_state: String,
    pub event: String,
}

#[derive(Clone)]
pub enum WorkflowStatus {
    Running,
    Completed,
    Suspended,
    Failed,
}
```

---

## 5. 与 Saga 模式的关系

| 特性 | 工作流状态机 | Saga |
|------|-------------|------|
| 关注点 | 流程编排 | 事务一致性 |
| 持久化 | 状态历史 | 事件日志 |
| 补偿 | 可选 | 核心机制 |
| 适用 | 复杂业务流程 | 分布式事务 |

---

**相关阅读**:

- [工作流概念族谱](../../WORKFLOW_CONCEPT_MINDMAP.md)
- [Saga 模式](../05_distributed/01_saga_pattern.md)
