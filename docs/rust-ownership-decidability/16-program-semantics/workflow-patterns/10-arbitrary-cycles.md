# 10 任意循环模式 (Arbitrary Cycles)

## 模式定义与语义

任意循环模式支持非结构化的循环控制流，允许流程图中存在任意形式的循环结构，而不仅限于嵌套良好的循环。

### 核心语义

与结构化循环（while、for）不同，任意循环允许：

- 多个入口点进入循环
- 多个出口点跳出循环
- 循环交叉（cross loops）

$$
\text{ArbitraryCycle} = \mu X. (P ; X) \oplus Q
$$

其中 $\mu$ 是固定点算子，$\oplus$ 表示非确定性选择。

### 形式化表示

**状态机表示：**

$$
\begin{aligned}
& \text{State} = \{ s_1, s_2, \ldots, s_n \} \\
& \text{Transition} \subseteq \text{State} \times \text{Event} \times \text{State} \\
& \text{其中 } \exists (s_i, e, s_j), (s_k, e', s_l): i > j \land k < l \\
& \text{（存在向后和向前跳转）}
\end{aligned}
$$

**控制流图（CFG）：**

$$
G = (V, E), \quad E = E_{\text{forward}} \cup E_{\text{back}} \\
\text{其中 } E_{\text{back}} = \{ (v, u) \in E \mid \text{depth}(v) \leq \text{depth}(u) \}
$$

## Rust 实现示例

```rust
use std::collections::HashMap;
use std::future::Future;
use std::pin::Pin;

/// 节点标识
type NodeId = usize;

/// 任意循环工作流图
pub struct ArbitraryCycleFlow<T> {
    nodes: HashMap<NodeId, Box<dyn Fn(&T) -> (T, Vec<NodeId>) + Send + Sync>>,
    entry: NodeId,
    exits: Vec<NodeId>,
}

impl<T: Clone + Send + 'static> ArbitraryCycleFlow<T> {
    pub fn new(entry: NodeId) -> Self {
        Self {
            nodes: HashMap::new(),
            entry,
            exits: Vec::new(),
        }
    }

    pub fn add_node(
        &mut self,
        id: NodeId,
        handler: impl Fn(&T) -> (T, Vec<NodeId>) + Send + Sync + 'static,
    ) {
        self.nodes.insert(id, Box::new(handler));
    }

    pub fn add_exit(&mut self, node_id: NodeId) {
        self.exits.push(node_id);
    }

    /// 执行工作流
    pub async fn execute(&self, initial_data: T) -> T {
        let mut current_nodes = vec![(self.entry, initial_data)];
        let mut completed = false;
        let mut final_data = None;

        while !completed {
            let mut next_nodes = Vec::new();

            for (node_id, data) in current_nodes {
                // 检查是否到达出口
                if self.exits.contains(&node_id) {
                    final_data = Some(data);
                    completed = true;
                    continue;
                }

                // 执行节点
                if let Some(handler) = self.nodes.get(&node_id) {
                    let (new_data, next_ids) = handler(&data);
                    for next_id in next_ids {
                        next_nodes.push((next_id, new_data.clone()));
                    }
                }
            }

            current_nodes = next_nodes;

            // 如果没有活跃节点，结束执行
            if current_nodes.is_empty() {
                completed = true;
            }
        }

        final_data.unwrap_or_else(|| initial_data) // 简化处理
    }
}

/// 使用示例：状态机实现任意循环
#[derive(Clone, Debug)]
enum WorkflowState {
    Start,
    Processing,
    Validation,
    Correction,
    Completed,
    Aborted,
}

pub struct StateMachineFlow {
    transitions: HashMap<WorkflowState, Vec<(WorkflowState, Box<dyn Fn(&Context) -> bool + Send + Sync>)>>,
}

pub struct Context {
    retry_count: u32,
    error_count: u32,
    data: String,
}

impl StateMachineFlow {
    pub fn new() -> Self {
        let mut flow = Self {
            transitions: HashMap::new(),
        };

        // 定义非结构化循环
        flow.add_transition(
            WorkflowState::Processing,
            WorkflowState::Validation,
            Box::new(|_| true),
        );

        // 验证失败回到处理（循环）
        flow.add_transition(
            WorkflowState::Validation,
            WorkflowState::Correction,
            Box::new(|ctx| ctx.error_count > 0),
        );

        // 修正后回到处理（另一个入口）
        flow.add_transition(
            WorkflowState::Correction,
            WorkflowState::Processing,
            Box::new(|_| true),
        );

        // 验证成功完成
        flow.add_transition(
            WorkflowState::Validation,
            WorkflowState::Completed,
            Box::new(|ctx| ctx.error_count == 0),
        );

        flow
    }

    fn add_transition(
        &mut self,
        from: WorkflowState,
        to: WorkflowState,
        guard: Box<dyn Fn(&Context) -> bool + Send + Sync>,
    ) {
        self.transitions
            .entry(from)
            .or_default()
            .push((to, guard));
    }

    pub async fn run(&self, mut ctx: Context) -> WorkflowState {
        let mut current = WorkflowState::Start;
        let max_iterations = 100;
        let mut iterations = 0;

        loop {
            if iterations > max_iterations {
                return WorkflowState::Aborted;
            }
            iterations += 1;

            match current {
                WorkflowState::Completed | WorkflowState::Aborted => return current,
                _ => {
                    if let Some(transitions) = self.transitions.get(&current) {
                        for (next_state, guard) in transitions {
                            if guard(&ctx) {
                                current = next_state.clone();
                                break;
                            }
                        }
                    }
                }
            }

            // 模拟异步处理
            tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
        }
    }
}

/// 标签跳转式实现（类似 goto）
pub struct LabeledFlow<T> {
    labels: HashMap<String, usize>,
    instructions: Vec<Instruction<T>>,
}

pub enum Instruction<T> {
    Execute(Box<dyn Fn(&mut T)>),
    Jump(String),
    JumpIf(String, Box<dyn Fn(&T) -> bool>),
    Halt,
}
```

## 与其他模式的关系

| 模式 | 结构 | 表达能力 |
|------|------|----------|
| while 循环 | 结构化 | 受限 |
| **任意循环** | 非结构化 | 完整 |
| 递归 | 结构化 | 栈限制 |
| 状态机 | 结构化 | 等价 |

**关系公式：**

$$
\text{StructuredLoops} \subset \text{ArbitraryCycles} \cong \text{StateMachines}
$$

## 应用场景

1. **复杂业务规则**：需要多入口多出口的业务流程
2. **工作流引擎**：支持 BPMN 中任意循环的实现
3. **解释器/虚拟机**：字节码执行需要任意跳转
4. **流程重构**：遗留系统的非结构化流程

### 注意事项

- 非结构化代码难以理解和维护
- 更容易引入死循环
- 建议使用状态机等价转换以提高可读性
- 验证终止性更加困难
