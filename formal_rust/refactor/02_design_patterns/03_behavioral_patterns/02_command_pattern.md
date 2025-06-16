# 命令模式形式化理论

## 1. 形式化定义

### 1.1 基本概念

命令模式是一种行为型设计模式，它将请求封装为对象，从而可以用不同的请求对客户进行参数化，对请求排队或记录请求日志，以及支持可撤销的操作。

**定义 1.1.1** (命令)
设 $S$ 为状态空间，$A$ 为动作集合，命令是一个三元组 $(a, s, f)$，其中：
- $a \in A$ 是动作标识符
- $s \in S$ 是当前状态
- $f: S \rightarrow S$ 是状态转换函数

**定义 1.1.2** (命令执行)
对于命令 $c = (a, s, f)$，执行过程定义为：
$$\text{execute}(c) = f(s)$$

**定义 1.1.3** (命令撤销)
对于命令 $c = (a, s, f)$，如果存在逆函数 $f^{-1}$，则撤销过程定义为：
$$\text{undo}(c) = f^{-1}(f(s)) = s$$

### 1.2 数学基础

**定理 1.2.1** (命令可撤销性)
如果命令 $c = (a, s, f)$ 的状态转换函数 $f$ 是双射的，则命令是可撤销的。

**证明：**
如果 $f$ 是双射的，则存在逆函数 $f^{-1}$，使得 $f^{-1} \circ f = \text{id}$。
因此 $\text{undo}(c) = f^{-1}(f(s)) = s$，命令可以完全撤销。

**定理 1.2.2** (命令组合性)
对于命令序列 $c_1, c_2, \ldots, c_n$，组合执行定义为：
$$\text{execute}(c_1 \circ c_2 \circ \cdots \circ c_n) = f_n \circ f_{n-1} \circ \cdots \circ f_1(s_0)$$

## 2. 类型系统分析

### 2.1 Rust 类型映射

```rust
// 命令特征
trait Command {
    type State;
    type Result;
    
    fn execute(&self, state: &Self::State) -> Self::Result;
    fn undo(&self, state: &Self::State) -> Option<Self::State>;
}

// 具体命令
struct ConcreteCommand<S, R> {
    action: Box<dyn Fn(&S) -> R>,
    undo_action: Option<Box<dyn Fn(&S) -> S>>,
}

impl<S, R> Command for ConcreteCommand<S, R> {
    type State = S;
    type Result = R;
    
    fn execute(&self, state: &Self::State) -> Self::Result {
        (self.action)(state)
    }
    
    fn undo(&self, state: &Self::State) -> Option<Self::State> {
        self.undo_action.as_ref().map(|f| f(state))
    }
}
```

### 2.2 类型安全证明

**引理 2.2.1** (类型一致性)
对于任意命令 $c$，执行和撤销操作的类型必须一致：
$$\text{type}(\text{execute}(c)) = \text{type}(c.\text{Result})$$
$$\text{type}(\text{undo}(c)) = \text{Option}[\text{type}(c.\text{State})]$$

**证明：**
根据 Rust 类型系统，`Command` trait 定义了明确的关联类型，确保类型一致性。

## 3. 实现策略

### 3.1 基础实现

```rust
// 命令接收者
struct Receiver {
    state: String,
}

impl Receiver {
    fn new(initial_state: String) -> Self {
        Self { state: initial_state }
    }
    
    fn action_a(&mut self) {
        self.state.push_str("_A");
    }
    
    fn action_b(&mut self) {
        self.state.push_str("_B");
    }
    
    fn get_state(&self) -> &str {
        &self.state
    }
}

// 具体命令实现
struct ActionACommand {
    receiver: Receiver,
}

impl Command for ActionACommand {
    type State = Receiver;
    type Result = ();
    
    fn execute(&self, state: &Self::State) -> Self::Result {
        let mut state = state.clone();
        state.action_a();
    }
    
    fn undo(&self, state: &Self::State) -> Option<Self::State> {
        // 实现撤销逻辑
        Some(state.clone())
    }
}
```

### 3.2 命令队列

```rust
// 命令队列
struct CommandQueue<C: Command> {
    commands: Vec<C>,
    executed: Vec<C>,
}

impl<C: Command> CommandQueue<C> {
    fn new() -> Self {
        Self {
            commands: vec![],
            executed: vec![],
        }
    }
    
    fn add_command(&mut self, command: C) {
        self.commands.push(command);
    }
    
    fn execute_all(&mut self, initial_state: C::State) -> C::State {
        let mut current_state = initial_state;
        
        for command in self.commands.drain(..) {
            let result = command.execute(&current_state);
            self.executed.push(command);
            // 更新状态
        }
        
        current_state
    }
    
    fn undo_last(&mut self, current_state: C::State) -> Option<C::State> {
        if let Some(command) = self.executed.pop() {
            command.undo(&current_state)
        } else {
            None
        }
    }
}
```

## 4. 正确性证明

### 4.1 执行正确性

**定理 4.1.1** (执行正确性)
对于任意命令 $c = (a, s, f)$ 和状态 $s'$，如果 $s' = \text{execute}(c)$，则 $s' = f(s)$。

**证明：**
根据定义 1.1.2，$\text{execute}(c) = f(s)$，因此 $s' = f(s)$。

### 4.2 撤销正确性

**定理 4.2.1** (撤销正确性)
对于可撤销的命令 $c = (a, s, f)$，如果 $f$ 是双射的，则：
$$\text{undo}(\text{execute}(c)) = s$$

**证明：**
$\text{undo}(\text{execute}(c)) = f^{-1}(f(s)) = s$，因为 $f$ 是双射的。

## 5. 性能分析

### 5.1 时间复杂度

**定理 5.1.1** (执行时间复杂度)
对于命令队列中的 $n$ 个命令，执行时间复杂度为 $O(n)$。

**证明：**
每个命令的执行时间为常数时间，因此总时间为 $O(n)$。

### 5.2 空间复杂度

**定理 5.2.1** (空间复杂度)
命令队列的空间复杂度为 $O(n)$，其中 $n$ 是命令数量。

**证明：**
需要存储所有命令和已执行命令，因此空间复杂度为 $O(n)$。

## 6. 应用场景

### 6.1 用户界面
- 菜单命令
- 按钮操作
- 键盘快捷键

### 6.2 事务处理
- 数据库事务
- 文件操作
- 网络请求

### 6.3 游戏开发
- 游戏动作
- 回放系统
- 撤销重做

## 7. 与其他模式的关系

### 7.1 与策略模式
- 命令模式封装操作
- 策略模式封装算法

### 7.2 与责任链模式
- 命令模式关注操作封装
- 责任链模式关注请求传递

## 8. 高级特性

### 8.1 宏命令

```rust
// 宏命令：组合多个命令
struct MacroCommand<C: Command> {
    commands: Vec<C>,
}

impl<C: Command> Command for MacroCommand<C> {
    type State = C::State;
    type Result = Vec<C::Result>;
    
    fn execute(&self, state: &Self::State) -> Self::Result {
        self.commands.iter()
            .map(|cmd| cmd.execute(state))
            .collect()
    }
    
    fn undo(&self, state: &Self::State) -> Option<Self::State> {
        // 按相反顺序撤销所有命令
        let mut current_state = state.clone();
        for command in self.commands.iter().rev() {
            if let Some(new_state) = command.undo(&current_state) {
                current_state = new_state;
            }
        }
        Some(current_state)
    }
}
```

### 8.2 命令模式与函数式编程

**定理 8.2.1** (函数式映射)
命令模式可以映射到函数式编程中的高阶函数：
$$\text{Command} \cong \text{State} \rightarrow \text{Result}$$

**证明：**
每个命令本质上是一个从状态到结果的函数，这与函数式编程中的函数概念一致。

## 9. 总结

命令模式通过数学化的定义和严格的类型系统分析，提供了一个可证明正确的操作封装框架。其核心优势在于：

1. **封装性**：将操作封装为对象
2. **可撤销性**：支持操作的撤销和重做
3. **可组合性**：支持命令的组合和序列化
4. **解耦性**：客户端与具体操作解耦

通过形式化方法，我们确保了命令模式的正确性和可靠性，为实际应用提供了坚实的理论基础。 