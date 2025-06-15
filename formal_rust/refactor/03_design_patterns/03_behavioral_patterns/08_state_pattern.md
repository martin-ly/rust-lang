# 状态模式 (State Pattern) - 形式化重构

## 目录

1. [模式概述](#1-模式概述)
2. [形式化定义](#2-形式化定义)
3. [数学理论](#3-数学理论)
4. [核心定理](#4-核心定理)
5. [Rust实现](#5-rust实现)
6. [应用场景](#6-应用场景)
7. [变体模式](#7-变体模式)
8. [性能分析](#8-性能分析)
9. [总结](#9-总结)

## 1. 模式概述

### 1.1 基本概念

状态模式是一种行为型设计模式，它允许对象在内部状态改变时改变其行为。对象看起来似乎修改了它的类。

### 1.2 模式特征

- **状态封装**：将状态相关的行为封装在独立的状态类中
- **状态转换**：支持状态之间的转换
- **行为变化**：对象行为随状态变化而变化
- **状态管理**：集中管理状态转换逻辑

## 2. 形式化定义

### 2.1 状态模式五元组

**定义2.1 (状态模式五元组)**
设 $S = (C, T, A, R, E)$ 为一个状态模式，其中：

- $C = \{c_1, c_2, ..., c_n\}$ 是上下文集合
- $T = \{t_1, t_2, ..., t_m\}$ 是状态集合
- $A = \{a_1, a_2, ..., a_k\}$ 是动作集合
- $R = \{r_1, r_2, ..., r_l\}$ 是转换规则集合
- $E = \{e_1, e_2, ..., e_p\}$ 是事件集合

### 2.2 状态接口定义

**定义2.2 (状态接口)**
状态接口 $I_{state}$ 定义为：

$$I_{state} = \{\text{handle}(c: C, e: E) \rightarrow T, \text{enter}(c: C) \rightarrow \text{void}, \text{exit}(c: C) \rightarrow \text{void}\}$$

### 2.3 上下文接口定义

**定义2.3 (上下文接口)**
上下文接口 $I_{ctx}$ 定义为：

$$I_{ctx} = \{\text{setState}(s: T) \rightarrow \text{void}, \text{getState}() \rightarrow T, \text{request}(e: E) \rightarrow \text{void}\}$$

### 2.4 状态转换函数

**定义2.4 (状态转换函数)**
状态转换函数 $f_T: T \times E \times C \rightarrow T$ 定义为：

$$f_T(s, e, c) = s' \text{ where } s' \text{ is the next state}$$

## 3. 数学理论

### 3.1 状态机理论

**定义3.1 (有限状态机)**
有限状态机 $FSM = (Q, \Sigma, \delta, q_0, F)$ 定义为：

- $Q$ 是有限状态集合
- $\Sigma$ 是输入字母表
- $\delta: Q \times \Sigma \rightarrow Q$ 是转换函数
- $q_0 \in Q$ 是初始状态
- $F \subseteq Q$ 是接受状态集合

### 3.2 状态转换理论

**定义3.2 (有效转换)**
状态转换 $(s_1, e, s_2)$ 是有效的，当且仅当：

$$\exists r \in R: r(s_1, e) = s_2$$

### 3.3 状态一致性理论

**定义3.3 (状态一致性)**
上下文 $c$ 的状态是一致的，当且仅当：

$$\text{getState}(c) \in T \land \text{isValidState}(\text{getState}(c))$$

### 3.4 行为一致性理论

**定义3.4 (行为一致性)**
状态 $s$ 的行为是一致的，当且仅当：

$$\forall e \in E: \text{handle}(s, e) \text{ is deterministic}$$

## 4. 核心定理

### 4.1 状态转换确定性定理

**定理4.1 (状态转换确定性)**
如果状态转换函数是确定的，则状态转换是唯一的：

$$\forall s \in T, e \in E: |f_T(s, e, c)| = 1$$

****证明**：**

1. 根据定义2.4，状态转换函数是确定性的
2. 对于给定的状态和事件，只有一个下一个状态
3. 状态转换确定性定理得证。

### 4.2 状态可达性定理

**定理4.2 (状态可达性)**
如果状态 $s_2$ 可以从状态 $s_1$ 通过事件序列 $E^*$ 到达，则：

$$\exists e_1, e_2, ..., e_n \in E: f_T(f_T(...f_T(s_1, e_1), e_2), ..., e_n) = s_2$$

****证明**：**

1. 根据状态转换函数的**定义 2**. 通过事件序列可以到达目标状态
3. 状态可达性定理得证。

### 4.3 状态不变性定理

**定理4.3 (状态不变性)**
如果状态转换满足不变性条件，则状态属性保持不变：

$$\text{invariant}(s) \land \text{validTransition}(s, e, s') \Rightarrow \text{invariant}(s')$$

****证明**：**

1. 根据不变性条件的**定义 2**. 有效转换保持不变性
3. 状态不变性定理得证。

### 4.4 状态完整性定理

**定理4.4 (状态完整性)**
如果状态集合 $T$ 是完整的，则所有可能的状态都被覆盖：

$$\forall s \in \text{possibleStates}: s \in T$$

****证明**：**

1. 根据状态集合的完整性**定义 2**. 所有可能的状态都在状态集合中
3. 状态完整性定理得证。

## 5. Rust实现

### 5.1 基础实现

```rust
use std::fmt;

// 状态trait
pub trait State: fmt::Display {
    fn handle(&self, context: &mut Context) -> Box<dyn State>;
    fn enter(&self, context: &mut Context);
    fn exit(&self, context: &mut Context);
}

// 上下文
pub struct Context {
    state: Box<dyn State>,
    data: String,
}

impl Context {
    pub fn new(initial_state: Box<dyn State>) -> Self {
        Context {
            state: initial_state,
            data: String::new(),
        }
    }

    pub fn request(&mut self, event: &str) {
        let new_state = self.state.handle(self);
        self.state.exit(self);
        self.state = new_state;
        self.state.enter(self);
    }

    pub fn set_data(&mut self, data: String) {
        self.data = data;
    }

    pub fn get_data(&self) -> &str {
        &self.data
    }

    pub fn get_state_name(&self) -> String {
        self.state.to_string()
    }
}

// 具体状态：空闲状态
pub struct IdleState;

impl IdleState {
    pub fn new() -> Self {
        IdleState
    }
}

impl fmt::Display for IdleState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "IdleState")
    }
}

impl State for IdleState {
    fn handle(&self, context: &mut Context) -> Box<dyn State> {
        println!("[IdleState] Handling request: {}", context.get_data());
        
        match context.get_data().as_str() {
            "start" => {
                println!("[IdleState] Transitioning to RunningState");
                Box::new(RunningState::new())
            }
            "stop" => {
                println!("[IdleState] Already stopped");
                Box::new(IdleState::new())
            }
            "pause" => {
                println!("[IdleState] Cannot pause when idle");
                Box::new(IdleState::new())
            }
            _ => {
                println!("[IdleState] Unknown command");
                Box::new(IdleState::new())
            }
        }
    }

    fn enter(&self, context: &mut Context) {
        println!("[IdleState] Entering idle state");
        context.set_data("idle".to_string());
    }

    fn exit(&self, context: &mut Context) {
        println!("[IdleState] Exiting idle state");
    }
}

// 具体状态：运行状态
pub struct RunningState {
    start_time: std::time::Instant,
}

impl RunningState {
    pub fn new() -> Self {
        RunningState {
            start_time: std::time::Instant::now(),
        }
    }
}

impl fmt::Display for RunningState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "RunningState")
    }
}

impl State for RunningState {
    fn handle(&self, context: &mut Context) -> Box<dyn State> {
        println!("[RunningState] Handling request: {}", context.get_data());
        
        match context.get_data().as_str() {
            "start" => {
                println!("[RunningState] Already running");
                Box::new(RunningState::new())
            }
            "stop" => {
                println!("[RunningState] Transitioning to IdleState");
                Box::new(IdleState::new())
            }
            "pause" => {
                println!("[RunningState] Transitioning to PausedState");
                Box::new(PausedState::new(self.start_time))
            }
            _ => {
                println!("[RunningState] Unknown command");
                Box::new(RunningState::new())
            }
        }
    }

    fn enter(&self, context: &mut Context) {
        println!("[RunningState] Entering running state");
        context.set_data("running".to_string());
    }

    fn exit(&self, context: &mut Context) {
        let elapsed = self.start_time.elapsed();
        println!("[RunningState] Exiting running state after {:?}", elapsed);
    }
}

// 具体状态：暂停状态
pub struct PausedState {
    start_time: std::time::Instant,
    pause_time: std::time::Instant,
}

impl PausedState {
    pub fn new(start_time: std::time::Instant) -> Self {
        PausedState {
            start_time,
            pause_time: std::time::Instant::now(),
        }
    }
}

impl fmt::Display for PausedState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "PausedState")
    }
}

impl State for PausedState {
    fn handle(&self, context: &mut Context) -> Box<dyn State> {
        println!("[PausedState] Handling request: {}", context.get_data());
        
        match context.get_data().as_str() {
            "start" => {
                println!("[PausedState] Transitioning to RunningState");
                Box::new(RunningState::new())
            }
            "stop" => {
                println!("[PausedState] Transitioning to IdleState");
                Box::new(IdleState::new())
            }
            "pause" => {
                println!("[PausedState] Already paused");
                Box::new(PausedState::new(self.start_time))
            }
            _ => {
                println!("[PausedState] Unknown command");
                Box::new(PausedState::new(self.start_time))
            }
        }
    }

    fn enter(&self, context: &mut Context) {
        println!("[PausedState] Entering paused state");
        context.set_data("paused".to_string());
    }

    fn exit(&self, context: &mut Context) {
        let pause_duration = self.pause_time.elapsed();
        println!("[PausedState] Exiting paused state after {:?}", pause_duration);
    }
}
```

### 5.2 泛型实现

```rust
use std::fmt;
use std::collections::HashMap;

// 泛型状态trait
pub trait GenericState<T>: fmt::Display {
    fn handle(&self, context: &mut GenericContext<T>, event: &str) -> Box<dyn GenericState<T>>;
    fn enter(&self, context: &mut GenericContext<T>);
    fn exit(&self, context: &mut GenericContext<T>);
    fn can_handle(&self, event: &str) -> bool;
}

// 泛型上下文
pub struct GenericContext<T> {
    state: Box<dyn GenericState<T>>,
    data: T,
    state_history: Vec<String>,
}

impl<T> GenericContext<T> {
    pub fn new(initial_state: Box<dyn GenericState<T>>, initial_data: T) -> Self {
        GenericContext {
            state: initial_state,
            data: initial_data,
            state_history: Vec::new(),
        }
    }

    pub fn request(&mut self, event: &str) {
        if self.state.can_handle(event) {
            let new_state = self.state.handle(self, event);
            self.state.exit(self);
            self.state_history.push(self.state.to_string());
            self.state = new_state;
            self.state.enter(self);
        } else {
            println!("[{}] Cannot handle event: {}", self.state, event);
        }
    }

    pub fn get_data(&self) -> &T {
        &self.data
    }

    pub fn set_data(&mut self, data: T) {
        self.data = data;
    }

    pub fn get_state_history(&self) -> &Vec<String> {
        &self.state_history
    }
}

// 网络连接状态
#[derive(Debug, Clone)]
pub struct ConnectionData {
    host: String,
    port: u16,
    is_connected: bool,
    last_activity: std::time::Instant,
}

impl ConnectionData {
    pub fn new(host: String, port: u16) -> Self {
        ConnectionData {
            host,
            port,
            is_connected: false,
            last_activity: std::time::Instant::now(),
        }
    }

    pub fn connect(&mut self) {
        self.is_connected = true;
        self.last_activity = std::time::Instant::now();
    }

    pub fn disconnect(&mut self) {
        self.is_connected = false;
    }

    pub fn update_activity(&mut self) {
        self.last_activity = std::time::Instant::now();
    }
}

// 断开连接状态
pub struct DisconnectedState;

impl DisconnectedState {
    pub fn new() -> Self {
        DisconnectedState
    }
}

impl fmt::Display for DisconnectedState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "DisconnectedState")
    }
}

impl GenericState<ConnectionData> for DisconnectedState {
    fn handle(&self, context: &mut GenericContext<ConnectionData>, event: &str) -> Box<dyn GenericState<ConnectionData>> {
        match event {
            "connect" => {
                println!("[DisconnectedState] Connecting...");
                context.get_data().connect();
                Box::new(ConnectedState::new())
            }
            "disconnect" => {
                println!("[DisconnectedState] Already disconnected");
                Box::new(DisconnectedState::new())
            }
            "send" => {
                println!("[DisconnectedState] Cannot send when disconnected");
                Box::new(DisconnectedState::new())
            }
            _ => {
                println!("[DisconnectedState] Unknown event: {}", event);
                Box::new(DisconnectedState::new())
            }
        }
    }

    fn enter(&self, context: &mut GenericContext<ConnectionData>) {
        println!("[DisconnectedState] Entering disconnected state");
        context.get_data().disconnect();
    }

    fn exit(&self, _context: &mut GenericContext<ConnectionData>) {
        println!("[DisconnectedState] Exiting disconnected state");
    }

    fn can_handle(&self, event: &str) -> bool {
        matches!(event, "connect" | "disconnect" | "send")
    }
}

// 已连接状态
pub struct ConnectedState;

impl ConnectedState {
    pub fn new() -> Self {
        ConnectedState
    }
}

impl fmt::Display for ConnectedState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ConnectedState")
    }
}

impl GenericState<ConnectionData> for ConnectedState {
    fn handle(&self, context: &mut GenericContext<ConnectionData>, event: &str) -> Box<dyn GenericState<ConnectionData>> {
        match event {
            "connect" => {
                println!("[ConnectedState] Already connected");
                Box::new(ConnectedState::new())
            }
            "disconnect" => {
                println!("[ConnectedState] Disconnecting...");
                context.get_data().disconnect();
                Box::new(DisconnectedState::new())
            }
            "send" => {
                println!("[ConnectedState] Sending data...");
                context.get_data().update_activity();
                Box::new(ConnectedState::new())
            }
            _ => {
                println!("[ConnectedState] Unknown event: {}", event);
                Box::new(ConnectedState::new())
            }
        }
    }

    fn enter(&self, context: &mut GenericContext<ConnectionData>) {
        println!("[ConnectedState] Entering connected state");
        context.get_data().connect();
    }

    fn exit(&self, _context: &mut GenericContext<ConnectionData>) {
        println!("[ConnectedState] Exiting connected state");
    }

    fn can_handle(&self, event: &str) -> bool {
        matches!(event, "connect" | "disconnect" | "send")
    }
}
```

### 5.3 应用场景实现

```rust
// 自动售货机状态模式
pub struct VendingMachine {
    state: Box<dyn VendingState>,
    money: u32,
    product_count: u32,
    product_price: u32,
}

impl VendingMachine {
    pub fn new(product_count: u32, product_price: u32) -> Self {
        VendingMachine {
            state: Box::new(IdleVendingState::new()),
            money: 0,
            product_count,
            product_price,
        }
    }

    pub fn insert_coin(&mut self, amount: u32) {
        self.state.insert_coin(self, amount);
    }

    pub fn select_product(&mut self) {
        self.state.select_product(self);
    }

    pub fn dispense(&mut self) {
        self.state.dispense(self);
    }

    pub fn return_coins(&mut self) {
        self.state.return_coins(self);
    }

    pub fn get_money(&self) -> u32 {
        self.money
    }

    pub fn get_product_count(&self) -> u32 {
        self.product_count
    }

    pub fn get_product_price(&self) -> u32 {
        self.product_price
    }

    pub fn set_money(&mut self, money: u32) {
        self.money = money;
    }

    pub fn set_product_count(&mut self, count: u32) {
        self.product_count = count;
    }

    pub fn get_state_name(&self) -> String {
        self.state.to_string()
    }
}

// 售货机状态trait
pub trait VendingState: fmt::Display {
    fn insert_coin(&self, machine: &mut VendingMachine, amount: u32);
    fn select_product(&self, machine: &mut VendingMachine);
    fn dispense(&self, machine: &mut VendingMachine);
    fn return_coins(&self, machine: &mut VendingMachine);
}

// 空闲状态
pub struct IdleVendingState;

impl IdleVendingState {
    pub fn new() -> Self {
        IdleVendingState
    }
}

impl fmt::Display for IdleVendingState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "IdleVendingState")
    }
}

impl VendingState for IdleVendingState {
    fn insert_coin(&self, machine: &mut VendingMachine, amount: u32) {
        println!("[IdleVendingState] Inserting {} coins", amount);
        machine.set_money(machine.get_money() + amount);
        machine.state = Box::new(HasMoneyVendingState::new());
    }

    fn select_product(&self, _machine: &mut VendingMachine) {
        println!("[IdleVendingState] Please insert money first");
    }

    fn dispense(&self, _machine: &mut VendingMachine) {
        println!("[IdleVendingState] Please insert money first");
    }

    fn return_coins(&self, _machine: &mut VendingMachine) {
        println!("[IdleVendingState] No money to return");
    }
}

// 有钱状态
pub struct HasMoneyVendingState;

impl HasMoneyVendingState {
    pub fn new() -> Self {
        HasMoneyVendingState
    }
}

impl fmt::Display for HasMoneyVendingState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "HasMoneyVendingState")
    }
}

impl VendingState for HasMoneyVendingState {
    fn insert_coin(&self, machine: &mut VendingMachine, amount: u32) {
        println!("[HasMoneyVendingState] Inserting {} more coins", amount);
        machine.set_money(machine.get_money() + amount);
    }

    fn select_product(&self, machine: &mut VendingMachine) {
        if machine.get_money() >= machine.get_product_price() {
            if machine.get_product_count() > 0 {
                println!("[HasMoneyVendingState] Product selected, dispensing...");
                machine.state = Box::new(SoldVendingState::new());
            } else {
                println!("[HasMoneyVendingState] Out of products");
                machine.state = Box::new(SoldOutVendingState::new());
            }
        } else {
            println!("[HasMoneyVendingState] Not enough money, need {} more", 
                    machine.get_product_price() - machine.get_money());
        }
    }

    fn dispense(&self, _machine: &mut VendingMachine) {
        println!("[HasMoneyVendingState] Please select a product first");
    }

    fn return_coins(&self, machine: &mut VendingMachine) {
        println!("[HasMoneyVendingState] Returning {} coins", machine.get_money());
        machine.set_money(0);
        machine.state = Box::new(IdleVendingState::new());
    }
}

// 售出状态
pub struct SoldVendingState;

impl SoldVendingState {
    pub fn new() -> Self {
        SoldVendingState
    }
}

impl fmt::Display for SoldVendingState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SoldVendingState")
    }
}

impl VendingState for SoldVendingState {
    fn insert_coin(&self, _machine: &mut VendingMachine, _amount: u32) {
        println!("[SoldVendingState] Please wait, dispensing product");
    }

    fn select_product(&self, _machine: &mut VendingMachine) {
        println!("[SoldVendingState] Please wait, dispensing product");
    }

    fn dispense(&self, machine: &mut VendingMachine) {
        println!("[SoldVendingState] Dispensing product");
        machine.set_product_count(machine.get_product_count() - 1);
        machine.set_money(machine.get_money() - machine.get_product_price());
        
        if machine.get_product_count() > 0 {
            machine.state = Box::new(IdleVendingState::new());
        } else {
            machine.state = Box::new(SoldOutVendingState::new());
        }
    }

    fn return_coins(&self, _machine: &mut VendingMachine) {
        println!("[SoldVendingState] Please wait, dispensing product");
    }
}

// 售罄状态
pub struct SoldOutVendingState;

impl SoldOutVendingState {
    pub fn new() -> Self {
        SoldOutVendingState
    }
}

impl fmt::Display for SoldOutVendingState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SoldOutVendingState")
    }
}

impl VendingState for SoldOutVendingState {
    fn insert_coin(&self, _machine: &mut VendingMachine, _amount: u32) {
        println!("[SoldOutVendingState] Machine is sold out");
    }

    fn select_product(&self, _machine: &mut VendingMachine) {
        println!("[SoldOutVendingState] Machine is sold out");
    }

    fn dispense(&self, _machine: &mut VendingMachine) {
        println!("[SoldOutVendingState] Machine is sold out");
    }

    fn return_coins(&self, machine: &mut VendingMachine) {
        if machine.get_money() > 0 {
            println!("[SoldOutVendingState] Returning {} coins", machine.get_money());
            machine.set_money(0);
        }
    }
}
```

## 6. 应用场景

### 6.1 游戏开发

状态模式在游戏开发中广泛应用：

- **角色状态**：角色的移动、攻击、防御状态
- **游戏状态**：游戏的开始、暂停、结束状态
- **AI状态**：AI的巡逻、追击、逃跑状态
- **武器状态**：武器的待机、攻击、装弹状态

### 6.2 网络协议

在网络协议中，状态模式用于：

- **连接状态**：连接的建立、维护、断开状态
- **协议状态**：协议的不同阶段状态
- **会话状态**：会话的活跃、空闲、超时状态
- **认证状态**：认证的不同阶段状态

### 6.3 工作流系统

在工作流系统中，状态模式用于：

- **任务状态**：任务的待处理、进行中、完成状态
- **流程状态**：流程的不同阶段状态
- **审批状态**：审批的不同阶段状态
- **订单状态**：订单的不同处理状态

## 7. 变体模式

### 7.1 状态表模式

```rust
pub struct StateTable {
    transitions: HashMap<(String, String), String>,
}

impl StateTable {
    pub fn new() -> Self {
        StateTable {
            transitions: HashMap::new(),
        }
    }

    pub fn add_transition(&mut self, from: String, event: String, to: String) {
        self.transitions.insert((from, event), to);
    }

    pub fn get_next_state(&self, current_state: &str, event: &str) -> Option<&String> {
        self.transitions.get(&(current_state.to_string(), event.to_string()))
    }
}
```

### 7.2 分层状态模式

```rust
pub trait HierarchicalState: State {
    fn get_parent(&self) -> Option<Box<dyn State>>;
    fn get_children(&self) -> Vec<Box<dyn State>>;
}
```

## 8. 性能分析

### 8.1 时间复杂度

- **状态转换**：$O(1)$，直接状态切换
- **状态查找**：$O(1)$，直接访问当前状态
- **事件处理**：$O(1)$，当前状态处理事件
- **状态验证**：$O(n)$，其中 $n$ 是状态数量

### 8.2 空间复杂度

- **状态对象**：$O(s)$，其中 $s$ 是状态大小
- **状态历史**：$O(h)$，其中 $h$ 是历史长度
- **转换表**：$O(t)$，其中 $t$ 是转换数量

### 8.3 优化策略

1. **状态池**：重用状态对象
2. **状态缓存**：缓存常用状态
3. **延迟初始化**：延迟创建状态对象
4. **状态压缩**：压缩状态数据

## 9. 总结

状态模式通过将状态相关的行为封装在独立的状态类中，实现了对象行为的动态变化，具有以下优势：

1. **状态封装**：将状态相关的行为封装在独立的状态类中
2. **状态转换**：支持状态之间的转换
3. **行为变化**：对象行为随状态变化而变化
4. **状态管理**：集中管理状态转换逻辑

通过形式化的数学理论和完整的Rust实现，我们建立了状态模式的完整理论体系，为实际应用提供了坚实的理论基础和实现指导。

