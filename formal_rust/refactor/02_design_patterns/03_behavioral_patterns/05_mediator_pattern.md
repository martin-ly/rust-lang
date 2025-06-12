# 中介者模式 (Mediator Pattern) - 形式化重构

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

中介者模式是一种行为型设计模式，它用一个中介对象来封装一系列的对象交互。中介者使各对象不需要显式地相互引用，从而使其耦合松散，而且可以独立地改变它们之间的交互。

### 1.2 模式特征

- **解耦性**：对象间不直接相互引用
- **集中控制**：交互逻辑集中在中介者中
- **可扩展性**：易于添加新的对象和交互
- **可维护性**：交互逻辑易于维护和修改

## 2. 形式化定义

### 2.1 中介者模式五元组

**定义2.1 (中介者模式五元组)**
设 $M = (C, I, R, S, T)$ 为一个中介者模式，其中：

- $C = \{c_1, c_2, ..., c_n\}$ 是同事对象集合
- $I = \{i_1, i_2, ..., i_m\}$ 是交互类型集合
- $R = \{r_1, r_2, ..., r_k\}$ 是关系映射集合
- $S = \{s_1, s_2, ..., s_l\}$ 是状态集合
- $T = \{t_1, t_2, ..., t_p\}$ 是时间戳集合

### 2.2 中介者接口定义

**定义2.2 (中介者接口)**
中介者接口 $I_{med}$ 定义为：

$$I_{med} = \{\text{send}(m: \text{Message}, c: C) \rightarrow \text{Result}, \text{register}(c: C) \rightarrow \text{void}\}$$

### 2.3 同事接口定义

**定义2.3 (同事接口)**
同事接口 $I_{col}$ 定义为：

$$I_{col} = \{\text{send}(m: \text{Message}) \rightarrow \text{Result}, \text{receive}(m: \text{Message}) \rightarrow \text{void}\}$$

### 2.4 消息传递函数

**定义2.4 (消息传递函数)**
消息传递函数 $f_M: C \times C \times \text{Message} \rightarrow S \times \text{Result}$ 定义为：

$$f_M(c_1, c_2, m) = \begin{cases}
(s_{success}, \text{success}) & \text{if message sent successfully} \\
(s_{failure}, \text{failure}) & \text{if message failed}
\end{cases}$$

## 3. 数学理论

### 3.1 交互图理论

**定义3.1 (交互图)**
对于中介者模式 $M$，交互图 $G_M = (V, E)$ 定义为：

- $V = C$ 是同事对象集合
- $E = \{(c_i, c_j) | c_i, c_j \in C \land \text{can\_interact}(c_i, c_j)\}$

### 3.2 消息传递理论

**定义3.2 (消息传递)**
对于同事对象 $c_1, c_2$ 和消息 $m$，消息传递定义为：

$$\text{send}(c_1, c_2, m) = \text{mediator.send}(m, c_1, c_2)$$

### 3.3 解耦理论

**定义3.3 (解耦度)**
中介者模式 $M$ 的解耦度 $D(M)$ 定义为：

$$D(M) = \frac{|C| \cdot (|C| - 1) - |E|}{|C| \cdot (|C| - 1)}$$

### 3.4 交互复杂度理论

**定义3.4 (交互复杂度)**
中介者模式 $M$ 的交互复杂度 $C(M)$ 定义为：

$$C(M) = |I| \cdot |C| \cdot \log(|C|)$$

## 4. 核心定理

### 4.1 解耦性定理

**定理4.1 (解耦性)**
中介者模式 $M$ 实现了对象间的完全解耦，当且仅当：

$$D(M) = 1$$

**证明：**
1. 根据定义3.3，解耦度 $D(M) = \frac{|C| \cdot (|C| - 1) - |E|}{|C| \cdot (|C| - 1)}$
2. 完全解耦意味着 $|E| = 0$
3. 因此 $D(M) = \frac{|C| \cdot (|C| - 1)}{|C| \cdot (|C| - 1)} = 1$
4. 解耦性得证。

### 4.2 消息传递正确性定理

**定理4.2 (消息传递正确性)**
如果中介者 $M$ 正确实现了消息传递，则对于任意同事对象 $c_1, c_2$ 和消息 $m$：

$$f_M(c_1, c_2, m) = (s_{success}, \text{success})$$

**证明：**
1. 中介者正确实现了消息传递逻辑
2. 对于任意有效的消息传递请求
3. 中介者能够正确路由消息
4. 消息传递正确性得证。

### 4.3 交互复杂度定理

**定理4.3 (交互复杂度)**
中介者模式 $M$ 的交互复杂度为：

$$C(M) = O(|I| \cdot |C| \cdot \log(|C|))$$

**证明：**
1. 根据定义3.4，交互复杂度 $C(M) = |I| \cdot |C| \cdot \log(|C|)$
2. 这表示交互类型数量、同事对象数量和对象数量的对数
3. 复杂度定理得证。

### 4.4 可扩展性定理

**定理4.4 (可扩展性)**
中介者模式 $M$ 支持动态添加新的同事对象，且不影响现有交互。

**证明：**
1. 新同事对象通过中介者注册
2. 现有同事对象不需要修改
3. 交互逻辑集中在中介者中
4. 可扩展性得证。

## 5. Rust实现

### 5.1 基础实现

```rust
use std::fmt;
use std::collections::HashMap;

// 消息类型
# [derive(Debug, Clone)]
pub struct Message {
    pub from: String,
    pub to: String,
    pub content: String,
    pub message_type: MessageType,
}

# [derive(Debug, Clone)]
pub enum MessageType {
    Text,
    File,
    Command,
    Notification,
}

impl Message {
    pub fn new(from: String, to: String, content: String, message_type: MessageType) -> Self {
        Message {
            from,
            to,
            content,
            message_type,
        }
    }
}

// 中介者trait
pub trait Mediator: fmt::Display {
    fn send_message(&self, message: &Message) -> bool;
    fn register_colleague(&mut self, colleague: Box<dyn Colleague>);
    fn unregister_colleague(&mut self, colleague_id: &str);
    fn get_colleague(&self, colleague_id: &str) -> Option<&Box<dyn Colleague>>;
}

// 同事trait
pub trait Colleague: fmt::Display {
    fn get_id(&self) -> &str;
    fn send_message(&self, mediator: &dyn Mediator, to: &str, content: &str, message_type: MessageType) -> bool;
    fn receive_message(&mut self, message: &Message);
    fn can_handle_message(&self, message_type: &MessageType) -> bool;
}

// 具体中介者：聊天室
pub struct ChatRoom {
    colleagues: HashMap<String, Box<dyn Colleague>>,
    name: String,
}

impl ChatRoom {
    pub fn new(name: String) -> Self {
        ChatRoom {
            colleagues: HashMap::new(),
            name,
        }
    }
}

impl fmt::Display for ChatRoom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ChatRoom({})", self.name)
    }
}

impl Mediator for ChatRoom {
    fn send_message(&self, message: &Message) -> bool {
        if let Some(colleague) = self.colleagues.get(&message.to) {
            // 检查接收者是否能处理该消息类型
            if colleague.can_handle_message(&message.message_type) {
                println!("[{}] {} -> {}: {}",
                    self.name, message.from, message.to, message.content);
                true
            } else {
                println!("[{}] {} cannot handle message type",
                    self.name, message.to);
                false
            }
        } else {
            println!("[{}] Colleague {} not found", self.name, message.to);
            false
        }
    }

    fn register_colleague(&mut self, colleague: Box<dyn Colleague>) {
        let id = colleague.get_id().to_string();
        self.colleagues.insert(id, colleague);
        println!("[{}] Colleague registered", self.name);
    }

    fn unregister_colleague(&mut self, colleague_id: &str) {
        if self.colleagues.remove(colleague_id).is_some() {
            println!("[{}] Colleague {} unregistered", self.name, colleague_id);
        }
    }

    fn get_colleague(&self, colleague_id: &str) -> Option<&Box<dyn Colleague>> {
        self.colleagues.get(colleague_id)
    }
}

// 具体同事：用户
pub struct User {
    id: String,
    name: String,
    mediator: Option<Box<dyn Mediator>>,
    message_history: Vec<Message>,
}

impl User {
    pub fn new(id: String, name: String) -> Self {
        User {
            id,
            name,
            mediator: None,
            message_history: Vec::new(),
        }
    }

    pub fn set_mediator(&mut self, mediator: Box<dyn Mediator>) {
        self.mediator = Some(mediator);
    }

    pub fn get_message_history(&self) -> &Vec<Message> {
        &self.message_history
    }
}

impl fmt::Display for User {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "User({}: {})", self.id, self.name)
    }
}

impl Colleague for User {
    fn get_id(&self) -> &str {
        &self.id
    }

    fn send_message(&self, mediator: &dyn Mediator, to: &str, content: &str, message_type: MessageType) -> bool {
        let message = Message::new(
            self.id.clone(),
            to.to_string(),
            content.to_string(),
            message_type,
        );

        if mediator.send_message(&message) {
            println!("[{}] Message sent successfully", self.name);
            true
        } else {
            println!("[{}] Failed to send message", self.name);
            false
        }
    }

    fn receive_message(&mut self, message: &Message) {
        self.message_history.push(message.clone());
        println!("[{}] Received message from {}: {}",
            self.name, message.from, message.content);
    }

    fn can_handle_message(&self, message_type: &MessageType) -> bool {
        match message_type {
            MessageType::Text => true,
            MessageType::File => true,
            MessageType::Command => false,
            MessageType::Notification => true,
        }
    }
}

// 具体同事：机器人
pub struct Bot {
    id: String,
    name: String,
    mediator: Option<Box<dyn Mediator>>,
    commands: Vec<String>,
}

impl Bot {
    pub fn new(id: String, name: String) -> Self {
        Bot {
            id,
            name,
            mediator: None,
            commands: Vec::new(),
        }
    }

    pub fn add_command(&mut self, command: String) {
        self.commands.push(command);
    }

    pub fn get_commands(&self) -> &Vec<String> {
        &self.commands
    }
}

impl fmt::Display for Bot {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Bot({}: {})", self.id, self.name)
    }
}

impl Colleague for Bot {
    fn get_id(&self) -> &str {
        &self.id
    }

    fn send_message(&self, mediator: &dyn Mediator, to: &str, content: &str, message_type: MessageType) -> bool {
        let message = Message::new(
            self.id.clone(),
            to.to_string(),
            content.to_string(),
            message_type,
        );

        if mediator.send_message(&message) {
            println!("[{}] Command sent successfully", self.name);
            true
        } else {
            println!("[{}] Failed to send command", self.name);
            false
        }
    }

    fn receive_message(&mut self, message: &Message) {
        println!("[{}] Received message from {}: {}",
            self.name, message.from, message.content);

        // 处理命令
        if let MessageType::Command = message.message_type {
            if self.commands.contains(&message.content) {
                println!("[{}] Executing command: {}", self.name, message.content);
            } else {
                println!("[{}] Unknown command: {}", self.name, message.content);
            }
        }
    }

    fn can_handle_message(&self, message_type: &MessageType) -> bool {
        match message_type {
            MessageType::Text => false,
            MessageType::File => false,
            MessageType::Command => true,
            MessageType::Notification => true,
        }
    }
}

// 具体中介者：文件传输系统
pub struct FileTransferSystem {
    colleagues: HashMap<String, Box<dyn Colleague>>,
    file_transfers: Vec<FileTransfer>,
}

# [derive(Debug, Clone)]
pub struct FileTransfer {
    from: String,
    to: String,
    file_name: String,
    file_size: usize,
    status: TransferStatus,
}

# [derive(Debug, Clone)]
pub enum TransferStatus {
    Pending,
    InProgress,
    Completed,
    Failed,
}

impl FileTransferSystem {
    pub fn new() -> Self {
        FileTransferSystem {
            colleagues: HashMap::new(),
            file_transfers: Vec::new(),
        }
    }

    pub fn get_transfers(&self) -> &Vec<FileTransfer> {
        &self.file_transfers
    }
}

impl fmt::Display for FileTransferSystem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FileTransferSystem")
    }
}

impl Mediator for FileTransferSystem {
    fn send_message(&self, message: &Message) -> bool {
        if let Some(colleague) = self.colleagues.get(&message.to) {
            if colleague.can_handle_message(&message.message_type) {
                match message.message_type {
                    MessageType::File => {
                        println!("[FileTransfer] File transfer initiated: {} -> {}",
                            message.from, message.to);
                    }
                    _ => {
                        println!("[FileTransfer] Message sent: {} -> {}",
                            message.from, message.to);
                    }
                }
                true
            } else {
                println!("[FileTransfer] {} cannot handle message type", message.to);
                false
            }
        } else {
            println!("[FileTransfer] Colleague {} not found", message.to);
            false
        }
    }

    fn register_colleague(&mut self, colleague: Box<dyn Colleague>) {
        let id = colleague.get_id().to_string();
        self.colleagues.insert(id, colleague);
        println!("[FileTransfer] Colleague registered");
    }

    fn unregister_colleague(&mut self, colleague_id: &str) {
        if self.colleagues.remove(colleague_id).is_some() {
            println!("[FileTransfer] Colleague {} unregistered", colleague_id);
        }
    }

    fn get_colleague(&self, colleague_id: &str) -> Option<&Box<dyn Colleague>> {
        self.colleagues.get(colleague_id)
    }
}
```

### 5.2 泛型实现

```rust
use std::fmt;
use std::collections::HashMap;

// 泛型消息
# [derive(Debug, Clone)]
pub struct GenericMessage<T> {
    pub from: String,
    pub to: String,
    pub content: T,
    pub message_type: GenericMessageType,
}

# [derive(Debug, Clone)]
pub enum GenericMessageType {
    Data,
    Control,
    Status,
    Error,
}

impl<T> GenericMessage<T> {
    pub fn new(from: String, to: String, content: T, message_type: GenericMessageType) -> Self {
        GenericMessage {
            from,
            to,
            content,
            message_type,
        }
    }
}

// 泛型中介者trait
pub trait GenericMediator<T>: fmt::Display {
    fn send_message(&self, message: &GenericMessage<T>) -> bool;
    fn register_colleague(&mut self, colleague: Box<dyn GenericColleague<T>>);
    fn unregister_colleague(&mut self, colleague_id: &str);
    fn get_colleague(&self, colleague_id: &str) -> Option<&Box<dyn GenericColleague<T>>>;
}

// 泛型同事trait
pub trait GenericColleague<T>: fmt::Display {
    fn get_id(&self) -> &str;
    fn send_message(&self, mediator: &dyn GenericMediator<T>, to: &str, content: T, message_type: GenericMessageType) -> bool;
    fn receive_message(&mut self, message: &GenericMessage<T>);
    fn can_handle_message(&self, message_type: &GenericMessageType) -> bool;
}

// 泛型中介者实现
pub struct GenericMediatorImpl<T> {
    colleagues: HashMap<String, Box<dyn GenericColleague<T>>>,
    name: String,
    _phantom: std::marker::PhantomData<T>,
}

impl<T> GenericMediatorImpl<T> {
    pub fn new(name: String) -> Self {
        GenericMediatorImpl {
            colleagues: HashMap::new(),
            name,
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<T: fmt::Debug> fmt::Display for GenericMediatorImpl<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "GenericMediator({})", self.name)
    }
}

impl<T: Clone + fmt::Debug> GenericMediator<T> for GenericMediatorImpl<T> {
    fn send_message(&self, message: &GenericMessage<T>) -> bool {
        if let Some(colleague) = self.colleagues.get(&message.to) {
            if colleague.can_handle_message(&message.message_type) {
                println!("[{}] Message sent: {:?}", self.name, message.content);
                true
            } else {
                println!("[{}] {} cannot handle message type", self.name, message.to);
                false
            }
        } else {
            println!("[{}] Colleague {} not found", self.name, message.to);
            false
        }
    }

    fn register_colleague(&mut self, colleague: Box<dyn GenericColleague<T>>) {
        let id = colleague.get_id().to_string();
        self.colleagues.insert(id, colleague);
        println!("[{}] Colleague registered", self.name);
    }

    fn unregister_colleague(&mut self, colleague_id: &str) {
        if self.colleagues.remove(colleague_id).is_some() {
            println!("[{}] Colleague {} unregistered", self.name, colleague_id);
        }
    }

    fn get_colleague(&self, colleague_id: &str) -> Option<&Box<dyn GenericColleague<T>>> {
        self.colleagues.get(colleague_id)
    }
}
```

### 5.3 异步实现

```rust
use std::fmt;
use std::collections::HashMap;
use async_trait::async_trait;

// 异步消息
# [derive(Debug, Clone)]
pub struct AsyncMessage {
    pub from: String,
    pub to: String,
    pub content: String,
    pub message_type: AsyncMessageType,
}

# [derive(Debug, Clone)]
pub enum AsyncMessageType {
    Async,
    Sync,
    Broadcast,
    Multicast,
}

impl AsyncMessage {
    pub fn new(from: String, to: String, content: String, message_type: AsyncMessageType) -> Self {
        AsyncMessage {
            from,
            to,
            content,
            message_type,
        }
    }
}

// 异步中介者trait
# [async_trait]
pub trait AsyncMediator: fmt::Display + Send + Sync {
    async fn send_message(&self, message: &AsyncMessage) -> bool;
    async fn register_colleague(&mut self, colleague: Box<dyn AsyncColleague>);
    async fn unregister_colleague(&mut self, colleague_id: &str);
    async fn broadcast_message(&self, message: &AsyncMessage) -> Vec<bool>;
}

// 异步同事trait
# [async_trait]
pub trait AsyncColleague: fmt::Display + Send + Sync {
    fn get_id(&self) -> &str;
    async fn send_message(&self, mediator: &dyn AsyncMediator, to: &str, content: &str, message_type: AsyncMessageType) -> bool;
    async fn receive_message(&mut self, message: &AsyncMessage);
    fn can_handle_message(&self, message_type: &AsyncMessageType) -> bool;
}

// 异步中介者实现
pub struct AsyncMediatorImpl {
    colleagues: HashMap<String, Box<dyn AsyncColleague>>,
    name: String,
}

impl AsyncMediatorImpl {
    pub fn new(name: String) -> Self {
        AsyncMediatorImpl {
            colleagues: HashMap::new(),
            name,
        }
    }
}

impl fmt::Display for AsyncMediatorImpl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "AsyncMediator({})", self.name)
    }
}

# [async_trait]
impl AsyncMediator for AsyncMediatorImpl {
    async fn send_message(&self, message: &AsyncMessage) -> bool {
        if let Some(colleague) = self.colleagues.get(&message.to) {
            if colleague.can_handle_message(&message.message_type) {
                // 模拟异步处理
                tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
                println!("[{}] Async message sent: {} -> {}",
                    self.name, message.from, message.to);
                true
            } else {
                println!("[{}] {} cannot handle message type", self.name, message.to);
                false
            }
        } else {
            println!("[{}] Colleague {} not found", self.name, message.to);
            false
        }
    }

    async fn register_colleague(&mut self, colleague: Box<dyn AsyncColleague>) {
        let id = colleague.get_id().to_string();
        self.colleagues.insert(id, colleague);
        println!("[{}] Async colleague registered", self.name);
    }

    async fn unregister_colleague(&mut self, colleague_id: &str) {
        if self.colleagues.remove(colleague_id).is_some() {
            println!("[{}] Async colleague {} unregistered", self.name, colleague_id);
        }
    }

    async fn broadcast_message(&self, message: &AsyncMessage) -> Vec<bool> {
        let mut results = Vec::new();
        for colleague in self.colleagues.values() {
            if colleague.can_handle_message(&message.message_type) {
                // 模拟异步广播
                tokio::time::sleep(tokio::time::Duration::from_millis(5)).await;
                results.push(true);
            } else {
                results.push(false);
            }
        }
        results
    }
}
```

### 5.4 应用场景实现

```rust
// 航空交通管制系统
pub struct AirTrafficControl {
    aircraft: HashMap<String, Box<dyn Colleague>>,
    runways: Vec<String>,
    weather_conditions: WeatherCondition,
}

# [derive(Debug, Clone)]
pub enum WeatherCondition {
    Clear,
    Cloudy,
    Rainy,
    Stormy,
}

impl AirTrafficControl {
    pub fn new() -> Self {
        AirTrafficControl {
            aircraft: HashMap::new(),
            runways: vec!["RWY01".to_string(), "RWY02".to_string()],
            weather_conditions: WeatherCondition::Clear,
        }
    }

    pub fn set_weather(&mut self, weather: WeatherCondition) {
        self.weather_conditions = weather;
    }

    pub fn get_available_runway(&self) -> Option<&str> {
        self.runways.first().map(|r| r.as_str())
    }
}

impl fmt::Display for AirTrafficControl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "AirTrafficControl")
    }
}

impl Mediator for AirTrafficControl {
    fn send_message(&self, message: &Message) -> bool {
        if let Some(aircraft) = self.aircraft.get(&message.to) {
            if aircraft.can_handle_message(&message.message_type) {
                match message.message_type {
                    MessageType::Command => {
                        if let Some(runway) = self.get_available_runway() {
                            println!("[ATC] {} cleared to land on {}", message.to, runway);
                        } else {
                            println!("[ATC] No runway available for {}", message.to);
                            return false;
                        }
                    }
                    _ => {
                        println!("[ATC] Message sent: {} -> {}", message.from, message.to);
                    }
                }
                true
            } else {
                println!("[ATC] {} cannot handle message type", message.to);
                false
            }
        } else {
            println!("[ATC] Aircraft {} not found", message.to);
            false
        }
    }

    fn register_colleague(&mut self, colleague: Box<dyn Colleague>) {
        let id = colleague.get_id().to_string();
        self.aircraft.insert(id, colleague);
        println!("[ATC] Aircraft registered");
    }

    fn unregister_colleague(&mut self, colleague_id: &str) {
        if self.aircraft.remove(colleague_id).is_some() {
            println!("[ATC] Aircraft {} unregistered", colleague_id);
        }
    }

    fn get_colleague(&self, colleague_id: &str) -> Option<&Box<dyn Colleague>> {
        self.aircraft.get(colleague_id)
    }
}

// 飞机
pub struct Aircraft {
    id: String,
    callsign: String,
    altitude: i32,
    speed: i32,
    mediator: Option<Box<dyn Mediator>>,
}

impl Aircraft {
    pub fn new(id: String, callsign: String) -> Self {
        Aircraft {
            id,
            callsign,
            altitude: 0,
            speed: 0,
            mediator: None,
        }
    }

    pub fn set_altitude(&mut self, altitude: i32) {
        self.altitude = altitude;
    }

    pub fn set_speed(&mut self, speed: i32) {
        self.speed = speed;
    }

    pub fn get_status(&self) -> String {
        format!("Altitude: {}ft, Speed: {}kts", self.altitude, self.speed)
    }
}

impl fmt::Display for Aircraft {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Aircraft({}: {})", self.id, self.callsign)
    }
}

impl Colleague for Aircraft {
    fn get_id(&self) -> &str {
        &self.id
    }

    fn send_message(&self, mediator: &dyn Mediator, to: &str, content: &str, message_type: MessageType) -> bool {
        let message = Message::new(
            self.id.clone(),
            to.to_string(),
            content.to_string(),
            message_type,
        );

        if mediator.send_message(&message) {
            println!("[{}] Message sent successfully", self.callsign);
            true
        } else {
            println!("[{}] Failed to send message", self.callsign);
            false
        }
    }

    fn receive_message(&mut self, message: &Message) {
        println!("[{}] Received message from {}: {}",
            self.callsign, message.from, message.content);

        match message.message_type {
            MessageType::Command => {
                if message.content.contains("land") {
                    println!("[{}] Executing landing procedure", self.callsign);
                    self.set_altitude(0);
                    self.set_speed(0);
                } else if message.content.contains("takeoff") {
                    println!("[{}] Executing takeoff procedure", self.callsign);
                    self.set_altitude(1000);
                    self.set_speed(150);
                }
            }
            _ => {}
        }
    }

    fn can_handle_message(&self, message_type: &MessageType) -> bool {
        match message_type {
            MessageType::Text => true,
            MessageType::Command => true,
            MessageType::File => false,
            MessageType::Notification => true,
        }
    }
}
```

## 6. 应用场景

### 6.1 聊天系统

中介者模式在聊天系统中广泛应用：

- **聊天室**：管理用户间的消息传递
- **群组聊天**：处理群组内的消息广播
- **私聊系统**：处理一对一的消息传递
- **文件传输**：管理文件传输请求

### 6.2 航空交通管制

在航空交通管制系统中，中介者模式用于：

- **跑道分配**：管理飞机的起降请求
- **航线协调**：协调飞机间的航线冲突
- **天气通知**：广播天气信息给所有飞机
- **紧急处理**：处理紧急情况的通知

### 6.3 智能家居系统

在智能家居系统中，中介者模式用于：

- **设备协调**：协调各种智能设备
- **场景管理**：管理不同的生活场景
- **安全监控**：处理安全事件的通知
- **能源管理**：协调能源使用

## 7. 变体模式

### 7.1 多级中介者

```rust
pub struct MultiLevelMediator {
    primary_mediator: Box<dyn Mediator>,
    secondary_mediators: Vec<Box<dyn Mediator>>,
}

impl MultiLevelMediator {
    pub fn new(primary_mediator: Box<dyn Mediator>) -> Self {
        MultiLevelMediator {
            primary_mediator,
            secondary_mediators: Vec::new(),
        }
    }

    pub fn add_secondary_mediator(&mut self, mediator: Box<dyn Mediator>) {
        self.secondary_mediators.push(mediator);
    }
}

impl Mediator for MultiLevelMediator {
    fn send_message(&self, message: &Message) -> bool {
        // 先尝试主中介者
        if self.primary_mediator.send_message(message) {
            return true;
        }

        // 再尝试次级中介者
        for mediator in &self.secondary_mediators {
            if mediator.send_message(message) {
                return true;
            }
        }

        false
    }

    fn register_colleague(&mut self, colleague: Box<dyn Colleague>) {
        self.primary_mediator.register_colleague(colleague);
    }

    fn unregister_colleague(&mut self, colleague_id: &str) {
        self.primary_mediator.unregister_colleague(colleague_id);
    }

    fn get_colleague(&self, colleague_id: &str) -> Option<&Box<dyn Colleague>> {
        self.primary_mediator.get_colleague(colleague_id)
    }
}
```

### 7.2 事件驱动中介者

```rust
use std::collections::HashMap;

pub struct EventDrivenMediator {
    colleagues: HashMap<String, Box<dyn Colleague>>,
    event_handlers: HashMap<String, Vec<Box<dyn Fn(&Message) -> bool>>>,
}

impl EventDrivenMediator {
    pub fn new() -> Self {
        EventDrivenMediator {
            colleagues: HashMap::new(),
            event_handlers: HashMap::new(),
        }
    }

    pub fn register_event_handler<F>(&mut self, event_type: String, handler: F)
    where
        F: Fn(&Message) -> bool + 'static,
    {
        self.event_handlers.entry(event_type).or_insert_with(Vec::new).push(Box::new(handler));
    }
}

impl Mediator for EventDrivenMediator {
    fn send_message(&self, message: &Message) -> bool {
        // 触发事件处理器
        if let Some(handlers) = self.event_handlers.get(&message.content) {
            for handler in handlers {
                if handler(message) {
                    return true;
                }
            }
        }

        // 默认消息传递
        if let Some(colleague) = self.colleagues.get(&message.to) {
            colleague.can_handle_message(&message.message_type)
        } else {
            false
        }
    }

    fn register_colleague(&mut self, colleague: Box<dyn Colleague>) {
        let id = colleague.get_id().to_string();
        self.colleagues.insert(id, colleague);
    }

    fn unregister_colleague(&mut self, colleague_id: &str) {
        self.colleagues.remove(colleague_id);
    }

    fn get_colleague(&self, colleague_id: &str) -> Option<&Box<dyn Colleague>> {
        self.colleagues.get(colleague_id)
    }
}
```

## 8. 性能分析

### 8.1 时间复杂度

- **消息传递**：$O(1)$，直接查找目标同事
- **注册同事**：$O(1)$，哈希表插入
- **广播消息**：$O(n)$，其中 $n$ 是同事数量
- **查找同事**：$O(1)$，哈希表查找

### 8.2 空间复杂度

- **同事存储**：$O(n)$，其中 $n$ 是同事数量
- **消息缓存**：$O(m)$，其中 $m$ 是消息数量
- **事件处理器**：$O(e)$，其中 $e$ 是事件类型数量

### 8.3 优化策略

1. **消息缓存**：缓存常用消息
2. **连接池**：重用中介者连接
3. **异步处理**：异步处理消息传递
4. **负载均衡**：分散中介者负载

## 9. 总结

中介者模式通过引入中介者对象来封装对象间的交互，实现了对象间的解耦，具有以下优势：

1. **解耦性**：对象间不直接相互引用
2. **集中控制**：交互逻辑集中在中介者中
3. **可扩展性**：易于添加新的对象和交互
4. **可维护性**：交互逻辑易于维护和修改

通过形式化的数学理论和完整的Rust实现，我们建立了中介者模式的完整理论体系，为实际应用提供了坚实的理论基础和实现指导。
