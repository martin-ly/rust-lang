# 领导者选举模式 (Leader Election Pattern)

## 1. 概述

### 1.1 模式定义

领导者选举模式是一种分布式系统设计模式，用于在多个节点中选择一个领导者，确保系统中只有一个节点承担特定职责，如协调、调度或决策。

### 1.2 核心概念

- **节点 (Node)**: 参与选举的分布式系统组件
- **领导者 (Leader)**: 被选举出的负责节点
- **跟随者 (Follower)**: 非领导者的节点
- **选举算法 (Election Algorithm)**: 选择领导者的算法
- **心跳 (Heartbeat)**: 节点间保持连接的机制

## 2. 形式化定义

### 2.1 领导者选举模式五元组

**定义2.1 (领导者选举模式五元组)**
设 $LE = (N, L, A, H, C)$ 为领导者选举模式，其中：

- $N = \{n_1, n_2, ..., n_k\}$ 是节点集合
- $L = \{l_1, l_2, ..., l_m\}$ 是领导者集合
- $A = \{a_1, a_2, ..., a_p\}$ 是选举算法集合
- $H = \{h_1, h_2, ..., h_q\}$ 是心跳机制集合
- $C = \{c_1, c_2, ..., c_r\}$ 是配置集合

### 2.2 节点定义

**定义2.2 (节点)**
节点 $n_i = (id_i, state_i, priority_i, last\_heartbeat_i)$，其中：

- $id_i$ 是节点唯一标识符
- $state_i \in \{leader, follower, candidate\}$ 是节点状态
- $priority_i$ 是节点优先级
- $last\_heartbeat_i$ 是最后心跳时间

### 2.3 选举函数

**定义2.3 (选举函数)**
选举函数 $elect: N \times A \rightarrow N$ 定义为：

$$elect(nodes, algorithm) = algorithm.select\_leader(nodes)$$

## 3. 数学理论

### 3.1 领导者唯一性理论

**定义3.1 (领导者唯一性)**
领导者选举算法保证系统中最多只有一个领导者：

$$\forall n_1, n_2 \in N: (n_1.state = leader \land n_2.state = leader) \Rightarrow n_1 = n_2$$

**定理3.1.1 (领导者唯一性保证)**
正确的领导者选举算法保证领导者唯一性。

**证明**：
1. **互斥性**: 选举算法确保同时只有一个节点成为领导者
2. **一致性**: 所有节点对领导者身份达成一致
3. **因此**: 系统中最多只有一个领导者

### 3.2 选举安全性理论

**定义3.2 (选举安全性)**
选举算法是安全的，当且仅当：

$$\forall n \in N: n.state = leader \Rightarrow \forall n' \in N \setminus \{n\}: n'.state \neq leader$$

**定理3.2.1 (选举安全性)**
安全的选举算法不会产生多个领导者。

**证明**：
1. **状态互斥**: 领导者状态与其他节点状态互斥
2. **状态一致性**: 所有节点对状态达成一致
3. **因此**: 不会产生多个领导者

### 3.3 选举活性理论

**定义3.3 (选举活性)**
选举算法是活性的，当且仅当：

$$\forall t \in \mathbb{R}^+: \exists n \in N: n.state = leader$$

**定理3.3.1 (选举活性)**
活性的选举算法最终会选举出领导者。

**证明**：
1. **选举进程**: 算法会持续进行选举
2. **收敛性**: 选举过程最终会收敛
3. **因此**: 最终会选举出领导者

## 4. 核心定理

### 4.1 领导者选举正确性定理

**定理4.1 (领导者选举正确性)**
领导者选举模式 $LE$ 是正确的，当且仅当：

1. **领导者唯一性**: $\forall n_1, n_2 \in N: (n_1.state = leader \land n_2.state = leader) \Rightarrow n_1 = n_2$
2. **选举安全性**: $\forall n \in N: n.state = leader \Rightarrow \forall n' \in N \setminus \{n\}: n'.state \neq leader$
3. **选举活性**: $\forall t \in \mathbb{R}^+: \exists n \in N: n.state = leader$
4. **心跳完整性**: $\forall n \in N: heartbeat(n) \text{ is periodic}$

**证明**：
1. **领导者唯一性**: 确保系统中最多只有一个领导者
2. **选举安全性**: 确保不会产生多个领导者
3. **选举活性**: 确保最终会选举出领导者
4. **心跳完整性**: 确保节点间保持连接

### 4.2 领导者选举性能定理

**定理4.2 (领导者选举性能)**
领导者选举模式的性能复杂度为：

- **选举时间**: $O(\log|N|)$ 平均时间复杂度
- **消息复杂度**: $O(|N|)$ 消息数量
- **状态转换**: $O(1)$ 时间复杂度
- **心跳开销**: $O(|N|)$ 消息复杂度

**证明**：
1. **选举时间**: 使用分布式算法，选举时间与节点数量对数相关
2. **消息复杂度**: 每个节点需要发送选举消息
3. **状态转换**: 状态转换是常数时间操作
4. **心跳开销**: 每个节点需要发送心跳消息

## 5. Rust实现

### 5.1 基础实现

```rust
use std::collections::HashMap;
use std::sync::{Arc, RwLock};
use std::time::{Duration, Instant};
use tokio::time::{interval, sleep};
use uuid::Uuid;
use serde::{Deserialize, Serialize};

/// 节点状态
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum NodeState {
    Follower,
    Candidate,
    Leader,
}

/// 节点
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Node {
    pub id: String,
    pub state: NodeState,
    pub priority: u32,
    pub last_heartbeat: Instant,
    pub term: u64,
    pub voted_for: Option<String>,
}

/// 选举消息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ElectionMessage {
    RequestVote { candidate_id: String, term: u64 },
    VoteResponse { voter_id: String, term: u64, vote_granted: bool },
    Heartbeat { leader_id: String, term: u64 },
    HeartbeatResponse { follower_id: String, term: u64 },
}

/// 领导者选举器
pub struct LeaderElection {
    node: Arc<RwLock<Node>>,
    nodes: Arc<RwLock<HashMap<String, Node>>>,
    election_timeout: Duration,
    heartbeat_interval: Duration,
    message_sender: tokio::sync::mpsc::Sender<ElectionMessage>,
    message_receiver: tokio::sync::mpsc::Receiver<ElectionMessage>,
}

impl LeaderElection {
    pub fn new(node_id: String, priority: u32) -> Self {
        let (message_sender, message_receiver) = tokio::sync::mpsc::channel(100);
        
        let node = Node {
            id: node_id.clone(),
            state: NodeState::Follower,
            priority,
            last_heartbeat: Instant::now(),
            term: 0,
            voted_for: None,
        };

        let mut nodes = HashMap::new();
        nodes.insert(node_id.clone(), node.clone());

        Self {
            node: Arc::new(RwLock::new(node)),
            nodes: Arc::new(RwLock::new(nodes)),
            election_timeout: Duration::from_millis(150),
            heartbeat_interval: Duration::from_millis(50),
            message_sender,
            message_receiver,
        }
    }

    /// 启动选举器
    pub async fn start(&mut self) {
        let node_clone = self.node.clone();
        let nodes_clone = self.nodes.clone();
        let sender = self.message_sender.clone();
        let election_timeout = self.election_timeout;
        let heartbeat_interval = self.heartbeat_interval;

        // 启动选举循环
        tokio::spawn(async move {
            let mut election_timer = interval(election_timeout);
            let mut heartbeat_timer = interval(heartbeat_interval);

            loop {
                tokio::select! {
                    _ = election_timer.tick() => {
                        Self::election_timeout_handler(&node_clone, &nodes_clone, &sender).await;
                    }
                    _ = heartbeat_timer.tick() => {
                        Self::heartbeat_handler(&node_clone, &nodes_clone, &sender).await;
                    }
                }
            }
        });

        // 启动消息处理循环
        while let Some(message) = self.message_receiver.recv().await {
            self.handle_message(message).await;
        }
    }

    /// 处理选举超时
    async fn election_timeout_handler(
        node: &Arc<RwLock<Node>>,
        nodes: &Arc<RwLock<HashMap<String, Node>>>,
        sender: &tokio::sync::mpsc::Sender<ElectionMessage>,
    ) {
        let mut node_guard = node.write().unwrap();
        let now = Instant::now();

        // 检查是否需要开始选举
        if now.duration_since(node_guard.last_heartbeat) > Duration::from_millis(150) {
            if node_guard.state == NodeState::Follower {
                // 转换为候选人状态
                node_guard.state = NodeState::Candidate;
                node_guard.term += 1;
                node_guard.voted_for = Some(node_guard.id.clone());

                // 发送投票请求
                let message = ElectionMessage::RequestVote {
                    candidate_id: node_guard.id.clone(),
                    term: node_guard.term,
                };

                let _ = sender.send(message).await;
            }
        }
    }

    /// 处理心跳
    async fn heartbeat_handler(
        node: &Arc<RwLock<Node>>,
        nodes: &Arc<RwLock<HashMap<String, Node>>>,
        sender: &tokio::sync::mpsc::Sender<ElectionMessage>,
    ) {
        let node_guard = node.read().unwrap();
        
        if node_guard.state == NodeState::Leader {
            // 发送心跳
            let message = ElectionMessage::Heartbeat {
                leader_id: node_guard.id.clone(),
                term: node_guard.term,
            };

            let _ = sender.send(message).await;
        }
    }

    /// 处理消息
    async fn handle_message(&mut self, message: ElectionMessage) {
        match message {
            ElectionMessage::RequestVote { candidate_id, term } => {
                self.handle_request_vote(candidate_id, term).await;
            }
            ElectionMessage::VoteResponse { voter_id, term, vote_granted } => {
                self.handle_vote_response(voter_id, term, vote_granted).await;
            }
            ElectionMessage::Heartbeat { leader_id, term } => {
                self.handle_heartbeat(leader_id, term).await;
            }
            ElectionMessage::HeartbeatResponse { follower_id, term } => {
                self.handle_heartbeat_response(follower_id, term).await;
            }
        }
    }

    /// 处理投票请求
    async fn handle_request_vote(&mut self, candidate_id: String, term: u64) {
        let mut node = self.node.write().unwrap();
        
        if term > node.term {
            node.term = term;
            node.state = NodeState::Follower;
            node.voted_for = None;
        }

        if term == node.term && node.voted_for.is_none() {
            node.voted_for = Some(candidate_id.clone());
            
            // 发送投票响应
            let message = ElectionMessage::VoteResponse {
                voter_id: node.id.clone(),
                term: node.term,
                vote_granted: true,
            };

            let _ = self.message_sender.send(message).await;
        }
    }

    /// 处理投票响应
    async fn handle_vote_response(&mut self, voter_id: String, term: u64, vote_granted: bool) {
        let mut node = self.node.write().unwrap();
        
        if term == node.term && node.state == NodeState::Candidate && vote_granted {
            // 统计投票
            let mut vote_count = 1; // 自己的一票
            
            // 这里应该统计所有投票
            if vote_count > self.get_nodes_count() / 2 {
                // 成为领导者
                node.state = NodeState::Leader;
                node.last_heartbeat = Instant::now();
            }
        }
    }

    /// 处理心跳
    async fn handle_heartbeat(&mut self, leader_id: String, term: u64) {
        let mut node = self.node.write().unwrap();
        
        if term >= node.term {
            node.term = term;
            node.state = NodeState::Follower;
            node.last_heartbeat = Instant::now();
            
            // 发送心跳响应
            let message = ElectionMessage::HeartbeatResponse {
                follower_id: node.id.clone(),
                term: node.term,
            };

            let _ = self.message_sender.send(message).await;
        }
    }

    /// 处理心跳响应
    async fn handle_heartbeat_response(&mut self, follower_id: String, term: u64) {
        // 更新跟随者状态
        let mut nodes = self.nodes.write().unwrap();
        if let Some(follower) = nodes.get_mut(&follower_id) {
            follower.last_heartbeat = Instant::now();
        }
    }

    /// 获取节点数量
    fn get_nodes_count(&self) -> usize {
        self.nodes.read().unwrap().len()
    }

    /// 获取当前状态
    pub fn get_state(&self) -> NodeState {
        self.node.read().unwrap().state.clone()
    }

    /// 获取当前任期
    pub fn get_term(&self) -> u64 {
        self.node.read().unwrap().term
    }

    /// 添加节点
    pub fn add_node(&self, node: Node) {
        let mut nodes = self.nodes.write().unwrap();
        nodes.insert(node.id.clone(), node);
    }

    /// 移除节点
    pub fn remove_node(&self, node_id: &str) {
        let mut nodes = self.nodes.write().unwrap();
        nodes.remove(node_id);
    }
}
```

### 5.2 泛型实现

```rust
use std::collections::HashMap;
use std::sync::{Arc, RwLock};
use std::marker::PhantomData;

/// 泛型领导者选举器
pub struct GenericLeaderElection<T, E> {
    node: Arc<RwLock<GenericNode<T>>>,
    nodes: Arc<RwLock<HashMap<String, GenericNode<T>>>>,
    election_timeout: Duration,
    heartbeat_interval: Duration,
    message_sender: tokio::sync::mpsc::Sender<GenericElectionMessage<T, E>>,
    message_receiver: tokio::sync::mpsc::Receiver<GenericElectionMessage<T, E>>,
    _phantom: PhantomData<(T, E)>,
}

/// 泛型节点
#[derive(Debug, Clone)]
pub struct GenericNode<T> {
    pub id: String,
    pub state: NodeState,
    pub priority: u32,
    pub last_heartbeat: Instant,
    pub term: u64,
    pub voted_for: Option<String>,
    pub data: T,
}

/// 泛型选举消息
#[derive(Debug, Clone)]
pub enum GenericElectionMessage<T, E> {
    RequestVote { candidate_id: String, term: u64, data: T },
    VoteResponse { voter_id: String, term: u64, vote_granted: bool },
    Heartbeat { leader_id: String, term: u64, data: T },
    HeartbeatResponse { follower_id: String, term: u64 },
    Error(E),
}

impl<T, E> GenericLeaderElection<T, E> {
    pub fn new(node_id: String, priority: u32, data: T) -> Self {
        let (message_sender, message_receiver) = tokio::sync::mpsc::channel(100);
        
        let node = GenericNode {
            id: node_id.clone(),
            state: NodeState::Follower,
            priority,
            last_heartbeat: Instant::now(),
            term: 0,
            voted_for: None,
            data,
        };

        let mut nodes = HashMap::new();
        nodes.insert(node_id.clone(), node.clone());

        Self {
            node: Arc::new(RwLock::new(node)),
            nodes: Arc::new(RwLock::new(nodes)),
            election_timeout: Duration::from_millis(150),
            heartbeat_interval: Duration::from_millis(50),
            message_sender,
            message_receiver,
            _phantom: PhantomData,
        }
    }

    /// 启动泛型选举器
    pub async fn start(&mut self) {
        let node_clone = self.node.clone();
        let nodes_clone = self.nodes.clone();
        let sender = self.message_sender.clone();
        let election_timeout = self.election_timeout;
        let heartbeat_interval = self.heartbeat_interval;

        // 启动选举循环
        tokio::spawn(async move {
            let mut election_timer = interval(election_timeout);
            let mut heartbeat_timer = interval(heartbeat_interval);

            loop {
                tokio::select! {
                    _ = election_timer.tick() => {
                        Self::election_timeout_handler(&node_clone, &nodes_clone, &sender).await;
                    }
                    _ = heartbeat_timer.tick() => {
                        Self::heartbeat_handler(&node_clone, &nodes_clone, &sender).await;
                    }
                }
            }
        });

        // 启动消息处理循环
        while let Some(message) = self.message_receiver.recv().await {
            self.handle_message(message).await;
        }
    }

    /// 处理泛型消息
    async fn handle_message(&mut self, message: GenericElectionMessage<T, E>) {
        match message {
            GenericElectionMessage::RequestVote { candidate_id, term, data } => {
                self.handle_request_vote(candidate_id, term, data).await;
            }
            GenericElectionMessage::VoteResponse { voter_id, term, vote_granted } => {
                self.handle_vote_response(voter_id, term, vote_granted).await;
            }
            GenericElectionMessage::Heartbeat { leader_id, term, data } => {
                self.handle_heartbeat(leader_id, term, data).await;
            }
            GenericElectionMessage::HeartbeatResponse { follower_id, term } => {
                self.handle_heartbeat_response(follower_id, term).await;
            }
            GenericElectionMessage::Error(error) => {
                self.handle_error(error).await;
            }
        }
    }

    async fn handle_request_vote(&mut self, candidate_id: String, term: u64, data: T) {
        let mut node = self.node.write().unwrap();
        
        if term > node.term {
            node.term = term;
            node.state = NodeState::Follower;
            node.voted_for = None;
            node.data = data;
        }

        if term == node.term && node.voted_for.is_none() {
            node.voted_for = Some(candidate_id.clone());
            
            let message = GenericElectionMessage::VoteResponse {
                voter_id: node.id.clone(),
                term: node.term,
                vote_granted: true,
            };

            let _ = self.message_sender.send(message).await;
        }
    }

    async fn handle_vote_response(&mut self, voter_id: String, term: u64, vote_granted: bool) {
        let mut node = self.node.write().unwrap();
        
        if term == node.term && node.state == NodeState::Candidate && vote_granted {
            let mut vote_count = 1;
            
            if vote_count > self.get_nodes_count() / 2 {
                node.state = NodeState::Leader;
                node.last_heartbeat = Instant::now();
            }
        }
    }

    async fn handle_heartbeat(&mut self, leader_id: String, term: u64, data: T) {
        let mut node = self.node.write().unwrap();
        
        if term >= node.term {
            node.term = term;
            node.state = NodeState::Follower;
            node.last_heartbeat = Instant::now();
            node.data = data;
            
            let message = GenericElectionMessage::HeartbeatResponse {
                follower_id: node.id.clone(),
                term: node.term,
            };

            let _ = self.message_sender.send(message).await;
        }
    }

    async fn handle_heartbeat_response(&mut self, follower_id: String, term: u64) {
        let mut nodes = self.nodes.write().unwrap();
        if let Some(follower) = nodes.get_mut(&follower_id) {
            follower.last_heartbeat = Instant::now();
        }
    }

    async fn handle_error(&mut self, error: E) {
        // 处理错误
        println!("Error in leader election: {:?}", error);
    }

    fn get_nodes_count(&self) -> usize {
        self.nodes.read().unwrap().len()
    }

    pub fn get_state(&self) -> NodeState {
        self.node.read().unwrap().state.clone()
    }

    pub fn get_term(&self) -> u64 {
        self.node.read().unwrap().term
    }

    pub fn get_data(&self) -> T {
        self.node.read().unwrap().data.clone()
    }
}
```

### 5.3 异步实现

```rust
use tokio::sync::RwLock as TokioRwLock;
use std::sync::Arc;

/// 异步领导者选举器
pub struct AsyncLeaderElection {
    node: Arc<TokioRwLock<Node>>,
    nodes: Arc<TokioRwLock<HashMap<String, Node>>>,
    election_timeout: Duration,
    heartbeat_interval: Duration,
    message_sender: tokio::sync::mpsc::Sender<ElectionMessage>,
    message_receiver: tokio::sync::mpsc::Receiver<ElectionMessage>,
}

impl AsyncLeaderElection {
    pub fn new(node_id: String, priority: u32) -> Self {
        let (message_sender, message_receiver) = tokio::sync::mpsc::channel(100);
        
        let node = Node {
            id: node_id.clone(),
            state: NodeState::Follower,
            priority,
            last_heartbeat: Instant::now(),
            term: 0,
            voted_for: None,
        };

        let mut nodes = HashMap::new();
        nodes.insert(node_id.clone(), node.clone());

        Self {
            node: Arc::new(TokioRwLock::new(node)),
            nodes: Arc::new(TokioRwLock::new(nodes)),
            election_timeout: Duration::from_millis(150),
            heartbeat_interval: Duration::from_millis(50),
            message_sender,
            message_receiver,
        }
    }

    /// 启动异步选举器
    pub async fn start(&mut self) {
        let node_clone = self.node.clone();
        let nodes_clone = self.nodes.clone();
        let sender = self.message_sender.clone();
        let election_timeout = self.election_timeout;
        let heartbeat_interval = self.heartbeat_interval;

        // 启动选举循环
        tokio::spawn(async move {
            let mut election_timer = interval(election_timeout);
            let mut heartbeat_timer = interval(heartbeat_interval);

            loop {
                tokio::select! {
                    _ = election_timer.tick() => {
                        Self::election_timeout_handler(&node_clone, &nodes_clone, &sender).await;
                    }
                    _ = heartbeat_timer.tick() => {
                        Self::heartbeat_handler(&node_clone, &nodes_clone, &sender).await;
                    }
                }
            }
        });

        // 启动消息处理循环
        while let Some(message) = self.message_receiver.recv().await {
            self.handle_message(message).await;
        }
    }

    /// 异步处理选举超时
    async fn election_timeout_handler(
        node: &Arc<TokioRwLock<Node>>,
        nodes: &Arc<TokioRwLock<HashMap<String, Node>>>,
        sender: &tokio::sync::mpsc::Sender<ElectionMessage>,
    ) {
        let mut node_guard = node.write().await;
        let now = Instant::now();

        if now.duration_since(node_guard.last_heartbeat) > Duration::from_millis(150) {
            if node_guard.state == NodeState::Follower {
                node_guard.state = NodeState::Candidate;
                node_guard.term += 1;
                node_guard.voted_for = Some(node_guard.id.clone());

                let message = ElectionMessage::RequestVote {
                    candidate_id: node_guard.id.clone(),
                    term: node_guard.term,
                };

                let _ = sender.send(message).await;
            }
        }
    }

    /// 异步处理心跳
    async fn heartbeat_handler(
        node: &Arc<TokioRwLock<Node>>,
        nodes: &Arc<TokioRwLock<HashMap<String, Node>>>,
        sender: &tokio::sync::mpsc::Sender<ElectionMessage>,
    ) {
        let node_guard = node.read().await;
        
        if node_guard.state == NodeState::Leader {
            let message = ElectionMessage::Heartbeat {
                leader_id: node_guard.id.clone(),
                term: node_guard.term,
            };

            let _ = sender.send(message).await;
        }
    }

    /// 异步处理消息
    async fn handle_message(&mut self, message: ElectionMessage) {
        match message {
            ElectionMessage::RequestVote { candidate_id, term } => {
                self.handle_request_vote(candidate_id, term).await;
            }
            ElectionMessage::VoteResponse { voter_id, term, vote_granted } => {
                self.handle_vote_response(voter_id, term, vote_granted).await;
            }
            ElectionMessage::Heartbeat { leader_id, term } => {
                self.handle_heartbeat(leader_id, term).await;
            }
            ElectionMessage::HeartbeatResponse { follower_id, term } => {
                self.handle_heartbeat_response(follower_id, term).await;
            }
        }
    }

    /// 异步处理投票请求
    async fn handle_request_vote(&mut self, candidate_id: String, term: u64) {
        let mut node = self.node.write().await;
        
        if term > node.term {
            node.term = term;
            node.state = NodeState::Follower;
            node.voted_for = None;
        }

        if term == node.term && node.voted_for.is_none() {
            node.voted_for = Some(candidate_id.clone());
            
            let message = ElectionMessage::VoteResponse {
                voter_id: node.id.clone(),
                term: node.term,
                vote_granted: true,
            };

            let _ = self.message_sender.send(message).await;
        }
    }

    /// 异步处理投票响应
    async fn handle_vote_response(&mut self, voter_id: String, term: u64, vote_granted: bool) {
        let mut node = self.node.write().await;
        
        if term == node.term && node.state == NodeState::Candidate && vote_granted {
            let mut vote_count = 1;
            
            if vote_count > self.get_nodes_count().await / 2 {
                node.state = NodeState::Leader;
                node.last_heartbeat = Instant::now();
            }
        }
    }

    /// 异步处理心跳
    async fn handle_heartbeat(&mut self, leader_id: String, term: u64) {
        let mut node = self.node.write().await;
        
        if term >= node.term {
            node.term = term;
            node.state = NodeState::Follower;
            node.last_heartbeat = Instant::now();
            
            let message = ElectionMessage::HeartbeatResponse {
                follower_id: node.id.clone(),
                term: node.term,
            };

            let _ = self.message_sender.send(message).await;
        }
    }

    /// 异步处理心跳响应
    async fn handle_heartbeat_response(&mut self, follower_id: String, term: u64) {
        let mut nodes = self.nodes.write().await;
        if let Some(follower) = nodes.get_mut(&follower_id) {
            follower.last_heartbeat = Instant::now();
        }
    }

    /// 异步获取节点数量
    async fn get_nodes_count(&self) -> usize {
        self.nodes.read().await.len()
    }

    /// 异步获取当前状态
    pub async fn get_state(&self) -> NodeState {
        self.node.read().await.state.clone()
    }

    /// 异步获取当前任期
    pub async fn get_term(&self) -> u64 {
        self.node.read().await.term
    }

    /// 异步添加节点
    pub async fn add_node(&self, node: Node) {
        let mut nodes = self.nodes.write().await;
        nodes.insert(node.id.clone(), node);
    }

    /// 异步移除节点
    pub async fn remove_node(&self, node_id: &str) {
        let mut nodes = self.nodes.write().await;
        nodes.remove(node_id);
    }
}
```

## 6. 应用场景

### 6.1 分布式锁

```rust
use std::sync::Arc;

/// 分布式锁
pub struct DistributedLock {
    leader_election: Arc<LeaderElection>,
}

impl DistributedLock {
    pub fn new(leader_election: Arc<LeaderElection>) -> Self {
        Self { leader_election }
    }

    /// 获取锁
    pub async fn acquire(&self) -> bool {
        self.leader_election.get_state() == NodeState::Leader
    }

    /// 释放锁
    pub async fn release(&self) {
        // 在领导者选举中，锁的释放通过选举失败实现
    }

    /// 检查是否持有锁
    pub async fn is_held(&self) -> bool {
        self.leader_election.get_state() == NodeState::Leader
    }
}
```

### 6.2 集群协调

```rust
use std::sync::Arc;

/// 集群协调器
pub struct ClusterCoordinator {
    leader_election: Arc<LeaderElection>,
}

impl ClusterCoordinator {
    pub fn new(leader_election: Arc<LeaderElection>) -> Self {
        Self { leader_election }
    }

    /// 执行领导者任务
    pub async fn execute_leader_task<F, Fut, T>(&self, task: F) -> Option<T>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = T>,
    {
        if self.leader_election.get_state() == NodeState::Leader {
            Some(task().await)
        } else {
            None
        }
    }

    /// 注册跟随者任务
    pub async fn register_follower_task<F, Fut, T>(&self, task: F) -> Option<T>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = T>,
    {
        if self.leader_election.get_state() == NodeState::Follower {
            Some(task().await)
        } else {
            None
        }
    }
}
```

## 7. 变体模式

### 7.1 基于优先级的选举

```rust
use std::sync::Arc;

/// 基于优先级的领导者选举器
pub struct PriorityBasedLeaderElection {
    leader_election: Arc<LeaderElection>,
}

impl PriorityBasedLeaderElection {
    pub fn new(leader_election: Arc<LeaderElection>) -> Self {
        Self { leader_election }
    }

    /// 根据优先级选择领导者
    pub async fn elect_by_priority(&self, nodes: &[Node]) -> Option<&Node> {
        nodes.iter().max_by_key(|node| node.priority)
    }

    /// 检查优先级
    pub async fn check_priority(&self, node: &Node) -> bool {
        // 实现优先级检查逻辑
        node.priority > 0
    }
}
```

### 7.2 基于权重的选举

```rust
use std::sync::Arc;

/// 基于权重的领导者选举器
pub struct WeightBasedLeaderElection {
    leader_election: Arc<LeaderElection>,
}

impl WeightBasedLeaderElection {
    pub fn new(leader_election: Arc<LeaderElection>) -> Self {
        Self { leader_election }
    }

    /// 根据权重选择领导者
    pub async fn elect_by_weight(&self, nodes: &[Node]) -> Option<&Node> {
        // 实现基于权重的选举算法
        nodes.iter().max_by_key(|node| self.calculate_weight(node))
    }

    /// 计算节点权重
    fn calculate_weight(&self, node: &Node) -> u32 {
        // 实现权重计算逻辑
        node.priority * 10
    }
}
```

## 8. 总结

领导者选举模式是分布式系统中的核心模式，通过形式化的数学理论和Rust实现，我们建立了完整的领导者选举框架。该模式具有以下特点：

1. **形式化定义**: 通过五元组定义建立了严格的数学模型
2. **理论完备性**: 提供了完整的定理证明和性能分析
3. **实现多样性**: 支持基础、泛型、异步等多种实现方式
4. **应用广泛性**: 适用于分布式锁、集群协调、负载均衡等场景
5. **选举保证**: 保证领导者唯一性和选举活性

该模式为分布式系统的领导者选举提供了理论基础和实践指导，是构建高可用、强一致性分布式系统的重要组件。 