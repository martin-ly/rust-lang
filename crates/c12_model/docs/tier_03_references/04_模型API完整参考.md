# 模型API完整参考

> **文档版本**: v1.0.0  
> **最后更新**: 2025-10-23  
> **难度等级**: ⭐⭐⭐☆☆  
> **预计阅读**: 40分钟

## 目录

- [模型API完整参考](#模型api完整参考)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [API 组织结构](#api-组织结构)
  - [2. 形式化建模API](#2-形式化建模api)
    - [2.1 Expression 类型](#21-expression-类型)
    - [2.2 SmallStepSemantics](#22-smallstepsemantics)
    - [2.3 BigStepSemantics](#23-bigstepsemantics)
    - [2.4 Environment](#24-environment)
    - [2.5 AxiomaticSemantics](#25-axiomaticsemantics)
  - [3. 分布式系统API](#3-分布式系统api)
    - [3.1 RaftProtocol](#31-raftprotocol)
    - [3.2 PaxosProtocol](#32-paxosprotocol)
    - [3.3 VectorClock](#33-vectorclock)
  - [4. 并发模型API](#4-并发模型api)
    - [4.1 CSPModel](#41-cspmodel)
    - [4.2 ActorSystem](#42-actorsystem)
    - [4.3 WorkStealingScheduler](#43-workstealingscheduler)
  - [5. 软件设计API](#5-软件设计api)
    - [5.1 LayeredArchitecture](#51-layeredarchitecture)
    - [5.2 EventDrivenArchitecture](#52-eventdrivenarchitecture)
    - [5.3 DataflowGraph](#53-dataflowgraph)
  - [6. 算法模型API](#6-算法模型api)
    - [6.1 DijkstraAlgorithm](#61-dijkstraalgorithm)
    - [6.2 KMPAlgorithm](#62-kmpalgorithm)
    - [6.3 GCDAlgorithm](#63-gcdalgorithm)
  - [7. 排队论API](#7-排队论api)
    - [7.1 MM1Model](#71-mm1model)
    - [7.2 MMcModel](#72-mmcmodel)
  - [8. 机器学习API](#8-机器学习api)
    - [8.1 LinearRegression](#81-linearregression)
  - [9. 数学建模API](#9-数学建模api)
    - [9.1 LinearProgramming](#91-linearprogramming)
  - [10. 错误处理](#10-错误处理)
    - [ModelError 类型](#modelerror-类型)
  - [11. 配置选项](#11-配置选项)
    - [ModelConfig](#modelconfig)
  - [12. 总结](#12-总结)

---

## 1. 概述

本文档提供 c12_model 所有公共 API 的完整参考，包括类型定义、函数签名、使用示例和注意事项。

### API 组织结构

```text
c12_model::
  ├── formal::              // 形式化建模
  │   ├── Expression
  │   ├── SmallStepSemantics
  │   ├── BigStepSemantics
  │   ├── DenotationalSemantics
  │   └── AxiomaticSemantics
  ├── distributed::         // 分布式系统
  │   ├── RaftProtocol
  │   ├── PaxosProtocol
  │   ├── TwoPhaseCommit
  │   ├── ThreePhaseCommit
  │   ├── DistributedSnapshot
  │   └── VectorClock
  ├── concurrent::          // 并发模型
  │   ├── CSPModel
  │   ├── ActorSystem
  │   ├── SharedMemoryModel
  │   └── WorkStealingScheduler
  ├── design::              // 软件设计
  │   ├── LayeredArchitecture
  │   ├── MicroservicesArchitecture
  │   ├── EventDrivenArchitecture
  │   ├── DataflowGraph
  │   └── ReactiveStream
  ├── algorithm::           // 算法模型
  │   ├── DijkstraAlgorithm
  │   ├── FloydWarshall
  │   ├── KMPAlgorithm
  │   ├── RabinKarp
  │   ├── GCDAlgorithm
  │   └── FastPower
  ├── queueing::            // 排队论
  │   ├── MM1Model
  │   ├── MMcModel
  │   └── MG1Model
  ├── ml::                  // 机器学习
  │   ├── LinearRegression
  │   ├── LogisticRegression
  │   └── DecisionTree
  └── math::                // 数学建模
      ├── LinearProgramming
      ├── NormalDistribution
      └── Optimizer
```

---

## 2. 形式化建模API

### 2.1 Expression 类型

表达式抽象语法树。

```rust
pub enum Expression<'a> {
    Var(&'a str),
    Num(i32),
    Bool(bool),
    Add(Box<Expression<'a>>, Box<Expression<'a>>),
    Sub(Box<Expression<'a>>, Box<Expression<'a>>),
    Mul(Box<Expression<'a>>, Box<Expression<'a>>),
    Div(Box<Expression<'a>>, Box<Expression<'a>>),
    Eq(Box<Expression<'a>>, Box<Expression<'a>>),
    Lt(Box<Expression<'a>>, Box<Expression<'a>>),
    And(Box<Expression<'a>>, Box<Expression<'a>>),
    Or(Box<Expression<'a>>, Box<Expression<'a>>),
    Not(Box<Expression<'a>>),
}
```

**示例**:

```rust
use c12_model::formal::Expression;

// 创建表达式: (2 + 3) * 4
let expr = Expression::Mul(
    Box::new(Expression::Add(
        Box::new(Expression::Num(2)),
        Box::new(Expression::Num(3)),
    )),
    Box::new(Expression::Num(4)),
);
```

### 2.2 SmallStepSemantics

小步操作语义求值器。

```rust
pub struct SmallStepSemantics {
    // 内部状态
}

impl SmallStepSemantics {
    /// 创建新的小步语义求值器
    pub fn new() -> Self { ... }
    
    /// 执行单步转换
    ///
    /// # Arguments
    /// * `expr` - 待转换的表达式
    ///
    /// # Returns
    /// * `Ok(Expression)` - 转换后的表达式
    /// * `Err(String)` - 转换错误
    pub fn step(&mut self, expr: Expression) -> Result<Expression, String> { ... }
    
    /// 检查表达式是否为值
    pub fn is_value(&self, expr: &Expression) -> bool { ... }
    
    /// 执行多步转换直到得到值
    pub fn eval(&mut self, expr: Expression) -> Result<Expression, String> { ... }
}
```

**示例**:

```rust
use c12_model::formal::{SmallStepSemantics, Expression};

let mut semantics = SmallStepSemantics::new();
let expr = Expression::Add(
    Box::new(Expression::Num(2)),
    Box::new(Expression::Num(3)),
);

let result = semantics.eval(expr)?;
assert_eq!(result, Expression::Num(5));
```

### 2.3 BigStepSemantics

大步操作语义求值器。

```rust
pub struct BigStepSemantics { ... }

impl BigStepSemantics {
    /// 创建新的大步语义求值器
    pub fn new() -> Self { ... }
    
    /// 直接求值表达式
    ///
    /// # Arguments
    /// * `expr` - 待求值的表达式
    ///
    /// # Returns
    /// * `Ok(Expression)` - 求值结果
    /// * `Err(String)` - 求值错误
    pub fn eval(&self, expr: &Expression) -> Result<Expression, String> { ... }
}
```

### 2.4 Environment

符号表（环境）。

```rust
pub struct Environment<'a> {
    bindings: std::collections::HashMap<&'a str, i32>,
}

impl<'a> Environment<'a> {
    /// 创建空环境
    pub fn new() -> Self { ... }
    
    /// 绑定变量到值
    ///
    /// # Arguments
    /// * `name` - 变量名
    /// * `value` - 变量值
    pub fn bind(&mut self, name: &'a str, value: i32) { ... }
    
    /// 查找变量的值
    ///
    /// # Arguments
    /// * `name` - 变量名
    ///
    /// # Returns
    /// * `Some(i32)` - 变量值
    /// * `None` - 变量未定义
    pub fn lookup(&self, name: &'a str) -> Option<i32> { ... }
}
```

### 2.5 AxiomaticSemantics

公理语义（Hoare逻辑）。

```rust
pub struct AxiomaticSemantics { ... }

#[derive(Debug, Clone)]
pub struct HoareTriple {
    pub precondition: Assertion,
    pub command: String,
    pub postcondition: Assertion,
}

#[derive(Debug, Clone)]
pub enum Assertion {
    True,
    False,
    Equal(String, i32),
    Greater(String, i32),
    Less(String, i32),
    And(Box<Assertion>, Box<Assertion>),
    Or(Box<Assertion>, Box<Assertion>),
    Not(Box<Assertion>),
}

impl AxiomaticSemantics {
    /// 创建新的公理语义验证器
    pub fn new() -> Self { ... }
    
    /// 验证 Hoare 三元组
    ///
    /// # Arguments
    /// * `triple` - Hoare 三元组 {P} C {Q}
    ///
    /// # Returns
    /// * `Ok(bool)` - 三元组是否有效
    /// * `Err(String)` - 验证错误
    pub fn verify_triple(&self, triple: &HoareTriple) -> Result<bool, String> { ... }
    
    /// 计算最弱前置条件
    ///
    /// # Arguments
    /// * `command` - 命令
    /// * `postcondition` - 后置条件
    ///
    /// # Returns
    /// * `Ok(Assertion)` - 最弱前置条件
    /// * `Err(String)` - 计算错误
    pub fn weakest_precondition(
        &self,
        command: &str,
        postcondition: &Assertion
    ) -> Result<Assertion, String> { ... }
}
```

---

## 3. 分布式系统API

### 3.1 RaftProtocol

Raft 共识协议实现。

```rust
pub struct RaftProtocol {
    // 内部状态
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RaftRole {
    Follower,
    Candidate,
    Leader,
}

impl RaftProtocol {
    /// 创建新的 Raft 节点
    ///
    /// # Arguments
    /// * `node_id` - 节点ID
    /// * `election_timeout` - 选举超时时间
    /// * `heartbeat_interval` - 心跳间隔
    pub fn new(
        node_id: String,
        election_timeout: Duration,
        heartbeat_interval: Duration,
    ) -> Self { ... }
    
    /// 添加对等节点
    ///
    /// # Arguments
    /// * `peer_id` - 对等节点ID
    pub fn add_peer(&mut self, peer_id: String) -> Result<(), String> { ... }
    
    /// 开始选举
    pub fn start_election(&mut self) -> Result<(), String> { ... }
    
    /// 处理投票请求
    ///
    /// # Arguments
    /// * `candidate_id` - 候选者ID
    /// * `term` - 任期
    ///
    /// # Returns
    /// * `Ok(bool)` - 是否投票
    pub fn handle_vote_request(
        &mut self,
        candidate_id: &str,
        term: u64
    ) -> Result<bool, String> { ... }
    
    /// 追加日志条目
    ///
    /// # Arguments
    /// * `entry` - 日志条目
    pub fn append_entry(&mut self, entry: String) -> Result<(), String> { ... }
    
    /// 获取当前角色
    pub fn get_role(&self) -> RaftRole { ... }
    
    /// 获取当前任期
    pub fn current_term(&self) -> u64 { ... }
    
    /// 获取已提交索引
    pub fn committed_index(&self) -> usize { ... }
}
```

**示例**:

```rust
use c12_model::distributed::RaftProtocol;
use std::time::Duration;

// 创建 Raft 节点
let mut raft = RaftProtocol::new(
    "node1".to_string(),
    Duration::from_millis(150),
    Duration::from_millis(50),
);

// 添加对等节点
raft.add_peer("node2".to_string())?;
raft.add_peer("node3".to_string())?;

// 开始选举
raft.start_election()?;

// 追加日志
raft.append_entry("SET x = 10".to_string())?;
```

### 3.2 PaxosProtocol

Paxos 协议实现。

```rust
pub struct PaxosProtocol { ... }

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PaxosPhase {
    Prepare,
    Promise,
    Accept,
    Accepted,
    Learn,
}

impl PaxosProtocol {
    /// 创建新的 Paxos 提议者
    pub fn new(proposer_id: String) -> Self { ... }
    
    /// 添加接受者
    pub fn add_acceptor(&mut self, acceptor_id: String) -> Result<(), String> { ... }
    
    /// 提议值
    pub fn propose(&mut self, value: String) -> Result<u64, String> { ... }
    
    /// 处理 Prepare 请求
    pub fn handle_prepare(&mut self, proposal_num: u64) -> Result<(), String> { ... }
    
    /// 处理 Accept 请求
    pub fn handle_accept(
        &mut self,
        proposal_num: u64,
        value: String
    ) -> Result<(), String> { ... }
    
    /// 获取已接受的值
    pub fn get_accepted_value(&self) -> Result<Option<String>, String> { ... }
}
```

### 3.3 VectorClock

向量时钟实现。

```rust
pub struct VectorClock {
    node_id: String,
    clocks: std::collections::HashMap<String, u64>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CausalRelation {
    HappensBefore,
    HappensAfter,
    Concurrent,
}

impl VectorClock {
    /// 创建新的向量时钟
    pub fn new(node_id: String) -> Self { ... }
    
    /// 递增本地时钟
    pub fn increment(&mut self) { ... }
    
    /// 合并其他向量时钟
    pub fn merge(&mut self, other: &VectorClock) { ... }
    
    /// 比较因果关系
    pub fn compare(&self, other: &VectorClock) -> CausalRelation { ... }
    
    /// 获取特定节点的时钟值
    pub fn get_clock(&self, node_id: &str) -> u64 { ... }
}
```

---

## 4. 并发模型API

### 4.1 CSPModel

CSP (Communicating Sequential Processes) 模型。

```rust
pub struct CSPModel { ... }

impl CSPModel {
    /// 创建新的 CSP 模型
    pub fn new() -> Self { ... }
    
    /// 添加进程
    pub fn add_process(&mut self, process_id: String) -> Result<(), String> { ... }
    
    /// 创建通道
    pub fn create_channel(&mut self, channel_id: String) -> Result<(), String> { ... }
    
    /// 发送消息
    ///
    /// # Arguments
    /// * `from` - 发送方进程ID
    /// * `channel` - 通道ID
    /// * `message` - 消息内容
    pub fn send(
        &mut self,
        from: &str,
        channel: &str,
        message: &str
    ) -> Result<(), String> { ... }
    
    /// 接收消息
    ///
    /// # Arguments
    /// * `to` - 接收方进程ID
    /// * `channel` - 通道ID
    ///
    /// # Returns
    /// * `Ok(String)` - 接收到的消息
    pub fn receive(&mut self, to: &str, channel: &str) -> Result<String, String> { ... }
}
```

### 4.2 ActorSystem

Actor 模型系统。

```rust
pub struct ActorSystem { ... }
pub struct ActorRef { ... }

impl ActorSystem {
    /// 创建新的 Actor 系统
    pub fn new(name: String) -> Self { ... }
    
    /// 生成新的 Actor
    pub fn spawn_actor(&mut self, actor_id: String) -> Result<ActorRef, String> { ... }
    
    /// 发送消息
    ///
    /// # Arguments
    /// * `from` - 发送方 Actor 引用
    /// * `to` - 接收方 Actor 引用
    /// * `message` - 消息内容
    pub fn send_message(
        &self,
        from: &ActorRef,
        to: &ActorRef,
        message: String
    ) -> Result<(), String> { ... }
    
    /// 广播消息
    pub fn broadcast(&self, from: &str, message: String) -> Result<(), String> { ... }
    
    /// 获取 Actor 数量
    pub fn actor_count(&self) -> usize { ... }
}
```

### 4.3 WorkStealingScheduler

Work-Stealing 调度器。

```rust
pub struct WorkStealingScheduler { ... }

impl WorkStealingScheduler {
    /// 创建新的调度器
    ///
    /// # Arguments
    /// * `num_workers` - 工作线程数量
    pub fn new(num_workers: usize) -> Self { ... }
    
    /// 启动调度器
    ///
    /// # Returns
    /// * 工作线程句柄数组
    pub fn start(&mut self) -> Result<Vec<std::thread::JoinHandle<()>>, String> { ... }
    
    /// 提交任务
    ///
    /// # Arguments
    /// * `task` - 任务闭包
    pub fn submit<F>(&mut self, task: F) -> Result<(), String>
    where
        F: FnOnce() + Send + 'static,
    { ... }
    
    /// 停止调度器
    pub fn shutdown(&mut self) { ... }
    
    /// 获取工作线程数量
    pub fn worker_count(&self) -> usize { ... }
}
```

---

## 5. 软件设计API

### 5.1 LayeredArchitecture

分层架构模型。

```rust
pub struct LayeredArchitecture { ... }

impl LayeredArchitecture {
    /// 创建新的分层架构
    pub fn new() -> Self { ... }
    
    /// 添加层
    pub fn add_layer(&mut self, layer_name: String) -> Result<(), String> { ... }
    
    /// 处理请求（自顶向下）
    pub fn handle_request(&self, request: &str) -> Result<String, String> { ... }
    
    /// 获取层数
    pub fn layer_count(&self) -> usize { ... }
}
```

### 5.2 EventDrivenArchitecture

事件驱动架构。

```rust
pub struct EventDrivenArchitecture { ... }

#[derive(Debug, Clone)]
pub struct Event {
    pub event_type: String,
    pub payload: String,
}

pub type EventHandler = Box<dyn Fn(&Event) -> Result<(), String> + Send + Sync>;

impl EventDrivenArchitecture {
    /// 创建新的事件驱动架构
    pub fn new() -> Self { ... }
    
    /// 注册事件处理器
    ///
    /// # Arguments
    /// * `event_type` - 事件类型
    /// * `handler` - 事件处理器
    pub fn register_handler(
        &mut self,
        event_type: &str,
        handler: EventHandler
    ) -> Result<(), String> { ... }
    
    /// 发布事件
    ///
    /// # Arguments
    /// * `event` - 事件
    pub fn publish_event(&self, event: Event) -> Result<(), String> { ... }
}
```

### 5.3 DataflowGraph

数据流图。

```rust
pub struct DataflowGraph { ... }

pub trait DataflowNode: Send {
    type Input;
    type Output;
    
    fn process(&mut self, input: Self::Input) -> Result<Self::Output, String>;
    fn name(&self) -> &str;
}

impl DataflowGraph {
    /// 创建新的数据流图
    pub fn new() -> Self { ... }
    
    /// 添加节点
    ///
    /// # Arguments
    /// * `node` - 数据流节点
    ///
    /// # Returns
    /// * 节点ID
    pub fn add_node(&mut self, node: Box<dyn DataflowNode<Input = i32, Output = i32>>) -> usize { ... }
    
    /// 添加边
    ///
    /// # Arguments
    /// * `from` - 源节点ID
    /// * `to` - 目标节点ID
    pub fn add_edge(&mut self, from: usize, to: usize) -> Result<(), String> { ... }
    
    /// 执行数据流
    ///
    /// # Arguments
    /// * `input` - 初始输入
    ///
    /// # Returns
    /// * 所有叶节点的输出
    pub fn execute(&mut self, input: i32) -> Result<Vec<i32>, String> { ... }
}
```

---

## 6. 算法模型API

### 6.1 DijkstraAlgorithm

Dijkstra 最短路径算法。

```rust
pub struct DijkstraAlgorithm { ... }

impl DijkstraAlgorithm {
    /// 创建新的 Dijkstra 算法实例
    pub fn new() -> Self { ... }
    
    /// 计算从源节点到所有其他节点的最短路径
    ///
    /// # Arguments
    /// * `vertices` - 所有顶点
    /// * `edges` - 所有边 (from, to, weight)
    /// * `source` - 源节点
    ///
    /// # Returns
    /// * `Ok(HashMap)` - 从源节点到各节点的最短距离
    pub fn shortest_path<'a>(
        &self,
        vertices: &[&'a str],
        edges: &[(&'a str, &'a str, f64)],
        source: &'a str
    ) -> Result<std::collections::HashMap<&'a str, f64>, String> { ... }
}
```

### 6.2 KMPAlgorithm

KMP 字符串匹配算法。

```rust
pub struct KMPAlgorithm { ... }

impl KMPAlgorithm {
    /// 创建新的 KMP 算法实例
    pub fn new() -> Self { ... }
    
    /// 在文本中搜索模式串
    ///
    /// # Arguments
    /// * `text` - 文本字符串
    /// * `pattern` - 模式串
    ///
    /// # Returns
    /// * `Ok(Vec<usize>)` - 模式串在文本中的所有起始位置
    pub fn search(&self, text: &str, pattern: &str) -> Result<Vec<usize>, String> { ... }
    
    /// 构建 KMP 失败函数
    pub fn build_failure_function(&self, pattern: &str) -> Vec<usize> { ... }
}
```

### 6.3 GCDAlgorithm

最大公约数算法。

```rust
pub struct GCDAlgorithm;

impl GCDAlgorithm {
    /// 欧几里得算法计算 GCD
    ///
    /// # Arguments
    /// * `a` - 第一个整数
    /// * `b` - 第二个整数
    ///
    /// # Returns
    /// * 最大公约数
    pub fn euclidean(a: i64, b: i64) -> i64 { ... }
    
    /// 扩展欧几里得算法
    ///
    /// # Returns
    /// * `(gcd, x, y)` 满足 `a*x + b*y = gcd`
    pub fn extended_euclidean(a: i64, b: i64) -> (i64, i64, i64) { ... }
}
```

---

## 7. 排队论API

### 7.1 MM1Model

M/M/1 排队模型。

```rust
pub struct MM1Model {
    arrival_rate: f64,      // λ
    service_rate: f64,      // μ
}

#[derive(Debug, Clone)]
pub struct QueueingMetrics {
    pub utilization: f64,           // ρ = λ/μ
    pub avg_queue_length: f64,      // L
    pub avg_waiting_time: f64,      // W
    pub avg_system_time: f64,       // Ws
    pub avg_customers_in_system: f64, // Ls
}

impl MM1Model {
    /// 创建新的 M/M/1 模型
    ///
    /// # Arguments
    /// * `arrival_rate` - 到达率 λ
    /// * `service_rate` - 服务率 μ
    ///
    /// # Panics
    /// * 如果 λ >= μ (系统不稳定)
    pub fn new(arrival_rate: f64, service_rate: f64) -> Self { ... }
    
    /// 计算性能指标
    pub fn calculate_metrics(&self) -> Result<QueueingMetrics, String> { ... }
}
```

**示例**:

```rust
use c12_model::queueing::MM1Model;

let model = MM1Model::new(
    0.5,  // λ = 0.5 req/s
    1.0,  // μ = 1.0 req/s
);

let metrics = model.calculate_metrics()?;
println!("平均等待时间: {:.2}s", metrics.avg_waiting_time);
println!("系统利用率: {:.2}%", metrics.utilization * 100.0);
```

### 7.2 MMcModel

M/M/c 排队模型。

```rust
pub struct MMcModel {
    arrival_rate: f64,
    service_rate: f64,
    servers: usize,         // c
}

impl MMcModel {
    /// 创建新的 M/M/c 模型
    ///
    /// # Arguments
    /// * `arrival_rate` - 到达率 λ
    /// * `service_rate` - 每个服务器的服务率 μ
    /// * `servers` - 服务器数量 c
    pub fn new(arrival_rate: f64, service_rate: f64, servers: usize) -> Self { ... }
    
    /// 计算性能指标
    pub fn calculate_metrics(&self) -> Result<QueueingMetrics, String> { ... }
}
```

---

## 8. 机器学习API

### 8.1 LinearRegression

线性回归模型。

```rust
pub struct LinearRegression {
    weights: Option<Vec<f64>>,
    bias: Option<f64>,
}

impl LinearRegression {
    /// 创建新的线性回归模型
    pub fn new() -> Self { ... }
    
    /// 训练模型
    ///
    /// # Arguments
    /// * `x_train` - 训练特征 (n_samples × n_features)
    /// * `y_train` - 训练标签 (n_samples)
    pub fn fit(
        &mut self,
        x_train: &[Vec<f64>],
        y_train: &[f64]
    ) -> Result<(), String> { ... }
    
    /// 预测
    ///
    /// # Arguments
    /// * `x_test` - 测试特征
    ///
    /// # Returns
    /// * 预测结果
    pub fn predict(&self, x_test: &[Vec<f64>]) -> Result<Vec<f64>, String> { ... }
    
    /// 计算 R² 分数
    pub fn score(&self, x_test: &[Vec<f64>], y_test: &[f64]) -> Result<f64, String> { ... }
}
```

**示例**:

```rust
use c12_model::ml::LinearRegression;

let mut model = LinearRegression::new();

let x_train = vec![
    vec![1.0, 2.0],
    vec![2.0, 3.0],
    vec![3.0, 4.0],
];
let y_train = vec![3.0, 5.0, 7.0];

model.fit(&x_train, &y_train)?;

let x_test = vec![vec![4.0, 5.0]];
let predictions = model.predict(&x_test)?;
println!("预测: {:?}", predictions);
```

---

## 9. 数学建模API

### 9.1 LinearProgramming

线性规划求解器。

```rust
pub struct LinearProgramming { ... }

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OptimizationDirection {
    Maximize,
    Minimize,
}

impl LinearProgramming {
    /// 创建新的线性规划求解器
    pub fn new() -> Self { ... }
    
    /// 添加变量
    ///
    /// # Arguments
    /// * `name` - 变量名
    /// * `lower_bound` - 下界
    /// * `upper_bound` - 上界
    ///
    /// # Returns
    /// * 变量ID
    pub fn add_variable(
        &mut self,
        name: &str,
        lower_bound: f64,
        upper_bound: f64
    ) -> usize { ... }
    
    /// 设置目标函数
    ///
    /// # Arguments
    /// * `coefficients` - (变量ID, 系数) 对
    /// * `direction` - 优化方向
    pub fn set_objective(
        &mut self,
        coefficients: Vec<(usize, f64)>,
        direction: OptimizationDirection
    ) { ... }
    
    /// 添加约束条件
    ///
    /// # Arguments
    /// * `coefficients` - (变量ID, 系数) 对
    /// * `relation` - 关系 ("<=", ">=", "==")
    /// * `rhs` - 右侧值
    pub fn add_constraint(
        &mut self,
        coefficients: Vec<(usize, f64)>,
        relation: &str,
        rhs: f64
    ) -> Result<(), String> { ... }
    
    /// 求解
    ///
    /// # Returns
    /// * 最优解 (变量ID -> 值的映射)
    pub fn solve(&self) -> Result<std::collections::HashMap<usize, f64>, String> { ... }
}
```

---

## 10. 错误处理

### ModelError 类型

```rust
#[derive(Debug, Clone)]
pub enum ModelError {
    /// 无效输入
    InvalidInput(String),
    
    /// 计算错误
    ComputationError(String),
    
    /// 状态错误
    StateError(String),
    
    /// 超时错误
    TimeoutError(String),
    
    /// 网络错误
    NetworkError(String),
    
    /// 并发错误
    ConcurrencyError(String),
}

impl std::fmt::Display for ModelError { ... }
impl std::error::Error for ModelError { ... }
```

**使用示例**:

```rust
use c12_model::ModelError;

fn my_function() -> Result<(), ModelError> {
    if some_condition {
        return Err(ModelError::InvalidInput("Invalid parameter".to_string()));
    }
    Ok(())
}

match my_function() {
    Ok(()) => println!("Success"),
    Err(ModelError::InvalidInput(msg)) => eprintln!("Input error: {}", msg),
    Err(e) => eprintln!("Error: {}", e),
}
```

---

## 11. 配置选项

### ModelConfig

```rust
#[derive(Debug, Clone)]
pub struct ModelConfig {
    /// 最大迭代次数
    pub max_iterations: usize,
    
    /// 超时时间（毫秒）
    pub timeout_ms: u64,
    
    /// 详细日志
    pub verbose: bool,
    
    /// 并行度
    pub parallelism: usize,
    
    /// 缓存大小
    pub cache_size: usize,
}

impl Default for ModelConfig {
    fn default() -> Self {
        Self {
            max_iterations: 1000,
            timeout_ms: 30000,
            verbose: false,
            parallelism: num_cpus::get(),
            cache_size: 1000,
        }
    }
}

impl ModelConfig {
    /// 创建新的配置
    pub fn new() -> Self {
        Self::default()
    }
    
    /// 设置最大迭代次数
    pub fn with_max_iterations(mut self, max_iterations: usize) -> Self {
        self.max_iterations = max_iterations;
        self
    }
    
    /// 设置超时时间
    pub fn with_timeout(mut self, timeout_ms: u64) -> Self {
        self.timeout_ms = timeout_ms;
        self
    }
    
    /// 启用详细日志
    pub fn with_verbose(mut self, verbose: bool) -> Self {
        self.verbose = verbose;
        self
    }
}
```

**示例**:

```rust
use c12_model::ModelConfig;

let config = ModelConfig::new()
    .with_max_iterations(5000)
    .with_timeout(60000)
    .with_verbose(true);
```

---

## 12. 总结

c12_model 提供了完整的 API 覆盖8大建模领域：

1. **形式化建模** - 操作语义、指称语义、公理语义
2. **分布式系统** - Raft、Paxos、2PC/3PC、向量时钟
3. **并发模型** - CSP、Actor、Work-Stealing
4. **软件设计** - 分层架构、事件驱动、数据流
5. **算法模型** - 图算法、字符串算法、数学算法
6. **排队论** - M/M/1、M/M/c、M/G/1
7. **机器学习** - 线性回归、逻辑回归
8. **数学建模** - 线性规划、概率分布

**API 设计原则**:

- ✅ 类型安全
- ✅ 错误处理清晰
- ✅ 零成本抽象
- ✅ 文档完整
- ✅ 示例丰富

**参考资源**:

- [Rust API 指南](https://rust-lang.github.io/api-guidelines/)
- [标准库文档](https://doc.rust-lang.org/std/)
- [c12_model 完整文档](https://docs.rs/c12_model)

---

**最后更新**: 2025-10-23  
**维护者**: C12 Model Team  
**许可证**: MIT
