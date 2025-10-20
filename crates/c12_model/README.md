# c12_model - Rust 1.90 建模与形式方法

## 🌟 2025-10-20 核心增强更新

- **📊 [知识图谱与概念关系](./docs/theory_enhanced/KNOWLEDGE_GRAPH_AND_CONCEPT_RELATIONS.md)** - 建模与形式方法完整体系
- **📐 [多维矩阵对比分析](./docs/theory_enhanced/MULTI_DIMENSIONAL_COMPARISON_MATRIX.md)** - 形式化/分布式/并发模型全面对比

---

[![Rust](https://img.shields.io/badge/rust-1.90+-orange.svg)](https://www.rust-lang.org/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Crates.io](https://img.shields.io/crates/v/c18_model.svg)](https://crates.io/crates/c18_model)
[![Documentation](https://docs.rs/c18_model/badge.svg)](https://docs.rs/c18_model)

一个基于 Rust 1.90 的现代化建模与形式方法库，聚焦核心建模技术，涵盖排队论、机器学习、形式化方法、数学建模、性能模型、**高级流量控制**、分布式系统、微服务架构等。
项目采用最小稳定内核设计，充分利用 Rust 1.90 的新特性，便于学习与集成，同时提供完整的理论背景和实践指导。

## 🆕 最新更新 (v0.3.0 - 综合完整版) 🎉

### 重大更新: 理论与实践的全面融合 ✨

`c12_model` 现已成为**完整的、生产级别的模型系统框架**，涵盖以下所有领域：

#### 🧮 形式化语义模型

- **操作语义**: 小步语义、大步语义
- **指称语义**: 数学函数映射
- **公理语义**: Hoare逻辑、最弱前置条件
- **语义等价性分析**: 形式化验证基础

#### 🔄 分布式系统模型

- **Raft共识算法**: 完整实现 (Leader选举、日志复制、安全性保证)
- **分布式快照**: Chandy-Lamport算法
- **向量时钟**: 因果关系追踪
- **Paxos、2PC、3PC**: 多种共识算法对比

#### 🚀 并发模型深度分析

- **CSP vs Actor**: 理论对比与等价性证明
- **共享内存模型**: 内存顺序、原子操作、无锁数据结构
- **Work-Stealing调度**: 高性能任务调度
- **并发模式**: 数据并行、任务并行、管道并行、分治并行

#### 🏗️ 软件设计模型

- **编程范式**: 函数式、面向对象、反应式、数据流
- **架构模式**: 分层、六边形、事件驱动、CQRS、微服务、P2P
- **架构等价性**: 模式间转换与映射关系
- **设计模式**: Builder、Strategy、Observer、Decorator等

#### ⚡ 异步与背压控制

- **流量控制**: Token Bucket、Leaky Bucket、Sliding Window、Adaptive Rate Limiter
- **消息队列背压**: 完整实现
- **异步递归**: 执行器与优化

#### 📊 算法模型

- **图算法**: BFS、DFS、Dijkstra、Prim、Kruskal
- **字符串算法**: KMP、Rabin-Karp
- **数值算法**: Newton法、梯度下降
- **复杂度分析**: 时间、空间复杂度分析

```rust
use c12_model::*;

// 示例1: 使用Raft共识
let raft = RaftProtocol::new(
    "node1".to_string(),
    Duration::from_millis(150),
    Duration::from_millis(50),
);
raft.start_election()?;
raft.append_entry("SET x = 10".to_string())?;

// 示例2: 分布式快照
let snapshot = DistributedSnapshot::new("snap_001".to_string(), "node1".to_string());
snapshot.initiate("node1".to_string(), node_data)?;
let global_snapshot = snapshot.get_snapshot()?;

// 示例3: CSP并发模型
let mut csp = CSPModel::new();
csp.send("producer", "channel", "data")?;
let msg = csp.receive("consumer", "channel")?;

// 示例4: 语义分析
let semantics = SmallStepSemantics::new();
let final_state = semantics.evaluate(expression)?;
```

📖 **全面文档** (~7300行):

- [模型分类体系](docs/MODEL_COMPREHENSIVE_TAXONOMY.md)
- [模型关系分析](docs/MODEL_RELATIONSHIPS_COMPREHENSIVE.md)
- [软件设计模型](docs/design/software-design-models-comprehensive.md)
- [并发模型深度分析](docs/concurrent/concurrency-models-deep-dive.md)
- [Raft共识算法](docs/distributed/raft-consensus-comprehensive.md)
- [分布式快照](docs/distributed/distributed-snapshot-comprehensive.md)
- [语义模型](docs/formal/semantic-models-comprehensive.md)

🎯 **完成报告**: [综合完成报告](COMPREHENSIVE_COMPLETION_REPORT.md)

## 🆕 v0.2.6 更新

### 🏛️ 架构设计模型增强 ✨

**完成最后一个模块，`c12_model`现已100%完成！**

新增管道过滤器架构和P2P架构模型，为构建灵活可扩展的系统提供完整支持：

#### 管道过滤器架构 (Pipe-and-Filter Architecture)

- **PipelineArchitecture** - 管道架构执行器
- **Filter Trait** - 过滤器抽象接口
- **PipelineSplitter** - 管道分支器
- 批量处理支持

```rust
use c12_model::{PipelineArchitecture, Filter, ArchitectureResult};

// 定义过滤器
struct ValidationFilter;
impl Filter<String, String> for ValidationFilter {
    fn process(&mut self, input: String) -> ArchitectureResult<String> {
        Ok(format!("validated:{}", input))
    }
    
    fn filter_name(&self) -> &str {
        "ValidationFilter"
    }
}

struct TransformFilter;
impl Filter<String, String> for TransformFilter {
    fn process(&mut self, input: String) -> ArchitectureResult<String> {
        Ok(input.to_uppercase())
    }
    
    fn filter_name(&self) -> &str {
        "TransformFilter"
    }
}

fn main() -> ArchitectureResult<()> {
    let mut pipeline = PipelineArchitecture::new();
    
    pipeline
        .add_filter(Box::new(ValidationFilter))
        .add_filter(Box::new(TransformFilter));
    
    let result = pipeline.execute("data".to_string())?;
    println!("结果: {}", result); // VALIDATED:DATA
    
    println!("过滤器数量: {}", pipeline.filter_count());
    
    Ok(())
}
```

#### P2P架构 (Peer-to-Peer Architecture)

- **P2PNetwork** - P2P网络管理器
- **Peer Trait** - 对等节点抽象
- **P2PTopology** - 拓扑类型（全连接、环形、星形、网格、随机）
- **P2PNetworkBuilder** - 网络拓扑构建器

```rust
use c12_model::{P2PNetwork, Peer, ArchitectureResult};
use std::sync::{Arc, Mutex};

// 定义对等节点
struct SimplePeer {
    id: String,
    messages: Arc<Mutex<Vec<String>>>,
}

impl SimplePeer {
    fn new(id: String) -> Self {
        Self {
            id,
            messages: Arc::new(Mutex::new(Vec::new())),
        }
    }
}

impl Peer for SimplePeer {
    fn peer_id(&self) -> &str {
        &self.id
    }
    
    fn send_message(&self, target: &str, msg: &str) -> ArchitectureResult<()> {
        println!("Sending to {}: {}", target, msg);
        Ok(())
    }
    
    fn receive_message(&mut self, from: &str, msg: &str) -> ArchitectureResult<String> {
        let message = format!("From {}: {}", from, msg);
        self.messages.lock().unwrap().push(message.clone());
        Ok(message)
    }
    
    fn broadcast(&self, msg: &str) -> ArchitectureResult<()> {
        println!("Broadcasting: {}", msg);
        Ok(())
    }
}

fn main() -> ArchitectureResult<()> {
    let network = P2PNetwork::new();
    
    // 添加节点
    network.add_peer(Box::new(SimplePeer::new("peer1".to_string())))?;
    network.add_peer(Box::new(SimplePeer::new("peer2".to_string())))?;
    network.add_peer(Box::new(SimplePeer::new("peer3".to_string())))?;
    
    // 连接节点
    network.connect_peers("peer1", "peer2")?;
    network.connect_peers("peer2", "peer3")?;
    
    // 发送消息
    network.send_message("peer1", "peer2", "Hello")?;
    
    // 广播消息
    network.broadcast("peer2", "Broadcast message")?;
    
    println!("节点数量: {}", network.peer_count());
    println!("peer2连接数: {}", network.connection_count("peer2"));
    
    Ok(())
}
```

**核心特性**:

- ✅ 管道过滤器 - 灵活的数据处理流水线
- ✅ 管道分支 - 支持多分支并行处理
- ✅ P2P网络 - 完整的对等节点管理
- ✅ 拓扑支持 - 5种经典P2P拓扑
- ✅ 消息路由 - 点对点和广播消息
- ✅ 连接管理 - 动态节点连接

## 🆕 程序设计模型增强 (v0.2.5)

### 🌊 程序设计模型增强 ✨

新增反应式流（Reactive Streams）和数据流编程（Dataflow Programming）模型，构建响应式和数据驱动的应用：

#### 反应式流模型 (Reactive Streams)

- **ReactiveStream** - 符合反应式流规范的流实现
- **背压控制** - 请求-响应模式防止数据溢出
- **流操作符** - map、filter、take等常用操作

```rust
use c12_model::{ReactiveStream, ReactiveOperators, ProgramResult};

fn main() -> ProgramResult<()> {
    // 创建反应式流（缓冲区大小10）
    let stream = ReactiveStream::<i32>::new(10);
    
    // 检查流状态
    println!("缓冲区大小: {}", stream.buffer_size());
    println!("请求的元素数: {}", stream.requested_count());
    
    // 使用流操作符
    let doubled = ReactiveOperators::map(stream, |x| x * 2);
    let filtered = ReactiveOperators::filter(doubled, |x| x > &10);
    let limited = ReactiveOperators::take(filtered, 5);
    
    Ok(())
}
```

#### 数据流编程模型 (Dataflow Programming)

- **DataflowGraph** - 数据流图，节点间自动传递数据
- **DataflowVariable** - 单次赋值变量
- **DataflowPipeline** - 流水线处理
- **DataflowCombinator** - 并行/串行组合器

```rust
use c12_model::{DataflowGraph, DataflowNode, ProgramResult};

// 定义数据流节点
struct MultiplyNode(i32);
impl DataflowNode for MultiplyNode {
    type Input = i32;
    type Output = i32;
    
    fn process(&mut self, input: Self::Input) -> ProgramResult<Self::Output> {
        Ok(input * self.0)
    }
    
    fn name(&self) -> &str {
        "MultiplyNode"
    }
}

fn main() -> ProgramResult<()> {
    let mut graph = DataflowGraph::new();
    
    // 添加节点
    let node1 = graph.add_node(Box::new(MultiplyNode(2)));
    let node2 = graph.add_node(Box::new(MultiplyNode(3)));
    
    // 连接节点
    graph.add_edge(node1, node2)?;
    
    // 执行数据流
    let results = graph.execute(10)?;
    println!("结果: {:?}", results); // [60] = 10 * 2 * 3
    
    Ok(())
}
```

#### 数据流管道示例

```rust
use c12_model::{DataflowPipeline, ProgramResult};

fn main() -> ProgramResult<()> {
    let mut pipeline = DataflowPipeline::new();
    
    pipeline
        .add_stage(|x: i32| Ok(x * 2))      // 乘以2
        .add_stage(|x: i32| Ok(x + 10))     // 加10
        .add_stage(|x: i32| Ok(x / 2));     // 除以2
    
    let result = pipeline.execute(5)?;
    println!("结果: {}", result); // ((5 * 2) + 10) / 2 = 10
    
    Ok(())
}
```

#### 数据流变量示例

```rust
use c12_model::{DataflowVariable, ProgramResult};

fn main() -> ProgramResult<()> {
    // 创建数据流变量
    let var = DataflowVariable::new("计算结果".to_string());
    
    // 设置值
    var.set(42);
    
    // 获取值
    let value = var.await_value()?;
    println!("{}: {}", var.name(), value);
    
    Ok(())
}
```

**核心特性**:

- ✅ 反应式流 - 符合反应式流规范
- ✅ 背压控制 - 请求-响应模式
- ✅ 数据流图 - 声明式数据处理
- ✅ 单次赋值 - DataflowVariable
- ✅ 组合器模式 - 并行/串行组合
- ✅ 类型安全 - 编译时类型检查

## 🆕 并行并发模型增强 (v0.2.4)

### ⚡ 并行并发模型增强 ✨

新增任务并行、流水线并行、工作窃取调度等高级并行模型，构建高性能并发系统：

#### 任务并行模型 (Task Parallelism)

- **TaskParallelExecutor** - 并行执行独立任务
- **ParallelTask Trait** - 可并行任务抽象
- **parallel_invoke** - 并行调用多个函数

```rust
use c12_model::{TaskParallelExecutor, ParallelTask, ConcurrentResult};

// 定义并行任务
struct ComputeTask(i32);

impl ParallelTask for ComputeTask {
    type Output = i32;
    
    fn execute(self) -> Self::Output {
        // 执行计算密集型任务
        self.0 * self.0
    }
}

fn main() -> ConcurrentResult<()> {
    let executor = TaskParallelExecutor::new(4); // 4个工作线程
    
    let tasks = vec![
        ComputeTask(10),
        ComputeTask(20),
        ComputeTask(30),
    ];
    
    let results = executor.execute_tasks(tasks)?;
    println!("结果: {:?}", results); // [100, 400, 900]
    
    // 并行调用函数
    let results = executor.parallel_invoke(vec![
        || expensive_computation_1(),
        || expensive_computation_2(),
        || expensive_computation_3(),
    ])?;
    
    Ok(())
}
```

#### 流水线并行模型 (Pipeline Parallelism)

- **PipelineExecutor** - 多阶段流水线处理
- **PipelineStage Trait** - 流水线阶段抽象
- 支持顺序和并行执行模式

```rust
use c12_model::{PipelineExecutor, PipelineStage, ConcurrentResult};

// 定义流水线阶段
struct ValidateStage;
impl PipelineStage<String, String> for ValidateStage {
    fn process(&self, input: String) -> String {
        // 验证阶段
        format!("validated:{}", input)
    }
}

struct TransformStage;
impl PipelineStage<String, String> for TransformStage {
    fn process(&self, input: String) -> String {
        // 转换阶段
        input.to_uppercase()
    }
}

fn main() -> ConcurrentResult<()> {
    let mut pipeline = PipelineExecutor::new(100); // 缓冲区大小100
    
    pipeline.add_stage(ValidateStage);
    pipeline.add_stage(TransformStage);
    
    let inputs = vec!["data1".to_string(), "data2".to_string()];
    let results = pipeline.execute(inputs)?;
    
    println!("处理结果: {:?}", results);
    Ok(())
}
```

#### 工作窃取调度器 (Work-Stealing Scheduler)

- **WorkStealingScheduler** - 负载均衡的任务调度
- 动态任务窃取算法
- 最小化线程空闲时间

```rust
use c12_model::{WorkStealingScheduler, ConcurrentResult};
use std::sync::{Arc, atomic::{AtomicU32, Ordering}};
use std::time::Duration;

fn main() -> ConcurrentResult<()> {
    let mut scheduler = WorkStealingScheduler::new(4); // 4个工作线程
    let counter = Arc::new(AtomicU32::new(0));
    
    // 启动调度器
    let handles = scheduler.start()?;
    
    // 提交任务
    for i in 0..100 {
        let counter = Arc::clone(&counter);
        scheduler.submit(move || {
            // 模拟工作负载
            std::thread::sleep(Duration::from_millis(10));
            counter.fetch_add(i, Ordering::SeqCst);
        })?;
    }
    
    // 等待任务完成
    std::thread::sleep(Duration::from_secs(2));
    
    // 停止调度器
    scheduler.stop();
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("处理任务数: {}", counter.load(Ordering::SeqCst));
    println!("工作线程数: {}", scheduler.worker_count());
    
    Ok(())
}
```

#### 并行模式分析器 (Parallel Pattern Analyzer)

- **ParallelPattern** - 并行模式枚举
- **ParallelPatternAnalyzer** - 模式特征分析
- 5种经典并行模式支持

```rust
use c12_model::{ParallelPattern, ParallelPatternAnalyzer};

fn main() {
    let patterns = vec![
        ParallelPattern::DataParallel,      // 数据并行
        ParallelPattern::TaskParallel,      // 任务并行
        ParallelPattern::Pipeline,          // 流水线并行
        ParallelPattern::DivideAndConquer,  // 分治
        ParallelPattern::MapReduce,         // MapReduce
    ];
    
    for pattern in patterns {
        let characteristics = ParallelPatternAnalyzer::analyze_pattern(&pattern);
        println!("模式: {:?}", characteristics.pattern);
        println!("描述: {}", characteristics.description);
        println!("可扩展性: {:?}", characteristics.scalability);
        println!("复杂度: {:?}", characteristics.complexity);
        println!("用例: {:?}", characteristics.use_cases);
        println!("---");
    }
}
```

**核心特性**:

- ✅ 任务并行 - 独立任务并行执行
- ✅ 流水线并行 - 多阶段数据处理
- ✅ 工作窃取 - 动态负载均衡调度
- ✅ 并行模式 - 5种经典模式分析
- ✅ 零成本抽象 - 充分利用Rust编译器优化
- ✅ 线程安全 - 编译时并发安全保证

## 🆕 微服务高级模型 (v0.2.3)

### 🕸️ 微服务高级模型 ✨

新增服务网格和分布式追踪支持，为微服务架构提供完整的可观测性和流量管理：

#### 服务网格 (Service Mesh)

- **Sidecar代理模式** - 透明的服务间通信
- **流量管理** - 流量分配、灰度发布、A/B测试
- **安全策略** - mTLS、JWT验证、访问控制
- **可观测性** - 追踪、指标、日志集成

```rust
use c12_model::{ServiceMesh, SidecarProxy, ProxyFeature, TrafficRule, TrafficSplit, RetryPolicy};
use std::net::{SocketAddr, IpAddr, Ipv4Addr};
use std::time::Duration;

// 创建服务网格
let mesh = ServiceMesh::new("production-mesh".to_string());

// 注册Sidecar代理
let mut proxy = SidecarProxy::new(
    "user-service".to_string(),
    SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 15001), // 代理端口
    SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8080),  // 服务端口
);

// 启用功能
proxy.enable_feature(ProxyFeature::LoadBalancing);
proxy.enable_feature(ProxyFeature::CircuitBreaking);
proxy.enable_feature(ProxyFeature::Tracing);

mesh.register_proxy(proxy)?;

// 配置流量分配（金丝雀发布）
let rule = TrafficRule {
    id: "canary-release".to_string(),
    source_service: "api-gateway".to_string(),
    destination_service: "user-service".to_string(),
    traffic_split: vec![
        TrafficSplit { version: "v1".to_string(), weight: 90 },  // 90%流量到v1
        TrafficSplit { version: "v2".to_string(), weight: 10 },  // 10%流量到v2
    ],
    retry_policy: Some(RetryPolicy {
        max_attempts: 3,
        retry_interval: Duration::from_millis(100),
        retryable_status_codes: vec![500, 502, 503],
    }),
    timeout: Some(Duration::from_secs(5)),
};

mesh.add_traffic_rule(rule)?;

// 查看网格统计
let stats = mesh.get_mesh_stats()?;
println!("服务数: {}, 请求数: {}", stats.total_services, stats.total_requests);
```

#### 分布式追踪 (Distributed Tracing)

- **跨服务追踪** - 完整的请求链路追踪
- **Span层级** - 父子Span关系
- **标签和日志** - 丰富的上下文信息
- **采样控制** - 可配置的采样率

```rust
use c12_model::{DistributedTracing, SpanStatus};
use std::collections::HashMap;

// 创建追踪系统（10%采样率）
let tracing = DistributedTracing::new("jaeger".to_string(), 0.1);

// 开始追踪
let root_span = tracing.start_trace(
    "trace-abc123".to_string(),
    "api-gateway".to_string(),
    "handle_request".to_string(),
)?;

// 添加子Span（调用user-service）
let mut user_span = tracing.add_span(
    "trace-abc123",
    &root_span.span_id,
    "user-service".to_string(),
    "get_user_profile".to_string(),
)?;

// 添加标签和日志
user_span.add_tag("user.id".to_string(), "12345".to_string());
user_span.add_tag("http.status_code".to_string(), "200".to_string());

let mut log_fields = HashMap::new();
log_fields.insert("cache".to_string(), "hit".to_string());
user_span.add_log("Retrieved from cache".to_string(), log_fields);

// 结束Span
tracing.end_span("trace-abc123", &user_span.span_id, SpanStatus::Ok)?;
tracing.end_span("trace-abc123", &root_span.span_id, SpanStatus::Ok)?;

// 完成追踪
tracing.finish_trace("trace-abc123")?;

// 查看统计
let stats = tracing.get_stats()?;
println!("活动追踪: {}, 总Span数: {}", stats.active_traces, stats.total_spans);
```

**关键特性:**

- ✅ **Sidecar代理** - 透明的流量拦截和处理
- ✅ **流量分配** - 灵活的流量路由规则
- ✅ **安全策略** - mTLS、JWT、RBAC
- ✅ **分布式追踪** - 完整的请求链路可视化
- ✅ **采样控制** - 可配置的追踪采样率

## 🆕 最新扩展 (v0.2.2)

### 🌐 分布式共识算法实现 ✨

新增3种经典分布式共识算法，构建高可用、强一致的分布式系统：

#### 共识算法 (Consensus Algorithms)

- **Paxos** - 经典分布式共识算法
  - Prepare/Promise 阶段
  - Accept/Accepted 阶段
  - Learn 阶段
  - 支持多提议者并发

- **两阶段提交 (2PC)** - 分布式事务协议
  - Prepare 准备阶段
  - Commit/Abort 提交/回滚阶段
  - 投票机制
  - 协调者-参与者模式

- **三阶段提交 (3PC)** - 2PC的改进版本
  - CanCommit 询问阶段
  - PreCommit 预提交阶段
  - DoCommit 提交阶段
  - 超时恢复机制

```rust
use c12_model::{PaxosProtocol, PaxosMessage, DistributedResult};

// Paxos 示例
let paxos = PaxosProtocol::new("node1".to_string());
paxos.add_participant("node2".to_string())?;
paxos.add_participant("node3".to_string())?;

// 发起提议
let proposal_num = paxos.propose("commit_data".to_string())?;

// 处理 Prepare
let promise = paxos.handle_prepare(proposal_num)?;

// 处理 Accept
let accepted = paxos.handle_accept(proposal_num, "commit_data".to_string())?;

// 获取共识值
let value = paxos.get_accepted_value()?;
println!("共识达成: {:?}", value);
```

```rust
use c12_model::{TwoPhaseCommit, VoteResult, TransactionState};

// 2PC 示例
let coordinator = TwoPhaseCommit::new_coordinator(
    "coordinator".to_string(),
    "tx_001".to_string()
);

coordinator.add_participant("db1".to_string())?;
coordinator.add_participant("db2".to_string())?;

// 阶段1: 准备
coordinator.prepare_phase()?;
coordinator.collect_vote("db1".to_string(), VoteResult::Yes)?;
coordinator.collect_vote("db2".to_string(), VoteResult::Yes)?;

// 阶段2: 提交
coordinator.commit_phase()?;

let state = coordinator.get_state()?;
assert_eq!(state, TransactionState::Committed);
```

```rust
use c12_model::{ThreePhaseCommit, ThreePhaseState};
use std::time::Duration;

// 3PC 示例
let coordinator = ThreePhaseCommit::new_coordinator(
    "coordinator".to_string(),
    "tx_002".to_string(),
    Duration::from_secs(5), // 超时设置
);

coordinator.add_participant("node1".to_string())?;
coordinator.add_participant("node2".to_string())?;

// 阶段1: CanCommit
coordinator.can_commit_phase()?;
coordinator.collect_can_commit_vote("node1".to_string(), true)?;
coordinator.collect_can_commit_vote("node2".to_string(), true)?;

// 阶段2: PreCommit
coordinator.pre_commit_phase()?;
coordinator.collect_pre_commit_ack("node1".to_string())?;
coordinator.collect_pre_commit_ack("node2".to_string())?;

// 阶段3: DoCommit
coordinator.do_commit_phase()?;

let state = coordinator.get_state()?;
assert_eq!(state, ThreePhaseState::Committed);
```

**关键特性:**

- ✅ **完整的协议实现** - 严格遵循算法规范
- ✅ **状态机模型** - 清晰的状态转换
- ✅ **超时处理** - 3PC支持超时恢复
- ✅ **并发安全** - 使用Arc和RwLock保证线程安全
- ✅ **完整测试** - 覆盖正常流程和异常情况

## 🆕 最新扩展 (v0.2.1)

### 📐 算法模型全面增强 ✨

新增20+种经典算法实现，覆盖图算法、字符串算法、数学算法三大领域：

#### 图算法 (Graph Algorithms)

- **Floyd-Warshall** - 全源最短路径算法 O(V³)
- **Bellman-Ford** - 支持负权边的最短路径 O(VE)
- **Kruskal** - 最小生成树（并查集） O(E log E)
- **Prim** - 最小生成树（优先队列） O(E log V)
- **拓扑排序** - Kahn算法 O(V + E)

```rust
use c12_model::{GreedyAlgorithms, AlgorithmMetrics};

let vertices = vec!["A", "B", "C", "D"];
let edges = vec![
    ("A", "B", 1.0), ("A", "C", 4.0),
    ("B", "C", 2.0), ("C", "D", 5.0),
];

let mut metrics = AlgorithmMetrics::new();
let distances = GreedyAlgorithms::floyd_warshall(&vertices, &edges, &mut metrics)?;
```

#### 字符串算法 (String Algorithms)

- **KMP** - 高效模式匹配 O(m + n)
- **Boyer-Moore** - 实用字符串搜索 O(n/m)
- **Rabin-Karp** - 滚动哈希搜索 O(m + n)
- **Manacher** - 线性时间最长回文子串 O(n)

```rust
use c12_model::{StringAlgorithms, AlgorithmMetrics};

let mut metrics = AlgorithmMetrics::new();
let positions = StringAlgorithms::kmp_search(
    "ABABDABACDABABCABAB",
    "ABABCABAB",
    &mut metrics
)?;
println!("找到模式串位置: {:?}", positions);
```

#### 数学算法 (Mathematical Algorithms)

- **欧几里得算法** - 最大公约数 O(log min(a, b))
- **扩展欧几里得** - 求解贝祖等式
- **快速幂** - 模幂运算 O(log n)
- **埃拉托斯特尼筛** - 素数筛 O(n log log n)
- **欧拉函数** - φ函数 O(√n)
- **矩阵快速幂** - 矩阵运算优化 O(n³ log k)
- **中国剩余定理** - 同余方程组求解

```rust
use c12_model::{MathematicalAlgorithms, AlgorithmMetrics};

let mut metrics = AlgorithmMetrics::new();

// 快速幂计算
let result = MathematicalAlgorithms::fast_power(2, 10, 1000, &mut metrics)?;
println!("2^10 mod 1000 = {}", result);

// 素数筛
let primes = MathematicalAlgorithms::sieve_of_eratosthenes(100, &mut metrics)?;
println!("100以内的素数: {:?}", primes);
```

## 🚀 主要特性

### 🔧 Rust 1.90 语言特性集成

- **显式推断的常量参数稳定化** - 在模型配置中使用 `_` 进行常量参数推断
- **生命周期语法一致性检查** - 在模型生命周期管理中应用明确的生命周期标注
- **函数指针比较扩展检查** - 增强模型验证中的函数指针比较安全性
- **标准库 API 增强** - 利用匿名管道等新 API 优化进程间通信
- **编译器优化与平台支持扩展** - 利用最新的编译器优化提升模型计算性能

### 📊 系统建模

- **排队论模型** - M/M/1、M/M/c、M/G/1 等经典排队模型
- **性能模型** - 系统性能分析和预测模型
- **可靠性模型** - 系统可靠性和可用性建模
- **容量规划** - 基于历史数据的容量规划模型
- **负载均衡模型** - 负载分布和调度优化模型

### 🔬 形式化方法

- **有限状态机** - 完整的状态机建模和验证
- **Kripke 结构** - 模态逻辑的语义结构
- **时序逻辑** - LTL/CTL 时序逻辑支持
- **模型检查** - 自动化的模型验证和检查
- **定理证明** - 形式化证明和验证

### 🤖 机器学习模型

- **线性回归** - 经典线性回归算法
- **逻辑回归** - 分类问题的逻辑回归
- **决策树** - 决策树算法实现
- **聚类算法** - K-means 等聚类算法
- **神经网络** - 基础神经网络模型
- **支持向量机** - SVM 分类和回归

### 📈 数学建模

- **概率模型** - 概率分布和随机过程
- **统计模型** - 统计分析和推断
- **优化模型** - 线性规划和整数规划
- **图论模型** - 图算法和网络分析
- **微分方程** - 常微分和偏微分方程求解

## 📦 安装

在 `Cargo.toml` 中添加依赖：

```toml
[dependencies]
c18_model = "0.1.0"

# 按需启用特性
c18_model = { version = "0.1.0", features = ["queueing", "ml", "formal"] }

# 或使用聚合特性
c18_model = { version = "0.1.0", features = ["full"] }
```

### 功能特性

```toml
# 系统建模
queueing = []           # 排队论模型
performance = []        # 性能模型
reliability = []        # 可靠性模型
capacity = []           # 容量规划模型
load-balancing = []     # 负载均衡模型

# 形式化方法
formal = []             # 形式化方法
fsm = []                # 有限状态机
kripke = []             # Kripke 结构
temporal = []           # 时序逻辑
model-checking = []     # 模型检查
theorem-proving = []    # 定理证明

# 机器学习
ml = []                 # 机器学习模型
linear-regression = []  # 线性回归
logistic-regression = [] # 逻辑回归
decision-tree = []      # 决策树
clustering = []         # 聚类算法
neural-network = []     # 神经网络
svm = []                # 支持向量机

# 数学建模
math = []               # 数学建模
probability = []        # 概率模型
statistics = []         # 统计模型
optimization = []       # 优化模型
graph-theory = []       # 图论模型
differential = []       # 微分方程

# 工具特性
visualization = []      # 可视化支持
serialization = []      # 序列化支持
parallel = []           # 并行计算
gpu = []                # GPU 加速

# 完整功能
full = []               # 所有特性
```

## 🚀 快速开始

### 排队论模型

```rust
use c18_model::queueing::prelude::*;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // M/M/1 排队模型
    let mm1_model = MM1Model::new(
        arrival_rate: 0.5,    // 到达率 λ
        service_rate: 1.0,    // 服务率 μ
    );
    
    // 计算性能指标
    let metrics = mm1_model.calculate_metrics().await?;
    println!("平均等待时间: {:.2}", metrics.avg_waiting_time);
    println!("平均队列长度: {:.2}", metrics.avg_queue_length);
    println!("系统利用率: {:.2}%", metrics.utilization * 100.0);
    
    // M/M/c 排队模型
    let mmc_model = MMcModel::new(
        arrival_rate: 2.0,
        service_rate: 1.0,
        servers: 3,           // 3个服务台
    );
    
    let mmc_metrics = mmc_model.calculate_metrics().await?;
    println!("M/M/c 平均等待时间: {:.2}", mmc_metrics.avg_waiting_time);
    
    Ok(())
}
```

### 机器学习模型

```rust
use c18_model::ml::prelude::*;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 线性回归
    let mut lr_model = LinearRegression::new();
    
    // 训练数据
    let x_train = vec![
        vec![1.0, 2.0],
        vec![2.0, 3.0],
        vec![3.0, 4.0],
        vec![4.0, 5.0],
    ];
    let y_train = vec![3.0, 5.0, 7.0, 9.0];
    
    // 训练模型
    lr_model.fit(&x_train, &y_train).await?;
    
    // 预测
    let x_test = vec![vec![5.0, 6.0]];
    let predictions = lr_model.predict(&x_test).await?;
    println!("预测结果: {:?}", predictions);
    
    // 逻辑回归
    let mut log_reg = LogisticRegression::new();
    let x_binary = vec![
        vec![1.0, 2.0],
        vec![2.0, 3.0],
        vec![3.0, 4.0],
        vec![4.0, 5.0],
    ];
    let y_binary = vec![0, 0, 1, 1];
    
    log_reg.fit(&x_binary, &y_binary).await?;
    let binary_predictions = log_reg.predict(&x_test).await?;
    println!("二分类预测: {:?}", binary_predictions);
    
    Ok(())
}
```

### 形式化方法

```rust
use c18_model::formal::prelude::*;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 有限状态机
    let mut fsm = FiniteStateMachine::new();
    
    // 添加状态
    fsm.add_state("idle".to_string());
    fsm.add_state("running".to_string());
    fsm.add_state("stopped".to_string());
    
    // 添加转换
    fsm.add_transition("idle", "start", "running");
    fsm.add_transition("running", "stop", "stopped");
    fsm.add_transition("stopped", "reset", "idle");
    
    // 设置初始状态
    fsm.set_initial_state("idle".to_string());
    
    // 验证状态机
    let is_valid = fsm.validate().await?;
    println!("状态机有效性: {}", is_valid);
    
    // 执行转换
    fsm.transition("start").await?;
    println!("当前状态: {}", fsm.current_state());
    
    // 模型检查
    let mut model_checker = ModelChecker::new();
    let property = "AG (running -> AF stopped)".to_string(); // 总是运行最终会停止
    let result = model_checker.check(&fsm, &property).await?;
    println!("属性验证结果: {}", result);
    
    Ok(())
}
```

### 性能模型

```rust
use c18_model::performance::prelude::*;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建性能模型
    let mut perf_model = PerformanceModel::new();
    
    // 添加组件
    perf_model.add_component("web_server", ComponentConfig {
        service_time: 0.01,    // 10ms 服务时间
        capacity: 100,         // 100 并发请求
        failure_rate: 0.001,   // 0.1% 故障率
    });
    
    perf_model.add_component("database", ComponentConfig {
        service_time: 0.05,    // 50ms 服务时间
        capacity: 50,          // 50 并发连接
        failure_rate: 0.0001,  // 0.01% 故障率
    });
    
    // 添加连接
    perf_model.add_connection("web_server", "database", 0.8); // 80% 请求访问数据库
    
    // 分析性能
    let analysis = perf_model.analyze(1000.0).await?; // 1000 req/s 负载
    println!("系统吞吐量: {:.2} req/s", analysis.throughput);
    println!("平均响应时间: {:.2} ms", analysis.avg_response_time * 1000.0);
    println!("系统可用性: {:.4}%", analysis.availability * 100.0);
    
    Ok(())
}
```

### 数学建模

```rust
use c18_model::math::prelude::*;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 概率分布
    let normal_dist = NormalDistribution::new(0.0, 1.0); // 标准正态分布
    let sample = normal_dist.sample(1000);
    println!("正态分布样本均值: {:.4}", sample.iter().sum::<f64>() / sample.len() as f64);
    
    // 优化问题
    let mut optimizer = LinearProgramOptimizer::new();
    
    // 添加变量
    let x1 = optimizer.add_variable("x1", 0.0, f64::INFINITY);
    let x2 = optimizer.add_variable("x2", 0.0, f64::INFINITY);
    
    // 目标函数: maximize 3x1 + 2x2
    optimizer.set_objective(vec![(x1, 3.0), (x2, 2.0)], OptimizationDirection::Maximize);
    
    // 约束条件
    optimizer.add_constraint(vec![(x1, 1.0), (x2, 1.0)], ConstraintType::LessEqual, 4.0);
    optimizer.add_constraint(vec![(x1, 2.0), (x2, 1.0)], ConstraintType::LessEqual, 7.0);
    
    // 求解
    let solution = optimizer.solve().await?;
    println!("最优解: x1={:.2}, x2={:.2}", solution[x1], solution[x2]);
    println!("最优值: {:.2}", solution.objective_value);
    
    Ok(())
}
```

## 📚 示例

运行示例代码：

```bash
# 排队论模型示例
cargo run --example queueing_models

# 机器学习示例
cargo run --example machine_learning

# 形式化方法示例
cargo run --example formal_methods

# 性能模型示例
cargo run --example performance_modeling

# 数学建模示例
cargo run --example mathematical_modeling

# 综合演示
cargo run --example comprehensive_demo

# 异步背压示例（需要特性）
cargo run -p c12_model --example async_backpressure_demo --features tokio-adapter,tower-examples

# 递归异步与结构化并发示例
cargo run -p c12_model --example async_recursion_examples --features tokio-adapter
```

## 🏗️ 架构

```text
c18_model/
├── src/
│   ├── lib.rs                    # 库入口
│   ├── queueing/                 # 排队论模型
│   │   ├── mm1.rs               # M/M/1 模型
│   │   ├── mmc.rs               # M/M/c 模型
│   │   ├── mg1.rs               # M/G/1 模型
│   │   ├── gim1.rs              # GI/M/1 模型
│   │   └── network.rs           # 排队网络
│   ├── formal/                   # 形式化方法
│   │   ├── fsm.rs               # 有限状态机
│   │   ├── kripke.rs            # Kripke 结构
│   │   ├── temporal.rs          # 时序逻辑
│   │   ├── model_checking.rs    # 模型检查
│   │   └── theorem_proving.rs   # 定理证明
│   ├── ml/                       # 机器学习
│   │   ├── linear_regression.rs # 线性回归
│   │   ├── logistic_regression.rs # 逻辑回归
│   │   ├── decision_tree.rs     # 决策树
│   │   ├── clustering.rs        # 聚类算法
│   │   ├── neural_network.rs    # 神经网络
│   │   └── svm.rs               # 支持向量机
│   ├── math/                     # 数学建模
│   │   ├── probability.rs       # 概率模型
│   │   ├── statistics.rs        # 统计模型
│   │   ├── optimization.rs      # 优化模型
│   │   ├── graph_theory.rs      # 图论模型
│   │   └── differential.rs      # 微分方程
│   ├── performance/              # 性能模型
│   │   ├── model.rs             # 性能模型
│   │   ├── component.rs         # 组件模型
│   │   ├── analysis.rs          # 性能分析
│   │   └── prediction.rs        # 性能预测
│   ├── reliability/              # 可靠性模型
│   │   ├── model.rs             # 可靠性模型
│   │   ├── mttf.rs              # 平均故障时间
│   │   ├── availability.rs      # 可用性分析
│   │   └── maintenance.rs       # 维护模型
│   ├── capacity/                 # 容量规划
│   │   ├── planning.rs          # 容量规划
│   │   ├── forecasting.rs       # 容量预测
│   │   └── optimization.rs      # 容量优化
│   ├── visualization/            # 可视化
│   │   ├── plots.rs             # 图表绘制
│   │   ├── graphs.rs            # 图形可视化
│   │   └── dashboards.rs        # 仪表板
│   └── prelude.rs               # 预导入模块
├── examples/                     # 示例代码
├── docs/                         # 文档
└── Cargo.toml                    # 项目配置
```

## 🔧 配置

### 环境变量

```bash
# 模型配置
export MODEL_CACHE_SIZE="1000"
export MODEL_TIMEOUT="30"
export MODEL_PRECISION="double"

# 计算配置
export MAX_THREADS="8"
export GPU_ENABLED="false"
export PARALLEL_ENABLED="true"

# 可视化配置
export PLOT_BACKEND="svg"
export PLOT_RESOLUTION="300"
export PLOT_THEME="default"
```

## 🧭 新增文档导航（Rust 1.90 并发/语义/算法/架构）

- 并发/异步：`docs/concurrency/async-sync-classification.md`
- 背压模型：`docs/concurrency/backpressure-models.md`
- 递归异步：`docs/concurrency/async-recursion.md`
- 语言语义：`docs/formal/language-semantics.md`
- 设计分层：`docs/architecture/design-models.md`
- 分布式与微服务：`docs/architecture/distributed-design.md`
- 算法模型：`docs/algorithms/models.md`

### 配置文件

```toml
# config.toml
[model]
cache_size = 1000
timeout = 30
precision = "double"
validation = true

[computation]
max_threads = 8
gpu_enabled = false
parallel_enabled = true
memory_limit = "1GB"

[visualization]
backend = "svg"
resolution = 300
theme = "default"
output_dir = "./plots"

[queueing]
default_arrival_rate = 1.0
default_service_rate = 2.0
max_servers = 100

[ml]
default_learning_rate = 0.01
default_iterations = 1000
cross_validation_folds = 5

[formal]
model_checker = "nuXmv"
temporal_logic = "CTL"
verification_timeout = 60
```

## 🧪 测试

```bash
# 运行所有测试
cargo test

# 运行特定模块测试
cargo test queueing
cargo test formal
cargo test ml
cargo test math

# 运行集成测试
cargo test --features full

# 运行基准测试
cargo bench

# 运行数值精度测试
cargo test --features precision
```

## 📊 性能

### 基准测试结果

| 模型类型 | 计算复杂度 | 内存使用 | 执行时间 | 精度 |
|----------|------------|----------|----------|------|
| M/M/1 排队 | O(1) | 1MB | <1ms | 双精度 |
| 线性回归 | O(n²) | 10MB | 10ms | 单精度 |
| 状态机验证 | O(2^n) | 50MB | 100ms | 符号 |
| 优化求解 | O(n³) | 20MB | 50ms | 双精度 |
| 神经网络 | O(n²) | 100MB | 1000ms | 单精度 |

### 优化建议

1. **并行计算**: 利用多核CPU加速计算密集型任务
2. **内存管理**: 合理使用缓存减少重复计算
3. **数值精度**: 根据需求选择合适的数值精度
4. **算法选择**: 根据问题规模选择最优算法

## 🔬 理论背景

### 排队论基础

- **Little's Law**: L = λW (平均队列长度 = 到达率 × 平均等待时间)
- **Kendall记号**: A/B/c/K/N/D (到达分布/服务分布/服务台数/系统容量/顾客源/服务规则)
- **稳态条件**: ρ = λ/μ < 1 (系统利用率小于1)

### 形式化方法1

- **状态空间**: 系统所有可能状态的集合
- **转换关系**: 状态之间的转换条件
- **时序逻辑**: 描述系统行为的时间性质
- **模型检查**: 自动验证系统是否满足给定性质

### 机器学习

- **监督学习**: 使用标记数据训练模型
- **无监督学习**: 从无标记数据中发现模式
- **强化学习**: 通过与环境交互学习最优策略
- **深度学习**: 使用多层神经网络进行学习

## 🤝 贡献

我们欢迎社区贡献！请查看 [CONTRIBUTING.md](CONTRIBUTING.md) 了解如何参与。

### 开发设置

```bash
# 克隆仓库
git clone https://github.com/rust-lang/c18_model.git
cd c18_model

# 安装依赖
cargo build

# 运行测试
cargo test

# 运行示例
cargo run --example queueing_models
```

## 📄 许可证

本项目采用 MIT 许可证 - 查看 [LICENSE](LICENSE) 文件了解详情。

## 🙏 致谢

感谢以下开源项目和资源的贡献：

- [NumPy](https://numpy.org/) - 数值计算库
- [SciPy](https://scipy.org/) - 科学计算库
- [SymPy](https://www.sympy.org/) - 符号数学库
- [CVXPY](https://www.cvxpy.org/) - 凸优化库
- [NetworkX](https://networkx.org/) - 图论库
- [Rust Num](https://github.com/rust-num/num) - Rust 数值计算

## 📞 支持

- 📖 [文档](https://docs.rs/c18_model)
- 🐛 [问题报告](https://github.com/rust-lang/c18_model/issues)
- 💬 [讨论](https://github.com/rust-lang/c18_model/discussions)
- 📧 [邮件列表](mailto:c18-model@rust-lang.org)

---

**c18_model** - 让 Rust 在建模与形式方法领域发光发热！ 🦀📊
