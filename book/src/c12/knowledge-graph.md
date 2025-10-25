# 知识图谱

本页展示领域建模与形式方法的概念关系。

---

## 📊 核心概念关系图

```text
                   [领域建模]
                         |
         +---------------+---------------+
         |               |               |
    [形式语义]     [分布式系统]    [并发模型]
         |               |               |
    +----+----+     +----+----+     +----+----+
    |    |    |     |    |    |     |    |    |
  操作  指称 公理   Raft  Paxos  Actor  CSP  STM
  语义  语义 语义   共识  共识   模型  模型  模型
```

---

## 🎯 概念层次

### 1. 形式语义 (Formal Semantics)

**语义模型**:

- **操作语义** (Operational Semantics):
  - 小步语义 (Small-step)
  - 大步语义 (Big-step)
  - 状态转换系统

- **指称语义** (Denotational Semantics):
  - 数学函数映射
  - 域理论
  - 组合性原则

- **公理语义** (Axiomatic Semantics):
  - Hoare逻辑
  - 最弱前置条件
  - 程序验证

**等价性分析**:

- 语义等价
- 观察等价
- 行为等价

---

### 2. 分布式系统 (Distributed Systems)

**共识算法**:

- **Raft**: 易理解的共识算法
  - Leader选举
  - 日志复制
  - 安全性保证

- **Paxos**: 经典共识算法
  - Basic Paxos
  - Multi-Paxos
  - Fast Paxos

- **2PC/3PC**: 两阶段/三阶段提交
  - 事务协调
  - 故障恢复

**分布式模型**:

- **分布式快照**: Chandy-Lamport算法
- **向量时钟**: 因果关系追踪
- **CAP定理**: 一致性权衡
- **最终一致性**: 弱一致性模型

---

### 3. 并发模型 (Concurrency Models)

**消息传递**:

- **Actor模型**:
  - 独立计算实体
  - 消息异步传递
  - 位置透明性

- **CSP模型** (Communicating Sequential Processes):
  - 通道通信
  - 进程同步
  - 组合性

**共享内存**:

- **内存模型**:
  - Sequential Consistency
  - Release/Acquire
  - Relaxed Ordering

- **STM** (Software Transactional Memory):
  - 原子事务
  - 乐观并发
  - 冲突检测

**并发模式**:

- Work-Stealing调度
- Fork-Join并行
- 数据并行
- 任务并行

---

## 🔗 概念关联

### 形式语义 ←→ Rust类型系统

```rust
// Hoare逻辑在Rust中的体现
// {前置条件} 代码 {后置条件}

// 使用类型系统表达不变量
pub struct SortedVec<T: Ord> {
    inner: Vec<T>,
}

impl<T: Ord> SortedVec<T> {
    // 前置条件: 无
    // 后置条件: 返回空的有序向量
    pub fn new() -> Self {
        SortedVec { inner: Vec::new() }
    }
    
    // 前置条件: self是有序的
    // 后置条件: self仍然有序，且包含value
    pub fn insert(&mut self, value: T) {
        let pos = self.inner.binary_search(&value).unwrap_or_else(|e| e);
        self.inner.insert(pos, value);
        // 不变量: inner始终保持有序
    }
    
    // 公理: 对于任何i < j，inner[i] <= inner[j]
    pub fn is_sorted(&self) -> bool {
        self.inner.windows(2).all(|w| w[0] <= w[1])
    }
}
```

### Raft ←→ 分布式一致性

```rust
use std::collections::HashMap;

// Raft节点状态
enum NodeState {
    Follower,
    Candidate,
    Leader,
}

// 日志条目
struct LogEntry {
    term: u64,
    command: String,
}

// Raft节点
struct RaftNode {
    state: NodeState,
    current_term: u64,
    voted_for: Option<u64>,
    log: Vec<LogEntry>,
    commit_index: usize,
    last_applied: usize,
}

impl RaftNode {
    pub fn new() -> Self {
        RaftNode {
            state: NodeState::Follower,
            current_term: 0,
            voted_for: None,
            log: Vec::new(),
            commit_index: 0,
            last_applied: 0,
        }
    }
    
    // Leader选举
    pub fn start_election(&mut self) {
        self.state = NodeState::Candidate;
        self.current_term += 1;
        self.voted_for = Some(self.get_id());
    }
    
    // 日志复制
    pub fn append_entry(&mut self, entry: LogEntry) {
        if matches!(self.state, NodeState::Leader) {
            self.log.push(entry);
        }
    }
}
```

### Actor模型 ←→ 消息传递

```rust
use tokio::sync::mpsc;

// Actor消息
enum Message {
    Get(String, tokio::sync::oneshot::Sender<Option<String>>),
    Set(String, String),
}

// 键值存储Actor
struct KVActor {
    store: std::collections::HashMap<String, String>,
    receiver: mpsc::Receiver<Message>,
}

impl KVActor {
    fn new() -> (Self, mpsc::Sender<Message>) {
        let (tx, rx) = mpsc::channel(32);
        let actor = KVActor {
            store: std::collections::HashMap::new(),
            receiver: rx,
        };
        (actor, tx)
    }
    
    async fn run(mut self) {
        while let Some(msg) = self.receiver.recv().await {
            match msg {
                Message::Get(key, reply) => {
                    let value = self.store.get(&key).cloned();
                    let _ = reply.send(value);
                }
                Message::Set(key, value) => {
                    self.store.insert(key, value);
                }
            }
        }
    }
}

// 使用示例
#[tokio::main]
async fn main() {
    let (actor, sender) = KVActor::new();
    tokio::spawn(actor.run());
    
    // 发送Set消息
    sender.send(Message::Set("key".to_string(), "value".to_string())).await.unwrap();
    
    // 发送Get消息
    let (tx, rx) = tokio::sync::oneshot::channel();
    sender.send(Message::Get("key".to_string(), tx)).await.unwrap();
    let value = rx.await.unwrap();
    println!("Value: {:?}", value);
}
```

---

## 📚 学习路径图

```text
第一步: 理解形式语义基础
    ↓
第二步: 学习分布式系统模型
    ↓
第三步: 掌握并发编程模型
    ↓
第四步: 形式化验证方法
    ↓
第五步: 实战应用与建模
```

---

## 🎓 模型分类体系

### 语义模型对比

| 模型 | 特点 | 适用场景 |
|------|------|---------|
| **操作语义** | 直观、机械化 | 实现验证 |
| **指称语义** | 数学化、组合性 | 理论分析 |
| **公理语义** | 逻辑化、证明 | 程序验证 |

### 共识算法对比

| 算法 | 复杂度 | 性能 | 容错性 |
|------|--------|------|--------|
| **Raft** | 中等 | 良好 | f < n/2 |
| **Paxos** | 高 | 优秀 | f < n/2 |
| **2PC** | 低 | 一般 | 不容错 |
| **3PC** | 中等 | 一般 | 部分容错 |

### 并发模型对比

| 模型 | 通信方式 | 状态共享 | 适用场景 |
|------|----------|----------|---------|
| **Actor** | 消息传递 | 无 | 分布式系统 |
| **CSP** | 通道同步 | 无 | 并发流程 |
| **STM** | 事务 | 有 | 复杂共享状态 |

---

## 💡 核心原则

### 1. 形式化思维

```text
形式语义 → 精确定义 → 可验证性
```

### 2. 分布式设计

```text
CAP定理 → 权衡选择 → 最终一致性
```

### 3. 并发安全

```text
类型系统 → 编译时检查 → 线程安全
```

---

## 🔍 Rust 1.90 特性应用

### 1. 类型级建模

```rust
// 使用类型系统表达领域模型
use std::marker::PhantomData;

// 状态标记
struct Draft;
struct Published;
struct Archived;

// 文章状态机
struct Article<State> {
    content: String,
    _state: PhantomData<State>,
}

impl Article<Draft> {
    fn new(content: String) -> Self {
        Article {
            content,
            _state: PhantomData,
        }
    }
    
    fn publish(self) -> Article<Published> {
        Article {
            content: self.content,
            _state: PhantomData,
        }
    }
}

impl Article<Published> {
    fn archive(self) -> Article<Archived> {
        Article {
            content: self.content,
            _state: PhantomData,
        }
    }
}

// 编译时保证状态转换正确
let article = Article::<Draft>::new("Hello".to_string());
let published = article.publish();
let archived = published.archive();
```

### 2. 异步分布式模型

```rust
use tokio::sync::{mpsc, RwLock};
use std::sync::Arc;

// 分布式缓存节点
struct CacheNode {
    id: u64,
    data: Arc<RwLock<HashMap<String, String>>>,
    peers: Vec<mpsc::Sender<CacheMessage>>,
}

enum CacheMessage {
    Put(String, String),
    Get(String, tokio::sync::oneshot::Sender<Option<String>>),
    Sync(HashMap<String, String>),
}

impl CacheNode {
    async fn handle_message(&self, msg: CacheMessage) {
        match msg {
            CacheMessage::Put(key, value) => {
                // 写入本地
                self.data.write().await.insert(key.clone(), value.clone());
                
                // 同步到其他节点
                for peer in &self.peers {
                    let mut sync_data = HashMap::new();
                    sync_data.insert(key.clone(), value.clone());
                    let _ = peer.send(CacheMessage::Sync(sync_data)).await;
                }
            }
            CacheMessage::Get(key, reply) => {
                let value = self.data.read().await.get(&key).cloned();
                let _ = reply.send(value);
            }
            CacheMessage::Sync(data) => {
                // 合并远程数据
                let mut local = self.data.write().await;
                local.extend(data);
            }
        }
    }
}
```

### 3. 形式化验证

```rust
// 使用proptest进行属性测试
use proptest::prelude::*;

proptest! {
    #[test]
    fn sorted_vec_maintains_order(values in prop::collection::vec(0..1000, 0..100)) {
        let mut sorted = SortedVec::new();
        for v in values {
            sorted.insert(v);
        }
        
        // 验证不变量：向量始终有序
        prop_assert!(sorted.is_sorted());
    }
    
    #[test]
    fn raft_log_append_preserves_order(
        entries in prop::collection::vec(any::<u64>(), 0..100)
    ) {
        let mut node = RaftNode::new();
        for term in entries {
            node.append_entry(LogEntry {
                term,
                command: format!("cmd{}", term),
            });
        }
        
        // 验证：日志term单调递增
        prop_assert!(node.log.windows(2).all(|w| w[0].term <= w[1].term));
    }
}
```

---

## 📖 相关章节

- **[基础概念](./foundations.md)** - 建模理论
- **[实践指南](./guides.md)** - 实现技巧
- **[代码示例](./examples.md)** - 完整实现 ⭐
- **[返回模块首页](./README.md)**

---

## 🔗 扩展学习

### 深入阅读

- [形式化方法详解](../../crates/c12_model/README.md)
- [TLA+规范语言](https://lamport.azurewebsites.net/tla/tla.html)
- [Raft论文](https://raft.github.io/)

### 相关模块

- **[C05: 多线程](../c05/README.md)** - 并发基础
- **[C06: 异步编程](../c06/README.md)** - 异步模型
- **[C13: 可靠性](../c13/README.md)** - 分布式容错

---

## 🎯 实践项目建议

### 入门级

- 简单状态机
- 类型级建模
- Actor示例

### 进阶级

- Raft共识实现
- 分布式缓存
- CSP通道模式

### 高级

- 形式化验证
- 分布式事务
- 自定义DSL

---

**掌握形式化建模是构建可靠系统的关键！** 🚀
