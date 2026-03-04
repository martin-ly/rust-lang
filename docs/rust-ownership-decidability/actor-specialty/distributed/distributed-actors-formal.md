# 分布式Actor形式化分析

> **CAP定理、一致性模型与分布式协议**

---

## 1. 分布式Actor基础

### 1.1 形式化定义

```text
定义 DISTRIBUTED-ACTOR-SYSTEM:

分布式Actor系统是一个五元组:
    D = (N, A, M, L, R)

其中:
    N: 节点集合, 每个节点运行一个Actor系统
    A: 全局Actor集合, 分布在各个节点上
    M: 消息集合
    L: 位置函数, A → N (Actor到节点的映射)
    R: 路由表, 记录Actor位置信息
```

### 1.2 消息传递语义

```text
定义 MESSAGE-DELIVERY-SEMANTICS:

At-most-once (最多一次):
    P(deliver(m)) ≤ 1
    消息可能丢失，但不会重复

At-least-once (至少一次):
    P(deliver(m)) ≥ 1
    消息可能重复，但不会丢失
    实现: 确认 + 重传

Exactly-once (恰好一次):
    P(deliver(m)) = 1
    消息既不丢失也不重复
    实现: 幂等 + 至少一次
```

---

## 2. CAP定理与Actor

### 2.1 CAP定理形式化

```text
定理 CAP-THEOREM:
分布式系统最多同时满足以下两项:
    - Consistency (一致性)
    - Availability (可用性)
    - Partition tolerance (分区容错性)

形式化:
    ∀分布式系统S.
    (C(S) ∧ A(S) ∧ P(S)) → False

    等价于:
    C(S) ∧ A(S) → ¬P(S)
    C(S) ∧ P(S) → ¬A(S)
    A(S) ∧ P(S) → ¬C(S)
```

### 2.2 Actor系统CAP选择

| 系统类型 | C | A | P | 适用场景 |
|:---:|:---:|:---:|:---:|:---|
| **CP Actor** | ✅ | ❌ | ✅ | 金融交易、配置管理 |
| **AP Actor** | ❌ | ✅ | ✅ | 社交网络、日志系统 |
| **CA Actor** | ✅ | ✅ | ❌ | 单数据中心系统 |

### 2.3 定理 ACTOR-CAP-TRADE-OFF

```text
定理 ACTOR-CAP-TRADE-OFF:
分布式Actor系统必须在一致性和可用性之间选择

证明:
1. 网络分区P必然发生
2. 分区期间:
   - 选择一致性: 拒绝写入，牺牲可用性
   - 选择可用性: 接受写入，牺牲一致性
3. ∴ 无法同时满足C和A

Actor具体表现:
CP选择 (如coerce集群):
    - 使用Raft/Paxos共识
    - 写入需要多数节点确认
    - 分区时停止写入

AP选择 (如Akka Cluster):
    - 使用Gossip协议
    - 本地写入立即确认
    - 分区时保持可用，最终一致
```

---

## 3. 一致性模型

### 3.1 一致性谱系

```text
一致性强度:

强 ────────────────────────────────────────────► 弱

Linearizable ──► Sequential ──► Causal ──► Eventual
(线性一致)       (顺序一致)      (因果一致)     (最终一致)

Actor系统通常选择:
- 强一致性: 使用Raft (如etcd集成)
- 因果一致: Vector clocks
- 最终一致: Gossip协议 (默认)
```

### 3.2 因果一致性

```text
定义 CAUSAL-CONSISTENCY:

Happens-before关系:
    e₁ → e₂ (e₁发生在e₂之前)

    条件:
    1. 同一Actor: e₁在e₂之前处理
    2. 发送-接收: e₁是发送，e₂是接收
    3. 传递性: e₁ → e₂ ∧ e₂ → e₃ ⇒ e₁ → e₃

因果一致性:
    ∀进程p. 如果p观察到e₁，且e₁ → e₂，
    则p必须已经观察到e₁才能观察到e₂
```

### 3.3 Vector Clocks实现

```rust
// Vector clock实现
#[derive(Clone, Debug)]
pub struct VectorClock {
    /// 每个节点的逻辑时钟
    clocks: HashMap<NodeId, u64>,
}

impl VectorClock {
    /// 递增本地时钟
    pub fn increment(&mut self, node: NodeId) {
        *self.clocks.entry(node).or_insert(0) += 1;
    }

    /// 合并另一个vector clock
    pub fn merge(&mut self, other: &VectorClock) {
        for (node, time) in &other.clocks {
            let entry = self.clocks.entry(*node).or_insert(0);
            *entry = (*entry).max(*time);
        }
    }

    /// 比较两个vector clock
    pub fn compare(&self, other: &VectorClock) -> Ordering {
        let dominates = |a: &VectorClock, b: &VectorClock| -> bool {
            b.clocks.iter().all(|(node, b_time)| {
                a.clocks.get(node).unwrap_or(&0) >= b_time
            })
        };

        if dominates(self, other) && !dominates(other, self) {
            Ordering::Greater  // self happens after other
        } else if dominates(other, self) && !dominates(self, other) {
            Ordering::Less     // self happens before other
        } else if dominates(self, other) && dominates(other, self) {
            Ordering::Equal    // same
        } else {
            Ordering::Unordered // concurrent
        }
    }
}
```

---

## 4. 分布式协议

### 4.1 Gossip协议

```text
定义 GOSSIP-PROTOCOL:

协议参数:
    fanout: 每次传播的节点数
    interval: 传播间隔
    ttl: 消息生存时间

算法:
    every interval:
        targets = random_select(peers, fanout)
        for target in targets:
            send(target, local_state)

        upon receive(state_from_peer):
            merge(local_state, state_from_peer)

收敛时间:
    期望传播轮数: O(log n)
    其中n为节点数
```

### 4.2 Raft共识

```text
定义 RAFT-CONSENSUS:

角色:
    Leader: 处理所有客户端请求
    Follower: 被动复制日志
    Candidate: 选举中的候选者

属性:
    选举安全: 最多一个Leader per term
    Leader追加: Leader只追加日志，不删除
    日志匹配: 如果两个日志条目有相同index和term，则内容相同
    Leader完整性: 已提交的条目在新Leader中必定存在
    状态机安全: 已提交的条目以相同顺序执行

与Actor集成:
    - Actor作为状态机
    - 消息日志作为事件源
    - 共识决定消息顺序
```

### 4.3 CRDTs (无冲突复制数据类型)

```text
定义 CRDT:

状态型CRDT (State-based):
    merge(s₁, s₂) 必须满足:
    - 交换律: merge(a, b) = merge(b, a)
    - 结合律: merge(merge(a, b), c) = merge(a, merge(b, c))
    - 幂等律: merge(a, a) = a

操作型CRDT (Operation-based):
    - 操作可交换
    - 操作幂等

Actor应用:
    - 分布式计数器 (G-Counter, PN-Counter)
    - 分布式集合 (G-Set, OR-Set)
    - 分布式映射
```

```rust
// G-Counter (增长计数器)
#[derive(Clone)]
pub struct GCounter {
    /// 每个节点的计数
    counters: HashMap<NodeId, u64>,
}

impl GCounter {
    /// 本地递增
    pub fn increment(&mut self, node: NodeId) {
        *self.counters.entry(node).or_insert(0) += 1;
    }

    /// 查询值
    pub fn value(&self) -> u64 {
        self.counters.values().sum()
    }

    /// 合并 (State-based CRDT)
    pub fn merge(&mut self, other: &GCounter) {
        for (node, count) in &other.counters {
            let entry = self.counters.entry(*node).or_insert(0);
            *entry = (*entry).max(*count);
        }
    }
}

// PN-Counter (可增可减计数器)
pub struct PNCounter {
    increments: GCounter,
    decrements: GCounter,
}

impl PNCounter {
    pub fn increment(&mut self, node: NodeId) {
        self.increments.increment(node);
    }

    pub fn decrement(&mut self, node: NodeId) {
        self.decrements.increment(node);
    }

    pub fn value(&self) -> i64 {
        self.increments.value() as i64 - self.decrements.value() as i64
    }

    pub fn merge(&mut self, other: &PNCounter) {
        self.increments.merge(&other.increments);
        self.decrements.merge(&other.decrements);
    }
}
```

---

## 5. Saga分布式事务

### 5.1 Saga形式化

```text
定义 SAGA-PATTERN:

Saga = (T, C, ≺)

其中:
    T = {t₁, t₂, ..., tₙ}: 事务步骤集合
    C = {c₁, c₂, ..., cₙ}: 补偿步骤集合 (cᵢ对应tᵢ)
    ≺: 偏序关系，定义执行顺序

执行语义:
    execute(Saga):
        completed = []
        for t in topological_sort(T, ≺):
            if t.execute() succeeds:
                completed.push(t)
            else:
                for c in reverse(completed):
                    c.execute()  // 补偿
                return Failure
        return Success

补偿保证:
    ∀t ∈ T. t.execute() ∧ c.execute() ≡ no_effect
```

### 5.2 Saga与2PC对比

| 特性 | Saga | 2PC |
|:---:|:---:|:---:|
| 原子性 | 补偿实现 | 准备+提交 |
| 隔离性 | 无 | 有 |
| 持久性 | 补偿日志 | 提交日志 |
| 阻塞 | 否 | 是 |
| 复杂度 | 中等 | 高 |
| 适用 | 长事务 | 短事务 |

### 5.3 Saga协调器Actor

```rust
// Saga协调器
pub struct SagaCoordinator {
    steps: Vec<SagaStep>,
    state: SagaState,
    executed: Vec<usize>,
}

enum SagaState {
    Pending,
    Executing,
    Compensating,
    Completed,
    Failed,
}

struct SagaStep {
    action: Box<dyn Fn() -> Future<Output = Result<()>>>,
    compensate: Box<dyn Fn() -> Future<Output = Result<()>>>,
}

impl SagaCoordinator {
    pub async fn execute(&mut self) -> Result<()> {
        self.state = SagaState::Executing;

        for (idx, step) in self.steps.iter().enumerate() {
            match (step.action)().await {
                Ok(_) => {
                    self.executed.push(idx);
                }
                Err(_) => {
                    self.compensate().await?;
                    self.state = SagaState::Failed;
                    return Err(SagaError::StepFailed(idx));
                }
            }
        }

        self.state = SagaState::Completed;
        Ok(())
    }

    async fn compensate(&mut self) -> Result<()> {
        self.state = SagaState::Compensating;

        for idx in self.executed.iter().rev() {
            if let Err(e) = (self.steps[*idx].compensate)().await {
                // 补偿失败，需要人工干预
                return Err(SagaError::CompensationFailed(*idx, e));
            }
        }

        Ok(())
    }
}
```

---

## 6. 网络分区处理

### 6.1 分区检测

```text
定义 PARTITION-DETECTION:

心跳机制:
    every heartbeat_interval:
        for node in nodes:
            if now - last_heartbeat(node) > timeout:
                mark_suspect(node)

    upon suspect(node):
        if confirm_with_majority(node) failed:
            declare_partition()

Phi累积失败检测:
    φ = -log10(1 - F(now - last))
    where F是到达时间分布的CDF

    if φ > threshold:
        mark_failed(node)
```

### 6.2 分区恢复策略

| 策略 | 描述 | 优点 | 缺点 |
|:---|:---|:---|:---|
| **自动合并** | 分区恢复后自动合并状态 | 无需人工 | 冲突复杂 |
| **人工介入** | 停止服务等待人工处理 | 安全 | 停机时间 |
| **优先级** | 保留某分区状态 | 简单 | 数据丢失 |
| **CRDT** | 自动解决冲突 | 无冲突 | 数据类型限制 |

---

## 7. coerce框架分布式特性

### 7.1 集群架构

```rust
// coerce集群配置
use coerce::actor::system::ActorSystem;
use coerce::remote::cluster::Cluster;

#[tokio::main]
async fn main() {
    // 创建Actor系统
    let system = ActorSystem::new();

    // 配置集群
    let cluster = Cluster::builder()
        .with_node_id("node-1".to_string())
        .with_listen_addr("0.0.0.0:50051".parse().unwrap())
        .with_seed_nodes(vec![
            "node-2:50051".to_string(),
            "node-3:50051".to_string(),
        ])
        .build()
        .await;

    // 启动集群
    cluster.start(system).await;
}
```

### 7.2 分片配置

```rust
use coerce::persistent::Shard;

// 定义分片Actor
#[derive(Shard)]
#[shard(name = "user-shard", extract = |msg: UserCmd| msg.user_id)]
struct UserActor {
    user_id: String,
    state: UserState,
}

// 分片自动路由
async fn handle_user_command(cmd: UserCmd, cluster: &Cluster) {
    // 自动路由到正确的分片
    let shard = cluster.shard::<UserActor>("user-shard", &cmd.user_id);
    shard.send(cmd).await;
}
```

---

**维护者**: Rust Distributed Actor Team
**更新日期**: 2026-03-05
**覆盖**: CAP定理、一致性模型、分布式协议、Saga、CRDT
