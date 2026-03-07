# 共识算法语义 (Consensus Algorithms Semantics)

## 目录

- [共识算法语义 (Consensus Algorithms Semantics)](#共识算法语义-consensus-algorithms-semantics)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 共识问题定义](#2-共识问题定义)
    - [2.1 形式化定义](#21-形式化定义)
    - [2.2 共识 vs 一致性](#22-共识-vs-一致性)
  - [3. Paxos 算法](#3-paxos-算法)
    - [3.1 Paxos 角色](#31-paxos-角色)
    - [3.2 Paxos 两阶段协议](#32-paxos-两阶段协议)
    - [3.3 Rust 实现框架](#33-rust-实现框架)
  - [4. Raft 算法](#4-raft-算法)
    - [4.1 Raft 核心机制](#41-raft-核心机制)
    - [4.2 Raft 日志复制](#42-raft-日志复制)
    - [4.3 Raft 安全保证](#43-raft-安全保证)
    - [4.4 Rust Raft 实现](#44-rust-raft-实现)
  - [5. 共识算法比较](#5-共识算法比较)
  - [6. 形式化验证](#6-形式化验证)
    - [6.1 TLA+ 规格](#61-tla-规格)
  - [7. 总结](#7-总结)

## 1. 引言

共识问题是分布式系统最核心的挑战之一，要求多个节点就某个值达成一致。本文档深入分析 Paxos、Raft 等共识算法的形式化语义和 Rust 实现。

---

## 2. 共识问题定义

### 2.1 形式化定义

```
共识问题 (Consensus Problem):

给定 n 个进程 {p₁, p₂, ..., pₙ}，每个进程提出一个值 vᵢ，
共识算法必须满足以下性质:

  终止性 (Termination):
    每个正确的进程最终决定要某个值

  一致性 (Agreement):
    如果某个正确进程决定 v，那么所有正确进程都决定 v

  有效性 (Validity):
    被决定的值必须是某个进程提出的值
```

**FLP 不可能结果:**

> Fischer, Lynch, Paterson 证明：在异步系统中，即使只有一个故障进程，也不存在确定性的共识算法。

这意味着实际共识算法必须使用：

- 超时机制
- 随机化
- 故障检测器（不完全可靠）

### 2.2 共识 vs 一致性

```
术语区分:

共识 (Consensus):
  ┌──────────┐
  │ 提出值    │
  │ (Propose) │
  └────┬─────┘
       ↓
  ┌──────────┐
  │ 达成决议  │
  │ (Decide)  │
  └──────────┘

  关注: 多个节点就单一值达成一致

一致性 (Consistency):
  ┌──────────┐
  │ 更新操作  │
  │ (Update)  │
  └────┬─────┘
       ↓
  ┌──────────┐
  │ 状态同步  │
  │ (Sync)    │
  └──────────┘

  关注: 多个副本保持数据一致

关系: 共识是构建一致性系统的核心原语
```

---

## 3. Paxos 算法

### 3.1 Paxos 角色

```
Paxos 架构:

┌──────────────────────────────────────────────────────────────┐
│                       Paxos 集群                              │
│                                                               │
│   ┌──────────┐        ┌──────────┐        ┌──────────┐      │
│   │ Proposer │───────→│ Acceptor │←───────│ Proposer │      │
│   │  (提议者) │        │ (接受者) │        │  (提议者) │      │
│   └──────────┘        └────┬─────┘        └──────────┘      │
│                            │                                 │
│                            ↓                                 │
│                      ┌──────────┐                            │
│                      │ Learner  │                            │
│                      │ (学习者) │                            │
│                      └──────────┘                            │
│                                                               │
└──────────────────────────────────────────────────────────────┘

角色说明:
  Proposer: 提出值，推动决议
  Acceptor: 投票决定是否接受提议
  Learner: 学习最终决议（可选）
```

### 3.2 Paxos 两阶段协议

```
Paxos 两阶段提交:

Phase 1: Prepare/Promise
─────────────────────────────────────
Proposer           Acceptor
   │                   │
   │──Prepare(n)────→│  n = proposal number
   │                   │
   │←──Promise(───────│  承诺不接受更小 n
   │     n, v_prev)   │  返回之前接受的值
   │                   │

Phase 2: Accept/Accepted
─────────────────────────────────────
Proposer           Acceptor
   │                   │
   │──Accept(n, v)───→│  提出值 v
   │                   │
   │←──Accepted(──────│  接受值
   │     n, v)        │
   │                   │

约束条件:
  - n 必须唯一且单调递增
  - Acceptor 只接受最大 n 的提议
  - 多数派接受即达成决议
```

### 3.3 Rust 实现框架

```rust
// Paxos 消息类型
#[derive(Clone, Debug)]
enum PaxosMessage {
    Prepare { proposal_number: u64, proposer_id: NodeId },
    Promise { proposal_number: u64, last_accepted: Option<(u64, Value)> },
    Accept { proposal_number: u64, value: Value },
    Accepted { proposal_number: u64, value: Value },
}

// Acceptor 状态
struct Acceptor {
    promised_n: Option<u64>,      // 已承诺的最大 n
    accepted: Option<(u64, Value)>, // 已接受的值
}

impl Acceptor {
    fn handle_prepare(&mut self, n: u64) -> Option<PaxosMessage> {
        if self.promised_n.map_or(true, |pn| n > pn) {
            self.promised_n = Some(n);
            Some(PaxosMessage::Promise {
                proposal_number: n,
                last_accepted: self.accepted.clone(),
            })
        } else {
            None // 拒绝
        }
    }

    fn handle_accept(&mut self, n: u64, v: Value) -> Option<PaxosMessage> {
        if self.promised_n == Some(n) {
            self.accepted = Some((n, v.clone()));
            Some(PaxosMessage::Accepted { proposal_number: n, value: v })
        } else {
            None // 拒绝
        }
    }
}

// Proposer 状态机
enum ProposerState {
    Idle,
    Preparing { n: u64, promises: Vec<Promise> },
    Accepting { n: u64, value: Value, accepts: usize },
    Decided { value: Value },
}

struct Proposer {
    node_id: NodeId,
    quorum_size: usize,
    state: ProposerState,
}

impl Proposer {
    async fn propose(&mut self, value: Value, acceptors: &[NodeId]) {
        let n = self.generate_proposal_number();

        // Phase 1: Prepare
        self.state = ProposerState::Preparing {
            n,
            promises: vec![],
        };

        for acceptor in acceptors {
            self.send_prepare(*acceptor, n).await;
        }

        // 等待多数派 Promise...
    }
}
```

---

## 4. Raft 算法

### 4.1 Raft 核心机制

```
Raft 状态机:

┌─────────────────────────────────────────────────────────────┐
│                      Raft 节点状态                           │
│                                                              │
│  ┌──────────┐    election timeout    ┌──────────┐          │
│  │ Follower │───────────────────────→│ Candidate│          │
│  │          │                       │          │          │
│  │ • 接收日志 │←─────────────────────│ • 发起选举 │          │
│  │ • 响应投票 │   发现更高 term      │ • 给自己投票│         │
│  └──────────┘                       └────┬─────┘          │
│       ↑                                   │                │
│       │         赢得选举                   │                │
│       └───────────────────────────────────┘                │
│                                           │                │
│                                           ↓                │
│                                    ┌──────────┐           │
│                                    │  Leader  │           │
│                                    │          │           │
│                                    │ • 接收客户端请求│       │
│                                    │ • 复制日志    │       │
│                                    │ • 发送心跳    │       │
│                                    └──────────┘           │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### 4.2 Raft 日志复制

```
日志复制流程:

Leader                    Follower
   │                          │
   │──AppendEntries──────────→│  prev_log_index, prev_log_term
   │  [index, term, command]  │  entries[], leader_commit
   │                          │
   │←──AppendEntries Response─│  success: true/false
   │                          │

成功条件:
  1. Follower 的 prev_log_index 处日志 term 匹配 prev_log_term
  2. 否则拒绝，Leader 递减 prev_log_index 重试
```

### 4.3 Raft 安全保证

```
Raft 安全性质:

选举安全 (Election Safety):
  任意时刻最多只有一个 Leader

  □ (Leader₁(t) ∧ Leader₂(t)) → (Leader₁ = Leader₂)

日志匹配 (Log Matching):
  如果两个日志条目索引和 term 相同，则内容相同

  ∀i, j. log₁[i].term = log₂[j].term ∧ i = j → log₁[i] = log₂[j]

Leader 完备性 (Leader Completeness):
  已提交的日志条目必定存在于未来 Leader 中

  □ (entry committed at term T →
     ∀leader. leader.term ≥ T → entry ∈ leader.log)

状态机安全 (State Machine Safety):
  如果节点应用了某索引的日志，则不会应用不同内容的日志

  ∀i. applied[i] = e₁ → ◇□ applied[i] ≠ e₂ (e₁ ≠ e₂)
```

### 4.4 Rust Raft 实现

```rust
// Raft 状态
enum NodeState {
    Follower {
        leader_id: Option<NodeId>,
        voted_for: Option<NodeId>,
    },
    Candidate {
        votes_received: HashSet<NodeId>,
    },
    Leader {
        next_index: HashMap<NodeId, u64>,
        match_index: HashMap<NodeId, u64>,
    },
}

struct RaftNode {
    id: NodeId,
    current_term: u64,
    state: NodeState,
    log: Vec<LogEntry>,
    commit_index: u64,
    last_applied: u64,
    config: ClusterConfig,
}

struct LogEntry {
    term: u64,
    index: u64,
    command: Command,
}

// 消息类型
#[derive(Clone, Debug)]
enum RaftMessage {
    RequestVote {
        term: u64,
        candidate_id: NodeId,
        last_log_index: u64,
        last_log_term: u64,
    },
    RequestVoteResponse {
        term: u64,
        vote_granted: bool,
    },
    AppendEntries {
        term: u64,
        leader_id: NodeId,
        prev_log_index: u64,
        prev_log_term: u64,
        entries: Vec<LogEntry>,
        leader_commit: u64,
    },
    AppendEntriesResponse {
        term: u64,
        success: bool,
        match_index: u64,
    },
}

impl RaftNode {
    // 处理客户端请求（仅 Leader）
    async fn handle_client_request(&mut self, cmd: Command) -> Result<(), RaftError> {
        match &self.state {
            NodeState::Leader { .. } => {
                // 追加到本地日志
                let entry = LogEntry {
                    term: self.current_term,
                    index: self.log.len() as u64 + 1,
                    command: cmd,
                };
                self.log.push(entry);

                // 异步复制到其他节点
                self.replicate_log().await;
                Ok(())
            }
            _ => Err(RaftError::NotLeader),
        }
    }

    // 处理 AppendEntries
    fn handle_append_entries(&mut self, msg: AppendEntries) -> AppendEntriesResponse {
        if msg.term < self.current_term {
            return AppendEntriesResponse {
                term: self.current_term,
                success: false,
                match_index: 0,
            };
        }

        // 重置选举超时
        self.reset_election_timeout();

        // 检查日志匹配
        if !self.log_matches(msg.prev_log_index, msg.prev_log_term) {
            return AppendEntriesResponse {
                term: self.current_term,
                success: false,
                match_index: self.find_conflict_index(),
            };
        }

        // 追加新条目
        self.append_entries(msg.entries);

        // 更新 commit_index
        if msg.leader_commit > self.commit_index {
            self.commit_index = min(msg.leader_commit, self.log.len() as u64);
        }

        AppendEntriesResponse {
            term: self.current_term,
            success: true,
            match_index: self.log.len() as u64,
        }
    }

    // 检查是否达成多数派
    fn check_commit(&mut self) {
        if let NodeState::Leader { match_index, .. } = &self.state {
            for n in (self.commit_index + 1)..=self.log.len() as u64 {
                let replicated = match_index.values()
                    .filter(|&&idx| idx >= n)
                    .count() + 1; // +1 包括 Leader 自己

                if replicated > self.config.nodes.len() / 2
                   && self.log[(n - 1) as usize].term == self.current_term {
                    self.commit_index = n;
                }
            }
        }
    }
}
```

---

## 5. 共识算法比较

| 特性 | Paxos | Raft | Multi-Paxos |
|------|-------|------|-------------|
| 可理解性 | 困难 | 容易 | 中等 |
| Leader 选举 | 隐含 | 显式 | 显式 |
| 日志复制 | 独立优化 | 内置 | 内置 |
| 成员变更 | 复杂 | 联合共识 | 复杂 |
| 生产实现 | Chubby, PaxosStore | etcd, TiKV | - |

---

## 6. 形式化验证

### 6.1 TLA+ 规格

```tla
(* Raft 的 TLA+ 规格片段 *)

VARIABLES currentTerm, state, log, commitIndex

ElectionSafety ==
  \A i, j \in Servers :
    state[i] = Leader /\ state[j] = Leader /\ currentTerm[i] = currentTerm[j]
    => i = j

LogMatching ==
  \A i, j \in Servers :
    \A n \in 1..Len(log[i]) :
      n \leq Len(log[j]) /\ log[i][n].term = log[j][n].term
      => SubSeq(log[i], 1, n) = SubSeq(log[j], 1, n)

LeaderCompleteness ==
  \A i \in Servers : state[i] = Leader =>
    \A n \in 1..commitIndex[i] :
      log[i][n] = log[j][n]
```

---

## 7. 总结

共识算法是分布式系统的核心基础：

1. **Paxos**: 理论优雅，实现复杂
2. **Raft**: 可理解性强，工业标准
3. **安全性**: 选举安全、日志匹配、状态机安全
4. **活性**: 超时机制保证进展

关键公式:

$$
\text{Consensus} = \text{Majority} \times \text{Term/View} \times \text{LogReplication}
$$
