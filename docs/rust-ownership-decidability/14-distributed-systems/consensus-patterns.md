# 分布式共识模式

> **难度**: 🔴 高级
> **应用场景**: 分布式数据库、区块链、协调服务

---

## 目录

- [分布式共识模式](#分布式共识模式)
  - [目录](#目录)
  - [概念](#概念)
    - [CAP 定理](#cap-定理)
  - [共识算法](#共识算法)
    - [Raft 算法](#raft-算法)
    - [使用示例](#使用示例)
  - [一致性级别](#一致性级别)
    - [线性一致性 (Linearizability)](#线性一致性-linearizability)
    - [最终一致性](#最终一致性)
  - [Rust 实现考量](#rust-实现考量)
    - [所有权与分布式状态](#所有权与分布式状态)
    - [错误处理](#错误处理)
  - [参考](#参考)

## 概念

分布式共识解决多个节点在不可靠网络中就某个值达成一致的挑战。

### CAP 定理

```text
┌─────────────────────────────────────────┐
│              CAP 定理                    │
│                                         │
│   一致性 (Consistency)                  │
│      ＼                                 │
│       ＼                                │
│   可用性＼______分区容错性              │
│   (Availability)  (Partition Tolerance) │
│                                         │
│   任何系统只能同时满足其中两个           │
└─────────────────────────────────────────┘
```

---

## 共识算法

### Raft 算法

Raft 通过选举领导者来实现共识。

```rust
// Raft 节点状态
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum NodeState {
    Follower,
    Candidate,
    Leader,
}

pub struct RaftNode {
    id: NodeId,
    state: NodeState,
    current_term: Term,
    voted_for: Option<NodeId>,
    log: Vec<LogEntry>,
    commit_index: u64,
    last_applied: u64,

    // 仅 Leader
    next_index: HashMap<NodeId, u64>,
    match_index: HashMap<NodeId, u64>,
}

impl RaftNode {
    // 处理投票请求
    pub fn handle_request_vote(&mut self, req: RequestVoteReq) -> RequestVoteRes {
        if req.term < self.current_term {
            return RequestVoteRes {
                term: self.current_term,
                vote_granted: false,
            };
        }

        if req.term > self.current_term {
            self.current_term = req.term;
            self.state = NodeState::Follower;
            self.voted_for = None;
        }

        let can_vote = self.voted_for.is_none() || self.voted_for == Some(req.candidate_id);
        let log_ok = req.last_log_term > self.last_log_term()
            || (req.last_log_term == self.last_log_term()
                && req.last_log_index >= self.log.len() as u64);

        if can_vote && log_ok {
            self.voted_for = Some(req.candidate_id);
            RequestVoteRes {
                term: self.current_term,
                vote_granted: true,
            }
        } else {
            RequestVoteRes {
                term: self.current_term,
                vote_granted: false,
            }
        }
    }

    // 追加日志 (Leader 调用 Follower)
    pub fn handle_append_entries(&mut self, req: AppendEntriesReq) -> AppendEntriesRes {
        if req.term < self.current_term {
            return AppendEntriesRes {
                term: self.current_term,
                success: false,
            };
        }

        self.current_term = req.term;
        self.state = NodeState::Follower;

        // 日志一致性检查
        if req.prev_log_index > 0 {
            if self.log.len() < req.prev_log_index as usize {
                return AppendEntriesRes {
                    term: self.current_term,
                    success: false,
                };
            }

            if self.log[req.prev_log_index as usize - 1].term != req.prev_log_term {
                // 日志冲突，删除后续
                self.log.truncate(req.prev_log_index as usize - 1);
                return AppendEntriesRes {
                    term: self.current_term,
                    success: false,
                };
            }
        }

        // 追加新条目
        for entry in req.entries {
            let idx = entry.index as usize;
            if idx <= self.log.len() {
                if self.log[idx - 1].term != entry.term {
                    self.log.truncate(idx - 1);
                    self.log.push(entry);
                }
            } else {
                self.log.push(entry);
            }
        }

        // 更新 commit_index
        if req.leader_commit > self.commit_index {
            self.commit_index = req.leader_commit.min(self.log.len() as u64);
        }

        AppendEntriesRes {
            term: self.current_term,
            success: true,
        }
    }
}
```

### 使用示例

```rust
// 创建 3 节点集群
let mut nodes: Vec<RaftNode> = (0..3)
    .map(|id| RaftNode::new(NodeId(id)))
    .collect();

// 模拟选举
nodes[0].become_candidate();
nodes[0].request_votes(&mut nodes[1..]);

// 提交日志
if nodes[0].is_leader() {
    nodes[0].append_entry(LogEntry {
        term: nodes[0].current_term,
        index: nodes[0].log.len() as u64 + 1,
        data: b"set x = 1".to_vec(),
    });
}
```

---

## 一致性级别

### 线性一致性 (Linearizability)

最强的单个对象一致性，所有操作看起来是原子的。

```rust
// 线性一致性保证
// 如果操作 A 在操作 B 开始前完成，
// 那么所有节点都看到 A 在 B 之前

// 使用原子操作 + 共识实现
pub struct LinearizableStore {
    raft: RaftNode,
    state: HashMap<String, String>,
}

impl LinearizableStore {
    pub fn write(&mut self, key: String, value: String) -> Result<(), Error> {
        // 1. 通过 Raft 复制日志
        let entry = LogEntry::Set { key, value };
        self.raft.propose(entry)?;

        // 2. 等待多数确认
        self.raft.wait_commit()?;

        Ok(())
    }

    pub fn read(&self, key: &str) -> Result<Option<String>, Error> {
        // 线性读：从 Leader 读取或走 Raft 日志
        self.raft.ensure_leader()?;
        Ok(self.state.get(key).cloned())
    }
}
```

### 最终一致性

弱一致性，保证如果没有更新，最终所有副本一致。

```rust
// Gossip 协议实现
pub struct GossipNode {
    id: NodeId,
    data: HashMap<String, VersionedValue>,
    neighbors: Vec<NodeId>,
}

impl GossipNode {
    pub fn merge(&mut self, other: &HashMap<String, VersionedValue>) {
        for (key, value) in other {
            match self.data.get(key) {
                Some(existing) if existing.version >= value.version => {}
                _ => {
                    self.data.insert(key.clone(), value.clone());
                }
            }
        }
    }

    pub fn gossip(&mut self, all_nodes: &mut HashMap<NodeId, GossipNode>) {
        for neighbor_id in &self.neighbors {
            if let Some(neighbor) = all_nodes.get_mut(neighbor_id) {
                // 交换数据
                let my_data = self.data.clone();
                neighbor.merge(&my_data);

                let their_data = neighbor.data.clone();
                self.merge(&their_data);
            }
        }
    }
}
```

---

## Rust 实现考量

### 所有权与分布式状态

```rust
// 消息传递避免共享状态
pub enum Message {
    RequestVote { term: Term, candidate_id: NodeId },
    AppendEntries { term: Term, entries: Vec<LogEntry> },
    ClientRequest { cmd: Command },
}

pub async fn node_loop(mut node: RaftNode, mut rx: mpsc::Receiver<Message>) {
    let mut interval = tokio::time::interval(Duration::from_millis(100));

    loop {
        tokio::select! {
            Some(msg) = rx.recv() => {
                match msg {
                    Message::RequestVote { term, candidate_id } => {
                        node.handle_request_vote(RequestVoteReq { term, candidate_id });
                    }
                    // ...
                }
            }
            _ = interval.tick() => {
                node.handle_timeout().await;
            }
        }
    }
}
```

### 错误处理

```rust
#[derive(Debug, thiserror::Error)]
pub enum ConsensusError {
    #[error("Not leader")]
    NotLeader { leader_hint: Option<NodeId> },

    #[error("Proposal timeout")]
    Timeout,

    #[error("Network error: {0}")]
    Network(String),

    #[error("Quorum not reached")]
    QuorumFailed,
}
```

---

## 参考

- [Raft Paper](https://raft.github.io/raft.pdf)
- [Paxos Made Simple](https://lamport.azurewebsites.net/pubs/paxos-simple.pdf)

---

*文档版本: 1.0.0*
