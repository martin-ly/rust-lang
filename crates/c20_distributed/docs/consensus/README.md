# 共识（Consensus）

- 覆盖：Raft、Paxos、Multi-Paxos、EPaxos、Viewstamped Replication
- 课程参考：MIT 6.824 Lab2/3、CMU 15-440、Berkeley CS262A
- 接口：`ConsensusApi`、`ConsensusRole`
- 实践要点：日志复制、领导者选举、提交/应用、快照

## 安全性（Safety）与活性（Liveness）

- 安全性：不产生相互矛盾的提交。Raft 依靠多数派日志匹配与领导者限制（leader completeness）保证。
- 活性：在网络稳定的情况下最终能前进。通过随机化选举超时与心跳机制降低分歧与冲突选举。
- 不变式：
  - 提交前条件：条目必须存储于多数派上且位于领导者任期内。
  - 应用前条件：应用层按 `commit_index` 单调推进；应用是确定性的状态机。

## 选举超时与心跳

- 心跳周期 T；跟随者选举超时 E 从区间 [a, b] 均匀抽样，一般 b≥3T。
- E 的随机化避免同时竞选；失败领导者退避，减少日志冲突。
- 与 `scheduling::TimerService` 协同：心跳使用周期定时，选举使用一次性随机超时。

## Raft（feature: consensus-raft）

提供最小 Raft 接口：

- `RaftState`、`Term`、`LogIndex`
- `AppendEntriesReq/Resp`、`RequestVoteReq/Resp`
- `RaftNode` trait

建议实验路线（对齐 MIT 6.824）：

1. 领导者选举与心跳
2. 日志复制与提交
3. 快照与恢复

### 日志匹配与提交

- 领导者在 `AppendEntries` 中携带 `(prev_log_index, prev_log_term)` 以进行匹配；冲突时回退并重试。
- 提交规则：领导者任期内的条目在多数派复制后即可推进 `commit_index`；应用顺序与日志顺序一致。

### 快照与截断

- 当日志过长时，创建快照并允许截断已有日志以降低恢复成本。
- 发送安装快照 RPC（若实现提供）给进度落后的跟随者。

最小示例（特性启用）：

```toml
[dev-dependencies]
c20_distributed = { version = "0.1", features = ["consensus-raft"] }
```

```rust
use c20_distributed::consensus_raft::{MinimalRaft, RaftNode, AppendEntriesReq, Term, LogIndex};
let mut r: MinimalRaft<Vec<u8>> = MinimalRaft::new();
let req = AppendEntriesReq { term: Term(1), leader_id: "n1".into(), prev_log_index: LogIndex(0), prev_log_term: Term(0), entries: vec![b"a".to_vec()], leader_commit: LogIndex(0) };
let _resp = r.handle_append_entries(req).unwrap();
```

## Paxos / Multi-Paxos / EPaxos 对比

- Paxos：两阶段（Prepare/Accept），保证单值共识；工程中常用 Multi-Paxos 复用领导者降低开销。
- Multi-Paxos：稳定领导者后只需 Accept 阶段；与 Raft 在工程可读性与领导者限制上有所取舍。
- EPaxos：无固定领导者，基于依赖关系和提交图并行提交，降低延迟但实现更复杂。

工程取舍：

- Raft 强调易实现与日志一致性；Paxos 家族理论简洁但工程细节多；EPaxos 适合跨地域低延迟但复杂度与冲突处理成本高。

## 实验指引（对齐课程）

1) 选举与心跳：验证领导者唯一性与故障切换时间；注入网络分区与时钟抖动。
2) 日志复制：构造冲突场景，验证回退策略与提交前置条件。
3) 快照与恢复：制造长日志，测量恢复时间；验证快照一致性与截断正确性。
4) 线性化读：实现 `read_index`/`lease read` 并在分区与时钟偏差下验证安全。

### 线性化读实现指引（read_index / lease read）

- read_index：领导者向多数派确认自身仍为领导者并获取当前 `commit_index`，随后在不附加日志的情况下提供只读；开销是一次多数派往返。
- lease read：基于时间租约，领导者在租约期内直接提供只读；需要安全时钟界（见 `time/`），防止时钟回拨导致过期租约误用。
- 推荐做法：在网络稳定期使用 lease 以降低延迟；检测到时钟异常或分区风险时降级为 read_index。

## 进一步阅读

- Wiki：`Paxos`, `Raft`, `EPaxos`, `Viewstamped Replication`
- 课程：MIT 6.824（Labs 2/3）、Berkeley CS262A 共识模块
- 论文：Paxos Made Simple、Raft：In Search of an Understandable Consensus、EPaxos、VR Revisited
