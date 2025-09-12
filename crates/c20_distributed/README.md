# c20_distributed — 分布式系统（Rust 1.89 对齐）

本 crate 聚焦分布式系统核心：成员管理、拓扑与分片、复制与一致性、共识抽象、事务与补偿、SWIM 故障检测与反熵、调度与逻辑时钟、存储与幂等。

## 快速导航

- 课程对标：`docs/COURSE_ALIGNMENT.md`
- Wiki 映射：`docs/WIKI_MAPPING.md`
- 概念模型（CRA）：`docs/CONCEPT_MODEL.md`
- 关键论证与公式：`docs/FORMAL_ARGUMENTS.md`
- 路线图：`docs/ROADMAP.md`
- 实验指南：`docs/EXPERIMENT_GUIDE.md`
- 常见陷阱：`docs/PITFALLS.md`

## 模块索引（与导出项）

- `membership`（成员） | `swim`（故障检测）
- `topology`（一致性哈希） | `partitioning`（分片）
- `replication`（法定人数/复制） | `consistency`（一致性级别）
- `consensus`（抽象；可选 `consensus-raft`）
- `transactions`（Saga） | `storage`（状态机/日志/幂等）
- `scheduling`（时钟/定时） | `transport`（RPC 抽象） | `codec`

## 特性开关

- `runtime-tokio`：启用 Tokio 运行时与异步功能。
- `consensus-raft`：启用最小 Raft 实验性实现与结构。

## 学习建议

按 `docs/COURSE_ALIGNMENT.md` 顺序实验：membership→topology→replication→consistency→storage→transactions→consensus（可选）。

## 运行与基准

- 运行测试：`cargo test -p c20_distributed`
- 运行示例：
  - Saga：`cargo run -p c20_distributed --example e2e_saga`
  - 复制：`cargo run -p c20_distributed --example e2e_replication`
- 基准（Criterion）：`cargo bench -p c20_distributed`

## 新增：Raft 作用域回调（避免 'static 闭包）

当启用 `consensus-raft` 特性时，可使用作用域回调避免在测试中引入 `Arc<Mutex<...>>`：

```rust
use c20_distributed::consensus_raft::{MinimalRaft, RaftNode, AppendEntriesReq, Term, LogIndex};

let mut raft: MinimalRaft<Vec<u8>> = MinimalRaft::new();
let mut buf: Vec<Vec<u8>> = Vec::new();
{
    let mut apply = |e: &Vec<u8>| buf.push(e.clone());
    let mut scoped = raft.set_apply_scoped(&mut apply);
    let req = AppendEntriesReq { term: Term(1), leader_id: "n1".into(), prev_log_index: LogIndex(0), prev_log_term: Term(0), entries: vec![b"x".to_vec()], leader_commit: LogIndex(1) };
    let _ = scoped.handle_append_entries(req);
}
assert_eq!(buf, vec![b"x".to_vec()]);
```

说明：`set_apply_scoped` 返回守卫对象 `ScopedApply`，在该作用域内对 Raft 的 `handle_append_entries` 调用将使用提供的非 `'static` 回调。

## 新增：Property Tests（随机化性质测试）

本 crate 使用 `proptest` 为 SWIM 与复制模块增加性质测试：

- `tests/prop_swim.rs`：
  - 直连探测与可达性一致（Alive/Suspect）。
  - 版本号优先级合并（高版本覆盖低版本）。
- `tests/prop_replication.rs`：
  - 多数仲裁性质：`required_acks >= floor(N/2)+1` 且 `<= N`。
  - 复制成功当且仅当 `acks >= required_acks`。

运行：`cargo test -p c20_distributed --all-features`
