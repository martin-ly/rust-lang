# 实践项目 15: 分布式KV存储

> **难度**: ⭐⭐⭐ 专家级
> **所需知识**: c05-c10
> **预计时间**: 15-20小时

---

## 项目目标

创建简单的分布式键值存储系统。

---

## 功能需求

- [ ] Raft共识算法
- [ ] 数据分片
- [ ] 节点发现
- [ ] 故障恢复
- [ ] 客户端SDK

---

## 学习要点

### Raft算法

```rust
enum RaftState {
    Follower,
    Candidate,
    Leader,
}

struct RaftNode {
    state: RaftState,
    term: u64,
    log: Vec<LogEntry>,
}
```

---

## 参考实现

完整参考实现位于: `examples/distributed-kv/`
