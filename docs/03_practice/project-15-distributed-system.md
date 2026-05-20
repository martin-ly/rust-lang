# 实践项目 15: 分布式KV存储

> **难度**: ⭐⭐⭐ 专家级
> **所需知识**: c05-c10
> **预计时间**: 15-20小时

---

## 项目目标
> **[来源: Rust Official Docs]**

创建简单的分布式键值存储系统。

---

## 功能需求
> **[来源: Rust Official Docs]**

- [ ] Raft共识算法
- [ ] 数据分片
- [ ] 节点发现
- [ ] 故障恢复
- [ ] 客户端SDK

---

## 学习要点
> **[来源: Rust Official Docs]**

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
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
