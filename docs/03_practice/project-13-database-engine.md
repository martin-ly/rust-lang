# 实践项目 13: 简易数据库引擎

> **难度**: ⭐⭐⭐ 专家级
> **所需知识**: c01-c08
> **预计时间**: 10-12小时

---

## 项目目标

创建支持SQL子集的嵌入式数据库。

---

## 功能需求

- [ ] B-Tree索引
- [ ] SQL解析
- [ ] 事务支持
- [ ] 持久化存储
- [ ] 并发控制

---

## 学习要点

### B-Tree实现

```rust
struct BTreeNode {
    keys: Vec<String>,
    values: Vec<String>,
    children: Vec<Box<BTreeNode>>,
    is_leaf: bool,
}
```

---

## 参考实现

完整参考实现位于: `examples/database-engine/`
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
