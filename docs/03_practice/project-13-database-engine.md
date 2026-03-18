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
