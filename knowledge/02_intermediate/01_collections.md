# 集合类型 (Collections)

> **EN**: Collections
> **Summary**: 集合类型 Collections. (stub/archive redirect)
> **权威来源**: 本主题深度解释见 [concept/01_foundation/08_collections.md](../../concept/01_foundation/08_collections.md)。
> **历史版本存档**: [archive/knowledge/02_intermediate/01_collections.md](../../archive/knowledge/02_intermediate/01_collections.md)
>
> **定位**: 本文件为精简知识卡片，保留核心规则/概念与常见陷阱。详细解释、形式化语义与代码示例请查看权威来源。

---

## 核心概念

1. `Vec<T>` 是动态数组，提供连续堆存储
2. `HashMap<K,V>` 平均 O(1) 查找，`BTreeMap` 保持键有序
3. `HashSet/BTreeSet` 分别对应无序与有序键集合
4. 迭代器统一访问集合元素，避免索引越界

## 关键区分

| 集合 | 有序性 | 重复 | 适用场景 |
|---|---|---|---|
| `Vec<T>` | 插入序 | 允许 | 序列/栈 |
| `HashMap` | 无序 | 键唯一 | 快速查找 |
| `BTreeMap` | 有序 | 键唯一 | 范围查询 |

## 常见陷阱

- 遍历中修改 `Vec` 导致索引错位
- 对 `HashMap` 假设稳定迭代顺序
- 忽略 `Vec::with_capacity` 减少重分配

---

**详细内容已迁移**：请点击上方 [concept/01_foundation/08_collections.md](../../concept/01_foundation/08_collections.md) 查看最新权威解释。
