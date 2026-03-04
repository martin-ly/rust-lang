# IndexMap/IndexSet 形式化分析

> **主题**: 保持插入顺序的集合
>
> **形式化框架**: 双数据结构 + 顺序保证
>
> **参考**: indexmap Documentation

---

## 目录

- [IndexMap/IndexSet 形式化分析](#indexmapindexset-形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 架构设计](#2-架构设计)
    - [2.1 双数据结构](#21-双数据结构)
    - [定义 2.1 (IndexMap结构)](#定义-21-indexmap结构)
    - [定理 2.1 (双映射)](#定理-21-双映射)
    - [2.2 顺序维护](#22-顺序维护)
    - [定理 2.2 (插入顺序)](#定理-22-插入顺序)
  - [3. 操作复杂度](#3-操作复杂度)
    - [复杂度表](#复杂度表)
    - [定理 3.1 (remove复杂度)](#定理-31-remove复杂度)
  - [4. 与HashMap对比](#4-与hashmap对比)
    - [定理 4.1 (适用场景)](#定理-41-适用场景)
  - [5. 反例](#5-反例)
    - [反例 5.1 (误用retain)](#反例-51-误用retain)
    - [反例 5.2 (容量规划)](#反例-52-容量规划)

---

## 1. 引言

IndexMap提供:

- O(1)平均查找
- O(1)索引访问
- 保持插入顺序
- 可排序操作

---

## 2. 架构设计

### 2.1 双数据结构

### 定义 2.1 (IndexMap结构)

```rust
pub struct IndexMap<K, V, S = RandomState> {
    core: IndexMapCore<K, V>,
    hash_builder: S,
}

struct IndexMapCore<K, V> {
    indices: RawTable<usize>,  // 哈希表: key → bucket索引
    entries: Vec<Bucket<K, V>>, // 稠密数组: 保持顺序
}

struct Bucket<K, V> {
    key: K,
    value: V,
}
```

### 定理 2.1 (双映射)

> IndexMap维护两个不变式:
>
> 1. indices: key → 在entries中的位置
> 2. entries: 按插入顺序存储

**形式化**:

$$
\forall k \in \text{keys}. \exists! i. \text{indices}[k] = i \land \text{entries}[i].\text{key} = k
$$

∎

### 2.2 顺序维护

### 定理 2.2 (插入顺序)

> entries向量保持插入顺序。

```rust
let mut map = IndexMap::new();
map.insert("a", 1);  // entries[0]
map.insert("b", 2);  // entries[1]
map.insert("c", 3);  // entries[2]

// 迭代顺序: a, b, c
for (k, v) in &map {
    println!("{}: {}", k, v);
}
```

∎

---

## 3. 操作复杂度

### 复杂度表

| 操作 | IndexMap | HashMap | BTreeMap |
|------|----------|---------|----------|
| insert | O(1)* | O(1)* | O(log n) |
| get | O(1)* | O(1)* | O(log n) |
| remove | O(n) | O(1)* | O(log n) |
| nth | O(1) | N/A | O(log n) |
| 内存 | 高 | 低 | 中 |

*平均情况

### 定理 3.1 (remove复杂度)

> remove需要O(n)移动entries维护顺序。

```rust
pub fn remove(&mut self, key: &Q) -> Option<V> {
    let idx = self.indices.remove(key)?;  // O(1)
    // 需要移动entries[idx+1..]填补空缺
    let bucket = self.entries.remove(idx);  // O(n)
    // 更新被移动项的indices
    for i in idx..self.entries.len() {
        self.indices.update(&self.entries[i].key, i);
    }
    Some(bucket.value)
}
```

∎

---

## 4. 与HashMap对比

### 定理 4.1 (适用场景)

> 使用IndexMap当需要:
>
> - 确定性迭代顺序
> - 按索引访问
> - JSON序列化顺序
>
> 使用HashMap当需要:
>
> - 最小内存
> - 快速删除
> - 不关心顺序

∎

---

## 5. 反例

### 反例 5.1 (误用retain)

```rust
// retain可能改变顺序期望
map.retain(|k, v| {
    *v > 10  // 过滤条件
});
// 保留的元素保持相对顺序，但需理解语义
```

### 反例 5.2 (容量规划)

```rust
// IndexMap内存开销更高
let map: IndexMap<i32, i32> = IndexMap::with_capacity(1000);
// 需要2倍于HashMap的内存

// 对于只读场景，可考虑:
// 1. 构建后冻结
// 2. 使用Vec + 二分查找
```

---

*文档版本: 1.0.0*
*定理数量: 6个*
