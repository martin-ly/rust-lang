# DashMap 并发HashMap形式化分析

> **主题**: 无锁并发哈希表
>
> **形式化框架**: 分段锁 + 无锁读取
>
> **参考**: DashMap Documentation; Concurrent Hash Tables

---

## 目录

- [DashMap 并发HashMap形式化分析](#dashmap-并发hashmap形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 架构设计](#2-架构设计)
    - [2.1 分段锁](#21-分段锁)
    - [定义 2.1 (Segmented Locking)](#定义-21-segmented-locking)
    - [定理 2.1 (锁分段)](#定理-21-锁分段)
    - [2.2 无锁读取](#22-无锁读取)
    - [定理 2.2 (读取优化)](#定理-22-读取优化)
  - [3. 操作语义](#3-操作语义)
    - [定理 3.1 (并发安全性)](#定理-31-并发安全性)
  - [4. 迭代器一致性](#4-迭代器一致性)
    - [定理 4.1 (弱一致性迭代)](#定理-41-弱一致性迭代)
  - [5. 与RwLock对比](#5-与rwlock对比)
  - [6. 反例](#6-反例)
    - [反例 6.1 (死锁风险)](#反例-61-死锁风险)

---

## 1. 引言

DashMap提供:

- 类似HashMap的API
- 并发安全
- 无锁读取路径
- 细粒度锁(分段)

---

## 2. 架构设计

### 2.1 分段锁

### 定义 2.1 (Segmented Locking)

```rust
pub struct DashMap<K, V> {
    shards: Box<[RwLock<HashMap<K, V>>]>,
    hasher: RandomState,
}
```

**形式化**:

$$
\text{DashMap} = \{ s_1, s_2, ..., s_n \} \text{ 其中每个 } s_i \text{ 是 } RwLock\langle HashMap \rangle
$$

### 定理 2.1 (锁分段)

> 不同key可能映射到不同shard，允许并发修改。

**哈希函数**:

```rust
fn shard_for_key(&self, key: &K) -> usize {
    let hash = self.hasher.hash_one(key);
    hash % self.shards.len()
}
```

**并发度**:

$$
\text{并发度} = \text{shard数量} (默认 = \text{CPU核心数} \times 4)
$$

∎

### 2.2 无锁读取

### 定理 2.2 (读取优化)

> DashMap支持无锁读取(使用读锁)。

**实现**:

```rust
pub fn get<Q>(&self, key: &Q) -> Option<Ref<K, V>>
where
    Q: Hash + Equivalent<K> + ?Sized,
{
    let shard = self.determine_shard(key);
    let guard = self.shards[shard].read();  // 读锁
    // 查找...
}
```

**优点**:

- 多读取者并发
- 不阻塞其他读取者
- 写入者阻塞读取者(短暂)

∎

---

## 3. 操作语义

### 定理 3.1 (并发安全性)

> DashMap操作是线程安全的。

**保证**:

- `get`: 读锁保护
- `insert`: 写锁保护
- `remove`: 写锁保护
- `entry`: 写锁保护

∎

---

## 4. 迭代器一致性

### 定理 4.1 (弱一致性迭代)

> DashMap迭代器反映某一时刻的快照，不反映后续修改。

**说明**:

- 迭代期间允许修改
- 可能看到或看不到并发修改
- 不会panic

∎

---

## 5. 与RwLock对比

| 特性 | DashMap | `RwLock<HashMap>` |
|------|---------|-----------------|
| 锁粒度 | 细(分段) | 粗(整体) |
| 并发度 | 高 | 低 |
| 读取 | 并发 | 并发 |
| 写入 | 分段并发 | 独占 |
| 内存 | 较高 | 较低 |

---

## 6. 反例

### 反例 6.1 (死锁风险)

```rust
// 危险: 嵌套获取
map.entry(key1).and_modify(|v| {
    let other = map.get(key2);  // 可能死锁!
});

// 正确: 先获取所有需要的数据
let val1 = map.get(key1);
let val2 = map.get(key2);
```

---

*文档版本: 1.0.0*
*定理数量: 5个*
