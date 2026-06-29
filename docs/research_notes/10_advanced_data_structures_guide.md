# 高级数据结构指南：Treap（树堆）与 Skip List（跳表）

> **概念族**: 算法 / 高级数据结构
>
> **层级**: L3-L5
> **Bloom 层级**: L3-L5（应用 / 分析 / 评价）
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **权威来源**:
>
> [CLRS – Introduction to Algorithms](https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/) |
> [William Pugh, Skip Lists: A Probabilistic Alternative to Balanced Trees](https://dl.acm.org/doi/10.1145/78973.78977) |
> [Seidel & Aragon, Randomized Search Trees](https://dl.acm.org/doi/10.1145/138403.138440) |
> [Rust Standard Library](https://doc.rust-lang.org/std/)

---

## 1. 为什么需要 Treap 与跳表

二叉搜索树（BST）在最坏情况下会退化为链表，导致 O(n) 的操作代价。
自平衡树（如 AVL、红黑树）通过旋转维持严格的高度上界，但实现复杂、边界情况多。

Treap 与跳表提供了一种**基于随机化的期望平衡**方案：

- **Treap** 将 BST 与堆结合，利用随机优先级隐式地保持平衡，期望高度 O(log n)。
- **Skip List** 用多层概率链表模拟二分搜索，代码简单、锁友好，是工业界常用的有序索引结构。

两者都在期望意义上达到 O(log n) 的查找/插入/删除，且实现复杂度远低于确定性平衡树。

---

## 2. Treap（树堆）

### 2.1 核心思想

Treap = **Tree（BST 按 key）+ Heap（按随机 priority）**。

每个节点保存 `(key, priority)`：

- 按 `key` 满足二叉搜索树性质。
- 按 `priority` 满足堆性质（通常为大根堆）。

由于优先级随机，树的期望形态等价于随机 BST，期望高度为 O(log n)。

### 2.2 插入与删除

- **插入**：沿 key 走到叶子插入新节点，然后沿父链旋转，直到堆性质恢复。
- **删除**：将目标节点旋转到叶子（每次与优先级更高的子节点旋转），然后直接摘除。

额外维护子树大小 `size` 后，可支持**顺序统计**：

- `kth(k)`：升序第 k 个元素。
- `rank(key)`：小于 key 的元素个数。

### 2.3 时间复杂度

| 操作 | 期望 | 最坏（概率极低） |
|------|------|------------------|
| 查找 | O(log n) | O(n) |
| 插入 | O(log n) | O(n) |
| 删除 | O(log n) | O(n) |
| kth / rank | O(log n) | O(n) |
| 空间 | O(n) | O(n) |

> 期望高度的严格证明基于随机优先级诱导的随机 BST 分布。

---

## 3. Skip List（跳表）

### 3.1 核心思想

在有序链表之上建立多层“快速通道”。
每个节点以概率 `p`（通常 0.5）决定拥有的层数，层数期望为 `1/(1-p)`，总节点数期望为 `O(n)`。

搜索时从顶层向右、向下移动，跳跃过大量中间节点，期望比较次数 O(log n)。

### 3.2 插入与删除

- **插入**：先确定新节点层数，再在各层找到插入位置并调整 forward 指针。
- **删除**：在各层找到前驱，跳过目标节点。

### 3.3 范围查询

跳表天然支持有序遍历。通过在第 0 层找到下界，然后顺序收集直到超过上界，即可实现 `O(log n + k)` 的范围查询。

### 3.4 时间复杂度

| 操作 | 期望 | 最坏（概率极低） |
|------|------|------------------|
| 查找 | O(log n) | O(n) |
| 插入 | O(log n) | O(n) |
| 删除 | O(log n) | O(n) |
| 范围查询 | O(log n + k) | O(n) |
| 空间 | O(n) | O(n) |

> 当 `p = 0.5` 时，跳表期望层数为 `log_{1/p} n = log_2 n`，与平衡树同阶。

---

## 4. Rust 实现要点

### 4.1 Treap

- 使用 `Box<Node>` 表达父子关系，避免裸指针并享受 Rust 所有权安全。
- 旋转后必须重新计算子树大小 `size`。
- 删除时先判断存在性，避免无意义的旋转路径。
- 重复键按集合语义忽略，或改为 multiset 需要额外计数器。

### 4.2 Skip List

- 使用 **arena 索引**（`Vec<Node>` + `usize`）而非 `Box`/`Rc`，避免复杂的借用链。
- 用 `usize::MAX` 作为 NIL 哨兵。
- `rand::Rng::random` 生成 `[0,1)` 浮点数决定层数。
- 范围查询利用底层有序链表，避免额外数据结构。

---

## 5. 反例与边界

### 5.1 Treap：非随机优先级导致退化

若所有节点优先级单调递增（例如插入顺序与优先级同序），Treap 会退化为链表，操作最坏 O(n)。
**必须保证 priority 随机且独立**。

### 5.2 Treap：重复键的语义选择

默认集合语义会忽略重复插入；若业务需要 multiset，应增加 `count` 字段，否则 `len()` 与 `delete()` 行为会出错。

### 5.3 Skip List：概率参数 `p` 的极端取值

- `p` 过大（接近 1）：层数期望高，空间浪费，但搜索跳跃次数少。
- `p` 过小（接近 0）：层数低，退化为普通链表，搜索变慢。
通常取 `p = 0.5` 作为空间与时间的折中。

### 5.4 Skip List：max_level 设置不足

当数据量远超 `max_level` 时，跳表失去多层加速效果，退化为接近链表。
应根据预期数据量设置 `max_level`，典型值为 `16`（可支持 2^16 ≈ 6.5 万节点，实际因概率分布可支撑更多）。

### 5.5 随机数源与可重复性

测试中使用确定性优先级可保证可重复性；生产环境应使用密码学安全或高质量伪随机数源，并注意 seeded RNG 的线程安全。

---

## 6. 代码实现锚点

本项目实现位于 `crates/c08_algorithms`：

| 数据结构 | 实现文件 | 示例 |
|----------|----------|------|
| Treap | [crates/c08_algorithms/src/data_structure/treap.rs](../../crates/c08_algorithms/src/data_structure/treap.rs) | [treap_skip_list_demo.rs](../../crates/c08_algorithms/examples/treap_skip_list_demo.rs) |
| Skip List | [crates/c08_algorithms/src/data_structure/skip_list.rs](../../crates/c08_algorithms/src/data_structure/skip_list.rs) | [treap_skip_list_demo.rs](../../crates/c08_algorithms/examples/treap_skip_list_demo.rs) |

---

## 7. 权威来源分级（P0 / P1 / P2）

- **P0（原始论文/官方实现）**:
  - [William Pugh, 1989 – Skip Lists: A Probabilistic Alternative to Balanced Trees](https://dl.acm.org/doi/10.1145/78973.78977)
  - [Seidel & Aragon, 1996 – Randomized Search Trees](https://dl.acm.org/doi/10.1145/138403.138440)
  - [CLRS – Introduction to Algorithms](https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/)

- **P1（经典教材/百科/权威博客）**:
  - [Wikipedia – Treap](https://en.wikipedia.org/wiki/Treap)
  - [Wikipedia – Skip list](https://en.wikipedia.org/wiki/Skip_list)
  - [Open Data Structures – Skiplist](http://opendatastructures.org/)

- **P2（社区实现/教学资料）**:
  - [Rust Standard Library – BTreeMap](https://doc.rust-lang.org/std/collections/struct.BTreeMap.html)
  - [crates.io – skiplist crate](https://crates.io/crates/skiplist)
  - [Algorithmica – Treap & Order Statistics](https://cp-algorithms.com/data_structures/treap.html)

---

## 8. 小结

| 数据结构 | 核心优势 | 主要劣势 | 典型场景 |
|----------|----------|----------|----------|
| Treap | 支持顺序统计、实现简洁、期望平衡 | 最坏 O(n)（概率极低）、需要随机源 | 动态顺序维护、线段树替代 |
| Skip List | 代码简单、锁友好、天然支持范围查询 | 最坏 O(n)（概率极低）、空间开销略高 | 数据库索引、日志存储、并发有序集合 |

Treap 与跳表共同展示了**随机化**在算法设计中的力量：
用概率换取实现的简洁性，同时在实践中保持优异性能。

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
