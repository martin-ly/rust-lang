# 并查集

**EN**: Union-Find (Disjoint Set Union)
**Summary**: A forest-based data structure that maintains a partition of elements into disjoint sets and supports near-constant-time union and find operations.

```mermaid
mindmap
  root((Union-Find))
    Definition
      Forest of trees representing disjoint sets
    Core Invariants
      Each element has a parent pointer
      Root is its own parent
      Path compression flattens trees
      Union by rank/size controls height
    Operations
      find O(α(n))
      union O(α(n))
      connected O(α(n))
    Rust Expression
      Vec<usize> parent + Vec<u8> rank
    Pitfalls
      Forgetting mutability
      Off-by-one element IDs
      Not compressing paths
```

> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L5-L6
> **权威来源**: 本文件为 `concept/` 权威页。
> **前置概念**: [`../../../01_foundation/05_collections/01_collections.md`](../../../01_foundation/05_collections/01_collections.md), [`../../../06_ecosystem/16_algorithm_patterns/01_algorithmic_paradigms.md`](../../../06_ecosystem/16_algorithm_patterns/01_algorithmic_paradigms.md), [`../../../04_formal/08_algorithm_semantics/01_hoare_logic_for_rust.md`](../../../04_formal/08_algorithm_semantics/01_hoare_logic_for_rust.md)
> **后置概念**: [`../04_graph_algorithms.md`](./04_graph_algorithms.md), [`../../../06_ecosystem/16_algorithm_patterns/14_network_flow_and_matching.md`](../../../06_ecosystem/16_algorithm_patterns/14_network_flow_and_matching.md), [`../../../06_ecosystem/16_algorithm_patterns/18_competitive_programming_idioms.md`](../../../06_ecosystem/16_algorithm_patterns/18_competitive_programming_idioms.md)

## 一、权威定义

并查集（Union-Find），又称不相交集合（Disjoint Set Union, DSU），维护一个由若干不相交集合组成的划分。每个集合用一棵树表示，树根代表该集合的标识。核心操作：

- **find(x)**：查找 `x` 所在集合的根，同时进行路径压缩（path compression），使树扁平化。
- **union(x, y)**：将 `x` 和 `y` 所在集合合并；通常按秩（rank）或大小合并，以保证树高受控。
- **connected(x, y)**：判断两个元素是否属于同一集合。

## 二、核心属性与关系

1. **父指针数组**：`parent[x]` 表示 `x` 的父节点；若 `parent[x] == x`，则 `x` 是根。
2. **路径压缩**：在 `find` 过程中，将访问过的所有节点直接挂到根下，使后续查询接近 O(1)。
3. **按秩合并（Union by Rank）**：将较矮的树挂到较高的树下，避免树高无节制增长。
4. **按大小合并（Union by Size）**：将较小的树挂到较大的树下，效果与按秩类似。
5. **与图算法的关系**：并查集是 Kruskal 最小生成树算法和动态连通性问题的核心组件。
6. **Ackermann 反函数**：在路径压缩 + 按秩合并的联合作用下，单次操作的均摊时间复杂度为 O(α(n))，其中 α 是反阿克曼函数，实际应用中可视为常数。

## 三、正向推理决策树

```text
需要维护动态分区并频繁判断两个元素是否同集合？
├── 否
│   └── 若只需静态分组，可用 HashMap 或 BTreeMap。
└── 是
    └── 是否需要按顺序遍历集合内所有元素？
        ├── 是 → 并查集不擅长遍历；考虑邻接表或 BFS/DFS。
        └── 否
            ├── 是否需要删除元素？
            │   ├── 是 → 标准并查集不支持删除；考虑支持删除的变体或替换结构。
            │   └── 否 → 使用并查集。
            │       ├── 是否需要可回滚？
            │       │   └── 是 → 使用可持久化/可撤销并查集。
            │       └── 否 → 标准并查集 + 路径压缩 + 按秩合并。
```

## 四、反向推理决策树

```text
并查集结果错误或性能下降？
├── 结果错误
│   ├── 初始化时 parent[i] 是否等于 i？
│   │   └── 否 → 根节点判定失败，connected 结果错误。
│   ├── union 时是否使用了 find 后的根而非原始 x, y？
│   │   └── 否 → 可能把非根节点挂到另一棵树上，破坏结构。
│   └── 元素 ID 是否越界？
│       └── 是 → 增加边界检查或改用 map-based DSU。
└── 性能下降
    ├── 是否启用了路径压缩？
    │   └── 否 → find 会退化为线性。
    ├── 是否使用了按秩/按大小合并？
    │   └── 否 → 树高可能接近 O(n)。
    └── 递归实现的 find 是否导致栈溢出？
        └── 是 → 改用迭代实现。
```

## 五、Rust 表达与示例

下面的实现使用路径压缩和按秩合并，完全基于标准库。

```rust
struct UnionFind {
    parent: Vec<usize>,
    rank: Vec<u8>,
}

impl UnionFind {
    fn new(n: usize) -> Self {
        Self {
            parent: (0..n).collect(),
            rank: vec![0; n],
        }
    }

    fn find(&mut self, x: usize) -> usize {
        let mut root = x;
        while self.parent[root] != root {
            root = self.parent[root];
        }
        // Path compression
        let mut cur = x;
        while self.parent[cur] != root {
            let next = self.parent[cur];
            self.parent[cur] = root;
            cur = next;
        }
        root
    }

    fn union(&mut self, x: usize, y: usize) -> bool {
        let rx = self.find(x);
        let ry = self.find(y);
        if rx == ry {
            return false;
        }
        if self.rank[rx] < self.rank[ry] {
            self.parent[rx] = ry;
        } else if self.rank[rx] > self.rank[ry] {
            self.parent[ry] = rx;
        } else {
            self.parent[ry] = rx;
            self.rank[rx] = self.rank[rx].saturating_add(1);
        }
        true
    }

    fn connected(&mut self, x: usize, y: usize) -> bool {
        self.find(x) == self.find(y)
    }
}

fn main() {
    let mut uf = UnionFind::new(10);
    uf.union(0, 1);
    uf.union(1, 2);
    uf.union(3, 4);

    assert!(uf.connected(0, 2));
    assert!(!uf.connected(0, 3));

    uf.union(2, 3);
    assert!(uf.connected(0, 4));
}
```

## 六、反例与常见错误

### 未声明为可变

`union` 与 `find` 都需要修改 `parent`，因此 `UnionFind` 变量必须是 `mut` 的。否则会触发 `E0596`。

```rust,compile_fail,E0596
struct UnionFind {
    parent: Vec<usize>,
}

impl UnionFind {
    fn new(n: usize) -> Self {
        Self { parent: (0..n).collect() }
    }

    fn union(&mut self, x: usize, y: usize) {
        let _ = (x, y);
    }
}

fn main() {
    let uf = UnionFind::new(10);
    // 错误：uf 不是 mut
    uf.union(0, 1);
}
```

### 忘记路径压缩

```rust
// 错误示例（运行时退化）
// find 只返回根而不更新 parent，导致长链查询退化为 O(n)。
```

### 越界访问

```rust
// 错误示例（运行时 panic）
// let mut uf = UnionFind::new(5);
// uf.find(10); // index out of bounds
```

## 七、复杂度与安全性分析

| 操作 | 均摊时间复杂度 | 最坏时间复杂度 |
|---|---|---|
| `find` | O(α(n)) | O(α(n))（实际应用近似常数） |
| `union` | O(α(n)) | O(α(n)) |
| `connected` | O(α(n)) | O(α(n)) |
| 空间 | O(n) | O(n) |

**安全性**：

- 实现无需 `unsafe`。
- `Vec` 的索引访问在越界时会触发运行时 panic，避免内存越界；若需要更安全的 API，可在 `find`/`union` 入口检查 `x < n`。
- 借用检查器确保在同一作用域内不会出现对 `parent` 与 `rank` 的非法别名。
- `rank` 使用 `saturating_add`，即使 `n` 极大也不会因 `u8` 溢出而破坏结构。

## 八、国际权威来源

- *Introduction to Algorithms* (CLRS), 4th ed. — 第 21 章 Disjoint-Set Forests。
- *The Algorithm Design Manual* (Skiena), 3rd ed. — Union-Find 与最小生成树。
- [cp-algorithms: Disjoint Set Union](https://cp-algorithms.com/data_structures/disjoint_set_union.html) — 并查集优化与扩展。
- [Rust Standard Library: `std::vec::Vec`](https://doc.rust-lang.org/std/vec/struct.Vec.html) — 父指针数组实现。

## 形式化基础

本页的工程模式可追溯到以下 L4 形式化/理论权威页：

- [算法语义与霍尔逻辑](../../../04_formal/08_algorithm_semantics/01_hoare_logic_for_rust.md)
- [算法等价性](../../../04_formal/08_algorithm_semantics/05_algorithm_equivalence.md)
- [形式化算法理论](../../../04_formal/00_type_theory/13_formal_algorithm_theory.md)

## 来源与延伸阅读

- [Concurrent Disjoint Set Union](https://arxiv.org/abs/2003.01203) — P1：并发并查集算法的学术分析。
- [Tarjan, Efficiency of a good but not linear set union algorithm](https://dl.acm.org/doi/10.1145/321879.321884) — P1：经典并查集复杂度理论来源。
- [union-find on crates.io](https://crates.io/crates/union-find) — P2：Rust Union-Find crate。
- [union-find docs on docs.rs](https://docs.rs/union-find/latest/union_find/) — P2：Union-Find API 文档。
- [disjoint-set on crates.io](https://crates.io/crates/disjoint-set) — P2：Tarjan Union-Find 的 Rust 实现。

- [Rust Algorithm Club](https://github.com/weihanglo/rust-algorithm-club)

- [CLRS — Introduction to Algorithms](https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/)

- [Sedgewick & Wayne — Algorithms](https://algs4.cs.princeton.edu/home/)
