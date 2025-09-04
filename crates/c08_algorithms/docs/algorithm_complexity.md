# 算法复杂度与性能评估（Rust 1.89 对齐）

本页参考国际百科的经典复杂度结论，对齐本仓库实现，给出时间/空间复杂度与入口链接，并提示并行/异步包装的性能特征。V 表示顶点数，E 表示边数，p 表示并行线程数。

---

## 排序（`src/sorting/mod.rs`）

- 快速排序：时间 O(n log n) 平均 / O(n²) 最坏，空间 O(log n)（递归栈）
- 归并排序：时间 O(n log n)，空间 O(n)
- 堆排序：时间 O(n log n)，空间 O(1)
- 并行：Rayon `par_sort`/`par_sort_unstable`，对大数据集在多核环境近似获得 ~O(n log n / p)
- 异步：Tokio `spawn_blocking` 包装，不改善纯 CPU 复杂度，仅改善异步上下文中的调度与延迟

实现入口：`sort_sync` / `sort_parallel` / `sort_async`

---

## 搜索（`src/searching/mod.rs`）

- 线性搜索：时间 O(n)，空间 O(1)
- 二分搜索（已排序）：时间 O(log n)，空间 O(1)
- 并行线性搜索：近似 O(n / p)，上界仍为 O(n)
- 异步包装：`linear_search_async`、`binary_search_async` 使用 `spawn_blocking`

实现入口：`linear_search_sync/async`、`binary_search_sync/async`、`parallel_search`

---

## 图论（`src/graph/mod.rs`）

- BFS 最短路径：时间 O(V+E)，空间 O(V)
- Dijkstra（非负权）：时间 O((V+E) log V)，空间 O(V)
- MST（Kruskal）：排序 O(E log E) + 并查集近似 α(V)
- MST（Prim，二叉堆）：O(E log V)
- 拓扑排序（Kahn）：O(V+E)

并行/异步说明：

- BFS 并行主要体现在按层展开的 frontier 构造；全并行化受限于数据依赖
- Dijkstra/MST 的核心堆操作不易并行，仅对边收集/初始化做并行化有边际收益
- 所有异步函数（如 `bfs_shortest_path_async`, `dijkstra_async` 等）采用 `spawn_blocking` 包装

---

## 分治与动态规划（目录占位）

- 最大子段和：O(n)，可做分块并行归并；
- 最近点对：O(n log n)（分治）；
- LCS：O(n·m)；0-1 背包：O(n·C) 或 O(C)（滚动数组）；

实现路径：`src/divide_and_conquer/`、`src/dynamic_programming/`（逐步补全）。

---

## 字符串算法（`src/string_algorithms/mod.rs`）

- KMP：时间 O(n + m)，空间 O(m)，其中 n 为文本长度、m 为模式长度；通过前缀函数避免回退
- Rabin-Karp：期望时间 O(n + m)，最坏 O(n·m)；空间 O(1)；通过滚动哈希做快速筛选（碰撞需二次比较）

并行/异步说明：

- 当前实现提供 `kmp_search_async` 与 `rabin_karp_search_async` 的异步包装（`spawn_blocking`），便于在异步上下文中调度

实现入口：`kmp_search` / `rabin_karp_search` 及其 `*_async`

---

## 基准

运行：

```bash
cargo bench --bench alg_benches
```

建议在 `--release` 下对比同步/并行/异步包装的延迟差异，并结合 `tracing` 分析热点。

更多 Rust 1.89 特性说明：见 `docs/rust_189_features.md`。
