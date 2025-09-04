# 算法与数据结构索引（按模块）

- 排序 `sorting`
  - 同步：`sort_sync`
  - 并行：`sort_parallel`
  - 异步：`sort_async`
- 搜索 `searching`
  - 线性：`linear_search_sync` / `linear_search_async`
  - 二分：`binary_search_sync` / `binary_search_async`
  - 并行：`parallel_search`
  - 图：`dfs_sync/bfs_sync` 与 `dfs_async/bfs_async`
  - 指数搜索：`exponential_search_sync/async`
  - 三分搜索（单峰极值）：`ternary_search_max/async`
- 图论 `graph`
  - BFS：`bfs_shortest_path_sync/parallel/async`
  - 最短路：`dijkstra_sync/async`
  - Bellman–Ford：`bellman_ford_sync/async`
  - Floyd–Warshall：`floyd_warshall_sync/async`
  - 最小生成树：`mst_kruskal_sync/parallel/async`, `mst_prim_sync/parallel/async`
  - 拓扑排序：`topo_sort_sync/parallel/async`
  - 强连通分量：`tarjan_scc_sync/async`
  - 最大流：`max_flow_dinic_sync/async`
  - LCA（二叉提升）：`LcaBinaryLift::new` / `lca`
  - 二分图匹配：`hopcroft_karp_sync/async`
- 分治 `divide_and_conquer`
  - 最大子段和：`max_subarray_sum_sync/parallel/async`
  - 最近点对：`closest_pair_sync/parallel/async`
  - 快速幂（模）：`fast_pow_mod/fast_pow_mod_async`
  - 快速矩阵幂：`Matrix::pow_mod` / `matrix_pow_mod_async`
- 动态规划 `dynamic_programming`
  - LCS：`lcs_sync/parallel/async`
  - 0-1 背包：`knapsack_01_sync/parallel/async`
  - LIS（最长上升子序列）：`lis_length_sync/async`
  - 编辑距离（Levenshtein）：`edit_distance_sync/async`
- 回溯 `backtracking`
  - N 皇后：`nqueens_solutions_sync/parallel/async`、`nqueens_count_sync/parallel`
  - 全排列/子集：`permutations_*` / `subsets_*`
- 字符串 `string_algorithms`
  - KMP：`kmp_search` / `kmp_search_async`
  - Rabin-Karp：`rabin_karp_search` / `rabin_karp_search_async`
  - Aho‑Corasick：`build_trie` + `Trie::ac_search` / `ac_search_async`
  - Z‑Algorithm：`z_algorithm` / `z_search[_async]`
  - Suffix Array + Kasai：`suffix_array` / `lcp_kasai`
  - Trie 构建/自动机：`build_trie` / `Trie::ac_search`
  - Manacher：`manacher_longest_palindrome[_async]`
  
— 数据结构 `data_structure`

- Fenwick：`Fenwick::new/add/sum_prefix/range_sum`
- Segment Tree：`SegmentTree::from_slice/update_point/query_sum`
- DSU：`DisjointSet::new/find/union`
- Priority Queue：`PriorityQueue`（`HeapKind::Min/Max`，`build_heap_async`）
- Sparse Table：`SparseTable::build/query_idempotent`
- LRU Cache：`LruCache`（可选 `thread_safe` 特性暴露并发版本）

- 计算几何 `geometry`
  - 凸包：`convex_hull`
  - 旋转卡壳直径：`rotating_calipers_diameter2`

- 数论 `number_theory`
  - 快速幂：`fast_pow_mod`
  - 扩展欧几里得/模逆：`egcd` / `mod_inv`
  - 素性测试：`is_prime`（Miller–Rabin）
  - 因式分解：`pollard_rho`

备注：异步接口多为 CPU 密集算法的 `spawn_blocking` 包装，主要用于在异步应用中解耦阻塞；纯计算任务推荐优先使用同步/并行版本。
