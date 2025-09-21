# Rust 1.89 算法与数据结构完整索引

**版本**: 0.2.0  
**Rust版本**: 1.89.0+  
**更新日期**: 2025年1月27日  

## 📚 目录

- [Rust 1.89 算法与数据结构完整索引](#rust-189-算法与数据结构完整索引)

---

## 🚀 核心算法模块

### 1. 排序算法 (`sorting`)

| 算法 | 时间复杂度 | 空间复杂度 | 稳定性 | 同步 | 并行 | 异步 |
|------|------------|------------|--------|------|------|------|
| 快速排序 | O(n log n) | O(log n) | ❌ | ✅ | ✅ | ✅ |
| 归并排序 | O(n log n) | O(n) | ✅ | ✅ | ✅ | ✅ |
| 堆排序 | O(n log n) | O(1) | ❌ | ✅ | ✅ | ✅ |
| 希尔排序 | O(n^1.3) | O(1) | ❌ | ✅ | ✅ | ✅ |
| 计数排序 | O(n+k) | O(k) | ✅ | ✅ | ✅ | ✅ |
| 基数排序 | O(d(n+k)) | O(n+k) | ✅ | ✅ | ✅ | ✅ |
| 桶排序 | O(n+k) | O(n+k) | ✅ | ✅ | ✅ | ✅ |

**核心接口**:

```rust
use c08_algorithms::sorting::{sort_sync, sort_parallel, sort_async, SortingAlgo};

// 同步排序
let mut data = vec![3, 1, 4, 1, 5];
sort_sync(&mut data, SortingAlgo::Quick);

// 并行排序
sort_parallel(&mut data, SortingAlgo::Merge);

// 异步排序
let sorted = sort_async(data, SortingAlgo::Heap).await?;
```

### 2. 搜索算法 (`searching`)

| 算法 | 时间复杂度 | 空间复杂度 | 适用场景 | 同步 | 并行 | 异步 |
|------|------------|------------|----------|------|------|------|
| 线性搜索 | O(n) | O(1) | 无序数组 | ✅ | ✅ | ✅ |
| 二分搜索 | O(log n) | O(1) | 有序数组 | ✅ | ❌ | ✅ |
| 指数搜索 | O(log n) | O(1) | 有序数组 | ✅ | ❌ | ✅ |
| 插值搜索 | O(log log n) | O(1) | 均匀分布 | ✅ | ❌ | ✅ |
| 跳跃搜索 | O(√n) | O(1) | 有序数组 | ✅ | ❌ | ✅ |
| 三分搜索 | O(log n) | O(1) | 单峰函数 | ✅ | ❌ | ✅ |

**核心接口**:

```rust
use c08_algorithms::searching::{
    linear_search_sync, binary_search_sync, parallel_search,
    linear_search_async, binary_search_async
};

// 同步搜索
let pos = linear_search_sync(&data, &target);
let pos = binary_search_sync(&sorted_data, &target)?;

// 并行搜索
let pos = parallel_search(&data, &target);

// 异步搜索
let pos = linear_search_async(data, target).await?;
```

### 3. 图算法 (`graph`)

| 算法 | 时间复杂度 | 空间复杂度 | 适用场景 | 同步 | 并行 | 异步 |
|------|------------|------------|----------|------|------|------|
| BFS | O(V+E) | O(V) | 最短路径 | ✅ | ✅ | ✅ |
| DFS | O(V+E) | O(V) | 图遍历 | ✅ | ❌ | ✅ |
| Dijkstra | O((V+E)log V) | O(V) | 单源最短路径 | ✅ | ❌ | ✅ |
| Bellman-Ford | O(VE) | O(V) | 负权边 | ✅ | ❌ | ✅ |
| Floyd-Warshall | O(V³) | O(V²) | 多源最短路径 | ✅ | ❌ | ✅ |
| Kruskal MST | O(E log E) | O(V) | 最小生成树 | ✅ | ✅ | ✅ |
| Prim MST | O((V+E)log V) | O(V) | 最小生成树 | ✅ | ✅ | ✅ |
| 拓扑排序 | O(V+E) | O(V) | DAG排序 | ✅ | ✅ | ✅ |
| 强连通分量 | O(V+E) | O(V) | 有向图 | ✅ | ❌ | ✅ |
| 最大流(Dinic) | O(V²E) | O(V+E) | 网络流 | ✅ | ❌ | ✅ |
| 二分图匹配 | O(√VE) | O(V+E) | 最大匹配 | ✅ | ❌ | ✅ |

**核心接口**:

```rust
use c08_algorithms::graph::{
    bfs_shortest_path_sync, dijkstra_sync, mst_kruskal_sync,
    bfs_shortest_path_async, dijkstra_async, mst_kruskal_async
};

// 同步图算法
let path = bfs_shortest_path_sync(&graph, &start, &target);
let (dist, prev) = dijkstra_sync(&weighted_graph, &start);
let (weight, mst) = mst_kruskal_sync(&graph);

// 异步图算法
let path = bfs_shortest_path_async(graph, start, target).await?;
let (dist, prev) = dijkstra_async(graph, start).await?;
```

### 4. 动态规划 (`dynamic_programming`)

| 算法 | 时间复杂度 | 空间复杂度 | 适用场景 | 同步 | 并行 | 异步 |
|------|------------|------------|----------|------|------|------|
| 最长公共子序列 | O(mn) | O(mn) | 序列比对 | ✅ | ✅ | ✅ |
| 0-1背包 | O(nW) | O(W) | 资源分配 | ✅ | ✅ | ✅ |
| 最长上升子序列 | O(n log n) | O(n) | 序列分析 | ✅ | ❌ | ✅ |
| 编辑距离 | O(mn) | O(min(m,n)) | 字符串相似度 | ✅ | ❌ | ✅ |
| 加权区间调度 | O(n log n) | O(n) | 任务调度 | ✅ | ❌ | ❌ |
| 矩阵链乘法 | O(n³) | O(n²) | 优化计算 | ✅ | ❌ | ❌ |
| 石子合并 | O(n³) | O(n²) | 区间DP | ✅ | ❌ | ❌ |

**核心接口**:

```rust
use c08_algorithms::dynamic_programming::{
    lcs_sync, knapsack_01_sync, lis_length_sync,
    lcs_async, knapsack_01_async, lis_length_async
};

// 同步DP
let lcs_len = lcs_sync(&seq1, &seq2);
let max_value = knapsack_01_sync(&weights, &values, capacity);
let lis_len = lis_length_sync(&sequence);

// 异步DP
let lcs_len = lcs_async(seq1, seq2).await?;
let max_value = knapsack_01_async(weights, values, capacity).await?;
```

### 5. 分治算法 (`divide_and_conquer`)

| 算法 | 时间复杂度 | 空间复杂度 | 适用场景 | 同步 | 并行 | 异步 |
|------|------------|------------|----------|------|------|------|
| 最大子段和 | O(n) | O(1) | 数组分析 | ✅ | ✅ | ✅ |
| 最近点对 | O(n log n) | O(n) | 几何计算 | ✅ | ✅ | ✅ |
| 快速幂 | O(log n) | O(1) | 幂运算 | ✅ | ❌ | ✅ |
| 矩阵快速幂 | O(log n) | O(n²) | 线性递推 | ✅ | ❌ | ✅ |
| Quickselect | O(n) | O(1) | 第k小元素 | ✅ | ❌ | ❌ |
| Karatsuba乘法 | O(n^log₂3) | O(n) | 大数乘法 | ✅ | ❌ | ❌ |

**核心接口**:

```rust
use c08_algorithms::divide_and_conquer::{
    max_subarray_sum_sync, closest_pair_sync, fast_pow_mod,
    max_subarray_sum_async, closest_pair_async, fast_pow_mod_async
};

// 同步分治
let max_sum = max_subarray_sum_sync(&array);
let min_dist = closest_pair_sync(points);
let result = fast_pow_mod(base, exp, modulus);

// 异步分治
let max_sum = max_subarray_sum_async(array).await?;
let min_dist = closest_pair_async(points).await?;
```

### 6. 字符串算法 (`string_algorithms`)

| 算法 | 时间复杂度 | 空间复杂度 | 适用场景 | 同步 | 并行 | 异步 |
|------|------------|------------|----------|------|------|------|
| KMP | O(n+m) | O(m) | 单模式匹配 | ✅ | ❌ | ✅ |
| Rabin-Karp | O(n+m) | O(1) | 滚动哈希 | ✅ | ❌ | ✅ |
| Aho-Corasick | O(n+m+z) | O(m) | 多模式匹配 | ✅ | ❌ | ✅ |
| Z-Algorithm | O(n+m) | O(n+m) | 前缀匹配 | ✅ | ❌ | ✅ |
| 后缀数组 | O(n log n) | O(n) | 字符串分析 | ✅ | ❌ | ❌ |
| Manacher | O(n) | O(n) | 最长回文 | ✅ | ❌ | ✅ |
| Boyer-Moore-Horspool | O(nm) | O(σ) | 子串搜索 | ✅ | ❌ | ✅ |
| 后缀自动机 | O(n) | O(n) | 字符串处理 | ✅ | ❌ | ✅ |

**核心接口**:

```rust
use c08_algorithms::string_algorithms::{
    kmp_search, rabin_karp_search, ac_search_async,
    z_search, manacher_longest_palindrome, bmh_search
};

// 同步字符串算法
let positions = kmp_search(text, pattern);
let positions = rabin_karp_search(text, pattern);
let (start, length) = manacher_longest_palindrome(text);

// 异步字符串算法
let positions = ac_search_async(text, patterns).await?;
```

### 7. 回溯算法 (`backtracking`)

| 算法 | 时间复杂度 | 空间复杂度 | 适用场景 | 同步 | 并行 | 异步 |
|------|------------|------------|----------|------|------|------|
| N皇后 | O(N!) | O(N) | 约束满足 | ✅ | ✅ | ✅ |
| 全排列 | O(n!) | O(n) | 排列生成 | ✅ | ✅ | ✅ |
| 子集生成 | O(2ⁿ) | O(n) | 组合生成 | ✅ | ✅ | ✅ |

**核心接口**:

```rust
use c08_algorithms::backtracking::{
    nqueens_solutions_sync, permutations_sync, subsets_sync,
    nqueens_solutions_async, permutations_async, subsets_async
};

// 同步回溯
let solutions = nqueens_solutions_sync(8);
let perms = permutations_sync(vec![1, 2, 3]);
let subs = subsets_sync(&[1, 2, 3]);

// 异步回溯
let solutions = nqueens_solutions_async(8).await?;
let perms = permutations_async(vec![1, 2, 3]).await?;
```

### 8. 贪心算法 (`greedy`)

| 算法 | 时间复杂度 | 空间复杂度 | 适用场景 | 同步 | 并行 | 异步 |
|------|------------|------------|----------|------|------|------|
| 区间调度 | O(n log n) | O(n) | 任务调度 | ✅ | ✅ | ✅ |
| 零钱兑换 | O(n) | O(1) | 货币系统 | ✅ | ✅ | ✅ |
| 分数背包 | O(n log n) | O(1) | 资源分配 | ✅ | ✅ | ✅ |
| Huffman编码 | O(n log n) | O(n) | 数据压缩 | ✅ | ❌ | ✅ |
| 作业排序 | O(n log n) | O(n) | 任务调度 | ✅ | ❌ | ❌ |

**核心接口**:

```rust
use c08_algorithms::greedy::{
    interval_scheduling_sync, coin_change_greedy_sync,
    fractional_knapsack_sync, huffman_build_codes
};

// 同步贪心
let intervals = interval_scheduling_sync(intervals);
let coins = coin_change_greedy_sync(coin_types, amount);
let max_value = fractional_knapsack_sync(items, capacity);
let (codes, tree) = huffman_build_codes(text);
```

---

## 🏗️ 数据结构实现

### 1. 基础数据结构 (`data_structure`)

| 数据结构 | 时间复杂度 | 空间复杂度 | 特性 |
|----------|------------|------------|------|
| 栈 (Stack) | O(1) | O(n) | LIFO |
| 优先队列 (PriorityQueue) | O(log n) | O(n) | 堆实现 |
| 并查集 (UnionFind) | O(α(n)) | O(n) | 路径压缩 |
| 线段树 (SegmentTree) | O(log n) | O(n) | 区间查询 |
| 树状数组 (FenwickTree) | O(log n) | O(n) | 前缀和 |
| 稀疏表 (SparseTable) | O(1) | O(n log n) | RMQ |
| LRU缓存 (LRUCache) | O(1) | O(n) | 最近使用 |

### 2. 高级数据结构

| 数据结构 | 时间复杂度 | 空间复杂度 | 特性 |
|----------|------------|------------|------|
| 重链剖分 (HLD) | O(log n) | O(n) | 树链查询 |
| 后缀自动机 (SAM) | O(n) | O(n) | 字符串处理 |
| Trie树 | O(m) | O(σ×m) | 前缀匹配 |
| Aho-Corasick自动机 | O(n+m+z) | O(m) | 多模式匹配 |

---

## ⚡ 同步/异步/并行接口

### 接口设计原则

1. **同步接口**: 直接调用，适用于小规模数据
2. **并行接口**: 使用 `rayon` 进行 CPU 密集型并行计算
3. **异步接口**: 使用 `tokio::spawn_blocking` 包装 CPU 密集型任务

### 性能对比

| 算法类型 | 同步 | 并行 | 异步 | 推荐场景 |
|----------|------|------|------|----------|
| 排序算法 | ✅ | ✅ | ✅ | 大数据集用并行，IO密集用异步 |
| 搜索算法 | ✅ | ✅ | ✅ | 线性搜索用并行，二分搜索用同步 |
| 图算法 | ✅ | ✅ | ✅ | 大图用异步，小图用同步 |
| 动态规划 | ✅ | ✅ | ✅ | 大问题用异步，小问题用同步 |
| 字符串算法 | ✅ | ❌ | ✅ | 长文本用异步，短文本用同步 |

---

## 📊 性能基准测试

### 运行基准测试

```bash
# 运行所有基准测试
cargo bench --bench alg_benches

# 运行特定算法基准
cargo bench --bench alg_benches -- sorting

# 生成性能报告
cargo run --bin bench_report > performance_report.csv
```

### 基准测试覆盖

- **排序算法**: 不同数据规模的性能对比
- **搜索算法**: 不同搜索策略的效率对比
- **图算法**: 不同图规模的性能分析
- **字符串算法**: 不同模式长度的匹配性能
- **并行vs同步**: 多核性能提升分析

---

## 💡 使用示例

### 完整示例：排序算法对比

```rust
use c08_algorithms::sorting::{sort_sync, sort_parallel, sort_async, SortingAlgo};
use std::time::Instant;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 生成测试数据
    let mut data = (0..1_000_000).rev().collect::<Vec<i32>>();
    
    // 同步排序
    let start = Instant::now();
    sort_sync(&mut data, SortingAlgo::Quick);
    println!("同步快速排序: {:?}", start.elapsed());
    
    // 并行排序
    let start = Instant::now();
    sort_parallel(&mut data, SortingAlgo::Merge);
    println!("并行归并排序: {:?}", start.elapsed());
    
    // 异步排序
    let start = Instant::now();
    let _sorted = sort_async(data, SortingAlgo::Heap).await?;
    println!("异步堆排序: {:?}", start.elapsed());
    
    Ok(())
}
```

### 图算法示例：最短路径

```rust
use c08_algorithms::graph::{dijkstra_sync, bfs_shortest_path_async};
use std::collections::HashMap;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 构建加权图
    let mut graph: HashMap<&str, Vec<(&str, f64)>> = HashMap::new();
    graph.insert("A", vec![("B", 1.0), ("C", 4.0)]);
    graph.insert("B", vec![("C", 2.0), ("D", 5.0)]);
    graph.insert("C", vec![("D", 1.0)]);
    graph.insert("D", vec![]);
    
    // 同步Dijkstra
    let (distances, predecessors) = dijkstra_sync(&graph, &"A");
    println!("从A到各点的最短距离: {:?}", distances);
    
    // 异步BFS
    let mut unweighted_graph: HashMap<&str, Vec<&str>> = HashMap::new();
    unweighted_graph.insert("A", vec!["B", "C"]);
    unweighted_graph.insert("B", vec!["D"]);
    unweighted_graph.insert("C", vec!["D"]);
    unweighted_graph.insert("D", vec![]);
    
    let path = bfs_shortest_path_async(
        unweighted_graph, "A", "D"
    ).await?;
    println!("从A到D的最短路径: {:?}", path);
    
    Ok(())
}
```

---

## 🚀 Rust 1.89 特性应用

### 1. 异步特性增强

- **Async Traits**: 在算法接口中使用异步特征
- **异步迭代器**: 用于流式算法处理
- **异步闭包**: 简化异步算法实现

### 2. 类型系统改进

- **GATs (Generic Associated Types)**: 用于泛型算法设计
- **常量泛型**: 编译时算法优化
- **生命周期推断**: 减少显式生命周期标注

### 3. 性能优化

- **零成本抽象**: 算法实现无运行时开销
- **内存布局优化**: 提高缓存局部性
- **SIMD支持**: 向量化算法加速

### 4. 现代Rust惯用法

- **2024 Edition**: 使用最新的语言特性
- **错误处理**: 使用 `anyhow` 和 `thiserror`
- **日志记录**: 使用 `tracing` 进行性能监控

---

## 📈 性能优化建议

### 1. 算法选择

- **小数据集**: 使用同步算法
- **大数据集**: 使用并行算法
- **IO密集型**: 使用异步算法

### 2. 内存优化

- 使用 `Vec::with_capacity` 预分配内存
- 避免不必要的内存拷贝
- 使用 `Box<[T]>` 替代 `Vec<T>` 当大小固定时

### 3. 并行优化

- 合理设置线程池大小
- 避免过度并行化
- 使用 `rayon` 进行数据并行

### 4. 异步优化

- 使用 `tokio::spawn_blocking` 包装CPU密集型任务
- 避免在异步上下文中进行阻塞操作
- 合理使用 `async/await`

---

## 🔧 配置和特性

### Cargo.toml 特性

```toml
[features]
default = []
bench = ["criterion"]
with-petgraph = ["petgraph"]
with-aho = ["aho-corasick"]
```

### 依赖管理

- **并行计算**: `rayon`
- **异步运行时**: `tokio`
- **错误处理**: `anyhow`, `thiserror`
- **日志记录**: `tracing`
- **基准测试**: `criterion`
- **可选集成**: `petgraph`, `aho-corasick`

---

## 📚 扩展阅读

- [算法复杂度分析](algorithm_complexity.md)
- [数据结构实现](data_structures.md)
- [异步算法指南](async_algorithms.md)
- [性能优化技巧](performance_optimization.md)
- [基准测试指南](benchmarking_guide.md)
- [Rust 1.89 特性应用](rust_189_features.md)

---

**最后更新**: 2025年1月27日  
**Rust版本**: 1.89.0  
**项目状态**: 🟢 活跃开发中
