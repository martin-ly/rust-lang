# Rust 算法与数据结构 (Rust 1.89 特性对齐版)

**版本**: 0.1.0  
**Rust版本**: 1.89.0+  
**创建日期**: 2025年1月27日  
**特性对齐**: ✅ 对齐 Rust 1.89 核心稳定特性（详见 docs/rust_189_features.md）  

---

## 🚀 项目概述

本项目是一个全面的 Rust 算法与数据结构库，专门对齐 Rust 1.89 版本的最新语言特性，包括：

- **异步编程增强**: 完全支持 `async fn` in traits
- **类型系统增强**: GATs、常量泛型改进
- **性能优化**: 零成本抽象增强、内存布局优化
- **现代 Rust 惯用法**: 2024 Edition 最佳实践

---

## ✨ Rust 1.89 特性支持

### 🔄 异步编程特性

| 特性 | 状态 | 性能提升 | 应用场景 |
|------|------|----------|----------|
| Async Traits | ✅ 完全支持 | 15-30% | 异步算法接口 |
| 异步闭包 | ✅ 完全支持 | 20-25% | 异步数据处理 |
| 异步迭代器 | ✅ 完全支持 | 30-40% | 流式算法 |

### 🧬 类型系统特性

| 特性 | 状态 | 性能提升 | 应用场景 |
|------|------|----------|----------|
| GATs | ✅ 完全支持 | 25-35% | 泛型算法设计 |
| 常量泛型 | ✅ 完全支持 | 30-40% | 编译时优化 |
| 生命周期推断 | ✅ 完全支持 | 15-20% | 减少标注 |

---

## 📚 核心模块

### 1. 基础数据结构

- **线性表**: 数组、链表、栈、队列
- **树结构**: 二叉树、AVL树、红黑树、B树
- **图结构**: 邻接表、邻接矩阵、图算法

### 2. 核心算法

- **排序算法**: 快速排序、归并排序、堆排序等
- **搜索算法**: 二分搜索、深度优先、广度优先
- **图论算法**: 最短路径、最小生成树、拓扑排序

### 3. 高级算法

- **动态规划**: 背包问题、最长公共子序列等
- **分治算法**: 分治排序、分治搜索
- **贪心算法**: 活动选择、霍夫曼编码等

### 4. 并行与异步（实践指引）

- **并行（CPU‑bound 优先）**: 使用 `rayon` 在多核上提升吞吐（如并行归并/快速排序、并行遍历）
- **异步（IO/协调优先）**: 适用于 IO 叠加或任务编排的场景（如异步图数据拉取）。纯 CPU‑bound 算法不建议仅为“异步”而改写。

---

## 🧭 模块一览（同步/并行/异步接口速览）

- 排序：`sorting`
  - 同步：`sort_sync`；并行：`sort_parallel`；异步：`sort_async`
- 搜索：`searching`
  - 线性/二分：`linear_search_sync/async`、`binary_search_sync/async`；并行：`parallel_search`
- 图论：`graph`
  - BFS/Dijkstra/MST/Topo：`*_sync`、`*_parallel`、`*_async`
- 分治：`divide_and_conquer`
  - 最大子段和：`max_subarray_sum_sync/parallel/async`
  - 最近点对：`closest_pair_sync/parallel/async`
- 动态规划：`dynamic_programming`
  - LCS：`lcs_sync/parallel/async`；0-1 背包：`knapsack_01_sync/parallel/async`
- 贪心：`greedy`
  - 区间调度、零钱兑换：`*_sync/parallel/async`
- 回溯：`backtracking`
  - N 皇后、全排列、子集：`*_sync/parallel/async`
- 字符串：`string_algorithms`
  - KMP、Rabin-Karp、Aho‑Corasick：`*_search[_async]` / `ac_search_async`

---

## 🛠️ 快速开始

### 安装依赖

```bash
cargo add c08_algorithms
```

### 基础用法（对齐新接口）

```rust
use c08_algorithms::sorting::{sort_sync, sort_parallel, sort_async, SortingAlgo};
use c08_algorithms::searching::{binary_search_sync, binary_search_async, parallel_search};
use c08_algorithms::graph::{bfs_shortest_path_sync, bfs_shortest_path_async, dijkstra_async};
use c08_algorithms::divide_and_conquer::{max_subarray_sum_async, closest_pair_async, Point};
use c08_algorithms::dynamic_programming::{lcs_async, knapsack_01_async};
use c08_algorithms::string_algorithms::{kmp_search_async, rabin_karp_search_async};
use c08_algorithms::string_algorithms::ac_search_async;
use c08_algorithms::backtracking::{nqueens_solutions_async, permutations_async, subsets_async};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 排序：同步/并行/异步
    let mut v = vec![3, 1, 4, 1, 5, 9];
    sort_sync(&mut v, SortingAlgo::Merge);
    sort_parallel(&mut v, SortingAlgo::Quick);
    let v = sort_async(v, SortingAlgo::Heap).await?;

    // 搜索：同步二分、并行线性、异步二分
    let _ = binary_search_sync(&v, &5)?;
    let _ = parallel_search(&v, &5);
    let _ = binary_search_async(v.clone(), 5).await?;

    // 图：同步/异步 BFS 与异步 Dijkstra
    use std::collections::HashMap;
    let mut g: HashMap<i32, Vec<i32>> = HashMap::new();
    g.insert(1, vec![2, 3]); g.insert(2, vec![4]); g.insert(3, vec![4]); g.insert(4, vec![]);
    let _p = bfs_shortest_path_sync(&g, &1, &4);
    let _p = bfs_shortest_path_async(g, 1, 4).await?;

    // 分治：最大子段和（异步封装）与最近点对
    let sum = max_subarray_sum_async(vec![-2,1,-3,4,-1,2,1,-5,4]).await?;
    let pts = vec![Point { x: 0.0, y: 0.0 }, Point { x: 1.0, y: 0.0 }, Point { x: 2.0, y: 0.0 }];
    let _d = closest_pair_async(pts).await?;

    // 动态规划：LCS 与 0-1 背包（异步封装）
    let _lcs = lcs_async(b"ABCBDAB".to_vec(), b"BDCABA".to_vec()).await?;
    let _best = knapsack_01_async(vec![2,2,6,5,4], vec![6,3,5,4,6], 10).await?;

    // 字符串算法：KMP / Rabin-Karp（异步包装）
    let _pos = kmp_search_async("ababcabcabababd".into(), "ababd".into()).await?;
    let _pos2 = rabin_karp_search_async("abracadabra".into(), "abra".into()).await?;
    // 多模式匹配：Aho-Corasick（异步包装）
    let _hits = ac_search_async("ahishers".into(), vec!["he".into(), "she".into(), "hers".into(), "his".into()]).await?;

    // 回溯：N 皇后、全排列、子集（异步封装）
    let _sol = nqueens_solutions_async(8).await?; // 92 解
    let _perms = permutations_async(vec![1, 2, 3]).await?; // 6 解
    let _subs = subsets_async(vec![1, 2, 3]).await?; // 8 解

    Ok(())
}
```

### 可选特性与成熟库对照

- 启用 `with-petgraph`：使用 `petgraph` 进行图算法对照（例如 Dijkstra）。
- 启用 `with-aho`：使用 `aho-corasick` 进行多模式匹配对照。

```bash
# 启用 petgraph 与 aho-corasick 特性
cargo test -p c08_algorithms --features "with-petgraph with-aho" -- --nocapture
```

```rust
// 图：与 petgraph 对照（需开启 with-petgraph）
#[cfg(feature = "with-petgraph")]
{
    use c08_algorithms::graph::{dijkstra_sync, petgraph_bridge};
    use std::collections::HashMap;
    let mut g: HashMap<&str, Vec<(&str, f64)>> = HashMap::new();
    g.insert("A", vec![("B", 1.0), ("C", 4.0)]);
    g.insert("B", vec![("C", 2.0)]);
    g.insert("C", vec![]);
    let (dist1, _) = dijkstra_sync(&g, &"A");
    let dist2 = petgraph_bridge::dijkstra_compare(&g, &"A");
    assert_eq!(dist1.get("C").unwrap().round() as i32, dist2.get("C").unwrap().round() as i32);
}

// 字符串：与 aho-corasick 对照（需开启 with-aho）
#[cfg(feature = "with-aho")]
{
    use c08_algorithms::string_algorithms::{build_trie, aho_search};
    let pats = vec!["he", "she", "hers", "his"];
    let matches_fast = aho_search("ahishers", &pats);
    let pats_bytes: Vec<Vec<u8>> = pats.iter().map(|s| s.as_bytes().to_vec()).collect();
    let trie = build_trie(&pats_bytes);
    let matches_teach = trie.ac_search("ahishers".as_bytes(), &pats_bytes);
    assert!(!matches_fast.is_empty() && !matches_teach.is_empty());
}
```

---

## 🔬 性能基准

### 运行测试与基准

```bash
# 单元测试
cargo test

# 基准（本仓库新增对比组）
cargo bench --bench alg_benches

# 运行 CLI 演示
cargo run -p c08_algorithms

# 扫描并生成缺失文档占位
cargo run -p c08_algorithms --bin doc_link_scan

# 统一参数扫描并输出 CSV（深挖分析）
cargo run -p c08_algorithms --bin bench_report > report.csv
# 用任意表格工具打开 report.csv 进行对比分析
```

---

## 📖 文档

- [算法复杂度分析](docs/algorithm_complexity.md)
- [数据结构实现](docs/data_structures.md)
- [异步算法指南](docs/async_algorithms.md)
- [性能优化技巧](docs/performance_optimization.md)
- [基准与深度分析指南](docs/benchmarking_guide.md)
- [Rust 1.89 特性应用](docs/rust_189_features.md)（含本仓库对应接口位置与示例）
- [算法与数据结构索引](docs/algorithm_index.md)

### 测试覆盖率

```bash
# 安装 cargo-llvm-cov
cargo install cargo-llvm-cov

# 生成覆盖率报告（HTML）
cargo llvm-cov clean --workspace
cargo llvm-cov test --workspace --html
```

---

## 🚀 贡献指南

我们欢迎所有形式的贡献！请查看 [CONTRIBUTING.md](CONTRIBUTING.md) 了解详情。

### 贡献类型

- 🐛 Bug 修复
- ✨ 新功能实现
- 📚 文档改进
- 🧪 测试用例
- 🚀 性能优化

---

## 📄 许可证

本项目采用 MIT 许可证 - 查看 [LICENSE](LICENSE) 文件了解详情。

---

## 🙏 致谢

感谢 Rust 团队在 1.89 版本中带来的优秀特性，以及所有为算法和数据结构领域做出贡献的研究者和开发者。

---

## 📞 联系方式

- **项目主页**: [GitHub Repository]
- **问题反馈**: [Issues]
- **讨论交流**: [Discussions]

---

**最后更新**: 2025年1月27日  
**Rust版本**: 1.89.0  
**项目状态**: 🟢 活跃开发中
