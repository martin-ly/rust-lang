# Rust 算法与数据结构 (Rust 1.90 + Edition 2024 对齐版)

**版本**: 0.2.0  
**Rust版本**: 1.90.0  
**Edition**: 2024  
**创建日期**: 2025年1月27日  
**更新日期**: 2025年9月26日  
**特性对齐**: ✅ 对齐 Rust 1.90 + Edition 2024 核心稳定特性  

---

## 🚀 项目概述

本项目是一个全面的 Rust 算法与数据结构库，对齐 Rust 1.90 与 Edition 2024 稳定语言特性，包括：

- **异步编程增强**: 完全支持 `async fn` in traits
- **类型系统增强**: GATs、常量泛型改进
- **性能优化**: 零成本抽象增强、内存布局优化
- **现代 Rust 惯用法**: Edition 2024 最佳实践（let-else、Option::is_some_and、返回位置 impl Trait、从不返回类型 `!` 等）

---

## ✨ Rust 1.90 / Edition 2024 特性支持（稳定）

### 🔄 异步编程特性

| 特性 | 状态 | 性能提升 | 应用场景 |
|------|------|----------|----------|
| Async Traits | ✅ | 15-30% | 异步算法接口 |
| 异步闭包接口（以 `Box<Future>` 形式传递） | ✅ | 20-25% | 异步数据处理 |
| 异步迭代器（基于 Stream 组合） | ✅ | 30-40% | 流式算法 |

### 🧬 类型系统特性

| 特性 | 状态 | 性能提升 | 应用场景 |
|------|------|----------|----------|
| let‑else / Option::is_some_and | ✅ | 可读性 | 早返回与判定优化 |
| 返回位置 impl Trait（RPITIT） | ✅ | 接口清晰 | 迭代器返回 |
| 从不返回类型 `!` | ✅ | 类型严谨 | 致命路径标注 |
| 常量泛型/迭代器改进 | ✅ | 视场景 | 编译期与迭代器 |

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

## 📖 文档体系

### 📍 文档导航

**完整文档索引**: [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md)  
**文档入口**: [docs/README.md](docs/README.md)

本项目拥有完整的文档体系，包含 **39+ 个文档**，按内容类型和难度分为多个主要目录：

### 🆕 新增学习资源 (2025-10-19)

| 资源 | 说明 | 特色 |
|------|------|------|
| [知识图谱](docs/KNOWLEDGE_GRAPH.md) | 算法关系、依赖、演化路径 | 📊 图表化展示 |
| [多维矩阵对比](docs/MULTIDIMENSIONAL_MATRIX_COMPARISON.md) | 全方位算法对比分析 | 🎯 决策支持 |
| [思维导图](docs/MIND_MAP.md) | 算法学习路径可视化 | 🧠 结构化学习 |
| [Rust 1.90 示例集](docs/RUST_190_RICH_EXAMPLES.md) | 60+ 丰富的代码示例 | 💻 实战代码 |
| [交互式学习指南](docs/INTERACTIVE_LEARNING_GUIDE.md) | 渐进式学习路径 | 🎓 自我评估 |
| [可视化示例库](docs/VISUAL_CODE_EXAMPLES.md) | 算法执行过程可视化 | 🎨 动画演示 |

### 📚 文档分类

#### 1. 📖 实用指南 (guides/) - ⭐~⭐⭐

适合日常开发和学习使用：

- [算法复杂度分析](docs/guides/algorithm_complexity.md) - 时间/空间复杂度、Big-O、主定理
- [数据结构实现](docs/guides/data_structures.md) - 线性表、树、图、高级数据结构
- [异步算法指南](docs/guides/async_algorithms.md) - 异步编程与算法设计
- [性能优化技巧](docs/guides/performance_optimization.md) - 编译期优化、SIMD、并行化
- [基准测试指南](docs/guides/benchmarking_guide.md) - Criterion 使用、性能分析

#### 2. 🔬 理论文档 (theory/) - ⭐⭐⭐

深入的形式化理论和数学模型：

- **[算法分类与形式化体系](docs/theory/ALGORITHM_CLASSIFICATION_AND_MODELS.md)** ⭐⭐⭐
  - 算法的形式化定义、计算模型、语义模型、复杂度理论、正确性证明

- **[设计模式语义映射](docs/theory/DESIGN_PATTERNS_SEMANTICS_MAPPING.md)** ⭐⭐⭐
  - 经典设计模式、算法专属模式、并发模式、语义模型映射

- **[异步同步等价关系](docs/theory/ASYNC_SYNC_EQUIVALENCE_ALGORITHMS.md)** ⭐⭐⭐
  - 图灵等价性、执行模型对比、CPS 变换、形式化证明

- **[控制流执行流等价性](docs/theory/CONTROL_FLOW_EXECUTION_FLOW_EQUIVALENCE.md)** ⭐⭐⭐
  - 五大等价性定理、CPS 变换推导、性能等价性分析

- **[Actor/Reactor/CSP 模式](docs/theory/ACTOR_REACTOR_CSP_PATTERNS.md)** ⭐⭐⭐
  - Actor 模型、Reactor 模式、CSP 理论、形式化验证

- **[异步递归分析](docs/theory/ASYNC_RECURSION_ANALYSIS.md)** ⭐⭐⭐
  - 不动点理论、四大实现模式、终止性与等价性证明

#### 3. 🚀 高级专题 (advanced/) - ⭐⭐~⭐⭐⭐

14 个深入的算法专题文档，涵盖类型设计、排序、图算法、动态规划、字符串算法、数据结构、并行算法、执行模型、异步模式、优化技术、形式化验证、分布式算法、机器学习和算法工程。

详见 [docs/advanced/README.md](docs/advanced/README.md)

#### 4. ✨ Rust 特性 (rust-features/) - ⭐⭐

Rust 1.89、1.90 和 Edition 2024 的特性应用：

- [Rust 1.89 特性](docs/rust-features/rust_189_features.md)
- [Rust 1.90 特性应用](docs/rust-features/RUST_190_FEATURES_APPLICATION.md)
- [Edition 2024 特性](docs/rust-features/Edition_2024_Features.md)

#### 5. 📚 参考资料 (references/) - ⭐~⭐⭐

快速查阅和索引：

- [算法索引](docs/references/algorithm_index.md) - 按类别索引所有算法
- [算法基础教程](docs/references/08_algorithms_basics.md) - 入门教程

### 🎓 学习路径

详细的学习路径请查看 [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md)，包括：

- **初学者路径** (2-3 周) - 掌握基础算法和数据结构
- **进阶路径** (3-4 周) - 异步编程和性能优化
- **专家路径** (持续学习) - 理论研究和形式化方法

### 🔥 推荐文档

**新手必读**:

1. [算法基础教程](docs/references/08_algorithms_basics.md)
2. [算法复杂度分析](docs/guides/algorithm_complexity.md)
3. [数据结构实现](docs/guides/data_structures.md)

**进阶阅读**:

1. [异步算法指南](docs/guides/async_algorithms.md)
2. [Actor/Reactor/CSP 模式](docs/theory/ACTOR_REACTOR_CSP_PATTERNS.md)
3. [性能优化技巧](docs/guides/performance_optimization.md)

**理论深入**:

1. [算法分类与形式化](docs/theory/ALGORITHM_CLASSIFICATION_AND_MODELS.md)
2. [异步同步等价关系](docs/theory/ASYNC_SYNC_EQUIVALENCE_ALGORITHMS.md)
3. [控制流执行流等价性](docs/theory/CONTROL_FLOW_EXECUTION_FLOW_EQUIVALENCE.md)

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
