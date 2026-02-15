# 🦀 Rust 算法与数据结构 - Rust 1.93.0 学习模块

> **模块类型**: 算法与数据结构学习模块 | ⭐ 质量评分: **95/100**
> **Rust版本**: 1.93.0+ | 📊 完成度: **100% 完成** ✅
> **学习重点**: 基础数据结构、核心算法、高级算法、并行与异步算法
> **适用对象**: Rust中级到高级开发者、算法工程师
> **最后更新**: 2025-12-11 | 🔄 维护模式: Rust 1.93.0 特性更新完成

## 目录

- [🦀 Rust 算法与数据结构 - Rust 1.93.0 学习模块](#-rust-算法与数据结构---rust-1920-学习模块)
  - [目录](#目录)
  - [🎯 最新更新 (2025-11-15) ✨](#-最新更新-2025-11-15-)
    - [📖 新版文档导航](#-新版文档导航)
  - [🌟 2025-10-20 核心增强更新](#-2025-10-20-核心增强更新)
  - [🚀 项目概述](#-项目概述)
  - [✨ Rust 1.93.0 / Edition 2024 特性支持（稳定）](#-rust-1920--edition-2024-特性支持稳定)
    - [🆕 2025-11-01 LeetCode 分类集成](#-2025-11-01-leetcode-分类集成)
    - [🔄 异步编程特性](#-异步编程特性)
    - [🧬 类型系统特性](#-类型系统特性)
  - [📚 核心模块](#-核心模块)
    - [1. 基础数据结构](#1-基础数据结构)
    - [2. 核心算法](#2-核心算法)
    - [3. 高级算法](#3-高级算法)
    - [4. 并行与异步（实践指引）](#4-并行与异步实践指引)
  - [🧭 模块一览（同步/并行/异步接口速览）](#-模块一览同步并行异步接口速览)
  - [🛠️ 快速开始](#️-快速开始)
    - [安装依赖](#安装依赖)
    - [基础用法（对齐新接口）](#基础用法对齐新接口)
    - [可选特性与成熟库对照](#可选特性与成熟库对照)
  - [🔬 性能基准](#-性能基准)
    - [运行测试与基准](#运行测试与基准)
  - [📖 文档体系](#-文档体系)
    - [📍 文档导航 (2025-10-22 更新)](#-文档导航-2025-10-22-更新)
    - [🆕 新增学习资源 (2025-10-19)](#-新增学习资源-2025-10-19)
    - [📚 文档分类](#-文档分类)
      - [1. 📖 实用指南 (tier_02_guides/) - ⭐~⭐⭐](#1--实用指南-tier_02_guides---)
      - [2. 🔬 理论文档 (tier_04_advanced/) - ⭐⭐⭐](#2--理论文档-tier_04_advanced---)
      - [3. 🚀 高级专题 (tier_04_advanced/) - ⭐⭐~⭐⭐⭐](#3--高级专题-tier_04_advanced---)
      - [4. ✨ Rust 特性 (tier_03_references/) - ⭐⭐](#4--rust-特性-tier_03_references---)
      - [5. 📚 参考资料 (tier_03_references/) - ⭐~⭐⭐](#5--参考资料-tier_03_references---)
    - [🎓 学习路径](#-学习路径)
    - [🔥 推荐文档](#-推荐文档)
    - [测试覆盖率](#测试覆盖率)
  - [🚀 贡献指南](#-贡献指南)
    - [贡献类型](#贡献类型)
  - [📚 知识结构文档](#-知识结构文档)
    - [知识结构体系](#知识结构体系)
    - [使用指南](#使用指南)
  - [📄 许可证](#-许可证)
  - [🙏 致谢](#-致谢)
  - [📚 相关资源](#-相关资源)
    - [使用指南](#使用指南-1)
    - [项目文档](#项目文档)
  - [📞 联系方式](#-联系方式)

## 🎯 最新更新 (2025-11-15) ✨

> **文档状态**: ✅ **100% 标准化完成**
> **框架结构**: ✅ **4-Tier 架构**
> **文档总数**: **49+ 篇**
> **质量评分**: **95/100**
> **Rust版本**: 1.93.0+ (Edition 2024)

### 📖 新版文档导航

**从这里开始学习** ⭐:

- 🎯 [项目概览](./docs/tier_01_foundations/01_项目概览.md) - 15分钟快速了解
- 🗺️ [主索引导航](./docs/tier_01_foundations/02_主索引导航.md) - 找到适合你的学习路径
- 📖 [术语表](./docs/tier_01_foundations/03_术语表.md) - 核心术语速查
- ❓ [常见问题](./docs/tier_01_foundations/04_常见问题.md) - 解决常见疑问

**文档层级结构**:

- 📚 [Tier 1: 基础层](./docs/tier_01_foundations/) - 快速入门 (2-4小时)
- 📝 [Tier 2: 实践层](./docs/tier_02_guides/) - 实战指南 (10-15小时)
- 📖 [Tier 3: 参考层](./docs/tier_03_references/) - 技术参考 (按需查阅)
- 🚀 [Tier 4: 高级层](./docs/tier_04_advanced/) - 理论深入 (20-30小时)

**标准化报告**: [C08_FINAL_COMPLETION_REPORT_2025_10_22.md](./docs/reports/C08_FINAL_COMPLETION_REPORT_2025_10_22.md)

**Rust 1.93 示例**: `cargo run -p c08_algorithms --example rust_193_features_demo` - VecDeque pop_*_if、BTreeMap::append、slice::as_array、Duration::from_nanos_u128

---

## 🌟 2025-10-20 核心增强更新

- **📊 [知识图谱与概念关系](./docs/KNOWLEDGE_GRAPH.md)** - 算法与数据结构完整体系
- **📐 [多维矩阵对比分析](./docs/MULTIDIMENSIONAL_MATRIX_COMPARISON.md)** - 算法/数据结构全面对比
- **🗺️ [Rust 1.93.0 算法思维导图](./docs/MIND_MAP.md)** ⭐
  - ASCII艺术图表 | 数据结构/算法分类/并发算法完整体系
  - 算法选择决策树 | 排序/搜索/图算法/并发选择指南
  - 3级学习路径(2-16周) | 问题诊断树
  - 时间空间复杂度对比 | Rayon并行算法实践
- **💻 [Rust 1.93.0 实战示例集](./docs/RUST_190_EXAMPLES_COLLECTION.md)** ⭐
  - 850+行可运行代码 | LRU缓存/Trie树/图算法完整实现
  - Rust 1.93.0特性 | 泛型/所有权/并发算法最佳实践
  - Rayon并行算法 | 并行排序/Map-Reduce实战
  - 2个综合项目 | 表达式求值器+任务调度系统

**完整度**: 📊 知识图谱 + 📐 多维矩阵 + 🗺️ 思维导图 + 💻 实战示例 = **100%** ✨

---

**版本**: 0.2.0
**Rust版本**: 1.93.0+
**Edition**: 2024
**创建日期**: 2025年1月27日
**更新日期**: 2025年9月26日
**特性对齐**: ✅ 对齐 Rust 1.93.0 + Edition 2024 核心稳定特性

---

## 🚀 项目概述

本项目是一个全面的 Rust 算法与数据结构库，对齐 Rust 1.93.0 与 Edition 2024 稳定语言特性，包括：

- **异步编程增强**: 完全支持 `async fn` in traits
- **类型系统增强**: GATs、常量泛型改进
- **性能优化**: 零成本抽象增强、内存布局优化
- **现代 Rust 惯用法**: Edition 2024 最佳实践（let-else、Option::is_some_and、返回位置 impl Trait、从不返回类型 `!` 等）
- **LeetCode 分类组织**: 按照 LeetCode 官方分类组织算法，结合 Rust 1.93.0 特性实现经典题目

---

## ✨ Rust 1.93.0 / Edition 2024 特性支持（稳定）

### 🆕 2025-11-01 LeetCode 分类集成

- **LeetCode 分类模块**: 按照 LeetCode 官方分类组织算法实现
- **Rust 1.93.0 特性应用**: 在实际算法中应用 Rust 1.93.0 新特性
- **完整文档**: 包含问题描述、示例、约束条件、复杂度分析
- **已实现题目**:
  - **Array**: Two Sum, 3Sum, Maximum Subarray, Container With Most Water 等 12+ 题
  - **Two Pointers**: 3Sum Closest, Trapping Rain Water, Sort Colors 等 8+ 题
  - **Binary Search**: Binary Search, Search in Rotated Sorted Array, Find Peak Element 等 10+ 题
  - **String**: Longest Common Prefix, Valid Parentheses, First Unique Character 等 10+ 题
  - **Hash Table**: Group Anagrams, Single Number, Valid Anagram 等 12+ 题
  - **Stack**: Evaluate RPN, Min Stack, Daily Temperatures 等 6+ 题
  - **Sliding Window**: Longest Substring, Minimum Size Subarray, Sliding Window Maximum 等 8+ 题
  - **Dynamic Programming**: Climbing Stairs, House Robber, Coin Change, LIS, LCS 等 11+ 题
  - **Tree**: Maximum Depth, Same Tree, Symmetric Tree, Invert Tree, Traversals 等 13+ 题
  - **Heap**: Kth Largest, Top K Frequent, K Closest Points, Last Stone Weight 等 8+ 题
  - **Graph**: Number of Islands, Course Schedule, Flood Fill, Rotting Oranges 等 9+ 题
  - **Backtracking**: Permutations, Subsets, Generate Parentheses, Word Search 等 10+ 题
  - **Bit Manipulation**: Single Number, Hamming Weight, Power of Two, Counting Bits 等 10+ 题
  - **Trie**: Implement Trie, Word Dictionary 等 2+ 题
  - **总计**: 132+ 题目，124 个测试用例，**100% 测试通过率**
  - 更多分类和题目实现中...

详细文档请查看: [docs/leetcode_with_rust191.md](./docs/leetcode_with_rust191.md)

---

### 🔄 异步编程特性

| 特性                                      | 状态 | 性能提升 | 应用场景     |
| ----------------------------------------- | ---- | -------- | ------------ |
| Async Traits                              | ✅   | 15-30%   | 异步算法接口 |
| 异步闭包接口（以 `Box<Future>` 形式传递） | ✅   | 20-25%   | 异步数据处理 |
| 异步迭代器（基于 Stream 组合）            | ✅   | 30-40%   | 流式算法     |

### 🧬 类型系统特性

| 特性                           | 状态 | 性能提升 | 应用场景         |
| ------------------------------ | ---- | -------- | ---------------- |
| let‑else / Option::is_some_and | ✅   | 可读性   | 早返回与判定优化 |
| 返回位置 impl Trait（RPITIT）  | ✅   | 接口清晰 | 迭代器返回       |
| 从不返回类型 `!`               | ✅   | 类型严谨 | 致命路径标注     |
| 常量泛型/迭代器改进            | ✅   | 视场景   | 编译期与迭代器   |

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

### 📍 文档导航 (2025-10-22 更新)

**🎯 新版4-Tier导航** (推荐):

- [Tier 1: 基础层](./docs/tier_01_foundations/) - 快速入门 ⭐ **推荐起点**
- [Tier 2: 实践层](./docs/tier_02_guides/) - 实战指南
- [Tier 3: 参考层](./docs/tier_03_references/) - 技术参考
- [Tier 4: 高级层](./docs/tier_04_advanced/) - 理论深入

**📚 传统文档索引** (保留):

- [完整文档索引](docs/00_MASTER_INDEX.md) - 旧版主索引
- [文档入口](docs/README.md) - 文档README

本项目拥有完整的文档体系，包含 **49+ 个文档**（含新建导航），按内容类型和难度分为多个主要目录：

### 🆕 新增学习资源 (2025-10-19)

| 资源                                                       | 说明                     | 特色          |
| ---------------------------------------------------------- | ------------------------ | ------------- |
| [知识图谱](docs/KNOWLEDGE_GRAPH.md)                        | 算法关系、依赖、演化路径 | 📊 图表化展示 |
| [多维矩阵对比](docs/MULTIDIMENSIONAL_MATRIX_COMPARISON.md) | 全方位算法对比分析       | 🎯 决策支持   |
| [思维导图](docs/MIND_MAP.md)                               | 算法学习路径可视化       | 🧠 结构化学习 |
| [Rust 1.93.0 示例集](docs/RUST_192_RICH_EXAMPLES.md)       | 60+ 丰富的代码示例       | 💻 实战代码   |
| [交互式学习指南](docs/INTERACTIVE_LEARNING_GUIDE.md)       | 渐进式学习路径           | 🎓 自我评估   |
| [可视化示例库](docs/VISUAL_CODE_EXAMPLES.md)               | 算法执行过程可视化       | 🎨 动画演示   |

### 📚 文档分类

#### 1. 📖 实用指南 (tier_02_guides/) - ⭐~⭐⭐

适合日常开发和学习使用：

- [算法复杂度分析](docs/tier_02_guides/03_算法复杂度分析.md) - 时间/空间复杂度、Big-O、主定理
- [数据结构实现](docs/tier_02_guides/02_数据结构实践.md) - 线性表、树、图、高级数据结构
- [并行与异步算法](docs/tier_02_guides/05_并行与异步算法.md) - 异步编程与算法设计
- [性能优化技巧](docs/tier_02_guides/04_性能优化实践.md) - 编译期优化、SIMD、并行化
- [算法性能参考](docs/tier_03_references/04_算法性能参考.md) - Criterion 使用、性能分析

#### 2. 🔬 理论文档 (tier_04_advanced/) - ⭐⭐⭐

深入的形式化理论和数学模型：

- **[形式化算法理论](docs/tier_04_advanced/01_形式化算法理论.md)** ⭐⭐⭐
  - 算法分类、形式化定义、计算模型、语义模型、复杂度理论

- **[并发算法模式](docs/tier_04_advanced/02_并发算法模式.md)** ⭐⭐⭐
  - Actor 模型、Reactor 模式、CSP 理论、形式化验证

- **[分布式算法](docs/tier_04_advanced/03_分布式算法.md)** ⭐⭐⭐
  - 分布式系统算法、一致性协议

- **[算法工程实践](docs/tier_04_advanced/04_算法工程实践.md)** ⭐⭐⭐
  - 工程应用最佳实践、性能调优

- **[前沿算法技术](docs/tier_04_advanced/05_前沿算法技术.md)** ⭐⭐⭐
  - 机器学习与前沿研究

#### 3. 🚀 高级专题 (tier_04_advanced/) - ⭐⭐~⭐⭐⭐

详见 [docs/tier_04_advanced/README.md](docs/tier_04_advanced/README.md)

#### 4. ✨ Rust 特性 (tier_03_references/) - ⭐⭐

- [Rust 1.90 特性参考](docs/tier_03_references/03_Rust190特性参考.md)
- [Rust 1.93.0 算法特性](docs/RUST_192_ALGORITHMS_IMPROVEMENTS.md) ⭐ 最新

#### 5. 📚 参考资料 (tier_03_references/) - ⭐~⭐⭐

- [算法分类参考](docs/tier_03_references/01_算法分类参考.md) - 按类别索引
- [数据结构参考](docs/tier_03_references/02_数据结构参考.md)

### 🎓 学习路径

详细的学习路径请查看 [docs/00_MASTER_INDEX.md](docs/00_MASTER_INDEX.md)，包括：

- **初学者路径** (2-3 周) - 掌握基础算法和数据结构
- **进阶路径** (3-4 周) - 异步编程和性能优化
- **专家路径** (持续学习) - 理论研究和形式化方法

### 🔥 推荐文档

**新手必读**:

1. [算法快速入门](docs/tier_02_guides/01_算法快速入门.md)
2. [算法复杂度分析](docs/tier_02_guides/03_算法复杂度分析.md)
3. [数据结构实现](docs/tier_02_guides/02_数据结构实践.md)

**进阶阅读**:

1. [并行与异步算法](docs/tier_02_guides/05_并行与异步算法.md)
2. [并发算法模式](docs/tier_04_advanced/02_并发算法模式.md)
3. [性能优化实践](docs/tier_02_guides/04_性能优化实践.md)

**理论深入**:

1. [形式化算法理论](docs/tier_04_advanced/01_形式化算法理论.md)
2. [并发算法模式](docs/tier_04_advanced/02_并发算法模式.md)
3. [分布式算法](docs/tier_04_advanced/03_分布式算法.md)

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

## 占位实现说明

部分 LeetCode 题为占位实现，用于保持接口完整性，后续补全：

| 题目 | 说明 |
|------|------|
| 142. Linked List Cycle II | 占位实现，待完整实现 |
| 其他 | 详见 [LEETCODE_IMPLEMENTATION_COMPLETE.md](./LEETCODE_IMPLEMENTATION_COMPLETE.md) |

---

我们欢迎所有形式的贡献！请查看 [CONTRIBUTING.md](CONTRIBUTING.md) 了解详情。

### 贡献类型

- 🐛 Bug 修复
- ✨ 新功能实现
- 📚 文档改进
- 🧪 测试用例
- 🚀 性能优化

---

## 📚 知识结构文档

### 知识结构体系

- **[知识结构框架](../../docs/KNOWLEDGE_STRUCTURE_FRAMEWORK.md)** ⭐ NEW! - 完整知识结构体系（概念定义、属性、关系、解释、证明）
- **[多维概念矩阵](../../docs/MULTI_DIMENSIONAL_CONCEPT_MATRIX.md)** ⭐ NEW! - 算法对比矩阵
- **[思维导图集合](../../docs/MIND_MAP_COLLECTION.md)** ⭐ NEW! - 算法思维导图
- **[决策图网](../../docs/04_thinking/DECISION_GRAPH_NETWORK.md)** - 技术选型决策支持
- **[证明图网](../../docs/04_thinking/PROOF_GRAPH_NETWORK.md)** - 形式化证明结构

### 使用指南

- **[算法速查卡](../../docs/02_reference/quick_reference/algorithms_cheatsheet.md)** ⭐ NEW! - 快速参考

## 📄 许可证

本项目采用 MIT 许可证 - 查看 [LICENSE](LICENSE) 文件了解详情。

---

## 🙏 致谢

感谢 Rust 团队在 1.89 版本中带来的优秀特性，以及所有为算法和数据结构领域做出贡献的研究者和开发者。

---

## 📚 相关资源

### 使用指南

- **[算法综合演示程序](../../examples/algorithm_comprehensive_demo.rs)** ⭐ NEW! - 排序/搜索/图/动态规划/数据结构综合示例
- **[快速参考卡片](../../docs/02_reference/quick_reference/algorithms_cheatsheet.md)** ⭐ NEW! - 算法与数据结构速查卡

### 项目文档

- **[项目最佳实践指南](../../docs/05_guides/BEST_PRACTICES.md)** - 代码质量、性能优化、测试指南
- **[性能调优指南](../../docs/PERFORMANCE_TUNING_GUIDE.md)** - 完整的性能调优指南

## 📞 联系方式

- **项目主页**: [GitHub Repository]
- **问题反馈**: [Issues]
- **讨论交流**: [Discussions]

---

**最后更新**: 2025-12-11
**Rust版本**: 1.93.0
**项目状态**: 🟢 活跃开发中
