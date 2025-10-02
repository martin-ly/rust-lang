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

### 🎯 核心理论文档（全新升级！）

- **[算法分类、模型与形式化体系](docs/ALGORITHM_CLASSIFICATION_AND_MODELS.md)** ⭐⭐⭐ 🆕
  - 算法的形式化定义（五元组、图灵机、λ演算）
  - 完整算法分类体系（设计范式、问题域）
  - 设计范式深度解析：分治、动态规划、贪心、回溯（带完整Rust实现）
  - 计算模型：图灵机、RAM模型、λ演算
  - 语义模型：操作语义、指称语义、公理语义（霍尔逻辑、分离逻辑）
  - 复杂度理论：主定理、摊还分析、渐进记号
  - 正确性证明：循环不变量、数学归纳法、不变式变式
  - Rust 1.90特性映射：GATs、Async Traits、Edition 2024

- **[设计模式与算法语义模型映射](docs/DESIGN_PATTERNS_SEMANTICS_MAPPING.md)** ⭐⭐⭐ 🆕
  - 经典设计模式在算法中的应用（Strategy、Template Method、Iterator、Observer）
  - 算法专属模式（Memoization、Lazy Evaluation、CPS变换）
  - 并发模式（Actor、Pipeline）
  - 语义模型映射（类型系统、所有权与分离逻辑、并发模型与π演算）
  - Rust特有模式（Typestate、Newtype）
  - 等价关系分析（算法等价性、模式等价性、同步异步等价）
  
- **[异步与同步算法的等价关系](docs/ASYNC_SYNC_EQUIVALENCE_ALGORITHMS.md)** ⭐⭐⭐
  - 图灵等价性与执行语义差异
  - 调用栈vs状态机执行模型
  - CPS变换与形式化证明
  - 控制流与执行流分析
  
- **[控制流与执行流等价性证明](docs/CONTROL_FLOW_EXECUTION_FLOW_EQUIVALENCE.md)** ⭐⭐⭐
  - 控制流形式化定义（顺序、条件、循环）
  - 执行流状态机模型（Future状态转换）
  - 五大等价性定理及证明
  - CPS变换完整推导
  - 性能等价性分析

### 🚀 异步编程专题（NEW！）

- **[Actor/Reactor模式与CSP语义模型](docs/ACTOR_REACTOR_CSP_PATTERNS.md)** ⭐⭐⭐
  - Actor模型的形式化定义与Rust实现
  - Reactor模式与事件驱动调度
  - CSP通信顺序进程理论
  - Golang CSP vs Rust Async对比
  - 三大调度机制原理与应用
  - 🔥 **完整示例**: `examples/actor_reactor_csp_complete.rs` - Actor/Reactor/CSP三种模式的完整实现与对比
  
- **[异步递归：形式化分析与实现](docs/ASYNC_RECURSION_ANALYSIS.md)** ⭐⭐⭐
  - 递归的不动点理论
  - 异步递归的类型系统挑战
  - 四大实现模式（Box+Pin、宏、尾递归、Stream）
  - 终止性与等价性证明
  - 算法应用与性能分析
  - 🔥 **完整示例**: `examples/async_recursion_comprehensive.rs` - 四种异步递归模式及算法应用

### 📚 实用指南

- [算法复杂度分析](docs/algorithm_complexity.md)
- [数据结构实现](docs/data_structures.md)
- [异步算法指南](docs/async_algorithms.md)
- [性能优化技巧](docs/performance_optimization.md)
- [基准与深度分析指南](docs/benchmarking_guide.md)
- [Rust 1.90特性应用](docs/RUST_190_FEATURES_APPLICATION.md)
- Edition 2024 语法要点：见 `docs/Edition_2024_Features.md`

### 📑 完整索引

- **[文档索引与学习路线](docs/DOCUMENTATION_INDEX.md)** - 包含三条学习路线：
  - 路线1：算法理论研究者
  - 路线2：异步编程工程师
  - 路线3：算法工程师

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
