# 异步算法指南（Rust 1.89 对齐）

本指南系统性对齐国际百科（如维基百科）中与“算法与数据结构”相关的目录与实践，给出在 Rust 1.89 环境下的异步化与并行化落地方式。对于 CPU 密集型算法，本项目采用 Tokio `spawn_blocking` 与 Rayon 并行组合；对于 I/O 或流式处理，采用异步流与任务组合（参考 `docs/rust_189_features.md`）。

---

## 目录对齐（参考国际 wiki）

- 排序（Sorting）：快速、归并、堆（并行/异步）
- 搜索（Searching）：线性、二分；图搜索（BFS/DFS）
- 最短路径（Shortest Paths）：Dijkstra（异步包装）
- 最小生成树（MST）：Kruskal、Prim（并行/异步）
- 拓扑排序（Topological Sorting）（异步包装）
- 分治（Divide and Conquer）：最大子段和、最近点对（目录与接口预留）
- 动态规划（Dynamic Programming）：LCS、0-1 背包（目录与接口预留）

注：分治与动态规划模块在 `src/divide_and_conquer/`、`src/dynamic_programming/` 已建目录，按本指南规范逐步完善。

---

## 使用方式总览

```rust
use c08_algorithms::sorting::{sort_async, sort_parallel, sort_sync, SortingAlgo};
use c08_algorithms::searching::{binary_search_async, linear_search_async, parallel_search};
use c08_algorithms::graph::{
    bfs_shortest_path_async, dijkstra_async, mst_kruskal_async, mst_prim_async, topo_sort_async,
};

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 排序：同步/并行/异步
    let mut v = vec![3, 1, 4, 1, 5, 9, 2];
    sort_sync(&mut v, SortingAlgo::Quick);
    sort_parallel(&mut v, SortingAlgo::Merge);
    let v = sort_async(v, SortingAlgo::Heap).await?;

    // 搜索：并行线性 + 异步二分
    let _idx_parallel = parallel_search(&v, &5);
    let _idx_async = binary_search_async(v.clone(), 5).await?;

    // 图算法：BFS、Dijkstra、MST、拓扑
    use std::collections::HashMap;
    let mut g: HashMap<i32, Vec<i32>> = HashMap::new();
    g.insert(1, vec![2, 3]); g.insert(2, vec![4]); g.insert(3, vec![4]); g.insert(4, vec![]);
    let _path = bfs_shortest_path_async(g, 1, 4).await?;

    let mut wg: HashMap<&str, Vec<(&str, f64)>> = HashMap::new();
    wg.insert("A", vec![("B", 1.0), ("C", 4.0)]);
    wg.insert("B", vec![("C", 2.0), ("D", 5.0)]);
    wg.insert("C", vec![("D", 1.0)]);
    wg.insert("D", vec![]);
    let (_dist, _prev) = dijkstra_async(wg.clone(), "A").await?;
    let (_w1, _e1) = mst_kruskal_async(wg.clone()).await?;
    let (_w2, _e2) = mst_prim_async(wg.clone(), "A").await?;

    let mut dag: HashMap<&str, Vec<&str>> = HashMap::new();
    dag.insert("A", vec!["B", "C"]);
    dag.insert("B", vec!["D"]);
    dag.insert("C", vec!["D"]);
    dag.insert("D", vec![]);
    let _order = topo_sort_async(dag).await?;

    Ok(())
}
```

---

## 模块与接口映射

- 排序：`src/sorting/mod.rs`
  - 同步：`sort_sync`
  - 并行：`sort_parallel`（Rayon）
  - 异步：`sort_async`（Tokio `spawn_blocking`）
- 搜索：`src/searching/mod.rs`
  - `linear_search_async`、`binary_search_async`、`parallel_search`
  - 图搜索（简版）：`dfs_async`、`bfs_async`
- 图论：`src/graph/mod.rs`
  - BFS 最短路径：`bfs_shortest_path_async`
  - Dijkstra：`dijkstra_async`
  - 最小生成树：`mst_kruskal_async`、`mst_prim_async`
  - 拓扑排序：`topo_sort_async`
- 分治/动态规划：占位（将提供 `*_async` 接口并与基准联动）
- 字符串算法：`src/string_algorithms/mod.rs`（`kmp_search_async`、`rabin_karp_search_async`）

---

## 设计模式（Rust 1.89）

- 异步包装 CPU 密集型算法：在异步上下文中使用 `tokio::task::spawn_blocking(move || { ... })` 将纯 CPU 工作移出调度器。
- 并行化优先：对可拆分工作优先选择 Rayon（`par_iter`/`par_sort`），在边界处以异步进行编排与 I/O。
- 异步 in traits 与异步闭包：在需要的抽象层（如“异步排序器”）可直接采用 `async fn` in traits；流式处理可使用异步闭包与 `Stream`（详见 `docs/rust_189_features.md`）。

---

## 示例片段

### 1) 异步排序（CPU 密集）

```rust
use c08_algorithms::sorting::{sort_async, SortingAlgo};

#[tokio::test]
async fn demo_async_sort() {
    let data = vec![10, 7, 3, 9, 1, 2];
    let out = sort_async(data, SortingAlgo::Merge).await.unwrap();
    assert!(out.windows(2).all(|w| w[0] <= w[1]));
}
```

### 2) 异步二分搜索（已排序）

```rust
use c08_algorithms::searching::binary_search_async;

#[tokio::test]
async fn demo_async_binary_search() {
    let data = vec![1, 2, 3, 5, 8, 13];
    let idx = binary_search_async(data.clone(), 8).await.unwrap();
    assert_eq!(idx, Some(4));
}
```

### 3) 异步 BFS 最短路径

```rust
use c08_algorithms::graph::bfs_shortest_path_async;
use std::collections::HashMap;

#[tokio::test]
async fn demo_async_bfs() {
    let mut g: HashMap<i32, Vec<i32>> = HashMap::new();
    g.insert(1, vec![2, 3]);
    g.insert(2, vec![4]);
    g.insert(3, vec![4]);
    g.insert(4, vec![]);

    let path = bfs_shortest_path_async(g, 1, 4).await.unwrap().unwrap();
    assert!(path == vec![1, 2, 4] || path == vec![1, 3, 4]);
}
```

---

## 基准与性能

- 运行：
  - `cargo bench --bench alg_benches`
  - 建议在 `--release` 下进行对照，观察并行/异步包装对延迟和吞吐的影响。
- 建议：
  - 大数据集排序优先 `par_sort`/`par_sort_unstable`；在异步环境用 `spawn_blocking` 包装。
  - 图算法的核心步骤通常难以完全并行化，优先对“边收集/初始化”等进行并行预处理。

---

## 最佳实践清单

- 避免在 async 任务内直接执行长耗时 CPU 密集计算，改用 `spawn_blocking`。
- 对可拆分工作（排序、独立块计算）优先选 Rayon 并行，异步层负责编排与 I/O。
- 使用 `tokio::join!`/`try_join!` 并行等待多个独立异步任务的完成。
- 通过基准与 `tracing` 观测异步/并行的分界点与粒度。

---

## 参考（国际 wiki 对齐）

- 排序算法（Sorting algorithms）
- 二分查找（Binary search algorithm）
- 广度优先搜索（Breadth-first search）
- Dijkstra 算法（Dijkstra's algorithm）
- 最小生成树（Minimum spanning tree）
- 拓扑排序（Topological sorting）
- KMP 字符串匹配（Knuth–Morris–Pratt algorithm）
- Rabin–Karp 字符串搜索（Rabin–Karp string search）

（以上可参见维基百科中文或英文词条获取数学定义与标准描述。）

---

更多 Rust 1.89 语言特性、异步 trait/闭包/迭代器的用法细节：见 `docs/rust_189_features.md`。
