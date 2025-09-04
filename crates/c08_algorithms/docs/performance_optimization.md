# 性能优化技巧（并行/异步与基准）

本页提供在 Rust 1.89 环境下针对算法与数据结构的性能优化要点与操作清单。

---

## 并行（Rayon）

- 典型场景：排序、独立块计算、Map-Reduce 风格任务
- API：`par_iter`、`par_sort`、`par_sort_unstable`
- 注意事项：
  - 分块粒度：避免过细导致调度开销过大
  - 数据共享：尽量使用不可变共享，减少锁竞争

示例：`src/sorting/mod.rs` 中的 `sort_parallel`

---

## 异步包装（Tokio spawn_blocking）

- 适用：在异步上下文中运行 CPU 密集任务避免阻塞调度器
- 限制：不改变算法复杂度；对吞吐/延迟的影响取决于任务粒度与调度

示例：`sort_async`、`binary_search_async`、`bfs_shortest_path_async` 等

---

## 基准与分析

- 运行基准：

```bash
cargo bench --bench alg_benches
```

- 运行单元测试（含示例断言）：

```bash
cargo test -p c08_algorithms
```

- 运行时剖析：参见 `src/performance_examples/runtime_profiling.rs`

---

## 实战建议

- 大数据排序优先使用并行排序，异步层作为编排
- 图算法优先并行化前处理（边收集/初始化），主循环谨慎并行
- 使用 `tracing` 标注关键路径，结合 Criterion 比较同步/并行/异步包装

### 字符串匹配优化

- 单模式匹配：短模式可用 KMP；随机文本下 Rabin‑Karp 期望更优但需防碰撞
- 多模式匹配：Aho‑Corasick 适合批量关键字；预构建自动机可复用；谨慎选择字母表与哈希
- 在异步环境中对大量文本块可采用分片并行 + `spawn_blocking` 包装

更多语言特性结合：见 `docs/rust_189_features.md`。
