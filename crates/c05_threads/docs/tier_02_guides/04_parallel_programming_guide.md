> **EN**: Parallel Programming Guide
> **Summary**: Practical guide to data parallelism with Rayon, including parallel iterators, fork-join, divide-and-conquer algorithms, and performance tuning. This crate document now redirects to the canonical concept page.

> **权威来源**: [concept/03_advanced/00_concurrency/07_parallel_distributed_pattern_spectrum.md](../../../../concept/03_advanced/00_concurrency/07_parallel_distributed_pattern_spectrum.md)

## 主题速览

- 数据并行与任务并行
- Rayon 并行迭代器（`par_iter`, `par_map`, `par_reduce`）
- `join` / `scope` / 自定义线程池
- 分治算法（并行快速排序、归并排序）
- Map-Reduce 与并行聚合
- 性能调优与常见陷阱

---

*本 stub 按 AGENTS.md §6.4 保留路径，原通用概念内容已归并至上方权威来源页。可执行代码示例见 [`crates/c05_threads/src`](../../../../crates/c05_threads/src)。*
