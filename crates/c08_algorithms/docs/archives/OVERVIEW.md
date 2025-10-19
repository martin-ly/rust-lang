# 概览：算法与数据结构（c08_algorithms）

本模块覆盖数据结构、复杂度分析、算法实现与性能优化，并包含异步算法与基准测试指南。

---

## 目录导航

- 基础与索引
  - [algorithm_index.md](./algorithm_index.md)
  - [data_structures.md](./data_structures.md)
  - [algorithm_complexity.md](./algorithm_complexity.md)

- 专题与实验
  - [async_algorithms.md](./async_algorithms.md)
  - [benchmarking_guide.md](./benchmarking_guide.md)
  - [performance_optimization.md](./performance_optimization.md)
  - 实验：`algorithm_exp01.md` … `algorithm_exp14.md`

- 版本对齐
  - [rust_189_features.md](./rust_189_features.md)

---

## 快速开始

1) 先读 `algorithm_index.md` 建立导航
2) 查看 `data_structures.md` 与 `algorithm_complexity.md`
3) 根据 `benchmarking_guide.md` 跑通性能基准

---

## 待完善

- 扩展并行算法与内存局部性的系统化评测
- 与 `c05_threads`/`c06_async` 的并发/异步算法案例互链

### 并行算法与内存局部性评测（补全）

- 指标与方法
  - 性能：吞吐、P95/P99 延迟、加速比/效率、Amdahl/Gustafson 分析
  - 局部性：缓存命中率、带宽利用、NUMA 跨节点访问比
  - 工具：`criterion`、`perf`/`vtune`/`likwid`、`tokio-console`（异步路径）

- 基准骨架

```rust
use criterion::{criterion_group, criterion_main, Criterion, black_box};

fn bench_par_map(c: &mut Criterion) {
    c.bench_function("par_map_1m", |b| {
        b.iter(|| {
            let v: Vec<u64> = (0..1_000_000).collect();
            let s: u64 = v.chunks(1024)
                .map(|chunk| chunk.iter().map(|x| x + 1).sum::<u64>())
                .sum();
            black_box(s)
        })
    });
}

criterion_group!(benches, bench_par_map);
criterion_main!(benches);
```

- 设计建议
  - 分块大小与预取：按缓存层次（L1/L2/L3）调优，避免 false sharing
  - 任务调度：`rayon`/`tokio` 的工作窃取与异步执行器差异
  - 数据布局：`Vec<Struct>` → `Struct of Arrays` 在 SIMD/缓存上的优势

### 互链

- 与 `c05_threads`：线程池/工作窃取/同步原语的选型与代价
- 与 `c06_async`：异步算法的背压与任务切换开销测量
