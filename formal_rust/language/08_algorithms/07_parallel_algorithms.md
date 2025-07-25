# 并行算法设计

## 1. 并行计算模型

- PRAM、Fork-Join、MapReduce等
- 并行复杂度、加速比、Amdahl定律

## 2. 分治与并行化

- 分治递归的并行实现
- 并行归并、并行快速排序、并行前缀和

## 3. 并行加速与负载均衡

- 动态任务分配、工作窃取、负载均衡
- Rust rayon、crossbeam等库支持

## 4. 工程案例

### 4.1 并行归并排序

```rust
use rayon::prelude::*;
pub fn parallel_merge_sort<T: Ord + Send + Clone>(arr: &mut [T]) { /* ... */ }
```

### 4.2 并行前缀和

```rust
use rayon::prelude::*;
pub fn parallel_prefix_sum(arr: &mut [i32]) { /* ... */ }
```

## 5. 批判性分析与未来展望

- 并行算法需关注任务划分、同步开销与可扩展性
- 未来可探索异构并行、分布式并行与AI驱动并行优化
