# 优化算法

## 1. 通用优化框架

- 目标函数、约束、可行域、最优性判据
- Rust trait抽象优化问题与优化器

## 2. 贪心、动态规划、分支限界

- 贪心算法：活动选择、最小生成树
- 动态规划：背包、最长子序列、矩阵链乘
- 分支限界：TSP、整数规划

## 3. 启发式与元启发式

- 局部搜索、模拟退火、遗传算法、蚁群/粒子群

## 4. 工程案例

### 4.1 动态规划背包

```rust
fn knapsack(weights: &[usize], values: &[usize], capacity: usize) -> usize { /* ... */ }
```

### 4.2 贪心活动选择

```rust
fn activity_selection(start: &[usize], finish: &[usize]) -> Vec<usize> { /* ... */ }
```

### 4.3 模拟退火TSP

```rust
struct SimulatedAnnealing { /* ... */ }
impl Optimizer<TSP> for SimulatedAnnealing { /* ... */ }
```

## 5. 批判性分析与未来展望

- 优化算法需关注问题规模、收敛性与工程可扩展性
- 未来可探索AI驱动的自适应优化与大规模分布式优化
