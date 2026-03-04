# Rayon并行计算形式化分析

> **主题**: 数据并行计算
> **形式化框架**: 工作窃取 + 分治算法 + 确定性保证
> **参考**: Rayon Documentation (<https://docs.rs/rayon>)

---

## 目录

- [Rayon并行计算形式化分析](#rayon并行计算形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 并行迭代器](#2-并行迭代器)
    - [定义 PAR-ITER-1 ( ParallelIterator )](#定义-par-iter-1--paralleliterator-)
    - [定义 PAR-ITER-2 ( 分块策略 )](#定义-par-iter-2--分块策略-)
    - [定理 PAR-ITER-T1 ( 顺序等价 )](#定理-par-iter-t1--顺序等价-)
  - [3. join模式](#3-join模式)
    - [定义 JOIN-1 ( 并行递归 )](#定义-join-1--并行递归-)
    - [定义 JOIN-2 ( 停止条件 )](#定义-join-2--停止条件-)
  - [4. 作用域线程](#4-作用域线程)
    - [定义 SCOPE-1 ( scope创建 )](#定义-scope-1--scope创建-)
    - [定理 SCOPE-T1 ( 借用安全 )](#定理-scope-t1--借用安全-)
  - [5. 确定性保证](#5-确定性保证)
    - [定义 DETERM-1 ( 确定性 )](#定义-determ-1--确定性-)
    - [定理 DETERM-T1 ( 无竞态 )](#定理-determ-t1--无竞态-)
  - [6. 定理与证明](#6-定理与证明)
    - [定理 RAYON-T1 ( 线程安全 )](#定理-rayon-t1--线程安全-)
    - [定理 RAYON-T2 ( 负载自适应 )](#定理-rayon-t2--负载自适应-)
  - [7. 代码示例](#7-代码示例)
    - [示例1: 并行排序](#示例1-并行排序)
    - [示例2: 并行归约](#示例2-并行归约)
    - [示例3: 分治算法](#示例3-分治算法)

---

## 1. 引言

Rayon特点：

- 无副作用的数据并行
- 自动工作窃取
- 顺序退化为单线程
- 确定性执行

---

## 2. 并行迭代器

### 定义 PAR-ITER-1 ( ParallelIterator )

```rust
vec.par_iter()
    .map(|x| x * x)
    .filter(|x| *x > 10)
    .reduce(|| 0, |a, b| a + b)
```

**形式化**:

$$
\text{ParIter}(S) = \{ \text{map}, \text{filter}, \text{reduce}, \text{collect} \}
$$

### 定义 PAR-ITER-2 ( 分块策略 )

$$
\text{split}(n, p) = \{ [0, n/p), [n/p, 2n/p), \ldots \}
$$

### 定理 PAR-ITER-T1 ( 顺序等价 )

并行迭代器与顺序迭代器结果相同。

$$
\text{par\_iter}().\text{collect}() = \text{iter}().\text{collect}()
$$

---

## 3. join模式

### 定义 JOIN-1 ( 并行递归 )

```rust
fn fib(n: u32) -> u32 {
    if n < 2 { return n; }
    let (a, b) = rayon::join(
        || fib(n - 1),
        || fib(n - 2),
    );
    a + b
}
```

**形式化**:

$$
\text{join}(f_1, f_2) = (f_1(), f_2()) \text{ in parallel}
$$

### 定义 JOIN-2 ( 停止条件 )

$$
\text{join}(f_1, f_2) = \begin{cases}
\text{sequential}(f_1, f_2) & \text{if } \text{depth} > \text{threshold} \\
\text{parallel}(f_1, f_2) & \text{otherwise}
\end{cases}
$$

---

## 4. 作用域线程

### 定义 SCOPE-1 ( scope创建 )

```rust
rayon::scope(|s| {
    s.spawn(|s| { /* work 1 */ });
    s.spawn(|s| { /* work 2 */ });
});
// 所有任务完成后才退出
```

**形式化**:

$$
\text{scope}(f) = f(\text{spawner}) \text{ waits } \forall t \in \text{spawned}
$$

### 定理 SCOPE-T1 ( 借用安全 )

作用域内可引用外部数据。

$$
\text{scope}(|s| \{ s.spawn(|_| \&x) \}) \text{ safe } \forall x : \&T
$$

---

## 5. 确定性保证

### 定义 DETERM-1 ( 确定性 )

$$
\forall r : \text{RayonOp}.\ r \text{ produces same result on every run}
$$

### 定理 DETERM-T1 ( 无竞态 )

纯函数操作无竞态条件。

$$
\text{par\_iter}().\text{map}(f) \text{ race-free if } f \text{ pure}
$$

---

## 6. 定理与证明

### 定理 RAYON-T1 ( 线程安全 )

操作自动满足Send + Sync。

$$
\text{par\_iter}() \text{ requires } T : \text{Send},\ f : \text{Send} + \text{Sync}
$$

### 定理 RAYON-T2 ( 负载自适应 )

线程数自动适应CPU核心。

$$
\text{thread\_pool\_size} = \text{num\_cpus}
$$

---

## 7. 代码示例

### 示例1: 并行排序

```rust
use rayon::prelude::*;

fn parallel_sort<T: Ord + Send>(data: &mut [T]) {
    data.par_sort();
}

fn parallel_sort_by_key<T, K, F>(data: &mut [T], f: F)
where
    T: Send,
    K: Ord + Send,
    F: Fn(&T) -> K + Sync,
{
    data.par_sort_by_key(f);
}
```

### 示例2: 并行归约

```rust
use rayon::prelude::*;

fn parallel_sum(data: &[i32]) -> i32 {
    data.par_iter().sum()
}

fn parallel_histogram(text: &str) -> HashMap<char, usize> {
    text.par_chars()
        .filter(|c| c.is_alphabetic())
        .map(|c| c.to_ascii_lowercase())
        .fold(
            || HashMap::new(),
            |mut map, c| {
                *map.entry(c).or_insert(0) += 1;
                map
            },
        )
        .reduce(
            || HashMap::new(),
            |mut a, b| {
                for (k, v) in b {
                    *a.entry(k).or_insert(0) += v;
                }
                a
            },
        )
}
```

### 示例3: 分治算法

```rust
use rayon::prelude::*;

// 并行矩阵乘法
fn parallel_matmul(a: &[Vec<f64>], b: &[Vec<f64>]) -> Vec<Vec<f64>> {
    let n = a.len();
    let m = b[0].len();
    let p = b.len();

    (0..n).into_par_iter()
        .map(|i| {
            (0..m)
                .map(|j| {
                    (0..p)
                        .map(|k| a[i][k] * b[k][j])
                        .sum()
                })
                .collect()
        })
        .collect()
}
```

---

**维护者**: Rust Parallel Computing Formal Methods Team
**创建日期**: 2026-03-05
**Rayon版本**: 1.x
**状态**: ✅ 已对齐
