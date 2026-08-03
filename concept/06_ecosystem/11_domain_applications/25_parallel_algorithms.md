> **内容分级**: [专家级]
> **本节关键术语**: 并行前缀和 · 并行图算法 · fork-join · work-stealing · NUMA · 并行扫描 · 并行归约 · Rayon — [完整对照表](../../00_meta/01_terminology/01_terminology_glossary.md)

# 并行与并发算法

> **EN**: Parallel and Concurrent Algorithms in Rust
> **Summary**: Parallel and concurrent algorithms in Rust: task/data parallelism, fork-join, work-stealing, message passing, shared-state synchronization, NUMA awareness, and the Rayon implementation principles.
>
> **Rust 版本**: 1.97.1+ (Edition 2024)
> **受众**: [专家]
> **Bloom 层级**: L5-L6
> **权威来源**: 本文件为 `concept/` 权威页。
> **定位**: 本页讲解 Rust 中利用多核的并行与并发算法设计，覆盖数据并行、任务并行、图并行、消息传递、共享状态同步与调度器原理，代码位于 `crates/c08_algorithms/src/algorithms/parallel_algorithms.rs`。
>
> **前置概念**: [Concurrency](../../03_advanced/00_concurrency/01_concurrency.md) · [Data Structures in Rust](09_data_structures_in_rust.md) · [Advanced Data Structures](24_advanced_data_structures_implementation.md)
> **后置概念**: [Algorithm Engineering Practice](08_algorithm_engineering_practice.md) · [Async](../../03_advanced/01_async/01_async.md)

---

> **来源**:
> [Introduction to Algorithms (Cormen et al.)](https://mitpress.mit.edu/books/introduction-algorithms-fourth-edition) ·
> [Algorithm Engineering (Saunders / Demetrescu)](https://people.mpi-inf.mpg.de/~mehlhorn/LEDAbook.html) ·
> [Rayon docs](https://docs.rs/rayon/latest/rayon/) ·
> [Rust Atomics and Locks](https://marabos.nl/atomics/) ·
> [The Rust Programming Language](https://doc.rust-lang.org/book/title-page.html)

---

## 📑 目录

- [并行与并发算法](#并行与并发算法)
  - [📑 目录](#-目录)
  - [一、并行计算模型](#一并行计算模型)
  - [一.5 权威定义、核心属性与概念关系](#一5-权威定义核心属性与概念关系)
    - [1.5.1 权威定义](#151-权威定义)
    - [1.5.2 关键属性](#152-关键属性)
    - [1.5.3 概念关系](#153-概念关系)
  - [一.6 并发模型选型决策树](#一6-并发模型选型决策树)
  - [二、并行前缀和（Parallel Prefix Sum / Scan）](#二并行前缀和parallel-prefix-sum--scan)
  - [三、并行图算法](#三并行图算法)
    - [3.1 并行 BFS](#31-并行-bfs)
    - [3.2 并行 SSSP](#32-并行-sssp)
    - [3.3 并行 MST](#33-并行-mst)
  - [四、Fork-Join 与 Work-Stealing](#四fork-join-与-work-stealing)
  - [五、并行扫描与归约](#五并行扫描与归约)
  - [六、NUMA 感知](#六numa-感知)
  - [七、Rayon 实现原理](#七rayon-实现原理)
    - [7.1 ParallelIterator 语义](#71-paralleliterator-语义)
    - [7.2 rayon::Scope / spawn](#72-rayonscope--spawn)
    - [7.3 Lock-Free Linearizability](#73-lock-free-linearizability)
    - [7.4 Memory Ordering](#74-memory-ordering)
  - [七.5 标准库示例：分块并行归约](#七5-标准库示例分块并行归约)
  - [八、反例与陷阱](#八反例与陷阱)
    - [反例 1：在并行循环中修改共享可变状态](#反例-1在并行循环中修改共享可变状态)
    - [反例 2：任务粒度过细](#反例-2任务粒度过细)
    - [反例 3：忽略 Amdahl 定律](#反例-3忽略-amdahl-定律)
    - [反例 4：将 `Rc` 跨线程移动](#反例-4将-rc-跨线程移动)
  - [九、边界测试](#九边界测试)
    - [9.1 边界测试：空输入的前缀和](#91-边界测试空输入的前缀和)
    - [9.2 边界测试：BFS 起点孤立](#92-边界测试bfs-起点孤立)
    - [9.3 边界测试：单线程环境](#93-边界测试单线程环境)
  - [相关概念](#相关概念)
  - [十、思维导图](#十思维导图)
  - [十一、国际权威参考](#十一国际权威参考)
    - [11.1 与国际权威来源的对齐说明](#111-与国际权威来源的对齐说明)

---

## 一、并行计算模型

并行算法设计的核心矛盾：**可扩展性（scalability）** 与 **开销（overhead）**。划分任务、通信、同步、负载均衡是四大成本来源。

Rust 中常用的并行抽象：

| 抽象 | 代表 | 适用场景 |
|:---|:---|:---|
| 数据并行 | `rayon::par_iter` | 数组/集合的同构操作 |
| 任务并行 | `rayon::join` / `spawn` | 分治、树遍历 |
| 线程池 | `rayon::ThreadPool` | 固定资源池的批量任务 |
| 异步并发 | `tokio::spawn` | I/O 密集型，非 CPU 并行 |
| 无锁结构 | `crossbeam` / 自定义 | 高频共享状态 |

> **Amdahl 定律**：加速比受限于串行部分比例。若串行部分占 10%，最大加速比为 10×。来源: [Introduction to Algorithms](https://mitpress.mit.edu/books/introduction-algorithms-fourth-edition)

---

## 一.5 权威定义、核心属性与概念关系

### 1.5.1 权威定义

**并行（Parallelism）** 指利用多核同时执行独立计算以缩短 wall-clock 时间；**并发（Concurrency）** 指多个任务在重叠时间段内推进，可能通过分时、事件循环或线程交错实现。Rust 的算法视角通常同时涉及二者：并行算法强调**分解与合并**，并发算法强调**同步与通信**。

> **来源**: [The Art of Multiprocessor Programming](https://dl.acm.org/doi/10.5555/2385452) · [Rust Atomics and Locks](https://marabos.nl/atomics/)

### 1.5.2 关键属性

| 属性 | 含义 | Rust 表达 |
|:---|:---|:---|
| **可分解性（Decomposability）** | 问题能否拆分为可独立执行的子任务 | `slice::chunks` / `split_at_mut` / `rayon::join` |
| **可结合性（Associativity）** | 归约/合并操作是否满足结合律，从而允许任意分组 | `reduce` 要求 `⊗` 满足结合律 |
| **通信模式（Communication Pattern）** | 任务间交换数据的方式 | `mpsc` / `Arc<Mutex<T>>` / 原子类型 |
| **同步粒度（Synchronization Granularity）** | 临界区大小与频率 | `Mutex` 粗粒度 vs `Atomic*` 细粒度 |
| **负载均衡（Load Balance）** | 各执行单元工作量是否均匀 | `rayon` work-stealing / 静态分块 |
| **内存局部性（Locality）** | 数据是否靠近使用它的核心 | SOA / NUMA 分区 / 缓存行对齐 |

### 1.5.3 概念关系

```mermaid
graph LR
    A[并行与并发算法] --> B[数据并行]
    A --> C[任务并行]
    A --> D[消息传递]
    A --> E[共享状态]
    B --> F[par_iter / map-reduce]
    C --> G[fork-join / spawn]
    D --> H[mpsc / channel]
    E --> I[Mutex / RwLock / Atomic]
    E --> J[lock-free 结构]
```

> **认知功能**: 该关系图将并行/并发算法按“分解方式”与“通信方式”正交拆分，帮助读者从问题结构出发选择 Rust 抽象。

---

## 一.6 并发模型选型决策树

```mermaid
graph TD
    A[需要同时推进多个任务?] --> B{任务间是否共享可变状态?}
    B -->|否| C[消息传递: std::sync::mpsc / tokio::sync]
    B -->|是| D{读写比例如何?}
    D -->|读多写少| E[std::sync::RwLock 或 原子读计数]
    D -->|频繁写| F[std::sync::Mutex 或 细粒度 Atomic]
    D -->|极高竞争 / 实时性| G[crossbeam::queue / 自定义 lock-free]
    C --> H{是否 CPU 密集型数据并行?}
    H -->|是| I[rayon::par_iter / join]
    H -->|否| J[async runtime: tokio::spawn]
    F --> K[保持临界区最小化]
    G --> L[证明 linearizability 与内存安全]
```

**选型说明**:

- 消息传递天然避免数据竞争，适合生产者-消费者、流水线。
- 共享可变状态需要 `Send`/`Sync` 边界；`Mutex` 简单但易成为瓶颈。
- 高竞争场景优先 lock-free / wait-free 结构，但实现复杂度和正确性证明成本更高。

> **来源**: [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) · [The Rust Programming Language — Fearless Concurrency](https://doc.rust-lang.org/book/ch16-00-concurrency.html)

---

## 二、并行前缀和（Parallel Prefix Sum / Scan）

并行前缀和是数据并行的经典问题：计算数组的累积和。两阶段算法时间复杂度 O(n/p + log p)。

```rust
// 来源: crates/c08_algorithms/src/algorithms/parallel_algorithms.rs
use c08_algorithms::algorithms::parallel_algorithms::parallel_prefix_sum;

fn main() {
    let input = vec![1, 2, 3, 4, 5];
    let result = parallel_prefix_sum(&input);
    assert_eq!(result, vec![1, 3, 6, 10, 15]);
}
```

> **原理**：
>
> 1. 将数组分块，每块独立计算局部前缀和；
> 2. 计算块间偏移量；
> 3. 将偏移量并行加到各块。
> 来源: [parallel_algorithms.rs](../../../../crates/c08_algorithms/src/algorithms/parallel_algorithms.rs)

---

## 三、并行图算法

### 3.1 并行 BFS

并行 BFS 把当前 frontier 的所有邻居并行展开，再合并去重。

```rust
use c08_algorithms::algorithms::parallel_algorithms::parallel_bfs;

fn main() {
    let graph = vec![
        vec![1, 2],
        vec![0, 3],
        vec![0, 3],
        vec![1, 2],
    ];
    let dist = parallel_bfs(&graph, 0);
    assert_eq!(dist, vec![Some(0), Some(1), Some(1), Some(2)]);
}
```

> **注意**：frontier 扩展的并行化收益取决于图的平均度数；稀疏图可能因同步开销而收益有限。来源: [parallel_algorithms.rs](../../../../crates/c08_algorithms/src/algorithms/parallel_algorithms.rs)

### 3.2 并行 SSSP

并行 Dijkstra 使用优先队列串行选择当前最近节点，但对其所有出边并行松弛。

```rust
use c08_algorithms::algorithms::parallel_algorithms::parallel_dijkstra;

fn main() {
    let graph = vec![
        vec![(1, 1), (2, 4)],
        vec![(2, 2), (3, 5)],
        vec![(3, 1)],
        vec![],
    ];
    let dist = parallel_dijkstra(&graph, 0);
    assert_eq!(dist, vec![Some(0), Some(1), Some(3), Some(4)]);
}
```

> **局限**：优先队列仍是串行瓶颈；Delta-stepping 或 Bellman-Ford 更适合大规模并行。来源: [parallel_algorithms.rs](../../../../crates/c08_algorithms/src/algorithms/parallel_algorithms.rs)

### 3.3 并行 MST

Kruskal 算法的排序步骤可并行化（`par_sort_unstable`），并查集合并通常串行执行。

```rust
use c08_algorithms::algorithms::parallel_algorithms::parallel_kruskal;

fn main() {
    let edges = vec![(0, 1, 1), (1, 2, 2), (0, 2, 3)];
    let mst = parallel_kruskal(3, edges);
    assert_eq!(mst.iter().map(|e| e.2).sum::<u64>(), 3);
}
```

> **来源**: [parallel_algorithms.rs](../../../../crates/c08_algorithms/src/algorithms/parallel_algorithms.rs)

---

## 四、Fork-Join 与 Work-Stealing

Fork-Join 是最自然的并行分治模型：任务分成两个子任务，分别执行，再合并结果。

```rust,ignore
// 依赖 workspace crate c08_algorithms，在独立测试 harness 中无法解析路径
use c08_algorithms::algorithms::parallel_algorithms::fork_join_sum;

fn main() {
    let input: Vec<i64> = (1..=1000).collect();
    assert_eq!(fork_join_sum(&input), input.iter().sum());
}
```

Work-stealing 调度器（如 Rayon）让每个线程维护一个双端队列：

- **owner** 在尾部 push/pop 自己产生的任务；
- **空闲线程** 从其他线程的头部 steal 任务。

这种设计减少了竞争：owner 操作无需同步，只有 steal 需要 CAS。来源: [Rust Atomics and Locks](https://marabos.nl/atomics/)

---

## 五、并行扫描与归约

| 操作 | 语义 | Rayon API |
|:---|:---|:---|
| 归约 | `a1 ⊗ a2 ⊗ ... ⊗ an` | `par_iter().reduce` / `sum` |
| 扫描 | 前缀累积 | `par_iter().fold` + 合并 |
| 过滤 | 保留满足条件的元素 | `par_iter().filter` |
| 映射 | 对每个元素独立变换 | `par_iter().map` |

```rust
use rayon::prelude::*;

fn main() {
    let v: Vec<i64> = (1..=100).collect();
    let sum: i64 = v.par_iter().sum();
    let evens: Vec<&i64> = v.par_iter().filter(|&&x| x % 2 == 0).collect();
    let squares: Vec<i64> = v.par_iter().map(|&x| x * x).collect();
}
```

---

## 六、NUMA 感知

NUMA（Non-Uniform Memory Access）下，访问本地节点内存比远程节点快数倍。NUMA 感知策略：

1. **数据局部性**：尽量让计算线程访问其所在节点的数据。
2. **首次写入定位**：由最终使用该数据的线程初始化内存，避免首次访问触发远程页错误。
3. **分区并行**：将大数组按 NUMA 节点分区，每节点独立计算后合并。

Rust 生态中可使用 `hwloc` / `numa` crate 获取拓扑信息。生产级 NUMA 优化通常需要自定义分配器与线程绑定。

```rust
use rayon::prelude::*;

// 概念性 NUMA 分区求和
fn numa_aware_sum(data: &[i64], numa_nodes: usize) -> i64 {
    let chunk_size = (data.len() + numa_nodes - 1) / numa_nodes;
    data.par_chunks(chunk_size)
        .map(|chunk| chunk.iter().sum::<i64>())
        .sum()
}
```

---

## 七、Rayon 实现原理

Rayon 是 Rust 生态最广泛使用的数据并行库，核心设计：

1. **无全局锁**：每个工作线程有自己的 work-stealing deque。
2. **惰性任务拆分**：`par_iter` 先按范围描述任务，只有线程需要工作时才拆分到更细粒度。
3. **自适应阈值**：当任务足够小时停止拆分，避免调度开销超过收益。
4. **借用安全**：Rayon 的 `ParallelIterator` 在编译期保证闭包满足 `Send`/`Sync`。

```rust
use rayon::prelude::*;

fn parallel_sum(data: &[i64]) -> i64 {
    data.par_iter().sum()
}
```

> **关键洞察**：Rayon 把"递归串行算法"通过 `join` 或 `par_iter` 自动并行化，调用方无需管理线程。来源: [Rayon docs](https://docs.rs/rayon/latest/rayon/)

### 7.1 ParallelIterator 语义

`ParallelIterator` 是 Rayon 对「可并行遍历集合」的抽象。它的关键语义保证：

1. **顺序无关性**：`par_iter()` 不保证元素处理顺序，依赖顺序的算法（如依赖前一项状态的前缀和）需要特殊处理；
2. **折叠与归约**：`fold` 对每个子范围独立累加，`reduce` 把子结果合并，要求合并操作满足结合律；
3. **惰性执行**：`par_iter().map(...).filter(...)` 不立即执行，直到遇到 `collect()` / `sum()` / `reduce()` 等终结操作；
4. **Send/Sync 保证**：闭包与数据必须满足 `Send`，闭包捕获的共享状态必须满足 `Sync`。

```rust,ignore
use rayon::prelude::*;

fn parallel_word_lengths(texts: &[String]) -> usize {
    texts
        .par_iter()
        .map(|s| s.len())
        .reduce(|| 0, |a, b| a + b)
}
```

> **注意**：`reduce` 的 identity 函数 `|| 0` 与合并函数 `|a, b| a + b` 必须满足结合律与单位元律，否则结果可能随任务拆分方式变化。

### 7.2 rayon::Scope / spawn

`rayon::scope` 允许在当前线程阻塞等待的同时，向线程池提交子任务。子任务可以借用父线程栈上的数据（因为 scope 保证所有子任务完成后才返回）。

```rust,ignore
use rayon::scope;

fn parallel_search(haystack: &[i32], needle: i32) -> Option<usize> {
    let mut result: Option<usize> = None;
    scope(|s| {
        let mid = haystack.len() / 2;
        let (left, right) = haystack.split_at(mid);
        s.spawn(|_| {
            if let Some(idx) = linear_search(left, needle) {
                // 注意：多个线程可能同时找到结果，需要同步写入
            }
        });
        s.spawn(|_| {
            if let Some(idx) = linear_search(right, needle) {
                result = Some(idx + mid);
            }
        });
    });
    result
}

fn linear_search(arr: &[i32], needle: i32) -> Option<usize> {
    arr.iter().position(|&x| x == needle)
}
```

> **安全保证**：`scope` 确保所有 `spawn` 的任务在 scope 结束前完成，因此子任务可以安全借用父作用域的引用。这与裸 `std::thread::spawn` 不同——后者要求 `'static` 闭包。

### 7.3 Lock-Free Linearizability

Lock-free 算法保证至少有一个线程在有限步内完成操作（系统整体持续进展）。其正确性通常用 **linearizability** 描述：每个并发操作看起来都在某个瞬间原子完成。

**与 Rayon 的区别**：

| 维度 | Rayon fork-join | Lock-free 数据结构 |
|---|---|---|
| 抽象层级 | 任务并行框架 | 共享状态并发原语 |
| 典型实现 | `par_iter()` / `join()` | `crossbeam::queue::ArrayQueue` |
| 同步机制 | work-stealing deque | CAS 循环 |
| 正确性标准 | 结果确定性 | linearizability |

```rust,ignore
use crossbeam::queue::ArrayQueue;
use std::sync::Arc;

fn lock_free_producer_consumer() {
    let q = Arc::new(ArrayQueue::new(1024));
    let q2 = Arc::clone(&q);

    std::thread::spawn(move || {
        for i in 0..100 {
            loop {
                if q2.push(i).is_ok() { break; }
            }
        }
    });

    for _ in 0..100 {
        loop {
            if let Some(v) = q.pop() {
                println!("{}", v);
                break;
            }
        }
    }
}
```

### 7.4 Memory Ordering

并行算法中，原子操作的内存序决定线程间可见性。Rust 标准库提供五种 ordering：

| Ordering | 语义 | 适用场景 |
|---|---|---|
| `Relaxed` | 仅保证原子性 | 单调计数器，不依赖顺序 |
| `Acquire` | 读操作，建立 happens-before | 读取共享指针/标志 |
| `Release` | 写操作，建立 happens-before | 写入共享指针/标志 |
| `AcqRel` | 读+写同时建立 | CAS 循环 |
| `SeqCst` | 全局一致顺序 | 多线程状态机、flag 同步 |

```rust
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread;

fn memory_ordering_example() {
    let data = AtomicUsize::new(0);
    let ready = AtomicBool::new(false);

    let ready_ref = Arc::new(ready);
    let data_ref = Arc::new(data);

    let r = Arc::clone(&ready_ref);
    let d = Arc::clone(&data_ref);
    thread::spawn(move || {
        d.store(42, Ordering::Release);
        r.store(true, Ordering::Release);
    });

    while !ready_ref.load(Ordering::Acquire) {
        thread::yield_now();
    }
    assert_eq!(data_ref.load(Ordering::Acquire), 42);
}
```

> **建议**：默认使用 `Acquire`/`Release` 组合；仅在能证明全局顺序必要时使用 `SeqCst`，因为更强的顺序会限制编译器/CPU 优化。来源: [Rust Atomics and Locks](https://marabos.nl/atomics/)

---

## 七.5 标准库示例：分块并行归约

下面的实现仅使用 `std::thread::scope`，不依赖 `rayon` 等外部 crate。`scope` 保证所有子线程在 scope 返回前结束，因此子任务可以安全借用父作用域的切片引用。

```rust
use std::thread;

fn parallel_chunk_sum(data: &[i64], workers: usize) -> i64 {
    if workers == 0 || data.is_empty() {
        return data.iter().sum();
    }
    let chunk_size = (data.len() + workers - 1) / workers;
    thread::scope(|s| {
        let handles: Vec<_> = data
            .chunks(chunk_size)
            .map(|chunk| s.spawn(move || chunk.iter().sum::<i64>()))
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).sum()
    })
}

fn main() {
    let v: Vec<i64> = (1..=1000).collect();
    assert_eq!(parallel_chunk_sum(&v, 4), v.iter().sum());
}
```

> **要点**:
>
> - `thread::scope` 子线程借用非 `'static` 数据，是 Rust 标准库对 fork-join 模型的直接支持；
> - 静态分块简单，但当各 chunk 工作量差异大时负载不均衡，此时应使用 work-stealing（如 Rayon）。
>
> **来源**: [The Rust Reference — Thread scopes](https://doc.rust-lang.org/reference/) · [The Rust Programming Language](https://doc.rust-lang.org/book/title-page.html)

---

## 八、反例与陷阱

### 反例 1：在并行循环中修改共享可变状态

```rust,compile_fail
use rayon::prelude::*;

fn main() {
    let mut sum = 0;
    (0..100).into_par_iter().for_each(|i| {
        sum += i; // ❌ 编译错误：sum 不能跨线程共享可变引用
    });
}
```

> **修正**：使用 `sum()`、`reduce()` 或 `AtomicUsize`。来源: [Rayon docs](https://docs.rs/rayon/latest/rayon/)

### 反例 2：任务粒度过细

```rust,ignore
// ❌ 每个元素都 spawn，调度开销爆炸
(0..1_000_000).into_par_iter().for_each(|_| tiny_work());

// ✅ 使用 par_iter，让 Rayon 自适应拆分
```

### 反例 3：忽略 Amdahl 定律

```rust,ignore
// ❌ 并行化一个串行部分占 90% 的算法
let result = serial_part(); // 90%
result.par_iter().map(|x| parallel_part(x)).collect(); // 10%
```

> **修正**：先优化串行瓶颈，再考虑并行化。来源: [The Rust Performance Book](https://nnethercote.github.io/perf-book/)

### 反例 4：将 `Rc` 跨线程移动

```rust,compile_fail,E0277
use std::rc::Rc;
use std::thread;

fn main() {
    let counter = Rc::new(0);
    let c = Rc::clone(&counter);
    thread::spawn(move || {
        println!("{}", c);
    });
}
```

> **错误原因**: `Rc<T>` 不是 `Send`，因为它使用非原子引用计数，跨线程移动会导致数据竞争。应改用 `Arc<T>`。
>
> **来源**: [The Rustonomicon — Send and Sync](https://doc.rust-lang.org/nomicon/send-and-sync.html) · [The Rust Programming Language](https://doc.rust-lang.org/book/ch16-00-concurrency.html)

---

## 九、边界测试

### 9.1 边界测试：空输入的前缀和

```rust
use c08_algorithms::algorithms::parallel_algorithms::parallel_prefix_sum;

fn main() {
    let result = parallel_prefix_sum(&[]);
    assert!(result.is_empty());
}
```

> **诊断**: 空输入应返回空 Vec，避免越界。来源: [parallel_algorithms.rs](../../../../crates/c08_algorithms/src/algorithms/parallel_algorithms.rs)

### 9.2 边界测试：BFS 起点孤立

```rust
use c08_algorithms::algorithms::parallel_algorithms::parallel_bfs;

fn main() {
    let graph = vec![vec![], vec![0]];
    let dist = parallel_bfs(&graph, 0);
    assert_eq!(dist, vec![Some(0), None]);
}
```

> **诊断**: 不可达节点应保持 `None`。来源: [parallel_algorithms.rs](../../../../crates/c08_algorithms/src/algorithms/parallel_algorithms.rs)

### 9.3 边界测试：单线程环境

```rust
use rayon::prelude::*;

fn main() {
    let pool = rayon::ThreadPoolBuilder::new().num_threads(1).build().unwrap();
    let sum: i64 = pool.install(|| (0..100).into_par_iter().sum());
    assert_eq!(sum, 4950);
}
```

> **诊断**: 单线程下并行算法应正确退化，结果与多线程一致。来源: [Rayon ThreadPoolBuilder](https://docs.rs/rayon/latest/rayon/struct.ThreadPoolBuilder.html)

---

---

## 相关概念

- [Rust vs C++：形式系统模型 vs 机制工程模型](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md)
- [形式化算法理论](../../04_formal/00_type_theory/13_formal_algorithm_theory.md)

## 十、思维导图

```mermaid
mindmap
  root((并行与并发算法))
    数据并行
      并行前缀和
      并行扫描
      并行归约
    图并行
      并行 BFS
      并行 SSSP
      并行 MST
    调度模型
      Fork-Join
      Work-Stealing
      NUMA 感知
    并发通信
      消息传递 mpsc
      共享状态 Mutex/RwLock
      Lock-Free 结构
    Rayon 语义
      ParallelIterator
      rayon::Scope / spawn
    内存模型
      Memory Ordering
      happens-before
    生态
      Rayon
      crossbeam
      std::thread::scope
```

> **认知功能**: 本 mindmap 按“数据并行、图并行、调度模型、并发通信、内存模型、生态”组织并行与并发算法知识，帮助读者从问题结构、通信方式到调度原理建立完整视图。来源: [Introduction to Algorithms](https://mitpress.mit.edu/books/introduction-algorithms-fourth-edition)

---

## 十一、国际权威参考

- **P1 学术**: [Introduction to Algorithms (Cormen et al.)](https://mitpress.mit.edu/books/introduction-algorithms-fourth-edition)
- **P1 学术**: [Algorithm Engineering (Saunders / Demetrescu)](https://people.mpi-inf.mpg.de/~mehlhorn/LEDAbook.html)
- **P1 学术**: [Blumofe & Leiserson — Scheduling Multithreaded Computations by Work Stealing (ACM)](https://dl.acm.org/doi/10.1145/209936.209958)
- **P1 学术**: [Blelloch — Prefix Sums and Their Applications (IEEE)](https://ieeexplore.ieee.org/document/42122)
- **P1 并发**: [Rust Atomics and Locks](https://marabos.nl/atomics/)
- **P1 并发**: [Herlihy & Shavit — The Art of Multiprocessor Programming](https://dl.acm.org/doi/10.5555/2385452)
- **P2 生态**: [Rayon docs](https://docs.rs/rayon/latest/rayon/)
- **P2 生态**: [crossbeam docs](https://docs.rs/crossbeam/latest/crossbeam/)
- **P0 官方**: [The Rust Programming Language](https://doc.rust-lang.org/book/title-page.html)
- **P0 官方**: [Rust Reference — Atomics](https://doc.rust-lang.org/reference/items/associated-items.html)
- **P0 官方**: [The Rustonomicon — Send and Sync](https://doc.rust-lang.org/nomicon/send-and-sync.html)
- **P0 官方**: [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)
- **P1 性能**: [The Rust Performance Book](https://nnethercote.github.io/perf-book/)

### 11.1 与国际权威来源的对齐说明

| 主题 | 权威来源 | 对齐要点 |
|:---|:---|:---|
| `Send`/`Sync` 边界 | The Rustonomicon | 跨线程移动/共享类型必须实现 `Send`/`Sync`；`Rc` 非 `Send` 是故意的性能-安全权衡 |
| 线程作用域与借用 | The Rust Reference / TRPL ch16 | `std::thread::scope` 允许非 `'static` 借用，官方对 fork-join 模型的支持 |
| 数据并行 API | Rayon docs | `ParallelIterator` 要求闭包 `Send`、归约操作满足结合律 |
| 并发算法理论 | Herlihy & Shavit | linearizability、work-stealing、lock-free/wait-free 分类 |
| 并行复杂度 | CLRS / Blelloch | 并行前缀和 `O(n/p + log p)`、Amdahl 定律 |
| API 设计 | Rust API Guidelines | 并发类型应显式标注 `Send`/`Sync`、避免隐藏的全局状态 |

> **权威来源**: [Introduction to Algorithms](https://mitpress.mit.edu/books/introduction-algorithms-fourth-edition), [Rayon docs](https://docs.rs/rayon/latest/rayon/), [Rust Atomics and Locks](https://marabos.nl/atomics/)
> **状态**: ✅ 概念文件扩展完成
> **最后更新**: 2026-08-03
