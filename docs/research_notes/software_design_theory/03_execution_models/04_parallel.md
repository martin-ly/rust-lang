# 并行执行模型形式化

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **分类**: 执行模型
> **安全边界**: 纯 Safe

---

## 📊 目录

- [并行执行模型形式化](#并行执行模型形式化)
  - [📊 目录](#-目录)
  - [形式化定义](#形式化定义)
  - [与并发的区别](#与并发的区别)
  - [Rust 实现与代码示例](#rust-实现与代码示例)
    - [Rayon 数据并行](#rayon-数据并行)
    - [std::thread 任务并行](#stdthread-任务并行)
  - [典型场景（实质内容）](#典型场景实质内容)
    - [与设计模式组合](#与设计模式组合)
    - [常见陷阱](#常见陷阱)
  - [Rayon 工作窃取与调度](#rayon-工作窃取与调度)
  - [原子操作与无锁](#原子操作与无锁)
  - [分治与递归并行](#分治与递归并行)
  - [典型场景扩展](#典型场景扩展)
  - [与异步组合](#与异步组合)
  - [反例](#反例)
  - [边界](#边界)
  - [与 Rust 1.93 的对应](#与-rust-193-的对应)
  - [实质内容五维自检](#实质内容五维自检)

---

## 形式化定义

**Def 1.1（并行执行）**:

并行执行满足：

- 多任务**同时**执行（多核）
- 数据并行：对集合 $S$ 划分为 $S_1, \ldots, S_k$，各子任务处理 $S_i$，结果合并
- 任务并行：fork-join，独立任务并行执行后汇合

**Def 1.2（数据并行）**:

$\mathit{par\_map}(f, S) = \mathit{merge}(\mathit{map}(f, S_1), \ldots, \mathit{map}(f, S_k))$，其中 $S = S_1 \cup \cdots \cup S_k$ 且 $S_i \cap S_j = \emptyset$。

**Axiom PL1**：并行任务无共享可变状态；或通过 Sync 保护。

**Axiom PL2**：任务结果合并顺序可无关（如归约满足结合律）；或任务顺序确定。

**定理 PL-T1**：Rayon 等库保证数据竞争自由；由 Send/Sync 与 [borrow_checker_proof](../../formal_methods/borrow_checker_proof.md)。

**引理 PL-L1（无共享可变）**：`par_iter` 闭包捕获为 move 或只读引用；各子任务无共享可变；归约满足结合律时结果确定。

*证明*：由 Axiom PL1；Rayon 工作窃取划分迭代器；闭包 `|x| x * 2` 无共享状态；`sum` 为结合归约。∎

**推论 PL-C1**：并行与异步可组合（如 `tokio::task::spawn_blocking` + rayon）；组合时 Send/Sync 约束取并集。

---

## 与并发的区别

| 概念 | 并发 | 并行 |
| :--- | :--- | :--- |
| 定义 | 多任务可交错 | 多任务同时执行 |
| 单核 | 可并发（时间片） | 不可并行 |
| 多核 | 可并发可并行 | 可并行 |

---

## Rust 实现与代码示例

### Rayon 数据并行

```rust
use rayon::prelude::*;

let v: Vec<i32> = (0..1000).collect();
let sum: i32 = v.par_iter()
    .map(|x| x * 2)
    .sum();
assert_eq!(sum, 999 * 1000);
```

### std::thread 任务并行

```rust
use std::thread;

let h1 = thread::spawn(|| 1 + 2);
let h2 = thread::spawn(|| 3 * 4);
let a = h1.join().unwrap();
let b = h2.join().unwrap();
assert_eq!(a + b, 15);
```

**形式化对应**：`par_iter` 将迭代器划分为子范围，各线程处理；`map` 为纯函数，无共享可变；`join` 等待子线程完成，获取返回值。

---

## 典型场景（实质内容）

| 场景 | 说明 | 代码示例 |
| :--- | :--- | :--- |
| 批量计算 | 矩阵运算、图像处理 | `v.par_iter().map(\|x\| x * 2).collect()` |
| 归约/聚合 | `par_iter().sum()`、`reduce` | `v.par_iter().sum()`、`reduce(\|\| 0, \|a, b\| a + b)` |
| 并行搜索 | 大集合中查找 | `par_iter().find_any(\|x\| x > 100)` |
| 分治 | `join` 递归划分 | `rayon::join(\|\| left(), \|\| right())` |
| 并行排序 | 多核快排 | `v.par_sort()`、`par_sort_unstable()` |
| 并行构建 | 并行构造集合 | `par_iter().map().collect()` |

### 与设计模式组合

| 组合 | 说明 |
| :--- | :--- |
| 并行 + Iterator | `par_iter` 扩展 `Iterator`；见 [iterator](../../01_design_patterns_formal/03_behavioral/iterator.md) |
| 并行 + Strategy | 可替换算法；`par_iter().map(\|x\| strategy.apply(x))` |
| 并行 + Flyweight | 共享不可变；`Arc` 在闭包中 move；见 [flyweight](../../01_design_patterns_formal/02_structural/flyweight.md) |
| 并行 + 通道 | 结果归约；`par_iter().for_each(\|x\| tx.send(x).ok())` |

### 常见陷阱

| 陷阱 | 后果 | 规避 |
| :--- | :--- | :--- |
| 闭包捕获非 Send | 编译错误 | 用 `Arc`；或 move 克隆 |
| 小数据量用 rayon | 调度开销大于收益 | 通常 > 1000 元素才考虑 |
| 归约非结合 | 结果非确定 | 仅用结合律操作（sum、product、min、max） |
| 并行闭包中共享可变 | 数据竞争 | 用 `Mutex` 或 每个任务独立输出后合并 |

---

## Rayon 工作窃取与调度

**Def 1.3（Work Stealing）**:

Rayon 使用工作窃取调度：线程池中空闲线程从忙碌线程的任务队列窃取任务，实现负载均衡。

**定理 PA-T2**：`par_iter` 划分无重叠；各闭包捕获需 `Send`；闭包内无共享可变（或通过 `Sync` 保护）；结果合并顺序由 `reduce`/`fold` 语义决定。

---

## 原子操作与无锁

**Def 1.4（原子操作）**:

```rust
use std::sync::atomic::{AtomicU64, Ordering};

let counter = AtomicU64::new(0);
counter.fetch_add(1, Ordering::SeqCst);

// 原子 CAS（Compare-And-Swap）
let mut current = counter.load(Ordering::Relaxed);
loop {
    match counter.compare_exchange(current, current + 1, Ordering::SeqCst, Ordering::Relaxed) {
        Ok(_) => break,
        Err(actual) => current = actual,
    }
}
```

**内存顺序**：`SeqCst`（最强）> `Acquire`/`Release` > `Relaxed`。跨线程同步需 `Acquire`-`Release` 配对。

---

## 分治与递归并行

```rust
use rayon::prelude::*;

fn parallel_quicksort<T: Send + Ord>(v: &mut [T]) {
    if v.len() <= 1 { return; }
    let mid = partition(v);
    let (left, right) = v.split_at_mut(mid);
    rayon::join(
        || parallel_quicksort(left),
        || parallel_quicksort(right),
    );
}
```

**形式化对应**：`rayon::join` 为 fork-join；`split_at_mut` 保证 disjoint 借用；`Send` 允许跨线程传递。

---

## 典型场景扩展

| 场景 | Rayon API | 说明 |
| :--- | :--- | :--- |
| map-reduce | `par_iter().map().reduce()` | 归约满足结合律 |
| 并行查找 | `par_iter().find_any()` | 找到即返回，不保证顺序 |
| 并行构造 | `par_iter().map().collect()` | 结果类型可 `FromParallelIterator` |
| 自定义并行 | `scope()`、`spawn()` | 受限作用域内 spawn |

---

## 与异步组合

| 组合 | 说明 | 示例 |
| :--- | :--- | :--- |
| 异步 + rayon | 在 async 中调用 `rayon::spawn` | CPU 密集在 rayon，I/O 在 tokio |
| 并行 + 通道 | 多个 rayon 任务向 channel 发送 | 生产者-消费者 |

---

## 反例

| 反例 | 后果 |
| :--- | :--- |
| 闭包捕获非 Send | 编译错误 |
| 在并行闭包中修改共享可变 | 数据竞争 |
| 递归深度过大 | 栈溢出；改用迭代 |

---

## 边界

| 维度 | 分类 |
| :--- | :--- |
| 安全 | 纯 Safe |
| 支持 | 库支持（rayon）；std 提供 thread |
| 表达 | 等价 |

---

## 与 Rust 1.93 的对应

| 1.93 特性 | 与本模型 | 说明 |
| :--- | :--- | :--- |
| 无新增影响 | — | rayon、并行原语语义稳定 |
| 92 项落点 | 无 | 见 [06_boundary_analysis](06_boundary_analysis.md#rust-193-执行模型相关变更) |

---

## 实质内容五维自检

| 自检项 | 状态 | 说明 |
| :--- | :--- | :--- |
| 形式化 | ✅ | Def 1.1、与并发区别 |
| 代码 | ✅ | 可运行示例 |
| 场景 | ✅ | 典型场景、Rayon 调度 |
| 反例 | ✅ | 闭包非 Send、共享可变 |
| 衔接 | ✅ | Send、ownership、async 组合 |
| 权威对应 | ✅ | [formal_methods](../../formal_methods/README.md)、[Rayon](https://github.com/rayon-rs/rayon) |
