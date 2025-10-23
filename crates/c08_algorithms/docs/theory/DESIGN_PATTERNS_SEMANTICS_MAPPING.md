# 设计模式与算法语义模型映射

**版本**: 1.0.0  
**Rust版本**: 1.90+  
**Edition**: 2024  
**最后更新**: 2025-10-02

---

## 📖 目录

- [设计模式与算法语义模型映射](#设计模式与算法语义模型映射)
  - [📖 目录](#-目录)
  - [1. 概述](#1-概述)
    - [1.1 设计模式与算法的关系](#11-设计模式与算法的关系)
    - [1.2 语义模型映射](#12-语义模型映射)
  - [2. 经典设计模式在算法中的应用](#2-经典设计模式在算法中的应用)
    - [2.1 Strategy Pattern（策略模式）](#21-strategy-pattern策略模式)
      - [形式化定义](#形式化定义)
      - [Rust实现](#rust实现)
      - [语义模型](#语义模型)
    - [2.2 Template Method Pattern（模板方法）](#22-template-method-pattern模板方法)
      - [Rust实现1](#rust实现1)
      - [语义模型（霍尔逻辑）](#语义模型霍尔逻辑)
    - [2.3 Iterator Pattern（迭代器）](#23-iterator-pattern迭代器)
      - [Rust实现（DFS迭代器）](#rust实现dfs迭代器)
      - [语义模型1](#语义模型1)
    - [2.4 Observer Pattern（观察者）](#24-observer-pattern观察者)
      - [Rust实现（增量最短路径）](#rust实现增量最短路径)
      - [语义模型2](#语义模型2)
  - [3. 算法专属模式](#3-算法专属模式)
    - [3.1 Memoization Pattern（记忆化）](#31-memoization-pattern记忆化)
      - [Rust实现2](#rust实现2)
      - [语义等价性](#语义等价性)
    - [3.2 Lazy Evaluation Pattern（惰性求值）](#32-lazy-evaluation-pattern惰性求值)
      - [Rust实现3](#rust实现3)
      - [语义模型（Call-by-Need）](#语义模型call-by-need)
    - [3.3 Continuation-Passing Style (CPS)](#33-continuation-passing-style-cps)
      - [Rust实现4](#rust实现4)
      - [语义模型3](#语义模型3)
  - [4. 并发模式](#4-并发模式)
    - [4.1 Actor Pattern](#41-actor-pattern)
      - [简要实现](#简要实现)
    - [4.2 Pipeline Pattern](#42-pipeline-pattern)
      - [Rust实现5](#rust实现5)
  - [5. 语义模型映射](#5-语义模型映射)
    - [5.1 类型系统映射](#51-类型系统映射)
    - [5.2 所有权与分离逻辑](#52-所有权与分离逻辑)
    - [5.3 并发模型映射](#53-并发模型映射)
  - [6. Rust特有模式](#6-rust特有模式)
    - [6.1 Typestate Pattern（类型状态）](#61-typestate-pattern类型状态)
      - [实现](#实现)
    - [6.2 Newtype Pattern](#62-newtype-pattern)
      - [实现3](#实现3)
  - [7. 等价关系分析](#7-等价关系分析)
    - [7.1 算法等价性](#71-算法等价性)
    - [7.2 模式等价性](#72-模式等价性)
    - [7.3 同步异步等价](#73-同步异步等价)
  - [总结](#总结)
    - [核心映射](#核心映射)
    - [学习路径](#学习路径)

---

## 1. 概述

### 1.1 设计模式与算法的关系

**设计模式** (Design Pattern) 是解决特定问题的可复用方案。  
**算法** (Algorithm) 是解决计算问题的具体步骤。

**映射关系**：

```text
设计模式          →  算法实现
────────────────────────────────
Strategy         →  算法族（排序、搜索）
Iterator         →  遍历算法（DFS、BFS）
Template Method  →  算法框架（分治、DP）
Observer         →  事件驱动算法
Visitor          →  图遍历
Composite        →  树形算法
State            →  状态机算法
```

### 1.2 语义模型映射

```text
设计模式语义      ↔  形式化语义
─────────────────────────────────
继承多态          ↔  子类型多态 (Subtyping)
泛型              ↔  参数多态 (Parametric)
接口              ↔  特设多态 (Ad-hoc/Traits)
组合              ↔  积类型 (Product Types)
变体              ↔  和类型 (Sum Types)
高阶函数          ↔  λ抽象
状态              ↔  单子 (Monad)
```

---

## 2. 经典设计模式在算法中的应用

### 2.1 Strategy Pattern（策略模式）

**定义**：定义算法族，封装每个算法，使它们可互换。

**算法应用**：排序算法族、搜索算法族

#### 形式化定义

```text
Strategy<I, O> = {
  algorithms: Set<Algorithm<I, O>>,
  select: Context → Algorithm<I, O>
}
```

#### Rust实现

```rust
/// 策略模式：算法族trait
pub trait SortStrategy<T> {
    /// 算法名称
    fn name(&self) -> &'static str;
    
    /// 执行排序
    fn sort(&self, data: &mut [T])
    where
        T: Ord;
    
    /// 时间复杂度
    fn time_complexity(&self) -> &'static str;
}

/// 快速排序策略
pub struct QuickSortStrategy;

impl<T> SortStrategy<T> for QuickSortStrategy {
    fn name(&self) -> &'static str {
        "QuickSort"
    }
    
    fn sort(&self, data: &mut [T])
    where
        T: Ord,
    {
        if data.len() <= 1 {
            return;
        }
        quick_sort_impl(data);
    }
    
    fn time_complexity(&self) -> &'static str {
        "O(n log n) average, O(n²) worst"
    }
}

/// 归并排序策略
pub struct MergeSortStrategy;

impl<T> SortStrategy<T> for MergeSortStrategy {
    fn name(&self) -> &'static str {
        "MergeSort"
    }
    
    fn sort(&self, data: &mut [T])
    where
        T: Ord + Clone,
    {
        let sorted = merge_sort_impl(data);
        data.copy_from_slice(&sorted);
    }
    
    fn time_complexity(&self) -> &'static str {
        "O(n log n) worst case"
    }
}

/// 上下文：选择策略
pub struct SortContext<T> {
    strategy: Box<dyn SortStrategy<T>>,
}

impl<T: Ord + Clone> SortContext<T> {
    /// 根据数据特征选择策略
    pub fn new(data: &[T]) -> Self {
        let strategy: Box<dyn SortStrategy<T>> = if data.len() < 100 {
            Box::new(InsertionSortStrategy)
        } else if data.is_sorted() {
            Box::new(TimSortStrategy)
        } else {
            Box::new(QuickSortStrategy)
        };
        
        Self { strategy }
    }
    
    pub fn execute(&self, data: &mut [T]) {
        self.strategy.sort(data);
    }
}

// 辅助函数定义
fn quick_sort_impl<T: Ord>(data: &mut [T]) {
    // 快排实现
    if data.len() <= 1 {
        return;
    }
    let pivot_idx = partition(data);
    let (left, right) = data.split_at_mut(pivot_idx);
    quick_sort_impl(left);
    if right.len() > 1 {
        quick_sort_impl(&mut right[1..]);
    }
}

fn partition<T: Ord>(data: &mut [T]) -> usize {
    let len = data.len();
    let pivot_idx = len - 1;
    let mut i = 0;
    for j in 0..pivot_idx {
        if data[j] <= data[pivot_idx] {
            data.swap(i, j);
            i += 1;
        }
    }
    data.swap(i, pivot_idx);
    i
}

fn merge_sort_impl<T: Ord + Clone>(data: &[T]) -> Vec<T> {
    // 归并排序实现
    if data.len() <= 1 {
        return data.to_vec();
    }
    let mid = data.len() / 2;
    let left = merge_sort_impl(&data[..mid]);
    let right = merge_sort_impl(&data[mid..]);
    merge(left, right)
}

fn merge<T: Ord + Clone>(left: Vec<T>, right: Vec<T>) -> Vec<T> {
    let mut result = Vec::with_capacity(left.len() + right.len());
    let mut i = 0;
    let mut j = 0;
    
    while i < left.len() && j < right.len() {
        if left[i] <= right[j] {
            result.push(left[i].clone());
            i += 1;
        } else {
            result.push(right[j].clone());
            j += 1;
        }
    }
    
    result.extend_from_slice(&left[i..]);
    result.extend_from_slice(&right[j..]);
    result
}

pub struct InsertionSortStrategy;
impl<T: Ord> SortStrategy<T> for InsertionSortStrategy {
    fn name(&self) -> &'static str { "InsertionSort" }
    fn sort(&self, data: &mut [T]) where T: Ord {
        for i in 1..data.len() {
            let mut j = i;
            while j > 0 && data[j-1] > data[j] {
                data.swap(j-1, j);
                j -= 1;
            }
        }
    }
    fn time_complexity(&self) -> &'static str { "O(n²)" }
}

pub struct TimSortStrategy;
impl<T: Ord + Clone> SortStrategy<T> for TimSortStrategy {
    fn name(&self) -> &'static str { "TimSort" }
    fn sort(&self, data: &mut [T]) where T: Ord {
        data.sort(); // 使用标准库的TimSort
    }
    fn time_complexity(&self) -> &'static str { "O(n log n)" }
}
```

#### 语义模型

```text
⟦Strategy⟧: (Context → Algorithm) × Input → Output

语义等价性：
  ∀algorithms a₁, a₂ ∈ Strategies.
    ∀input i.
      a₁.compute(i) = a₂.compute(i)  (功能等价)
      但 complexity(a₁) ≠ complexity(a₂)  (性能不同)
```

### 2.2 Template Method Pattern（模板方法）

**定义**：定义算法骨架，将某些步骤延迟到子类。

**算法应用**：分治算法、动态规划框架

#### Rust实现1

```rust
/// 模板方法：分治算法框架
pub trait DivideConquerTemplate<P, S> {
    /// 判断基础情况（钩子方法）
    fn is_base_case(&self, problem: &P) -> bool;
    
    /// 解决基础情况（钩子方法）
    fn solve_base(&self, problem: P) -> S;
    
    /// 分解问题（钩子方法）
    fn divide(&self, problem: P) -> Vec<P>;
    
    /// 合并解（钩子方法）
    fn combine(&self, solutions: Vec<S>) -> S;
    
    /// 模板方法：固定算法骨架
    fn solve(&self, problem: P) -> S 
    where
        P: Clone,
    {
        // 算法骨架（不可重写）
        if self.is_base_case(&problem) {
            self.solve_base(problem)
        } else {
            let subproblems = self.divide(problem);
            let subsolutions: Vec<_> = subproblems
                .into_iter()
                .map(|p| self.solve(p))
                .collect();
            self.combine(subsolutions)
        }
    }
}

/// 具体算法：归并排序
pub struct MergeSortTemplate;

impl DivideConquerTemplate<Vec<i32>, Vec<i32>> for MergeSortTemplate {
    fn is_base_case(&self, problem: &Vec<i32>) -> bool {
        problem.len() <= 1
    }
    
    fn solve_base(&self, problem: Vec<i32>) -> Vec<i32> {
        problem
    }
    
    fn divide(&self, mut problem: Vec<i32>) -> Vec<Vec<i32>> {
        let mid = problem.len() / 2;
        let right = problem.split_off(mid);
        vec![problem, right]
    }
    
    fn combine(&self, mut solutions: Vec<Vec<i32>>) -> Vec<i32> {
        let right = solutions.pop().unwrap();
        let left = solutions.pop().unwrap();
        merge(left, right)
    }
}

/// 具体算法：快速排序
pub struct QuickSortTemplate;

impl DivideConquerTemplate<Vec<i32>, Vec<i32>> for QuickSortTemplate {
    fn is_base_case(&self, problem: &Vec<i32>) -> bool {
        problem.len() <= 1
    }
    
    fn solve_base(&self, problem: Vec<i32>) -> Vec<i32> {
        problem
    }
    
    fn divide(&self, mut problem: Vec<i32>) -> Vec<Vec<i32>> {
        if problem.is_empty() {
            return vec![problem];
        }
        let pivot = problem.pop().unwrap();
        let (mut left, mut right): (Vec<_>, Vec<_>) = problem
            .into_iter()
            .partition(|&x| x < pivot);
        right.push(pivot);
        vec![left, right]
    }
    
    fn combine(&self, mut solutions: Vec<Vec<i32>>) -> Vec<i32> {
        let right = solutions.pop().unwrap();
        let mut left = solutions.pop().unwrap();
        left.extend(right);
        left
    }
}
```

#### 语义模型（霍尔逻辑）

```text
模板方法的契约：

{P} solve(problem) {Q}

展开为：

if is_base_case(problem):
  {P ∧ is_base_case} solve_base(problem) {Q}
else:
  {P ∧ ¬is_base_case} divide(problem) {Q_divide}
  {Q_divide} ∀p ∈ subproblems. solve(p) {Q_solve}
  {Q_solve} combine(subsolutions) {Q}
```

### 2.3 Iterator Pattern（迭代器）

**定义**：提供顺序访问聚合对象元素的方法。

**算法应用**：图遍历、树遍历、生成器

#### Rust实现（DFS迭代器）

```rust
use std::collections::HashSet;

/// DFS迭代器（深度优先遍历）
pub struct DfsIterator<'a, T> {
    graph: &'a std::collections::HashMap<T, Vec<T>>,
    stack: Vec<T>,
    visited: HashSet<T>,
}

impl<'a, T> DfsIterator<'a, T>
where
    T: Clone + Eq + std::hash::Hash,
{
    pub fn new(graph: &'a std::collections::HashMap<T, Vec<T>>, start: T) -> Self {
        let mut stack = Vec::new();
        stack.push(start);
        Self {
            graph,
            stack,
            visited: HashSet::new(),
        }
    }
}

impl<'a, T> Iterator for DfsIterator<'a, T>
where
    T: Clone + Eq + std::hash::Hash,
{
    type Item = T;
    
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(node) = self.stack.pop() {
            if self.visited.insert(node.clone()) {
                // 将邻居加入栈
                if let Some(neighbors) = self.graph.get(&node) {
                    for neighbor in neighbors.iter().rev() {
                        if !self.visited.contains(neighbor) {
                            self.stack.push(neighbor.clone());
                        }
                    }
                }
                return Some(node);
            }
        }
        None
    }
}

/// BFS迭代器（广度优先遍历）
pub struct BfsIterator<'a, T> {
    graph: &'a std::collections::HashMap<T, Vec<T>>,
    queue: std::collections::VecDeque<T>,
    visited: HashSet<T>,
}

impl<'a, T> BfsIterator<'a, T>
where
    T: Clone + Eq + std::hash::Hash,
{
    pub fn new(graph: &'a std::collections::HashMap<T, Vec<T>>, start: T) -> Self {
        let mut queue = std::collections::VecDeque::new();
        queue.push_back(start);
        Self {
            graph,
            queue,
            visited: HashSet::new(),
        }
    }
}

impl<'a, T> Iterator for BfsIterator<'a, T>
where
    T: Clone + Eq + std::hash::Hash,
{
    type Item = T;
    
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(node) = self.queue.pop_front() {
            if self.visited.insert(node.clone()) {
                // 将邻居加入队列
                if let Some(neighbors) = self.graph.get(&node) {
                    for neighbor in neighbors {
                        if !self.visited.contains(neighbor) {
                            self.queue.push_back(neighbor.clone());
                        }
                    }
                }
                return Some(node);
            }
        }
        None
    }
}

/// 使用示例
pub fn graph_traversal_example() {
    use std::collections::HashMap;
    
    let mut graph = HashMap::new();
    graph.insert(1, vec![2, 3]);
    graph.insert(2, vec![4]);
    graph.insert(3, vec![4]);
    graph.insert(4, vec![]);
    
    // DFS遍历
    let dfs: Vec<_> = DfsIterator::new(&graph, 1).collect();
    println!("DFS: {:?}", dfs);
    
    // BFS遍历
    let bfs: Vec<_> = BfsIterator::new(&graph, 1).collect();
    println!("BFS: {:?}", bfs);
}
```

#### 语义模型1

```text
Iterator<T> 的代数语义：

Iterator = μX. 1 + T × X

对应递归类型：
- 1: 迭代结束 (None)
- T × X: 当前元素 + 剩余迭代器 (Some(item))

不变量：
  ∀iterator. visited ∩ to_visit = ∅
  ∀iterator. visited ∪ to_visit = reachable_nodes
```

### 2.4 Observer Pattern（观察者）

**定义**：定义对象间一对多依赖，当一个对象状态改变时，所有依赖者都得到通知。

**算法应用**：事件驱动算法、增量计算

#### Rust实现（增量最短路径）

```rust
use std::collections::HashMap;

/// 观察者trait：监听图变化
pub trait GraphObserver<T> {
    fn on_edge_added(&mut self, from: T, to: T, weight: f64);
    fn on_edge_removed(&mut self, from: T, to: T);
}

/// 具体观察者：增量最短路径计算
pub struct IncrementalShortestPath<T> {
    distances: HashMap<(T, T), f64>,
}

impl<T: Clone + Eq + std::hash::Hash> IncrementalShortestPath<T> {
    pub fn new() -> Self {
        Self {
            distances: HashMap::new(),
        }
    }
    
    pub fn get_distance(&self, from: &T, to: &T) -> Option<f64> {
        self.distances.get(&(from.clone(), to.clone())).copied()
    }
}

impl<T: Clone + Eq + std::hash::Hash> GraphObserver<T> for IncrementalShortestPath<T> {
    fn on_edge_added(&mut self, from: T, to: T, weight: f64) {
        // 增量更新最短路径
        self.distances.insert((from.clone(), to.clone()), weight);
        
        // 松弛操作（简化版）
        let keys: Vec<_> = self.distances.keys().cloned().collect();
        for (u, v) in keys {
            if let Some(&dist_uv) = self.distances.get(&(u.clone(), v.clone())) {
                if let Some(&dist_from_u) = self.distances.get(&(from.clone(), u.clone())) {
                    let new_dist = dist_from_u + weight;
                    self.distances.entry((from.clone(), v.clone()))
                        .and_modify(|d| *d = d.min(new_dist))
                        .or_insert(new_dist);
                }
            }
        }
    }
    
    fn on_edge_removed(&mut self, from: T, to: T) {
        self.distances.remove(&(from, to));
        // 需要重新计算受影响的路径
    }
}

/// 被观察者：图
pub struct ObservableGraph<T> {
    edges: HashMap<T, Vec<(T, f64)>>,
    observers: Vec<Box<dyn GraphObserver<T>>>,
}

impl<T: Clone + Eq + std::hash::Hash> ObservableGraph<T> {
    pub fn new() -> Self {
        Self {
            edges: HashMap::new(),
            observers: Vec::new(),
        }
    }
    
    pub fn add_observer(&mut self, observer: Box<dyn GraphObserver<T>>) {
        self.observers.push(observer);
    }
    
    pub fn add_edge(&mut self, from: T, to: T, weight: f64) {
        self.edges.entry(from.clone())
            .or_insert_with(Vec::new)
            .push((to.clone(), weight));
        
        // 通知所有观察者
        for observer in &mut self.observers {
            observer.on_edge_added(from.clone(), to.clone(), weight);
        }
    }
}
```

#### 语义模型2

```text
Observer模式的π演算表示：

Subject = !notify(event).Subject
Observer = notify(event).process(event).Observer

组合：Subject | Observer₁ | Observer₂ | ...

性质：
1. 解耦：Subject不依赖具体Observer
2. 广播：一次notify通知所有Observer
3. 异步：通知可以是异步的
```

---

## 3. 算法专属模式

### 3.1 Memoization Pattern（记忆化）

**定义**：缓存函数结果，避免重复计算。

**应用**：动态规划、递归优化

#### Rust实现2

```rust
use std::collections::HashMap;
use std::hash::Hash;

/// 记忆化函数包装器
pub struct Memoized<F, I, O>
where
    F: FnMut(&I) -> O,
    I: Hash + Eq + Clone,
    O: Clone,
{
    func: F,
    cache: HashMap<I, O>,
}

impl<F, I, O> Memoized<F, I, O>
where
    F: FnMut(&I) -> O,
    I: Hash + Eq + Clone,
    O: Clone,
{
    pub fn new(func: F) -> Self {
        Self {
            func,
            cache: HashMap::new(),
        }
    }
    
    pub fn call(&mut self, input: &I) -> O {
        if let Some(result) = self.cache.get(input) {
            return result.clone();
        }
        
        let result = (self.func)(input);
        self.cache.insert(input.clone(), result.clone());
        result
    }
}

/// 示例：斐波那契（记忆化）
pub fn fibonacci_memoized(n: u64) -> u64 {
    fn fib_inner(n: &u64, memo: &mut Memoized<impl FnMut(&u64) -> u64, u64, u64>) -> u64 {
        match *n {
            0 => 0,
            1 => 1,
            _ => {
                let a = memo.call(&(n - 1));
                let b = memo.call(&(n - 2));
                a + b
            }
        }
    }
    
    let mut memo = Memoized::new(|_: &u64| 0); // 占位
    fib_inner(&n, &mut memo)
}

/// 更简单的记忆化宏
#[macro_export]
macro_rules! memoize {
    ($func:expr) => {{
        let mut cache = std::collections::HashMap::new();
        move |input| {
            if let Some(result) = cache.get(&input) {
                return result.clone();
            }
            let result = $func(input);
            cache.insert(input, result.clone());
            result
        }
    }};
}
```

#### 语义等价性

```text
定理：记忆化保持语义等价

设 f: A → B 是纯函数（无副作用）
记忆化版本 f': A → B

则：∀a ∈ A. f(a) = f'(a)

证明：
  - 首次调用：f'(a) = f(a)，存入缓存
  - 后续调用：f'(a) 返回缓存值 = f(a)
  - 纯函数保证结果一致 ∎

性能改进：
  时间：O(n) vs O(2ⁿ) (斐波那契)
  空间：O(n) 额外空间
```

### 3.2 Lazy Evaluation Pattern（惰性求值）

**定义**：延迟计算直到需要结果时。

**应用**：无限序列、按需计算

#### Rust实现3

```rust
/// 惰性值
pub struct Lazy<T, F>
where
    F: FnOnce() -> T,
{
    value: Option<T>,
    init: Option<F>,
}

impl<T, F> Lazy<T, F>
where
    F: FnOnce() -> T,
{
    pub fn new(init: F) -> Self {
        Self {
            value: None,
            init: Some(init),
        }
    }
    
    pub fn force(&mut self) -> &T {
        if self.value.is_none() {
            let init = self.init.take().unwrap();
            self.value = Some(init());
        }
        self.value.as_ref().unwrap()
    }
}

/// 惰性列表（流）
pub enum LazyList<T> {
    Nil,
    Cons(T, Box<Lazy<LazyList<T>, Box<dyn FnOnce() -> LazyList<T>>>>),
}

/// 无限斐波那契流
pub fn fibonacci_stream() -> LazyList<u64> {
    fn fib_from(a: u64, b: u64) -> LazyList<u64> {
        LazyList::Cons(
            a,
            Box::new(Lazy::new(Box::new(move || fib_from(b, a + b)))),
        )
    }
    fib_from(0, 1)
}

/// 惰性迭代器（Rust标准）
pub fn lazy_filter_map_example() {
    let result: Vec<_> = (0..1000)
        .filter(|x| x % 2 == 0)     // 惰性
        .map(|x| x * x)              // 惰性
        .take(10)                    // 只计算需要的
        .collect();                  // 强制求值
    
    println!("{:?}", result);
}
```

#### 语义模型（Call-by-Need）

```text
求值策略对比：

Call-by-Value (严格求值):
  (λx.e) v → e[x := v]
  先求值参数 v

Call-by-Name (惰性求值):
  (λx.e) exp → e[x := exp]
  直接替换表达式

Call-by-Need (记忆化惰性):
  (λx.e) exp → e[x := thunk(exp)]
  创建thunk，首次求值后缓存

Rust迭代器 ≈ Call-by-Need
```

### 3.3 Continuation-Passing Style (CPS)

**定义**：将控制流显式化为延续函数。

**应用**：异步转换、异常处理、回溯

#### Rust实现4

```rust
/// CPS变换：阶乘
/// 
/// 直接风格：
/// ```
/// fn factorial(n: u64) -> u64 {
///     if n == 0 { 1 } else { n * factorial(n-1) }
/// }
/// ```
/// 
/// CPS风格：
/// ```
/// fn factorial_cps(n: u64, cont: impl FnOnce(u64)) {
///     if n == 0 {
///         cont(1)
///     } else {
///         factorial_cps(n-1, |result| cont(n * result))
///     }
/// }
/// ```
pub fn factorial_cps<F>(n: u64, cont: F) -> u64
where
    F: FnOnce(u64) -> u64,
{
    if n == 0 {
        cont(1)
    } else {
        factorial_cps(n - 1, |result| cont(n * result))
    }
}

/// CPS斐波那契
pub fn fibonacci_cps<F>(n: u64, cont: F) -> u64
where
    F: FnOnce(u64) -> u64,
{
    match n {
        0 => cont(0),
        1 => cont(1),
        _ => fibonacci_cps(n - 1, |a| {
            fibonacci_cps(n - 2, |b| cont(a + b))
        }),
    }
}

/// 使用示例
pub fn cps_example() {
    let result = factorial_cps(5, |x| x);
    println!("5! = {}", result);
    
    let result = fibonacci_cps(10, |x| x * 2); // 可组合延续
    println!("fib(10) * 2 = {}", result);
}
```

#### 语义模型3

```text
CPS变换的形式化定义：

⟦·⟧: Expr → (Val → Answer) → Answer

⟦n⟧k = k(n)
⟦x⟧k = k(x)
⟦e₁ + e₂⟧k = ⟦e₁⟧(λv₁. ⟦e₂⟧(λv₂. k(v₁ + v₂)))
⟦if e then e₁ else e₂⟧k = ⟦e⟧(λv. if v then ⟦e₁⟧k else ⟦e₂⟧k)

CPS与异步的关系：
  async/await ≈ 自动CPS变换
  Future<T> ≈ (T → Answer) → Answer
```

---

## 4. 并发模式

### 4.1 Actor Pattern

**定义**：独立计算实体，通过消息通信。

**应用**：并行算法、分布式计算

（详见 `ACTOR_REACTOR_CSP_PATTERNS.md`）

#### 简要实现

```rust
use tokio::sync::mpsc;

/// Actor trait
pub trait Actor: Send + 'static {
    type Message: Send;
    
    async fn handle(&mut self, msg: Self::Message);
}

/// Actor句柄
pub struct ActorHandle<M> {
    sender: mpsc::UnboundedSender<M>,
}

impl<M: Send + 'static> ActorHandle<M> {
    pub fn send(&self, msg: M) {
        let _ = self.sender.send(msg);
    }
}

/// 启动Actor
pub fn spawn_actor<A>(mut actor: A) -> ActorHandle<A::Message>
where
    A: Actor,
{
    let (tx, mut rx) = mpsc::unbounded_channel();
    
    tokio::spawn(async move {
        while let Some(msg) = rx.recv().await {
            actor.handle(msg).await;
        }
    });
    
    ActorHandle { sender: tx }
}

/// 示例：并行归并排序Actor
pub struct MergeSortActor;

pub enum SortMessage {
    Sort(Vec<i32>, tokio::sync::oneshot::Sender<Vec<i32>>),
}

impl Actor for MergeSortActor {
    type Message = SortMessage;
    
    async fn handle(&mut self, msg: Self::Message) {
        match msg {
            SortMessage::Sort(data, reply) => {
                let sorted = merge_sort_actor(data).await;
                let _ = reply.send(sorted);
            }
        }
    }
}

async fn merge_sort_actor(data: Vec<i32>) -> Vec<i32> {
    if data.len() <= 1 {
        return data;
    }
    
    let mid = data.len() / 2;
    let (left, right) = data.split_at(mid);
    
    let (left_sorted, right_sorted) = tokio::join!(
        Box::pin(merge_sort_actor(left.to_vec())),
        Box::pin(merge_sort_actor(right.to_vec()))
    );
    
    merge(left_sorted, right_sorted)
}
```

### 4.2 Pipeline Pattern

**定义**：将计算分解为多个阶段，流水线处理。

**应用**：数据处理、流式计算

#### Rust实现5

```rust
use tokio::sync::mpsc;

/// 流水线阶段
pub trait PipelineStage<I, O>: Send + 'static {
    fn process(&mut self, input: I) -> O;
}

/// 构建流水线
pub fn build_pipeline<I, O>(
    input: mpsc::Receiver<I>,
    stages: Vec<Box<dyn PipelineStage<I, O>>>,
) -> mpsc::Receiver<O>
where
    I: Send + 'static,
    O: Send + 'static,
{
    // 简化版：单阶段
    let (tx, rx) = mpsc::channel(100);
    
    tokio::spawn(async move {
        // 实际应该串联多个阶段
    });
    
    rx
}

/// 示例：数据处理流水线
pub struct FilterStage;
impl PipelineStage<i32, Option<i32>> for FilterStage {
    fn process(&mut self, input: i32) -> Option<i32> {
        if input % 2 == 0 {
            Some(input)
        } else {
            None
        }
    }
}

pub struct MapStage;
impl PipelineStage<i32, i32> for MapStage {
    fn process(&mut self, input: i32) -> i32 {
        input * input
    }
}
```

---

## 5. 语义模型映射

### 5.1 类型系统映射

```text
Rust类型系统          ↔  类型理论
────────────────────────────────────
struct/enum           ↔  代数数据类型 (ADT)
trait                 ↔  类型类 (Type Class)
泛型<T>               ↔  全称量化 (∀T)
生命周期<'a>          ↔  区域类型 (Region)
&T/&mut T             ↔  线性类型 (Linear)
Box<T>                ↔  堆分配
Rc<T>                 ↔  引用计数
Arc<T>                ↔  原子引用计数
```

### 5.2 所有权与分离逻辑

```text
Rust所有权规则      ↔  分离逻辑
──────────────────────────────────
所有者唯一          ↔  资源独占
借用检查            ↔  别名分析
生命周期            ↔  时序逻辑
move语义            ↔  资源转移
&mut独占            ↔  分离合取 (*)
```

**示例**：

```rust
// Rust代码
let mut x = vec![1, 2, 3];
let y = &mut x;        // 独占借用
// x不可访问（借用检查）

// 分离逻辑表示
// {x ↦ [1,2,3]} let y = &mut x {y ↦ [1,2,3] * emp(x)}
```

### 5.3 并发模型映射

```text
Rust并发            ↔  π演算/CSP
────────────────────────────────────
tokio::spawn        ↔  并行组合 (P | Q)
mpsc::channel       ↔  通道 (c!v / c?x)
async/await         ↔  延续 (Continuation)
Future              ↔  进程 (Process)
.await              ↔  同步点 (Sync)
```

---

## 6. Rust特有模式

### 6.1 Typestate Pattern（类型状态）

**定义**：用类型系统编码状态机，编译期检查状态转换。

#### 实现

```rust
/// 类型状态：文件状态机
pub struct File<State> {
    path: String,
    _state: std::marker::PhantomData<State>,
}

pub struct Closed;
pub struct Open;

impl File<Closed> {
    pub fn new(path: String) -> Self {
        File {
            path,
            _state: std::marker::PhantomData,
        }
    }
    
    pub fn open(self) -> Result<File<Open>, std::io::Error> {
        // 打开文件
        Ok(File {
            path: self.path,
            _state: std::marker::PhantomData,
        })
    }
}

impl File<Open> {
    pub fn read(&self) -> String {
        // 只有Open状态才能读
        format!("Reading from {}", self.path)
    }
    
    pub fn close(self) -> File<Closed> {
        File {
            path: self.path,
            _state: std::marker::PhantomData,
        }
    }
}

/// 使用：编译期保证正确性
pub fn typestate_example() {
    let file = File::<Closed>::new("data.txt".into());
    // file.read(); // 编译错误！
    
    let file = file.open().unwrap();
    println!("{}", file.read()); // OK
    
    let file = file.close();
    // file.read(); // 编译错误！
}
```

### 6.2 Newtype Pattern

**定义**：用类型包装增强类型安全。

#### 实现3

```rust
/// 距离类型（保证单位）
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub struct Meters(pub f64);

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub struct Kilometers(pub f64);

impl Meters {
    pub fn to_kilometers(self) -> Kilometers {
        Kilometers(self.0 / 1000.0)
    }
}

impl Kilometers {
    pub fn to_meters(self) -> Meters {
        Meters(self.0 * 1000.0)
    }
}

// 类型安全：不能混淆单位
pub fn distance_example() {
    let m = Meters(1500.0);
    let km = m.to_kilometers();
    assert_eq!(km, Kilometers(1.5));
    
    // let sum = m + km; // 编译错误！不同类型
    let sum = m.0 + km.to_meters().0; // 显式转换
}
```

---

## 7. 等价关系分析

### 7.1 算法等价性

**定义**：两个算法功能等价但实现不同。

```text
定理：策略模式中的算法等价

∀strategies S₁, S₂ ∈ SortStrategies.
∀input I.
  S₁.sort(I) = S₂.sort(I)  (结果集相同)
  
但：
  complexity(S₁) ≠ complexity(S₂)  (复杂度不同)
  implementation(S₁) ≠ implementation(S₂)  (实现不同)
```

### 7.2 模式等价性

**不同模式可实现相同语义**：

```text
Strategy Pattern ≈ 函数参数
  context.execute(strategy) ≈ algorithm(data)

Template Method ≈ 高阶函数
  template.solve() ≈ fold/reduce

Observer ≈ 消息传递
  subject.notify() ≈ channel.send()

Iterator ≈ 生成器
  iterator.next() ≈ yield value
```

### 7.3 同步异步等价

**CPS变换建立等价性**：

```text
同步算法 f: A → B
异步算法 f_async: A → Future<B>

等价关系：
  f(a) = block_on(f_async(a))
  f_async(a) = async { f(a) }

语义保持：
  ⟦f⟧ = ⟦f_async⟧  (指称语义相同)
```

---

## 总结

### 核心映射

1. **设计模式 → 算法**: Strategy/Template/Iterator直接应用于算法设计
2. **模式 → 类型理论**: Rust类型系统编码设计模式
3. **模式 → 形式语义**: 每个模式都有对应的数学模型
4. **Rust特性 → 模式**: 所有权、类型状态等独特模式

### 学习路径

```text
基础模式 → 算法应用 → 并发模式 → 形式化验证
    ↓
Strategy/Template/Iterator → 分治/DP/图遍历 → Actor/Pipeline → 等价性证明
```

---

**参考文献**:

- *Design Patterns* (GoF)
- *Types and Programming Languages* (Pierce)
- *Rust Design Patterns Book*
- *Structure and Interpretation of Computer Programs* (SICP)
