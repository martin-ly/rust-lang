# 3. 并行模式形式化理论

 (Parallel Patterns Formalization)

## 目录

- [3. 并行模式形式化理论](#3-并行模式形式化理论)
  - [目录](#目录)
  - [3.1. 理论基础](#31-理论基础)
    - [3.1.1. 并行计算模型](#311-并行计算模型)
    - [3.1.2. 并行度](#312-并行度)
  - [3.2. 数据并行模式](#32-数据并行模式)
    - [3.2.1. 数据并行模型](#321-数据并行模型)
    - [3.2.2. Map-Reduce模式](#322-map-reduce模式)
  - [3.3. 任务并行模式](#33-任务并行模式)
    - [3.3.1. 任务并行模型](#331-任务并行模型)
    - [3.3.2. 任务调度算法](#332-任务调度算法)
  - [3.4. 流水线模式](#34-流水线模式)
    - [3.4.1. 流水线模型](#341-流水线模型)
    - [3.4.2. 流水线实现](#342-流水线实现)
  - [3.5. 分治模式](#35-分治模式)
    - [3.5.1. 分治模型](#351-分治模型)
    - [3.5.2. 并行分治](#352-并行分治)
  - [3.6. 核心定理证明](#36-核心定理证明)
    - [3.6.1. 并行加速比定理](#361-并行加速比定理)
    - [3.6.2. 并行效率定理](#362-并行效率定理)
    - [3.6.3. 负载均衡定理](#363-负载均衡定理)
  - [3.7. Rust实现](#37-rust实现)
    - [3.7.1. 并行迭代器](#371-并行迭代器)
    - [3.7.2. 并行数据结构](#372-并行数据结构)
    - [3.7.3. 并行算法库](#373-并行算法库)
  - [3.8. 性能分析](#38-性能分析)
    - [3.8.1. 时间复杂度分析](#381-时间复杂度分析)
    - [3.8.2. 空间复杂度分析](#382-空间复杂度分析)
    - [3.8.3. 性能基准](#383-性能基准)
  - [总结](#总结)
  
---

## 3.1. 理论基础

### 3.1.1. 并行计算模型

****定义 3**.1.1** (并行计算模型)
并行计算模型是一个六元组 $\mathcal{P} = (P, M, C, T, \mu, \sigma)$，其中：

- $P$ 是处理器集合
- $M$ 是内存集合
- $C$ 是通信网络
- $T$ 是任务集合
- $\mu: T \rightarrow P$ 是任务映射函数
- $\sigma: P \times P \rightarrow \mathbb{R}^+$ 是通信开销函数

****定义 3**.1.2** (并行执行)
对于任务集合 $T' \subseteq T$，并行执行定义为：
$$\text{parallel}(T') = \bigotimes_{t \in T'} \text{execute}(t)$$

### 3.1.2. 并行度

****定义 3**.1.3** (并行度)
并行度是同时执行的任务数量：
$$\text{parallelism}(T') = |\{t \in T' \mid \text{active}(t)\}|$$

****定义 3**.1.4** (加速比)
加速比是串行执行时间与并行执行时间的比值：
$$\text{speedup} = \frac{T_{\text{serial}}}{T_{\text{parallel}}}$$

---

## 3.2. 数据并行模式

### 3.2.1. 数据并行模型

****定义 3**.2.1** (数据并行)
数据并行是一个四元组 $\mathcal{D} = (D, F, P, \pi)$，其中：

- $D$ 是数据集合
- $F$ 是函数集合
- $P$ 是处理器集合
- $\pi: D \rightarrow P$ 是数据分布函数

****定义 3**.2.2** (数据并行执行)
数据并行执行定义为：
$$\text{data\_parallel}(D, f) = \bigotimes_{d \in D} f(d)$$

### 3.2.2. Map-Reduce模式

****定义 3**.2.3** (Map-Reduce)
Map-Reduce是一个三元组 $\text{MapReduce}(D, \text{map}, \text{reduce})$，其中：

- $D$ 是输入数据集合
- $\text{map}: D \rightarrow K \times V$ 是映射函数
- $\text{reduce}: K \times [V] \rightarrow V'$ 是归约函数

**算法 3.2.1** (Map-Reduce实现)

```rust
async fn map_reduce<D, K, V, V2>(
    data: Vec<D>,
    map_fn: impl Fn(D) -> (K, V) + Send + Sync,
    reduce_fn: impl Fn(K, Vec<V>) -> V2 + Send + Sync,
) -> HashMap<K, V2>
where
    D: Send + Sync,
    K: Eq + Hash + Send + Sync,
    V: Send + Sync,
    V2: Send + Sync,
{
    // Map阶段
    let map_results: Vec<(K, V)> = data
        .into_par_iter()
        .map(map_fn)
        .collect();

    // Shuffle阶段
    let mut grouped: HashMap<K, Vec<V>> = HashMap::new();
    for (k, v) in map_results {
        grouped.entry(k).or_insert_with(Vec::new).push(v);
    }

    // Reduce阶段
    grouped
        .into_par_iter()
        .map(|(k, vs)| (k, reduce_fn(k, vs)))
        .collect()
}
```

****定理 3**.2.1** (Map-Reduce正确性)
如果map和reduce函数都是纯函数，则Map-Reduce的结果是确定的。

**证明**:
由于map和reduce都是纯函数，相同的输入总是产生相同的输出，因此结果确定。

---

## 3.3. 任务并行模式

### 3.3.1. 任务并行模型

****定义 3**.3.1** (任务并行)
任务并行是一个四元组 $\mathcal{T} = (T, D, P, \mu)$，其中：

- $T$ 是任务集合
- $D$ 是依赖关系图
- $P$ 是处理器集合
- $\mu: T \rightarrow P$ 是任务调度函数

****定义 3**.3.2** (任务依赖)
任务 $t_1$ 依赖于任务 $t_2$，当且仅当：
$$t_1 \rightarrow t_2 \iff \text{output}(t_2) \cap \text{input}(t_1) \neq \emptyset$$

### 3.3.2. 任务调度算法

**算法 3.3.1** (贪心调度)

```rust
fn greedy_schedule(tasks: &[Task], processors: &[Processor]) -> HashMap<TaskId, ProcessorId> {
    let mut schedule = HashMap::new();
    let mut processor_loads = vec![0; processors.len()];
    
    for task in tasks {
        // 选择负载最小的处理器
        let processor_id = processor_loads
            .iter()
            .enumerate()
            .min_by_key(|(_, &load)| load)
            .map(|(id, _)| id)
            .unwrap();
        
        schedule.insert(task.id, processor_id);
        processor_loads[processor_id] += task.estimated_time;
    }
    
    schedule
}
```

**算法 3.3.2** (关键路径调度)

```rust
fn critical_path_schedule(tasks: &[Task], dependencies: &[(TaskId, TaskId)]) -> Vec<TaskId> {
    // 构建依赖图
    let mut graph = HashMap::new();
    for (from, to) in dependencies {
        graph.entry(*from).or_insert_with(Vec::new).push(*to);
    }
    
    // 计算关键路径
    let mut critical_path = Vec::new();
    let mut visited = HashSet::new();
    
    fn dfs(
        task: TaskId,
        graph: &HashMap<TaskId, Vec<TaskId>>,
        visited: &mut HashSet<TaskId>,
        path: &mut Vec<TaskId>,
    ) {
        if visited.contains(&task) {
            return;
        }
        
        visited.insert(task);
        path.push(task);
        
        if let Some(deps) = graph.get(&task) {
            for dep in deps {
                dfs(*dep, graph, visited, path);
            }
        }
    }
    
    // 从所有入度为0的节点开始
    let mut in_degree = HashMap::new();
    for (_, deps) in &graph {
        for dep in deps {
            *in_degree.entry(*dep).or_insert(0) += 1;
        }
    }
    
    for task in tasks {
        if in_degree.get(&task.id).unwrap_or(&0) == &0 {
            dfs(task.id, &graph, &mut visited, &mut critical_path);
        }
    }
    
    critical_path
}
```

---

## 3.4. 流水线模式

### 3.4.1. 流水线模型

****定义 3**.4.1** (流水线)
流水线是一个五元组 $\mathcal{P} = (S, B, F, Q, \tau)$，其中：

- $S$ 是阶段集合
- $B$ 是缓冲区集合
- $F: S \times B \rightarrow B$ 是处理函数
- $Q$ 是队列集合
- $\tau: S \rightarrow \mathbb{R}^+$ 是阶段延迟函数

****定义 3**.4.2** (流水线吞吐量)
流水线吞吐量定义为：
$$\text{throughput}(\mathcal{P}) = \frac{1}{\max_{s \in S} \tau(s)}$$

### 3.4.2. 流水线实现

**算法 3.4.1** (流水线构建)

```rust
pub struct Pipeline<I, O> {
    stages: Vec<Box<dyn PipelineStage>>,
    input_queue: mpsc::Sender<I>,
    output_queue: mpsc::Receiver<O>,
}

impl<I, O> Pipeline<I, O> {
    pub fn new() -> Self {
        let (input_tx, input_rx) = mpsc::channel(100);
        let (output_tx, output_rx) = mpsc::channel(100);
        
        Self {
            stages: Vec::new(),
            input_queue: input_tx,
            output_queue: output_rx,
        }
    }
    
    pub fn add_stage<S>(&mut self, stage: S)
    where
        S: PipelineStage + 'static,
    {
        self.stages.push(Box::new(stage));
    }
    
    pub async fn run(&mut self) -> Result<(), Error> {
        let mut input_rx = self.input_queue.subscribe();
        let mut output_tx = self.output_queue.clone();
        
        // 启动所有阶段
        let mut stage_handles = Vec::new();
        for stage in &self.stages {
            let handle = tokio::spawn(stage.run());
            stage_handles.push(handle);
        }
        
        // 等待所有阶段完成
        for handle in stage_handles {
            handle.await?;
        }
        
        Ok(())
    }
}

#[async_trait::async_trait]
pub trait PipelineStage: Send + Sync {
    async fn process(&self, input: Vec<u8>) -> Result<Vec<u8>, Error>;
    async fn run(&self) -> Result<(), Error>;
}
```

**算法 3.4.2** (流水线调度)

```rust
pub struct PipelineScheduler {
    stages: Vec<Arc<dyn PipelineStage>>,
    buffers: Vec<Arc<Mutex<VecDeque<Vec<u8>>>>>,
}

impl PipelineScheduler {
    pub fn new(stages: Vec<Arc<dyn PipelineStage>>) -> Self {
        let buffers = (0..stages.len() + 1)
            .map(|_| Arc::new(Mutex::new(VecDeque::new())))
            .collect();
        
        Self { stages, buffers }
    }
    
    pub async fn run(&self, input: Vec<Vec<u8>>) -> Result<Vec<Vec<u8>>, Error> {
        // 初始化输入缓冲区
        {
            let mut input_buffer = self.buffers[0].lock().unwrap();
            for data in input {
                input_buffer.push_back(data);
            }
        }
        
        // 启动所有阶段
        let mut handles = Vec::new();
        for (i, stage) in self.stages.iter().enumerate() {
            let stage = stage.clone();
            let input_buffer = self.buffers[i].clone();
            let output_buffer = self.buffers[i + 1].clone();
            
            let handle = tokio::spawn(async move {
                loop {
                    let input_data = {
                        let mut buffer = input_buffer.lock().unwrap();
                        buffer.pop_front()
                    };
                    
                    if let Some(data) = input_data {
                        let output_data = stage.process(data).await?;
                        let mut buffer = output_buffer.lock().unwrap();
                        buffer.push_back(output_data);
                    } else {
                        break;
                    }
                }
                Ok::<(), Error>(())
            });
            
            handles.push(handle);
        }
        
        // 等待所有阶段完成
        for handle in handles {
            handle.await??;
        }
        
        // 收集输出
        let output_buffer = &self.buffers[self.stages.len()];
        let buffer = output_buffer.lock().unwrap();
        Ok(buffer.iter().cloned().collect())
    }
}
```

---

## 3.5. 分治模式

### 3.5.1. 分治模型

****定义 3**.5.1** (分治算法)
分治算法是一个四元组 $\mathcal{D} = (P, C, M, B)$，其中：

- $P$ 是问题集合
- $C: P \rightarrow [P]$ 是分解函数
- $M: [P] \rightarrow P$ 是合并函数
- $B: P \rightarrow \text{bool}$ 是基础情况判断函数

****定义 3**.5.2** (分治执行)
分治执行定义为：

```latex
$$\text{divide\_and\_conquer}(p) = \begin{cases}
\text{solve}(p) & \text{if } B(p) \\
M(\text{map}(\text{divide\_and\_conquer}, C(p))) & \text{otherwise}
\end{cases}$$
```

### 3.5.2. 并行分治

**算法 3.5.1** (并行归并排序)
```rust
pub fn parallel_merge_sort<T>(data: Vec<T>) -> Vec<T>
where
    T: Ord + Send + Sync + Clone,
{
    if data.len() <= 1 {
        return data;
    }

    let mid = data.len() / 2;
    let (left, right) = data.split_at(mid);

    let (left_sorted, right_sorted) = rayon::join(
        || parallel_merge_sort(left.to_vec()),
        || parallel_merge_sort(right.to_vec()),
    );

    merge(left_sorted, right_sorted)
}

fn merge<T>(left: Vec<T>, right: Vec<T>) -> Vec<T>
where
    T: Ord + Clone,
{
    let mut result = Vec::with_capacity(left.len() + right.len());
    let mut left_iter = left.into_iter();
    let mut right_iter = right.into_iter();
    let mut left_peek = left_iter.next();
    let mut right_peek = right_iter.next();

    loop {
        match (left_peek, right_peek) {
            (Some(l), Some(r)) => {
                if l <= r {
                    result.push(l);
                    left_peek = left_iter.next();
                } else {
                    result.push(r);
                    right_peek = right_iter.next();
                }
            }
            (Some(l), None) => {
                result.push(l);
                result.extend(left_iter);
                break;
            }
            (None, Some(r)) => {
                result.push(r);
                result.extend(right_iter);
                break;
            }
            (None, None) => break,
        }
    }

    result
}
```

**算法 3.5.2** (并行快速排序)
```rust
pub fn parallel_quick_sort<T>(data: Vec<T>) -> Vec<T>
where
    T: Ord + Send + Sync + Clone,
{
    if data.len() <= 1 {
        return data;
    }

    let pivot = data[0].clone();
    let (less, equal, greater): (Vec<_>, Vec<_>, Vec<_>) = data
        .into_iter()
        .fold((Vec::new(), Vec::new(), Vec::new()), |mut acc, x| {
            match x.cmp(&pivot) {
                std::cmp::Ordering::Less => acc.0.push(x),
                std::cmp::Ordering::Equal => acc.1.push(x),
                std::cmp::Ordering::Greater => acc.2.push(x),
            }
            acc
        });

    let (less_sorted, greater_sorted) = rayon::join(
        || parallel_quick_sort(less),
        || parallel_quick_sort(greater),
    );

    let mut result = less_sorted;
    result.extend(equal);
    result.extend(greater_sorted);
    result
}
```

---

## 3.6. 核心定理证明

### 3.6.1. 并行加速比定理

****定理 3**.6.1** (Amdahl定律)
如果程序中有 $f$ 比例的部分必须串行执行，则最大加速比为：
$$S_{\max} = \frac{1}{f + \frac{1-f}{p}}$$

其中 $p$ 是处理器数量。

**证明**:
设总执行时间为 $T$，串行部分时间为 $fT$，并行部分时间为 $(1-f)T$。
并行执行时间为 $fT + \frac{(1-f)T}{p}$。
因此加速比为：
$$S = \frac{T}{fT + \frac{(1-f)T}{p}} = \frac{1}{f + \frac{1-f}{p}}$$

当 $p \rightarrow \infty$ 时，$S_{\max} = \frac{1}{f}$。

### 3.6.2. 并行效率定理

****定理 3**.6.2** (并行效率)
并行效率定义为：
$$E = \frac{S}{p} = \frac{T_{\text{serial}}}{p \cdot T_{\text{parallel}}}$$

**证明**:
根据定义，并行效率是加速比与处理器数量的比值，表示处理器的利用率。

### 3.6.3. 负载均衡定理

****定理 3**.6.3** (负载均衡)
如果任务均匀分布到所有处理器，则并行效率最大化。

**证明**:
当任务均匀分布时，所有处理器的执行时间相等，避免了等待时间，因此效率最大化。

---

## 3.7. Rust实现

### 3.7.1. 并行迭代器

```rust
use rayon::prelude::*;
use std::sync::{Arc, Mutex};

/// 并行迭代器包装器
pub struct ParallelIterator<T> {
    data: Vec<T>,
    chunk_size: usize,
}

impl<T> ParallelIterator<T> {
    pub fn new(data: Vec<T>) -> Self {
        Self {
            data,
            chunk_size: 1000,
        }
    }

    pub fn with_chunk_size(mut self, chunk_size: usize) -> Self {
        self.chunk_size = chunk_size;
        self
    }

    pub fn map<F, R>(self, f: F) -> ParallelIterator<R>
    where
        T: Send + Sync,
        F: Fn(T) -> R + Send + Sync,
        R: Send + Sync,
    {
        let results: Vec<R> = self.data
            .into_par_iter()
            .map(f)
            .collect();

        ParallelIterator {
            data: results,
            chunk_size: self.chunk_size,
        }
    }

    pub fn filter<F>(self, f: F) -> ParallelIterator<T>
    where
        T: Send + Sync,
        F: Fn(&T) -> bool + Send + Sync,
    {
        let results: Vec<T> = self.data
            .into_par_iter()
            .filter(f)
            .collect();

        ParallelIterator {
            data: results,
            chunk_size: self.chunk_size,
        }
    }

    pub fn reduce<F>(self, f: F) -> Option<T>
    where
        T: Send + Sync,
        F: Fn(T, T) -> T + Send + Sync,
    {
        self.data.into_par_iter().reduce(f)
    }

    pub fn collect(self) -> Vec<T> {
        self.data
    }
}

/// 并行数据处理管道
pub struct ParallelPipeline<I, O> {
    stages: Vec<Box<dyn PipelineStage<I, O>>>,
}

impl<I, O> ParallelPipeline<I, O> {
    pub fn new() -> Self {
        Self {
            stages: Vec::new(),
        }
    }

    pub fn add_stage<S>(&mut self, stage: S)
    where
        S: PipelineStage<I, O> + 'static,
    {
        self.stages.push(Box::new(stage));
    }

    pub fn process(&self, input: Vec<I>) -> Vec<O>
    where
        I: Send + Sync + Clone,
        O: Send + Sync,
    {
        let mut current_data = input;

        for stage in &self.stages {
            current_data = stage.process_parallel(current_data);
        }

        current_data
    }
}

# [async_trait::async_trait]
pub trait PipelineStage<I, O>: Send + Sync {
    fn process_parallel(&self, input: Vec<I>) -> Vec<O>;
}

/// 并行Map阶段
pub struct ParallelMapStage<I, O, F> {
    map_fn: F,
    _phantom: std::marker::PhantomData<(I, O)>,
}

impl<I, O, F> ParallelMapStage<I, O, F>
where
    F: Fn(I) -> O + Send + Sync,
{
    pub fn new(map_fn: F) -> Self {
        Self {
            map_fn,
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<I, O, F> PipelineStage<I, O> for ParallelMapStage<I, O, F>
where
    I: Send + Sync,
    O: Send + Sync,
    F: Fn(I) -> O + Send + Sync,
{
    fn process_parallel(&self, input: Vec<I>) -> Vec<O> {
        input.into_par_iter().map(&self.map_fn).collect()
    }
}

/// 并行Filter阶段
pub struct ParallelFilterStage<T, F> {
    filter_fn: F,
    _phantom: std::marker::PhantomData<T>,
}

impl<T, F> ParallelFilterStage<T, F>
where
    F: Fn(&T) -> bool + Send + Sync,
{
    pub fn new(filter_fn: F) -> Self {
        Self {
            filter_fn,
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<T, F> PipelineStage<T, T> for ParallelFilterStage<T, F>
where
    T: Send + Sync,
    F: Fn(&T) -> bool + Send + Sync,
{
    fn process_parallel(&self, input: Vec<T>) -> Vec<T> {
        input.into_par_iter().filter(&self.filter_fn).collect()
    }
}
```

### 3.7.2. 并行数据结构

```rust
use std::sync::{Arc, RwLock};
use std::collections::HashMap;

/// 并行HashMap
pub struct ParallelHashMap<K, V> {
    inner: Arc<RwLock<HashMap<K, V>>>,
}

impl<K, V> ParallelHashMap<K, V>
where
    K: Eq + std::hash::Hash + Clone + Send + Sync,
    V: Clone + Send + Sync,
{
    pub fn new() -> Self {
        Self {
            inner: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    pub fn insert(&self, key: K, value: V) -> Option<V> {
        let mut map = self.inner.write().unwrap();
        map.insert(key, value)
    }

    pub fn get(&self, key: &K) -> Option<V> {
        let map = self.inner.read().unwrap();
        map.get(key).cloned()
    }

    pub fn remove(&self, key: &K) -> Option<V> {
        let mut map = self.inner.write().unwrap();
        map.remove(key)
    }

    pub fn len(&self) -> usize {
        let map = self.inner.read().unwrap();
        map.len()
    }

    pub fn is_empty(&self) -> bool {
        let map = self.inner.read().unwrap();
        map.is_empty()
    }
}

/// 并行向量
pub struct ParallelVector<T> {
    inner: Arc<RwLock<Vec<T>>>,
}

impl<T> ParallelVector<T>
where
    T: Clone + Send + Sync,
{
    pub fn new() -> Self {
        Self {
            inner: Arc::new(RwLock::new(Vec::new())),
        }
    }

    pub fn push(&self, value: T) {
        let mut vec = self.inner.write().unwrap();
        vec.push(value);
    }

    pub fn pop(&self) -> Option<T> {
        let mut vec = self.inner.write().unwrap();
        vec.pop()
    }

    pub fn len(&self) -> usize {
        let vec = self.inner.read().unwrap();
        vec.len()
    }

    pub fn is_empty(&self) -> bool {
        let vec = self.inner.read().unwrap();
        vec.is_empty()
    }

    pub fn parallel_map<F, R>(&self, f: F) -> ParallelVector<R>
    where
        F: Fn(T) -> R + Send + Sync,
        R: Clone + Send + Sync,
    {
        let vec = self.inner.read().unwrap();
        let results: Vec<R> = vec.par_iter().map(|x| f(x.clone())).collect();

        ParallelVector {
            inner: Arc::new(RwLock::new(results)),
        }
    }
}
```

### 3.7.3. 并行算法库

```rust
use rayon::prelude::*;
use std::sync::{Arc, Mutex};

/// 并行算法集合
pub struct ParallelAlgorithms;

impl ParallelAlgorithms {
    /// 并行查找
    pub fn parallel_find<T, F>(data: &[T], predicate: F) -> Option<usize>
    where
        T: Send + Sync,
        F: Fn(&T) -> bool + Send + Sync,
    {
        data.par_iter()
            .enumerate()
            .find_any(|(_, item)| predicate(item))
            .map(|(index, _)| index)
    }

    /// 并行计数
    pub fn parallel_count<T, F>(data: &[T], predicate: F) -> usize
    where
        T: Send + Sync,
        F: Fn(&T) -> bool + Send + Sync,
    {
        data.par_iter()
            .filter(|item| predicate(item))
            .count()
    }

    /// 并行最大值
    pub fn parallel_max<T>(data: &[T]) -> Option<&T>
    where
        T: Ord + Send + Sync,
    {
        data.par_iter().max()
    }

    /// 并行最小值
    pub fn parallel_min<T>(data: &[T]) -> Option<&T>
    where
        T: Ord + Send + Sync,
    {
        data.par_iter().min()
    }

    /// 并行求和
    pub fn parallel_sum<T>(data: &[T]) -> T
    where
        T: Send + Sync + std::ops::Add<Output = T> + std::iter::Sum,
    {
        data.par_iter().sum()
    }

    /// 并行乘积
    pub fn parallel_product<T>(data: &[T]) -> T
    where
        T: Send + Sync + std::ops::Mul<Output = T> + std::iter::Product,
    {
        data.par_iter().product()
    }

    /// 并行去重
    pub fn parallel_dedup<T>(data: Vec<T>) -> Vec<T>
    where
        T: Send + Sync + Eq + std::hash::Hash,
    {
        let mut seen = std::collections::HashSet::new();
        data.into_par_iter()
            .filter(|item| seen.insert(item.clone()))
            .collect()
    }

    /// 并行排序
    pub fn parallel_sort<T>(mut data: Vec<T>) -> Vec<T>
    where
        T: Send + Sync + Ord,
    {
        data.par_sort();
        data
    }

    /// 并行分组
    pub fn parallel_group_by<T, K, F>(data: Vec<T>, key_fn: F) -> HashMap<K, Vec<T>>
    where
        T: Send + Sync,
        K: Send + Sync + Eq + std::hash::Hash,
        F: Fn(&T) -> K + Send + Sync,
    {
        data.into_par_iter()
            .fold(
                || HashMap::new(),
                |mut acc, item| {
                    let key = key_fn(&item);
                    acc.entry(key).or_insert_with(Vec::new).push(item);
                    acc
                },
            )
            .reduce(
                || HashMap::new(),
                |mut acc, group| {
                    for (key, values) in group {
                        acc.entry(key).or_insert_with(Vec::new).extend(values);
                    }
                    acc
                },
            )
    }
}
```

---

## 3.8. 性能分析

### 3.8.1. 时间复杂度分析

****定理 3**.8.1** (并行算法复杂度)
对于包含 $n$ 个元素的并行算法，使用 $p$ 个处理器：
$$T(n, p) = O\left(\frac{n}{p} + \log p\right)$$

**证明**:
每个处理器处理 $\frac{n}{p}$ 个元素，需要 $O(\log p)$ 时间进行同步。

### 3.8.2. 空间复杂度分析

****定理 3**.8.2** (并行算法空间复杂度)
并行算法的空间复杂度为：
$$S(n, p) = O(n + p)$$

**证明**:
需要存储所有数据 $O(n)$ 和每个处理器的额外空间 $O(p)$。

### 3.8.3. 性能基准

```rust
# [cfg(test)]
mod tests {
    use super::*;
    use std::time::Instant;

    #[test]
    fn test_parallel_sort_performance() {
        let data: Vec<i32> = (0..1000000).rev().collect();

        // 串行排序
        let start = Instant::now();
        let mut serial_data = data.clone();
        serial_data.sort();
        let serial_time = start.elapsed();

        // 并行排序
        let start = Instant::now();
        let parallel_data = parallel_merge_sort(data);
        let parallel_time = start.elapsed();

        assert_eq!(serial_data, parallel_data);
        println!("Serial sort: {:?}", serial_time);
        println!("Parallel sort: {:?}", parallel_time);
        println!("Speedup: {:.2}x", serial_time.as_millis() as f64 / parallel_time.as_millis() as f64);
    }

    #[test]
    fn test_parallel_map_performance() {
        let data: Vec<i32> = (0..1000000).collect();

        // 串行映射
        let start = Instant::now();
        let serial_result: Vec<i32> = data.iter().map(|x| x * 2).collect();
        let serial_time = start.elapsed();

        // 并行映射
        let start = Instant::now();
        let parallel_result: Vec<i32> = data.par_iter().map(|x| x * 2).collect();
        let parallel_time = start.elapsed();

        assert_eq!(serial_result, parallel_result);
        println!("Serial map: {:?}", serial_time);
        println!("Parallel map: {:?}", parallel_time);
        println!("Speedup: {:.2}x", serial_time.as_millis() as f64 / parallel_time.as_millis() as f64);
    }

    #[test]
    fn test_parallel_reduce_performance() {
        let data: Vec<i32> = (0..1000000).collect();

        // 串行归约
        let start = Instant::now();
        let serial_result: i32 = data.iter().sum();
        let serial_time = start.elapsed();

        // 并行归约
        let start = Instant::now();
        let parallel_result: i32 = data.par_iter().sum();
        let parallel_time = start.elapsed();

        assert_eq!(serial_result, parallel_result);
        println!("Serial reduce: {:?}", serial_time);
        println!("Parallel reduce: {:?}", parallel_time);
        println!("Speedup: {:.2}x", serial_time.as_millis() as f64 / parallel_time.as_millis() as f64);
    }
}
```

---

## 总结

本章建立了并行模式的形式化理论体系，包括：

1. **理论基础**: 定义了并行计算模型和并行度概念
2. **数据并行模式**: 建立了Map-Reduce等数据并行算法
3. **任务并行模式**: 提供了任务调度和依赖管理
4. **流水线模式**: 实现了流水线处理和调度
5. **分治模式**: 提供了并行分治算法
6. **核心定理证明**: 证明了Amdahl定律和并行效率**定理 7**. **Rust实现**: 提供了完整的并行算法实现
8. **性能分析**: 分析了时间复杂度和空间复杂度

这些理论为并行编程提供了严格的数学基础，确保了算法的正确性和性能。

