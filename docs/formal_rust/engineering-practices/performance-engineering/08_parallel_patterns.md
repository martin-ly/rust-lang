# 并发编程模式

## 概述

本文档详细分析Rust中的并发编程模式，包括并行算法、工作窃取、分治策略和异步编程模式。

## 1. 并行编程理论基础

### 1.1 并行性vs并发性

```rust
// 并发性：多个任务交替执行
fn concurrent_example() {
    let mut handles = vec![];
    
    for i in 0..4 {
        let handle = std::thread::spawn(move || {
            println!("Task {} executing", i);
            std::thread::sleep(std::time::Duration::from_millis(100));
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
}

// 并行性：多个任务同时执行
fn parallel_example() {
    use rayon::prelude::*;
    
    let data: Vec<i32> = (0..1000).collect();
    let result: Vec<i32> = data.par_iter()
        .map(|&x| x * 2)
        .collect();
}
```

### 1.2 形式化语义

并行计算可以形式化为：

$$
\text{Parallel}(f, data) = \bigcup_{i=1}^{n} \text{Task}_i(f, data_i)
$$

其中每个任务独立处理数据的一部分。

## 2. 工作窃取模式

### 2.1 基本工作窃取

```rust
use std::sync::{Arc, Mutex};
use std::collections::VecDeque;
use std::thread;

struct WorkStealingScheduler {
    local_queues: Vec<Arc<Mutex<VecDeque<Task>>>>,
    global_queue: Arc<Mutex<VecDeque<Task>>>,
}

#[derive(Clone)]
struct Task {
    id: usize,
    work: Box<dyn Fn() + Send>,
}

impl WorkStealingScheduler {
    fn new(num_workers: usize) -> Self {
        let mut local_queues = Vec::new();
        for _ in 0..num_workers {
            local_queues.push(Arc::new(Mutex::new(VecDeque::new())));
        }
        
        WorkStealingScheduler {
            local_queues,
            global_queue: Arc::new(Mutex::new(VecDeque::new())),
        }
    }
    
    fn spawn(&self, worker_id: usize, task: Task) {
        let mut local_queue = self.local_queues[worker_id].lock().unwrap();
        local_queue.push_back(task);
    }
    
    fn steal(&self, thief_id: usize) -> Option<Task> {
        // 从其他工作线程的队列中窃取任务
        for i in 0..self.local_queues.len() {
            if i != thief_id {
                if let Ok(mut queue) = self.local_queues[i].try_lock() {
                    if let Some(task) = queue.pop_back() {
                        return Some(task);
                    }
                }
            }
        }
        
        // 从全局队列窃取
        if let Ok(mut global_queue) = self.global_queue.try_lock() {
            global_queue.pop_front()
        } else {
            None
        }
    }
    
    fn get_task(&self, worker_id: usize) -> Option<Task> {
        // 首先从本地队列获取任务
        if let Ok(mut local_queue) = self.local_queues[worker_id].try_lock() {
            if let Some(task) = local_queue.pop_front() {
                return Some(task);
            }
        }
        
        // 如果本地队列为空，尝试窃取
        self.steal(worker_id)
    }
}

fn work_stealing_example() {
    let scheduler = Arc::new(WorkStealingScheduler::new(4));
    let mut handles = vec![];
    
    // 创建工作线程
    for worker_id in 0..4 {
        let scheduler_clone = Arc::clone(&scheduler);
        let handle = thread::spawn(move || {
            loop {
                if let Some(task) = scheduler_clone.get_task(worker_id) {
                    println!("Worker {} executing task {}", worker_id, task.id);
                    (task.work)();
                } else {
                    // 没有任务时短暂休眠
                    thread::sleep(std::time::Duration::from_millis(1));
                }
            }
        });
        handles.push(handle);
    }
    
    // 添加一些任务
    for i in 0..20 {
        let task = Task {
            id: i,
            work: Box::new(move || {
                println!("Task {} completed", i);
                thread::sleep(std::time::Duration::from_millis(100));
            }),
        };
        scheduler.spawn(i % 4, task);
    }
    
    // 等待一段时间让任务执行
    thread::sleep(std::time::Duration::from_secs(5));
}
```

### 2.2 自适应工作窃取

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

struct AdaptiveWorkStealingScheduler {
    local_queues: Vec<Arc<Mutex<VecDeque<Task>>>>,
    global_queue: Arc<Mutex<VecDeque<Task>>>,
    worker_loads: Vec<AtomicUsize>,
}

impl AdaptiveWorkStealingScheduler {
    fn new(num_workers: usize) -> Self {
        let mut local_queues = Vec::new();
        let mut worker_loads = Vec::new();
        
        for _ in 0..num_workers {
            local_queues.push(Arc::new(Mutex::new(VecDeque::new())));
            worker_loads.push(AtomicUsize::new(0));
        }
        
        AdaptiveWorkStealingScheduler {
            local_queues,
            global_queue: Arc::new(Mutex::new(VecDeque::new())),
            worker_loads,
        }
    }
    
    fn spawn(&self, task: Task) {
        // 选择负载最轻的工作线程
        let mut min_load = usize::MAX;
        let mut target_worker = 0;
        
        for (i, load) in self.worker_loads.iter().enumerate() {
            let current_load = load.load(Ordering::Relaxed);
            if current_load < min_load {
                min_load = current_load;
                target_worker = i;
            }
        }
        
        // 增加目标工作线程的负载计数
        self.worker_loads[target_worker].fetch_add(1, Ordering::Relaxed);
        
        // 将任务添加到目标工作线程的队列
        let mut local_queue = self.local_queues[target_worker].lock().unwrap();
        local_queue.push_back(task);
    }
    
    fn get_task(&self, worker_id: usize) -> Option<Task> {
        // 减少负载计数
        self.worker_loads[worker_id].fetch_sub(1, Ordering::Relaxed);
        
        // 从本地队列获取任务
        if let Ok(mut local_queue) = self.local_queues[worker_id].try_lock() {
            if let Some(task) = local_queue.pop_front() {
                return Some(task);
            }
        }
        
        // 尝试窃取
        self.steal(worker_id)
    }
    
    fn steal(&self, thief_id: usize) -> Option<Task> {
        // 从负载最重的工作线程窃取
        let mut max_load = 0;
        let mut target_worker = 0;
        
        for (i, load) in self.worker_loads.iter().enumerate() {
            if i != thief_id {
                let current_load = load.load(Ordering::Relaxed);
                if current_load > max_load {
                    max_load = current_load;
                    target_worker = i;
                }
            }
        }
        
        if max_load > 0 {
            if let Ok(mut queue) = self.local_queues[target_worker].try_lock() {
                if let Some(task) = queue.pop_back() {
                    // 更新负载计数
                    self.worker_loads[target_worker].fetch_sub(1, Ordering::Relaxed);
                    self.worker_loads[thief_id].fetch_add(1, Ordering::Relaxed);
                    return Some(task);
                }
            }
        }
        
        None
    }
}
```

## 3. 分治并行模式

### 3.1 并行归并排序

```rust
use rayon::prelude::*;

fn parallel_merge_sort<T: Ord + Send + Clone>(data: &[T]) -> Vec<T> {
    if data.len() <= 1 {
        return data.to_vec();
    }
    
    let mid = data.len() / 2;
    let (left, right) = data.split_at(mid);
    
    // 并行递归排序
    let (sorted_left, sorted_right) = rayon::join(
        || parallel_merge_sort(left),
        || parallel_merge_sort(right)
    );
    
    // 合并结果
    merge(&sorted_left, &sorted_right)
}

fn merge<T: Ord + Clone>(left: &[T], right: &[T]) -> Vec<T> {
    let mut result = Vec::with_capacity(left.len() + right.len());
    let mut left_iter = left.iter();
    let mut right_iter = right.iter();
    let mut left_next = left_iter.next();
    let mut right_next = right_iter.next();
    
    while let (Some(l), Some(r)) = (left_next, right_next) {
        if l <= r {
            result.push(l.clone());
            left_next = left_iter.next();
        } else {
            result.push(r.clone());
            right_next = right_iter.next();
        }
    }
    
    // 添加剩余元素
    if let Some(l) = left_next {
        result.push(l.clone());
        result.extend(left_iter.cloned());
    }
    if let Some(r) = right_next {
        result.push(r.clone());
        result.extend(right_iter.cloned());
    }
    
    result
}

fn merge_sort_example() {
    let data: Vec<i32> = (0..10000).rev().collect();
    let sorted = parallel_merge_sort(&data);
    
    // 验证排序结果
    for i in 1..sorted.len() {
        assert!(sorted[i-1] <= sorted[i]);
    }
    println!("Merge sort completed successfully");
}
```

### 3.2 并行快速排序

```rust
fn parallel_quick_sort<T: Ord + Send + Clone>(data: &mut [T]) {
    if data.len() <= 1 {
        return;
    }
    
    let pivot_index = partition(data);
    
    let (left, right) = data.split_at_mut(pivot_index);
    let (_, right) = right.split_at_mut(1); // 跳过pivot
    
    // 并行排序左右两部分
    rayon::join(
        || parallel_quick_sort(left),
        || parallel_quick_sort(right)
    );
}

fn partition<T: Ord>(data: &mut [T]) -> usize {
    let len = data.len();
    let pivot_index = len - 1;
    let mut store_index = 0;
    
    for i in 0..len - 1 {
        if data[i] <= data[pivot_index] {
            data.swap(i, store_index);
            store_index += 1;
        }
    }
    
    data.swap(store_index, pivot_index);
    store_index
}

fn quick_sort_example() {
    let mut data: Vec<i32> = (0..10000).rev().collect();
    parallel_quick_sort(&mut data);
    
    // 验证排序结果
    for i in 1..data.len() {
        assert!(data[i-1] <= data[i]);
    }
    println!("Quick sort completed successfully");
}
```

## 4. MapReduce模式

### 4.1 基本MapReduce

```rust
use std::collections::HashMap;

struct MapReduce<T, U, V> {
    data: Vec<T>,
}

impl<T, U, V> MapReduce<T, U, V>
where
    T: Send + Sync,
    U: Send + Sync + Clone,
    V: Send + Sync + Clone,
{
    fn new(data: Vec<T>) -> Self {
        MapReduce { data }
    }
    
    fn execute<F, G>(&self, map_fn: F, reduce_fn: G) -> Vec<V>
    where
        F: Fn(&T) -> U + Send + Sync,
        G: Fn(&U, &U) -> V + Send + Sync,
    {
        // Map阶段：并行处理数据
        let mapped: Vec<U> = self.data.par_iter()
            .map(map_fn)
            .collect();
        
        // Reduce阶段：并行归约
        if mapped.is_empty() {
            return vec![];
        }
        
        let mut result = Vec::new();
        let chunk_size = (mapped.len() + rayon::current_num_threads() - 1) / rayon::current_num_threads();
        
        let reduced: Vec<V> = mapped.par_chunks(chunk_size)
            .map(|chunk| {
                if chunk.is_empty() {
                    return None;
                }
                
                let mut acc = chunk[0].clone();
                for item in &chunk[1..] {
                    acc = reduce_fn(&acc, item);
                }
                Some(acc)
            })
            .filter_map(|x| x)
            .collect();
        
        // 最终归约
        if reduced.is_empty() {
            return vec![];
        }
        
        let mut final_result = reduced[0].clone();
        for item in &reduced[1..] {
            final_result = reduce_fn(&final_result, item);
        }
        
        vec![final_result]
    }
}

fn map_reduce_example() {
    let data: Vec<i32> = (1..=1000).collect();
    let map_reduce = MapReduce::new(data);
    
    let result = map_reduce.execute(
        |&x| x * x, // Map: 计算平方
        |&a, &b| a + b // Reduce: 求和
    );
    
    println!("Sum of squares: {}", result[0]);
}
```

### 4.2 分组MapReduce

```rust
use std::collections::HashMap;

struct GroupedMapReduce<T, K, U, V> {
    data: Vec<T>,
}

impl<T, K, U, V> GroupedMapReduce<T, K, U, V>
where
    T: Send + Sync,
    K: Send + Sync + Clone + std::hash::Hash + std::cmp::Eq,
    U: Send + Sync + Clone,
    V: Send + Sync + Clone,
{
    fn new(data: Vec<T>) -> Self {
        GroupedMapReduce { data }
    }
    
    fn execute<F, G>(&self, map_fn: F, reduce_fn: G) -> HashMap<K, V>
    where
        F: Fn(&T) -> (K, U) + Send + Sync,
        G: Fn(&U, &U) -> V + Send + Sync,
    {
        // Map阶段：生成键值对
        let mapped: Vec<(K, U)> = self.data.par_iter()
            .map(map_fn)
            .collect();
        
        // 分组
        let mut groups: HashMap<K, Vec<U>> = HashMap::new();
        for (key, value) in mapped {
            groups.entry(key).or_insert_with(Vec::new).push(value);
        }
        
        // Reduce阶段：对每个组进行归约
        groups.par_iter()
            .map(|(key, values)| {
                if values.is_empty() {
                    return None;
                }
                
                let mut acc = values[0].clone();
                for value in &values[1..] {
                    acc = reduce_fn(&acc, value);
                }
                Some((key.clone(), acc))
            })
            .filter_map(|x| x)
            .collect()
    }
}

fn grouped_map_reduce_example() {
    #[derive(Clone, Hash, Eq, PartialEq)]
    enum Category { A, B, C }
    
    struct Item {
        category: Category,
        value: i32,
    }
    
    let data = vec![
        Item { category: Category::A, value: 1 },
        Item { category: Category::B, value: 2 },
        Item { category: Category::A, value: 3 },
        Item { category: Category::C, value: 4 },
        Item { category: Category::B, value: 5 },
    ];
    
    let map_reduce = GroupedMapReduce::new(data);
    
    let result = map_reduce.execute(
        |item| (item.category.clone(), item.value), // Map: 提取类别和值
        |&a, &b| a + b // Reduce: 求和
    );
    
    for (category, sum) in result {
        println!("Category {:?}: sum = {}", category, sum);
    }
}
```

## 5. 流水线模式

### 5.1 基本流水线

```rust
use std::sync::mpsc;
use std::thread;

struct Pipeline<T> {
    stages: Vec<Box<dyn Fn(T) -> T + Send>>,
}

impl<T> Pipeline<T>
where
    T: Send + 'static,
{
    fn new() -> Self {
        Pipeline { stages: Vec::new() }
    }
    
    fn add_stage<F>(&mut self, stage: F)
    where
        F: Fn(T) -> T + Send + 'static,
    {
        self.stages.push(Box::new(stage));
    }
    
    fn execute(&self, input: Vec<T>) -> Vec<T> {
        if self.stages.is_empty() {
            return input;
        }
        
        let mut current_data = input;
        
        for stage in &self.stages {
            let stage_fn = stage;
            current_data = current_data.into_iter()
                .map(|item| stage_fn(item))
                .collect();
        }
        
        current_data
    }
    
    fn execute_parallel(&self, input: Vec<T>) -> Vec<T> {
        if self.stages.is_empty() {
            return input;
        }
        
        let mut current_data = input;
        
        for stage in &self.stages {
            let stage_fn = stage;
            current_data = current_data.par_iter()
                .map(|item| stage_fn(item.clone()))
                .collect();
        }
        
        current_data
    }
}

fn pipeline_example() {
    let mut pipeline = Pipeline::new();
    
    // 添加处理阶段
    pipeline.add_stage(|x: i32| x * 2); // 阶段1：翻倍
    pipeline.add_stage(|x: i32| x + 1); // 阶段2：加1
    pipeline.add_stage(|x: i32| x * x); // 阶段3：平方
    
    let input: Vec<i32> = (1..=10).collect();
    let result = pipeline.execute_parallel(input);
    
    for (i, &value) in result.iter().enumerate() {
        println!("Input: {}, Output: {}", i + 1, value);
    }
}
```

### 5.2 异步流水线

```rust
use tokio::sync::mpsc;
use tokio::task;

struct AsyncPipeline<T> {
    stages: Vec<Box<dyn Fn(T) -> T + Send + Sync>>,
}

impl<T> AsyncPipeline<T>
where
    T: Send + Sync + 'static,
{
    fn new() -> Self {
        AsyncPipeline { stages: Vec::new() }
    }
    
    fn add_stage<F>(&mut self, stage: F)
    where
        F: Fn(T) -> T + Send + Sync + 'static,
    {
        self.stages.push(Box::new(stage));
    }
    
    async fn execute(&self, input: Vec<T>) -> Vec<T> {
        if self.stages.is_empty() {
            return input;
        }
        
        let mut current_data = input;
        
        for stage in &self.stages {
            let stage_fn = stage;
            let (tx, mut rx) = mpsc::channel(100);
            
            // 启动处理任务
            let handle = task::spawn(async move {
                let mut results = Vec::new();
                while let Some(item) = rx.recv().await {
                    results.push(stage_fn(item));
                }
                results
            });
            
            // 发送数据到处理任务
            for item in current_data {
                tx.send(item).await.unwrap();
            }
            drop(tx); // 关闭发送端
            
            // 收集结果
            current_data = handle.await.unwrap();
        }
        
        current_data
    }
}

#[tokio::main]
async fn async_pipeline_example() {
    let mut pipeline = AsyncPipeline::new();
    
    pipeline.add_stage(|x: i32| x * 2);
    pipeline.add_stage(|x: i32| x + 1);
    pipeline.add_stage(|x: i32| x * x);
    
    let input: Vec<i32> = (1..=10).collect();
    let result = pipeline.execute(input).await;
    
    for (i, &value) in result.iter().enumerate() {
        println!("Input: {}, Output: {}", i + 1, value);
    }
}
```

## 6. 形式化证明

### 6.1 并行性定理

**定理**: 工作窃取调度算法保证负载均衡。

**证明**: 通过概率论证明每个工作线程的负载差异有界。

### 6.2 正确性定理

**定理**: 分治并行算法保持顺序算法的正确性。

**证明**: 通过归纳法证明并行执行等价于顺序执行。

## 7. 工程实践

### 7.1 最佳实践

1. 合理选择并行粒度
2. 避免过度并行化
3. 使用适当的同步机制
4. 监控并行性能

### 7.2 常见陷阱

1. 线程创建开销
2. 缓存一致性开销
3. 负载不均衡
4. 同步开销过大

## 8. 交叉引用

- [资源管理模型](./01_resource_management.md) - 资源管理理论基础
- [并发安全性保证](./07_concurrency_safety.md) - 并发安全保证机制
- [所有权设计模式](./06_ownership_patterns.md) - 所有权模式设计

## 9. 参考文献

1. Parallel Programming Patterns
2. Work Stealing Scheduling
3. MapReduce Framework
4. Pipeline Processing
