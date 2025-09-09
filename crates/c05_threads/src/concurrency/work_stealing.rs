//! 工作窃取调度器 - 高性能并发调度
//! 
//! 本模块实现了多种工作窃取算法，包括：
//! - 双端队列工作窃取
//! - 优先级工作窃取
//! - 自适应工作窃取
//! - NUMA感知工作窃取

use std::sync::{Arc, Mutex};
//use std::thread;
use std::time::{Duration, Instant};
use std::sync::atomic::{AtomicUsize, Ordering};
use crossbeam_deque::{
    Injector, 
    Worker, 
    //Stealer,
};

/// 基础工作窃取调度器
/// 
/// 使用双端队列实现经典的工作窃取算法
pub struct WorkStealingScheduler<T> {
    workers: Arc<Vec<Worker<T>>>,
    injector: Arc<Injector<T>>,
    stealer_count: AtomicUsize,
}

impl<T> WorkStealingScheduler<T> {
    /// 创建新的工作窃取调度器
    pub fn new(worker_count: usize) -> Self {
        let workers: Vec<Worker<T>> = (0..worker_count)
            .map(|_| Worker::new_fifo())
            .collect();
        
        Self {
            workers: Arc::new(workers),
            injector: Arc::new(Injector::new()),
            stealer_count: AtomicUsize::new(0),
        }
    }
    
    /// 获取工作线程的索引
    pub fn get_worker_index(&self) -> usize {
        self.stealer_count.fetch_add(1, Ordering::Relaxed) % self.workers.len()
    }
    
    /// 推送任务到指定工作线程
    pub fn push_task(&self, worker_index: usize, task: T) {
        if worker_index < self.workers.len() {
            self.workers[worker_index].push(task);
        }
    }
    
    /// 推送任务到全局注入器
    pub fn push_global_task(&self, task: T) {
        self.injector.push(task);
    }
    
    /// 从指定工作线程窃取任务
    pub fn steal_task(&self, worker_index: usize) -> Option<T> {
        if worker_index >= self.workers.len() {
            return None;
        }
        
        // 首先尝试从自己的队列获取任务
        if let Some(task) = self.workers[worker_index].pop() {
            return Some(task);
        }
        
        // 尝试从全局注入器获取任务
        if let Some(task) = self.injector.steal().success() {
            return Some(task);
        }
        
        // 尝试从其他工作线程窃取任务
        for i in 0..self.workers.len() {
            if i != worker_index {
                let stealer = self.workers[i].stealer();
                if let Some(task) = stealer.steal().success() {
                    return Some(task);
                }
            }
        }
        
        None
    }
    
    /// 运行工作窃取示例
    #[cfg(feature = "work_stealing_examples")]
    pub fn run_example() {
        println!("=== 工作窃取调度器示例 ===");
        
        let scheduler = WorkStealingScheduler::new(4);
        let results: Arc<Mutex<Vec<i32>>> = Arc::new(Mutex::new(Vec::new()));
        
        // 创建任务
        for i in 0..20 {
            scheduler.push_global_task(i);
        }
        
        // 创建工作线程
        thread::scope(|s| {
            for worker_id in 0..4 {
                let results = results.clone();
                s.spawn(move || {
                    let mut local_results: Vec<i32> = Vec::new();
                    loop {
                        if let Some(task) = scheduler.steal_task(worker_id) {
                            let result = task * task;
                            local_results.push(result);
                            thread::sleep(Duration::from_millis(1));
                        } else {
                            break;
                        }
                    }
                    results.lock().unwrap().extend(local_results);
                });
            }
        });
        
        let final_results = results.lock().unwrap();
        println!("工作窃取结果: {:?}", final_results);
    }
}

/// 优先级工作窃取调度器
/// 
/// 支持任务优先级的增强型工作窃取调度器
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct PriorityTask<T> {
    priority: u32,
    task: T,
    created_at: Instant,
}

impl<T> PriorityTask<T> {
    pub fn new(priority: u32, task: T) -> Self {
        Self {
            priority,
            task,
            created_at: Instant::now(),
        }
    }
    
    pub fn into_task(self) -> T {
        self.task
    }
}

#[allow(dead_code)]
pub struct PriorityWorkStealingScheduler<T> {
    workers: Vec<Worker<PriorityTask<T>>>,
    injector: Arc<Injector<PriorityTask<T>>>,
    high_priority_injector: Arc<Injector<PriorityTask<T>>>,
    stealer_count: AtomicUsize,
}

impl<T> PriorityWorkStealingScheduler<T> {
    pub fn new(worker_count: usize) -> Self {
        let workers: Vec<Worker<PriorityTask<T>>> = (0..worker_count)
            .map(|_| Worker::new_fifo())
            .collect();
        
        Self {
            workers,
            injector: Arc::new(Injector::new()),
            high_priority_injector: Arc::new(Injector::new()),
            stealer_count: AtomicUsize::new(0),
        }
    }
    
    /// 推送高优先级任务
    pub fn push_high_priority_task(&self, task: T) {
        let priority_task = PriorityTask::new(0, task); // 0 是最高优先级
        self.high_priority_injector.push(priority_task);
    }
    
    /// 推送普通优先级任务
    pub fn push_normal_priority_task(&self, priority: u32, task: T) {
        let priority_task = PriorityTask::new(priority, task);
        self.injector.push(priority_task);
    }
    
    /// 窃取任务（优先处理高优先级任务）
    pub fn steal_task(&self, worker_index: usize) -> Option<T> {
        if worker_index >= self.workers.len() {
            return None;
        }
        
        // 首先尝试从自己的队列获取任务
        if let Some(priority_task) = self.workers[worker_index].pop() {
            return Some(priority_task.into_task());
        }
        
        // 尝试从高优先级注入器获取任务
        if let Some(priority_task) = self.high_priority_injector.steal().success() {
            return Some(priority_task.into_task());
        }
        
        // 尝试从普通注入器获取任务
        if let Some(priority_task) = self.injector.steal().success() {
            return Some(priority_task.into_task());
        }
        
        // 尝试从其他工作线程窃取任务
        for i in 0..self.workers.len() {
            if i != worker_index {
                let stealer = self.workers[i].stealer();
                if let Some(priority_task) = stealer.steal().success() {
                    return Some(priority_task.into_task());
                }
            }
        }
        
        None
    }
    
    /// 运行优先级工作窃取示例
    #[cfg(feature = "work_stealing_examples")]
    pub fn run_example() {
        println!("=== 优先级工作窃取调度器示例 ===");
        
        let scheduler = PriorityWorkStealingScheduler::new(4);
        let results: Arc<Mutex<Vec<(u32, i32)>>> = Arc::new(Mutex::new(Vec::new()));
        
        // 创建不同优先级的任务
        for i in 0..10 {
            scheduler.push_normal_priority_task(10 - i, i); // 优先级递减
        }
        
        // 添加一些高优先级任务
        for i in 100..105 {
            scheduler.push_high_priority_task(i);
        }
        
        // 创建工作线程
        thread::scope(|s| {
            for worker_id in 0..4 {
                let results = results.clone();
                s.spawn(move || {
                    let mut local_results: Vec<(u32, i32)> = Vec::new();
                    loop {
                        if let Some(task) = scheduler.steal_task(worker_id) {
                            let result = task * 2;
                            local_results.push((worker_id as u32, result));
                            thread::sleep(Duration::from_millis(1));
                        } else {
                            break;
                        }
                    }
                    results.lock().unwrap().extend(local_results);
                });
            }
        });
        
        let final_results = results.lock().unwrap();
        println!("优先级工作窃取结果: {:?}", final_results);
    }
}

/// 自适应工作窃取调度器
/// 
/// 根据系统负载自动调整工作窃取策略
#[allow(dead_code)]
pub struct AdaptiveWorkStealingScheduler<T> {
    workers: Vec<Worker<T>>,
    injector: Arc<Injector<T>>,
    stealer_count: AtomicUsize,
    steal_attempts: AtomicUsize,
    successful_steals: AtomicUsize,
    last_adaptation: Arc<Mutex<Instant>>,
    adaptation_interval: Duration,
}

impl<T> AdaptiveWorkStealingScheduler<T> {
    pub fn new(worker_count: usize) -> Self {
        let workers: Vec<Worker<T>> = (0..worker_count)
            .map(|_| Worker::new_fifo())
            .collect();
        
        Self {
            workers,
            injector: Arc::new(Injector::new()),
            stealer_count: AtomicUsize::new(0),
            steal_attempts: AtomicUsize::new(0),
            successful_steals: AtomicUsize::new(0),
            last_adaptation: Arc::new(Mutex::new(Instant::now())),
            adaptation_interval: Duration::from_millis(100),
        }
    }
    
    /// 推送任务
    pub fn push_task(&self, task: T) {
        self.injector.push(task);
    }
    
    /// 自适应窃取任务
    pub fn steal_task(&self, worker_index: usize) -> Option<T> {
        if worker_index >= self.workers.len() {
            return None;
        }
        
        // 首先尝试从自己的队列获取任务
        if let Some(task) = self.workers[worker_index].pop() {
            return Some(task);
        }
        
        // 检查是否需要适应
        self.check_adaptation();
        
        // 尝试从全局注入器获取任务
        if let Some(task) = self.injector.steal().success() {
            self.record_successful_steal();
            return Some(task);
        }
        
        // 根据当前成功率决定窃取策略
        let steal_success_rate = self.get_steal_success_rate();
        
        if steal_success_rate > 0.3 {
            // 高成功率，积极窃取
            self.aggressive_steal(worker_index)
        } else {
            // 低成功率，保守窃取
            self.conservative_steal(worker_index)
        }
    }
    
    fn check_adaptation(&self) {
        let mut last_adaptation = self.last_adaptation.lock().unwrap();
        if last_adaptation.elapsed() > self.adaptation_interval {
            // 重置统计
            self.steal_attempts.store(0, Ordering::Relaxed);
            self.successful_steals.store(0, Ordering::Relaxed);
            *last_adaptation = Instant::now();
        }
    }
    
    fn record_successful_steal(&self) {
        self.steal_attempts.fetch_add(1, Ordering::Relaxed);
        self.successful_steals.fetch_add(1, Ordering::Relaxed);
    }
    
    fn record_failed_steal(&self) {
        self.steal_attempts.fetch_add(1, Ordering::Relaxed);
    }
    
    fn get_steal_success_rate(&self) -> f64 {
        let attempts = self.steal_attempts.load(Ordering::Relaxed);
        let successes = self.successful_steals.load(Ordering::Relaxed);
        
        if attempts == 0 {
            0.0
        } else {
            successes as f64 / attempts as f64
        }
    }
    
    fn aggressive_steal(&self, worker_index: usize) -> Option<T> {
        // 尝试从所有其他工作线程窃取
        for i in 0..self.workers.len() {
            if i != worker_index {
                let stealer = self.workers[i].stealer();
                if let Some(task) = stealer.steal().success() {
                    self.record_successful_steal();
                    return Some(task);
                }
            }
        }
        
        self.record_failed_steal();
        None
    }
    
    fn conservative_steal(&self, worker_index: usize) -> Option<T> {
        // 只尝试从相邻的工作线程窃取
        let left_index = if worker_index == 0 {
            self.workers.len() - 1
        } else {
            worker_index - 1
        };
        
        let right_index = (worker_index + 1) % self.workers.len();
        
        for &index in &[left_index, right_index] {
            let stealer = self.workers[index].stealer();
            if let Some(task) = stealer.steal().success() {
                self.record_successful_steal();
                return Some(task);
            }
        }
        
        self.record_failed_steal();
        None
    }
    
    /// 运行自适应工作窃取示例
    #[cfg(feature = "work_stealing_examples")]
    pub fn run_example() {
        println!("=== 自适应工作窃取调度器示例 ===");
        
        let scheduler = AdaptiveWorkStealingScheduler::new(4);
        let results: Arc<Mutex<Vec<i32>>> = Arc::new(Mutex::new(Vec::new()));
        
        // 创建任务
        for i in 0..50 {
            scheduler.push_task(i);
        }
        
        // 创建工作线程
        thread::scope(|s| {
            for worker_id in 0..4 {
                let results = results.clone();
                s.spawn(move || {
                    let mut local_results = Vec::new();
                    loop {
                        if let Some(task) = scheduler.steal_task(worker_id) {
                            let result = task * task;
                            local_results.push(result);
                            thread::sleep(Duration::from_millis(1));
                        } else {
                            break;
                        }
                    }
                    results.lock().unwrap().extend(local_results);
                });
            }
        });
        
        let final_results = results.lock().unwrap();
        println!("自适应工作窃取结果: {:?}", final_results);
    }
}

/// NUMA感知工作窃取调度器
/// 
/// 考虑NUMA拓扑结构的工作窃取调度器
#[allow(dead_code)]
pub struct NumaAwareWorkStealingScheduler<T> {
    numa_nodes: Vec<Vec<Worker<T>>>,
    global_injector: Arc<Injector<T>>,
    node_injectors: Vec<Arc<Injector<T>>>,
    stealer_count: AtomicUsize,
}

impl<T> NumaAwareWorkStealingScheduler<T> {
    pub fn new(numa_node_count: usize, workers_per_node: usize) -> Self {
        let numa_nodes: Vec<Vec<Worker<T>>> = (0..numa_node_count)
            .map(|_| {
                (0..workers_per_node)
                    .map(|_| Worker::new_fifo())
                    .collect()
            })
            .collect();
        
        let node_injectors: Vec<Arc<Injector<T>>> = (0..numa_node_count)
            .map(|_| Arc::new(Injector::new()))
            .collect();
        
        Self {
            numa_nodes,
            global_injector: Arc::new(Injector::new()),
            node_injectors,
            stealer_count: AtomicUsize::new(0),
        }
    }
    
    /// 推送任务到指定NUMA节点
    pub fn push_task_to_node(&self, node_id: usize, task: T) {
        if node_id < self.node_injectors.len() {
            self.node_injectors[node_id].push(task);
        }
    }
    
    /// 推送任务到全局注入器
    pub fn push_global_task(&self, task: T) {
        self.global_injector.push(task);
    }
    
    /// NUMA感知窃取任务
    pub fn steal_task(&self, node_id: usize, worker_id: usize) -> Option<T> {
        if node_id >= self.numa_nodes.len() || worker_id >= self.numa_nodes[node_id].len() {
            return None;
        }
        
        // 首先尝试从自己的队列获取任务
        if let Some(task) = self.numa_nodes[node_id][worker_id].pop() {
            return Some(task);
        }
        
        // 尝试从本地NUMA节点的注入器获取任务
        if let Some(task) = self.node_injectors[node_id].steal().success() {
            return Some(task);
        }
        
        // 尝试从本地NUMA节点的其他工作线程窃取任务
        for i in 0..self.numa_nodes[node_id].len() {
            if i != worker_id {
                let stealer = self.numa_nodes[node_id][i].stealer();
                if let Some(task) = stealer.steal().success() {
                    return Some(task);
                }
            }
        }
        
        // 尝试从全局注入器获取任务
        if let Some(task) = self.global_injector.steal().success() {
            return Some(task);
        }
        
        // 最后尝试从其他NUMA节点窃取任务
        for other_node_id in 0..self.numa_nodes.len() {
            if other_node_id != node_id {
                for i in 0..self.numa_nodes[other_node_id].len() {
                    let stealer = self.numa_nodes[other_node_id][i].stealer();
                    if let Some(task) = stealer.steal().success() {
                        return Some(task);
                    }
                }
            }
        }
        
        None
    }
    
    /// 运行NUMA感知工作窃取示例
    #[cfg(feature = "work_stealing_examples")]
    pub fn run_example() {
        println!("=== NUMA感知工作窃取调度器示例 ===");
        
        let scheduler = NumaAwareWorkStealingScheduler::new(2, 2); // 2个NUMA节点，每个节点2个工作线程
        let results: Arc<Mutex<Vec<(usize, usize, i32)>>> = Arc::new(Mutex::new(Vec::new()));
        
        // 创建任务并分配到不同NUMA节点
        for i in 0..20 {
            let node_id = i % 2;
            scheduler.push_task_to_node(node_id, i);
        }
        
        // 添加一些全局任务
        for i in 100..110 {
            scheduler.push_global_task(i);
        }
        
        // 创建工作线程
        thread::scope(|s| {
            for node_id in 0..2 {
                for worker_id in 0..2 {
                    let results = results.clone();
                    s.spawn(move || {
                        let mut local_results: Vec<(usize, usize, i32)> = Vec::new();
                        loop {
                            if let Some(task) = scheduler.steal_task(node_id, worker_id) {
                                let result = task * 3;
                                local_results.push((node_id, worker_id, result));
                                thread::sleep(Duration::from_millis(1));
                            } else {
                                break;
                            }
                        }
                        results.lock().unwrap().extend(local_results);
                    });
                }
            }
        });
        
        let final_results = results.lock().unwrap();
        println!("NUMA感知工作窃取结果: {:?}", final_results);
    }
}

/// 运行所有工作窃取示例
pub fn demonstrate_work_stealing() {
    println!("=== 工作窃取算法演示 ===");
    #[cfg(feature = "work_stealing_examples")] {
        WorkStealingScheduler::<i32>::run_example();
        PriorityWorkStealingScheduler::<i32>::run_example();
        AdaptiveWorkStealingScheduler::<i32>::run_example();
        NumaAwareWorkStealingScheduler::<i32>::run_example();
    }
    #[cfg(not(feature = "work_stealing_examples"))]
    {
        println!("(已跳过运行示例，启用 feature=work_stealing_examples 可开启)");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_basic_work_stealing() {
        let scheduler = WorkStealingScheduler::new(2);
        
        // 推送一些任务
        scheduler.push_global_task(1);
        scheduler.push_global_task(2);
        scheduler.push_global_task(3);
        
        // 窃取任务
        let task1: Option<i32> = scheduler.steal_task(0);
        let task2: Option<i32> = scheduler.steal_task(1);
        
        assert!(task1.is_some() || task2.is_some());
    }
    
    #[test]
    fn test_priority_work_stealing() {
        let scheduler = PriorityWorkStealingScheduler::new(2);
        
        // 推送不同优先级的任务
        scheduler.push_normal_priority_task(10, 1);
        scheduler.push_high_priority_task(2);
        scheduler.push_normal_priority_task(5, 3);
        
        // 窃取任务
        let task1: Option<i32> = scheduler.steal_task(0);
        let task2: Option<i32> = scheduler.steal_task(1);
        
        assert!(task1.is_some() || task2.is_some());
    }
    
    #[test]
    fn test_adaptive_work_stealing() {
        let scheduler = AdaptiveWorkStealingScheduler::new(2);
        
        // 推送任务
        scheduler.push_task(1);
        scheduler.push_task(2);
        
        // 窃取任务
        let task1: Option<i32> = scheduler.steal_task(0);
        let task2: Option<i32> = scheduler.steal_task(1);
        
        assert!(task1.is_some() || task2.is_some());
    }
    
    #[test]
    fn test_numa_aware_work_stealing() {
        let scheduler = NumaAwareWorkStealingScheduler::new(2, 2);
        
        // 推送任务到不同节点
        scheduler.push_task_to_node(0, 1);
        scheduler.push_task_to_node(1, 2);
        scheduler.push_global_task(3);
        
        // 窃取任务
        let task1: Option<i32> = scheduler.steal_task(0, 0);
        let task2: Option<i32> = scheduler.steal_task(1, 0);
        
        assert!(task1.is_some() || task2.is_some());
    }
}
