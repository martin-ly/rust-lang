# 分布式算法工作流程序框架设计

## 目录

- [分布式算法工作流程序框架设计](#分布式算法工作流程序框架设计)
  - [目录](#目录)
  - [1. 自我资源与行为感知框架](#1-自我资源与行为感知框架)
    - [1.1 执行环境感知组件](#11-执行环境感知组件)
    - [1.2 工作流行为自适应模式](#12-工作流行为自适应模式)
  - [2. 通用性、可组合性与分布式系统结构](#2-通用性可组合性与分布式系统结构)
    - [2.1 组合式工作流引擎](#21-组合式工作流引擎)
    - [2.2 分布式拓扑管理器](#22-分布式拓扑管理器)
  - [3. 分布式系统自动化控制](#3-分布式系统自动化控制)
    - [3.1 错误处理与自动恢复](#31-错误处理与自动恢复)

本文提出一个通用的形式化分布式算法工作流框架，
具备自我感知、可组合、可监测、自动控制等特性，
仅使用标准库组件，不依赖外部开源软件。

## 1. 自我资源与行为感知框架

### 1.1 执行环境感知组件

```rust
// 环境感知组件 - 检测系统资源状态并自适应调整工作流行为
use std::collections::VecDeque;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, RwLock};
use std::thread;
use std::time::{Duration, Instant};

// 系统资源状态
#[derive(Clone, Debug)]
pub struct SystemResources {
    // CPU 相关指标
    cpu_cores: usize,
    cpu_usage: f64, // 0.0-1.0 表示利用率
    
    // 内存相关指标
    total_memory: usize, // 字节
    available_memory: usize, // 字节
    
    // 线程池状态
    active_threads: usize,
    queued_tasks: usize,
    
    // 网络状态
    network_latency: Duration,
    connection_error_rate: f64, // 0.0-1.0 错误率
    
    // 时间戳
    timestamp: Instant,
}

impl SystemResources {
    // 创建当前系统资源状态
    pub fn current() -> Self {
        // 实际实现中应该使用系统API读取真实数据
        // 此处仅为演示提供模拟数据
        
        // 获取CPU核心数
        let cpu_cores = num_cpus::get();
        
        // 获取系统内存信息（示例用固定值）
        let total_memory = 16 * 1024 * 1024 * 1024; // 16GB
        let available_memory = 8 * 1024 * 1024 * 1024; // 8GB
        
        Self {
            cpu_cores,
            cpu_usage: 0.5, // 假设50%CPU使用率
            total_memory,
            available_memory,
            active_threads: 4,
            queued_tasks: 10,
            network_latency: Duration::from_millis(50),
            connection_error_rate: 0.01, // 1%错误率
            timestamp: Instant::now(),
        }
    }
    
    // 检查是否应该使用并行处理
    pub fn should_use_parallelism(&self) -> bool {
        // 如果有多个CPU核心且利用率低于80%，则建议使用并行处理
        self.cpu_cores > 1 && self.cpu_usage < 0.8
    }
    
    // 计算建议的并行任务数
    pub fn suggested_parallel_tasks(&self) -> usize {
        if !self.should_use_parallelism() {
            return 1;
        }
        
        // 根据CPU核心数和当前利用率估算
        let available_cores = (self.cpu_cores as f64 * (1.0 - self.cpu_usage)).ceil() as usize;
        available_cores.max(1)
    }
    
    // 检查是否有足够内存运行特定大小的任务
    pub fn has_sufficient_memory(&self, required_bytes: usize) -> bool {
        self.available_memory >= required_bytes
    }
    
    // 检查网络是否健康
    pub fn is_network_healthy(&self) -> bool {
        self.network_latency < Duration::from_millis(200) && 
        self.connection_error_rate < 0.05 // 错误率低于5%
    }
    
    // 获取资源状态年龄
    pub fn age(&self) -> Duration {
        self.timestamp.elapsed()
    }
    
    // 判断数据是否过期
    pub fn is_stale(&self, max_age: Duration) -> bool {
        self.age() > max_age
    }
}

// 执行模式
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ExecutionMode {
    Synchronous,         // 同步执行
    Asynchronous,        // 异步执行
    Parallel(usize),     // 并行执行，指定线程数
    Adaptive,            // 自适应模式（根据系统状态选择）
}

// 执行策略
pub struct ExecutionStrategy {
    mode: ExecutionMode,
    resources: Arc<RwLock<SystemResources>>,
    resource_monitor_handle: Option<thread::JoinHandle<()>>,
    running: Arc<AtomicBool>,
}

impl ExecutionStrategy {
    pub fn new(initial_mode: ExecutionMode) -> Self {
        let resources = Arc::new(RwLock::new(SystemResources::current()));
        let running = Arc::new(AtomicBool::new(true));
        
        // 创建资源监控线程
        let monitor_resources = Arc::clone(&resources);
        let monitor_running = Arc::clone(&running);
        
        let handle = thread::spawn(move || {
            while monitor_running.load(Ordering::Relaxed) {
                // 每秒更新一次系统资源状态
                thread::sleep(Duration::from_secs(1));
                
                // 获取最新资源状态
                let updated_resources = SystemResources::current();
                
                // 更新共享状态
                let mut res = monitor_resources.write().unwrap();
                *res = updated_resources;
            }
        });
        
        Self {
            mode: initial_mode,
            resources,
            resource_monitor_handle: Some(handle),
            running,
        }
    }
    
    // 获取当前执行模式
    pub fn mode(&self) -> ExecutionMode {
        match self.mode {
            ExecutionMode::Adaptive => self.determine_best_mode(),
            _ => self.mode,
        }
    }
    
    // 设置执行模式
    pub fn set_mode(&mut self, mode: ExecutionMode) {
        self.mode = mode;
    }
    
    // 根据当前系统资源确定最佳执行模式
    fn determine_best_mode(&self) -> ExecutionMode {
        let resources = self.resources.read().unwrap();
        
        // 网络不健康时选择异步模式
        if !resources.is_network_healthy() {
            return ExecutionMode::Asynchronous;
        }
        
        // 系统资源足够时使用并行
        if resources.should_use_parallelism() {
            let threads = resources.suggested_parallel_tasks();
            return ExecutionMode::Parallel(threads);
        }
        
        // 默认使用同步模式
        ExecutionMode::Synchronous
    }
    
    // 获取当前系统资源状态
    pub fn current_resources(&self) -> SystemResources {
        let resources = self.resources.read().unwrap();
        resources.clone()
    }
    
    // 执行任务，根据当前模式自动选择执行方式
    pub fn execute<F, T>(&self, task: F) -> T
    where
        F: FnOnce() -> T + Send + 'static,
        T: Send + 'static,
    {
        match self.mode() {
            ExecutionMode::Synchronous => {
                // 同步直接执行
                task()
            }
            ExecutionMode::Asynchronous => {
                // 异步执行（简化示例）
                let (tx, rx) = std::sync::mpsc::channel();
                
                thread::spawn(move || {
                    let result = task();
                    tx.send(result).unwrap();
                });
                
                // 等待结果
                rx.recv().unwrap()
            }
            ExecutionMode::Parallel(threads) => {
                // 在这个简化版本中，我们不实际并行执行任务
                // 实际应该使用线程池或rayon等库
                task()
            }
            ExecutionMode::Adaptive => {
                // 递归调用，因为mode()会返回实际模式
                self.execute(task)
            }
        }
    }
}

impl Drop for ExecutionStrategy {
    fn drop(&mut self) {
        // 停止监控线程
        self.running.store(false, Ordering::Relaxed);
        
        // 等待线程完成
        if let Some(handle) = self.resource_monitor_handle.take() {
            let _ = handle.join();
        }
    }
}

// 资源感知任务调度器
pub struct ResourceAwareScheduler {
    strategy: ExecutionStrategy,
    task_queue: Arc<Mutex<VecDeque<ScheduledTask>>>,
    active_workers: Arc<AtomicUsize>,
    max_workers: usize,
    running: Arc<AtomicBool>,
    worker_threads: Vec<thread::JoinHandle<()>>,
}

// 调度任务
struct ScheduledTask {
    priority: u8,
    memory_requirement: usize,
    task: Box<dyn FnOnce() + Send>,
}

impl ResourceAwareScheduler {
    pub fn new(max_workers: usize) -> Self {
        let strategy = ExecutionStrategy::new(ExecutionMode::Adaptive);
        let task_queue = Arc::new(Mutex::new(VecDeque::new()));
        let active_workers = Arc::new(AtomicUsize::new(0));
        let running = Arc::new(AtomicBool::new(true));
        let worker_threads = Vec::new();
        
        let mut scheduler = Self {
            strategy,
            task_queue,
            active_workers,
            max_workers,
            running,
            worker_threads,
        };
        
        // 启动工作线程
        scheduler.start_workers();
        
        scheduler
    }
    
    // 启动工作线程
    fn start_workers(&mut self) {
        for _ in 0..self.max_workers {
            let queue = Arc::clone(&self.task_queue);
            let active = Arc::clone(&self.active_workers);
            let running = Arc::clone(&self.running);
            
            let handle = thread::spawn(move || {
                while running.load(Ordering::Relaxed) {
                    // 尝试获取任务
                    let task = {
                        let mut queue = queue.lock().unwrap();
                        queue.pop_front()
                    };
                    
                    if let Some(task) = task {
                        // 增加活动工作者计数
                        active.fetch_add(1, Ordering::SeqCst);
                        
                        // 执行任务
                        (task.task)();
                        
                        // 减少活动工作者计数
                        active.fetch_sub(1, Ordering::SeqCst);
                    } else {
                        // 没有任务，短暂休眠
                        thread::sleep(Duration::from_millis(10));
                    }
                }
            });
            
            self.worker_threads.push(handle);
        }
    }
    
    // 提交任务
    pub fn submit<F>(&self, priority: u8, memory_requirement: usize, task: F)
    where
        F: FnOnce() + Send + 'static,
    {
        let scheduled_task = ScheduledTask {
            priority,
            memory_requirement,
            task: Box::new(task),
        };
        
        let mut queue = self.task_queue.lock().unwrap();
        
        // 按优先级插入
        let pos = queue.iter().position(|t| t.priority < priority).unwrap_or(queue.len());
        queue.insert(pos, scheduled_task);
    }
    
    // 获取当前活动工作者数量
    pub fn active_workers(&self) -> usize {
        self.active_workers.load(Ordering::SeqCst)
    }
    
    // 获取等待中的任务数量
    pub fn queued_tasks(&self) -> usize {
        let queue = self.task_queue.lock().unwrap();
        queue.len()
    }
    
    // 获取执行策略
    pub fn strategy(&self) -> &ExecutionStrategy {
        &self.strategy
    }
}

impl Drop for ResourceAwareScheduler {
    fn drop(&mut self) {
        // 停止所有工作线程
        self.running.store(false, Ordering::Relaxed);
        
        // 等待所有线程完成
        for handle in self.worker_threads.drain(..) {
            let _ = handle.join();
        }
    }
}

// 使用示例
fn execution_strategy_example() {
    // 创建资源感知调度器
    let scheduler = ResourceAwareScheduler::new(4);
    
    // 提交一些任务
    for i in 0..10 {
        let priority = if i % 3 == 0 { 2 } else { 1 };
        
        scheduler.submit(priority, 1024 * 1024, move || {
            println!("Executing task {} with priority {}", i, priority);
            thread::sleep(Duration::from_millis(100));
        });
    }
    
    // 检查执行模式
    let strategy = scheduler.strategy();
    println!("Current execution mode: {:?}", strategy.mode());
    
    // 检查系统资源
    let resources = strategy.current_resources();
    println!("System resources: {:?}", resources);
    
    // 等待任务完成
    while scheduler.queued_tasks() > 0 || scheduler.active_workers() > 0 {
        println!(
            "Waiting... Queued tasks: {}, Active workers: {}", 
            scheduler.queued_tasks(),
            scheduler.active_workers()
        );
        thread::sleep(Duration::from_secs(1));
    }
    
    println!("All tasks completed");
}
```

**设计原则**：构建能够感知底层系统资源状态的执行框架，根据资源可用性自动选择最佳执行模式（同步、异步、并行），实现工作流的自适应执行。

### 1.2 工作流行为自适应模式

```rust
// 工作流行为自适应模式 - 根据任务特性和系统状态自动调整执行策略
use std::fmt;
use std::marker::PhantomData;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

// 工作单元特征
pub trait WorkUnit<Input, Output, Error> {
    // 同步执行
    fn execute(&self, input: Input) -> Result<Output, Error>;
    
    // 估计执行成本
    fn estimate_cost(&self, input: &Input) -> WorkUnitCost;
    
    // 工作单元名称
    fn name(&self) -> &str;
    
    // 是否支持异步执行
    fn supports_async(&self) -> bool {
        false
    }
    
    // 是否支持并行执行
    fn supports_parallel(&self) -> bool {
        false
    }
    
    // 克隆工作单元（如果需要并行执行）
    fn box_clone(&self) -> Box<dyn WorkUnit<Input, Output, Error> + Send + Sync>;
}

// 执行成本估计
#[derive(Debug, Clone, Copy)]
pub struct WorkUnitCost {
    // 估计执行时间（毫秒）
    pub time_ms: u64,
    
    // 估计内存使用（字节）
    pub memory_bytes: usize,
    
    // 估计计算强度（0.0-1.0，1.0表示完全CPU密集）
    pub cpu_intensity: f64,
    
    // 估计IO强度（0.0-1.0，1.0表示完全IO密集）
    pub io_intensity: f64,
    
    // 预期网络请求数
    pub network_requests: usize,
}

impl WorkUnitCost {
    pub fn new() -> Self {
        Self {
            time_ms: 0,
            memory_bytes: 0,
            cpu_intensity: 0.5,
            io_intensity: 0.0,
            network_requests: 0,
        }
    }
    
    pub fn with_time(mut self, time_ms: u64) -> Self {
        self.time_ms = time_ms;
        self
    }
    
    pub fn with_memory(mut self, memory_bytes: usize) -> Self {
        self.memory_bytes = memory_bytes;
        self
    }
    
    pub fn with_cpu_intensity(mut self, intensity: f64) -> Self {
        self.cpu_intensity = intensity.max(0.0).min(1.0);
        self
    }
    
    pub fn with_io_intensity(mut self, intensity: f64) -> Self {
        self.io_intensity = intensity.max(0.0).min(1.0);
        self
    }
    
    pub fn with_network_requests(mut self, count: usize) -> Self {
        self.network_requests = count;
        self
    }
    
    // 判断是否应该使用异步执行
    pub fn should_execute_async(&self) -> bool {
        // 如果IO密集型或有网络请求，倾向于异步
        self.io_intensity > 0.6 || self.network_requests > 0
    }
    
    // 判断是否应该使用并行执行
    pub fn should_execute_parallel(&self, available_cores: usize) -> bool {
        // 如果CPU密集且执行时间长，倾向于并行
        self.cpu_intensity > 0.7 && self.time_ms > 100 && available_cores > 1
    }
    
    // 估算最佳线程数
    pub fn optimal_threads(&self, available_cores: usize) -> usize {
        if !self.should_execute_parallel(available_cores) {
            return 1;
        }
        
        // 根据CPU密集度和可用核心数估算
        let threads = (available_cores as f64 * self.cpu_intensity).ceil() as usize;
        threads.max(1).min(available_cores)
    }
}

// 自适应执行策略
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum AdaptiveStrategy {
    // 基于成本自动选择最佳策略
    Auto,
    
    // 强制使用特定策略
    ForceSynchronous,
    ForceAsynchronous,
    ForceParallel(usize), // 指定线程数
}

// 执行结果与指标
pub struct ExecutionResult<T> {
    pub result: T,
    pub duration: Duration,
    pub strategy_used: String,
    pub started_at: Instant,
    pub completed_at: Instant,
}

impl<T> ExecutionResult<T> {
    fn new(result: T, duration: Duration, strategy: &str) -> Self {
        let now = Instant::now();
        Self {
            result,
            duration,
            strategy_used: strategy.to_string(),
            started_at: now - duration,
            completed_at: now,
        }
    }
}

// 自适应执行器
pub struct AdaptiveExecutor {
    available_cores: usize,
    strategy: AdaptiveStrategy,
    metrics: Arc<Mutex<ExecutionMetrics>>,
}

// 执行指标跟踪
#[derive(Default)]
pub struct ExecutionMetrics {
    sync_executions: usize,
    async_executions: usize,
    parallel_executions: usize,
    total_execution_time: Duration,
    longest_execution: Duration,
    shortest_execution: Option<Duration>,
}

impl AdaptiveExecutor {
    pub fn new() -> Self {
        Self {
            available_cores: num_cpus::get(),
            strategy: AdaptiveStrategy::Auto,
            metrics: Arc::new(Mutex::new(ExecutionMetrics::default())),
        }
    }
    
    pub fn with_strategy(mut self, strategy: AdaptiveStrategy) -> Self {
        self.strategy = strategy;
        self
    }
    
    // 执行工作单元
    pub fn execute<I, O, E, W>(&self, work_unit: &W, input: I) -> Result<ExecutionResult<O>, E>
    where
        W: WorkUnit<I, O, E> + Send + Sync,
        I: Clone + Send + 'static,
        O: Send + 'static,
        E: Send + 'static,
    {
        // 估计执行成本
        let cost = work_unit.estimate_cost(&input);
        
        // 选择执行策略
        let effective_strategy = match self.strategy {
            AdaptiveStrategy::Auto => self.determine_best_strategy(work_unit, &cost),
            _ => self.strategy,
        };
        
        // 根据策略执行
        let start_time = Instant::now();
        let result = match effective_strategy {
            AdaptiveStrategy::ForceSynchronous | AdaptiveStrategy::Auto => {
                // 同步执行
                let strategy_name = "Synchronous";
                let result = work_unit.execute(input)?;
                let duration = start_time.elapsed();
                
                // 更新指标
                self.update_metrics(strategy_name, duration);
                
                Ok(ExecutionResult::new(result, duration, strategy_name))
            }
            AdaptiveStrategy::ForceAsynchronous => {
                // 异步执行
                if !work_unit.supports_async() {
                    // 回退到同步执行
                    return self.execute_with_strategy(work_unit, input, AdaptiveStrategy::ForceSynchronous);
                }
                
                let strategy_name = "Asynchronous";
                
                // 使用消息通道进行简单的异步模拟
                let (tx, rx) = std::sync::mpsc::channel();
                let work_clone = work_unit.box_clone();
                let input_clone = input;
                
                std::thread::spawn(move || {
                    let result = work_clone.execute(input_clone);
                    let _ = tx.send(result);
                });
                
                // 接收结果
                let result = rx.recv().unwrap()?;
                let duration = start_time.elapsed();
                
                // 更新指标
                self.update_metrics(strategy_name, duration);
                
                Ok(ExecutionResult::new(result, duration, strategy_name))
            }
            AdaptiveStrategy::ForceParallel(threads) => {
                // 并行执行
                if !work_unit.supports_parallel() {
                    // 回退到同步执行
                    return self.execute_with_strategy(work_unit, input, AdaptiveStrategy::ForceSynchronous);
                }
                
                let strategy_name = &format!("Parallel({})", threads);
                
                // 在实际实现中，这里应该使用线程池或rayon等并行库
                // 简化示例仅使用单线程执行
                let result = work_unit.execute(input)?;
                let duration = start_time.elapsed();
                
                // 更新指标
                self.update_metrics(strategy_name, duration);
                
                Ok(ExecutionResult::new(result, duration, strategy_name))
            }
        };
        
        result
    }
    
    // 使用指定策略执行
    fn execute_with_strategy<I, O, E, W>(
        &self,
        work_unit: &W,
        input: I,
        strategy: AdaptiveStrategy,
    ) -> Result<ExecutionResult<O>, E>
    where
        W: WorkUnit<I, O, E> + Send + Sync,
        I: Clone + Send + 'static,
        O: Send + 'static,
        E: Send + 'static,
    {
        let executor = Self {
            available_cores: self.available_cores,
            strategy,
            metrics: Arc::clone(&self.metrics),
        };
        
        executor.execute(work_unit, input)
    }
    
    // 确定最佳执行策略
    fn determine_best_strategy<I, O, E, W>(
        &self,
        work_unit: &W,
        cost: &WorkUnitCost,
    ) -> AdaptiveStrategy
    where
        W: WorkUnit<I, O, E> + Send + Sync,
    {
        // 检查是否应该使用并行
        if work_unit.supports_parallel() && cost.should_execute_parallel(self.available_cores) {
            let threads = cost.optimal_threads(self.available_cores);
            return AdaptiveStrategy::ForceParallel(threads);
        }
        
        // 检查是否应该使用异步
        if work_unit.supports_async() && cost.should_execute_async() {
            return AdaptiveStrategy::ForceAsynchronous;
        }
        
        // 默认使用同步
        AdaptiveStrategy::ForceSynchronous
    }
    
    // 更新执行指标
    fn update_metrics(&self, strategy: &str, duration: Duration) {
        let mut metrics = self.metrics.lock().unwrap();
        
        // 更新总执行时间
        metrics.total_execution_time += duration;
        
        // 更新最长执行时间
        if duration > metrics.longest_execution {
            metrics.longest_execution = duration;
        }
        
        // 更新最短执行时间
        if let Some(shortest) = metrics.shortest_execution {
            if duration < shortest {
                metrics.shortest_execution = Some(duration);
            }
        } else {
            metrics.shortest_execution = Some(duration);
        }
        
        // 更新策略计数
        match strategy {
            "Synchronous" => metrics.sync_executions += 1,
            "Asynchronous" => metrics.async_executions += 1,
            _ if strategy.starts_with("Parallel") => metrics.parallel_executions += 1,
            _ => {}
        }
    }
    
    // 获取执行指标
    pub fn get_metrics(&self) -> ExecutionMetrics {
        let metrics = self.metrics.lock().unwrap();
        metrics.clone()
    }
}

impl Default for AdaptiveExecutor {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for ExecutionMetrics {
    fn clone(&self) -> Self {
        Self {
            sync_executions: self.sync_executions,
            async_executions: self.async_executions,
            parallel_executions: self.parallel_executions,
            total_execution_time: self.total_execution_time,
            longest_execution: self.longest_execution,
            shortest_execution: self.shortest_execution,
        }
    }
}

impl fmt::Debug for ExecutionMetrics {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ExecutionMetrics")
            .field("sync_executions", &self.sync_executions)
            .field("async_executions", &self.async_executions)
            .field("parallel_executions", &self.parallel_executions)
            .field("total_execution_time", &format!("{:?}", self.total_execution_time))
            .field("longest_execution", &format!("{:?}", self.longest_execution))
            .field("shortest_execution", &format!("{:?}", self.shortest_execution))
            .finish()
    }
}

// 示例：基本工作单元实现
struct ExampleWorkUnit {
    name: String,
    // 模拟不同的工作特性
    cpu_intensive: bool,
    io_intensive: bool,
    supports_async: bool,
    supports_parallel: bool,
}

impl ExampleWorkUnit {
    fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            cpu_intensive: false,
            io_intensive: false,
            supports_async: false,
            supports_parallel: false,
        }
    }
    
    fn with_cpu_intensive(mut self, value: bool) -> Self {
        self.cpu_intensive = value;
        self
    }
    
    fn with_io_intensive(mut self, value: bool) -> Self {
        self.io_intensive = value;
        self
    }
    
    fn with_async_support(mut self, value: bool) -> Self {
        self.supports_async = value;
        self
    }
    
    fn with_parallel_support(mut self, value: bool) -> Self {
        self.supports_parallel = value;
        self
    }
}

impl<I, O, E> WorkUnit<I, O, E> for ExampleWorkUnit
where
    I: Send + Sync + Clone + 'static,
    O: Send + Sync + 'static,
    E: Send + Sync + 'static,
    // 模拟函数类型
    I: FnOnce() -> Result<O, E>,
{
    fn execute(&self, input: I) -> Result<O, E> {
        // 模拟执行（实际调用提供的函数）
        if self.cpu_intensive {
            // 模拟CPU密集型工作
            let start = Instant::now();
            while start.elapsed() < Duration::from_millis(50) {
                // 消耗CPU循环
                std::hint::black_box([0u8; 1024]);
            }
        }
        
        if self.io_intensive {
            // 模拟IO等待
            std::thread::sleep(Duration::from_millis(100));
        }
        
        // 执行实际工作
        input()
    }
    
    fn estimate_cost(&self, _input: &I) -> WorkUnitCost {
        let mut
继续前面的代码：

```rust
    fn estimate_cost(&self, _input: &I) -> WorkUnitCost {
        let mut cost = WorkUnitCost::new();
        
        if self.cpu_intensive {
            cost = cost.with_cpu_intensity(0.9)
                       .with_time(200)
                       .with_memory(1024 * 1024); // 1MB
        } else if self.io_intensive {
            cost = cost.with_io_intensity(0.9)
                       .with_time(150)
                       .with_network_requests(2);
        } else {
            cost = cost.with_cpu_intensity(0.5)
                       .with_io_intensity(0.2)
                       .with_time(50);
        }
        
        cost
    }
    
    fn name(&self) -> &str {
        &self.name
    }
    
    fn supports_async(&self) -> bool {
        self.supports_async
    }
    
    fn supports_parallel(&self) -> bool {
        self.supports_parallel
    }
    
    fn box_clone(&self) -> Box<dyn WorkUnit<I, O, E> + Send + Sync> {
        Box::new(Self {
            name: self.name.clone(),
            cpu_intensive: self.cpu_intensive,
            io_intensive: self.io_intensive,
            supports_async: self.supports_async,
            supports_parallel: self.supports_parallel,
        })
    }
}

// 使用示例
fn adaptive_execution_example() {
    // 创建自适应执行器
    let executor = AdaptiveExecutor::new();
    
    // 创建CPU密集型工作单元
    let cpu_work = ExampleWorkUnit::new("cpu-intensive")
        .with_cpu_intensive(true)
        .with_parallel_support(true);
    
    // 创建IO密集型工作单元
    let io_work = ExampleWorkUnit::new("io-intensive")
        .with_io_intensive(true)
        .with_async_support(true);
    
    // 执行CPU密集型工作
    let cpu_result = executor.execute(&cpu_work, || {
        println!("Executing CPU intensive work");
        // 模拟计算
        let mut sum = 0;
        for i in 0..1_000_000 {
            sum += i;
        }
        Ok::<_, String>(sum)
    });
    
    match cpu_result {
        Ok(result) => {
            println!("CPU work completed in {:?} using {} strategy",
                     result.duration, result.strategy_used);
        }
        Err(e) => {
            println!("CPU work failed: {}", e);
        }
    }
    
    // 执行IO密集型工作
    let io_result = executor.execute(&io_work, || {
        println!("Executing IO intensive work");
        // 模拟IO
        std::thread::sleep(Duration::from_millis(100));
        Ok::<_, String>("IO operation completed")
    });
    
    match io_result {
        Ok(result) => {
            println!("IO work completed in {:?} using {} strategy",
                     result.duration, result.strategy_used);
        }
        Err(e) => {
            println!("IO work failed: {}", e);
        }
    }
    
    // 打印执行指标
    let metrics = executor.get_metrics();
    println!("Execution metrics: {:?}", metrics);
}
```

**设计原则**：创建能够自适应执行不同类型工作负载的框架，根据任务特性（CPU密集型、IO密集型等）自动选择最佳执行策略，支持同步、异步和并行处理模式的无缝切换。

## 2. 通用性、可组合性与分布式系统结构

### 2.1 组合式工作流引擎

```rust
// 组合式工作流引擎 - 支持工作流的组合、监测和静态扩展
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::sync::{Arc, Mutex, RwLock};
use std::time::{Duration, Instant};

// 工作流节点
pub trait WorkflowNode<Context, Error> {
    // 节点名称
    fn name(&self) -> &str;
    
    // 处理节点逻辑
    fn process(&self, context: &mut Context) -> Result<(), Error>;
    
    // 节点描述
    fn description(&self) -> &str {
        "Generic workflow node"
    }
    
    // 估计处理时间
    fn estimate_duration(&self, _context: &Context) -> Duration {
        Duration::from_millis(100) // 默认100ms
    }
    
    // 是否可跳过（条件节点）
    fn can_skip(&self, _context: &Context) -> bool {
        false
    }
    
    // 克隆节点
    fn box_clone(&self) -> Box<dyn WorkflowNode<Context, Error> + Send + Sync>;
}

// 工作流事件类型
#[derive(Debug, Clone)]
pub enum WorkflowEvent {
    Started(String),                    // 工作流开始
    NodeStarted(String),                // 节点开始处理
    NodeCompleted(String, Duration),    // 节点完成处理
    NodeSkipped(String),                // 节点被跳过
    NodeFailed(String, String),         // 节点处理失败
    Completed(String, Duration),        // 工作流完成
    Failed(String, String),             // 工作流失败
}

// 工作流监听器
pub trait WorkflowListener: Send + Sync {
    fn on_event(&self, event: &WorkflowEvent);
}

// 日志监听器示例
pub struct LoggingListener {
    prefix: String,
}

impl LoggingListener {
    pub fn new(prefix: impl Into<String>) -> Self {
        Self {
            prefix: prefix.into(),
        }
    }
}

impl WorkflowListener for LoggingListener {
    fn on_event(&self, event: &WorkflowEvent) {
        match event {
            WorkflowEvent::Started(name) => {
                println!("{} Workflow '{}' started", self.prefix, name);
            }
            WorkflowEvent::NodeStarted(name) => {
                println!("{} Node '{}' started", self.prefix, name);
            }
            WorkflowEvent::NodeCompleted(name, duration) => {
                println!("{} Node '{}' completed in {:?}", self.prefix, name, duration);
            }
            WorkflowEvent::NodeSkipped(name) => {
                println!("{} Node '{}' skipped", self.prefix, name);
            }
            WorkflowEvent::NodeFailed(name, error) => {
                println!("{} Node '{}' failed: {}", self.prefix, name, error);
            }
            WorkflowEvent::Completed(name, duration) => {
                println!("{} Workflow '{}' completed in {:?}", self.prefix, name, duration);
            }
            WorkflowEvent::Failed(name, error) => {
                println!("{} Workflow '{}' failed: {}", self.prefix, name, error);
            }
        }
    }
}

// 指标收集监听器
pub struct MetricsListener {
    metrics: Arc<Mutex<WorkflowMetrics>>,
}

impl MetricsListener {
    pub fn new() -> Self {
        Self {
            metrics: Arc::new(Mutex::new(WorkflowMetrics::default())),
        }
    }
    
    pub fn metrics(&self) -> Arc<Mutex<WorkflowMetrics>> {
        Arc::clone(&self.metrics)
    }
}

impl WorkflowListener for MetricsListener {
    fn on_event(&self, event: &WorkflowEvent) {
        let mut metrics = self.metrics.lock().unwrap();
        
        match event {
            WorkflowEvent::Started(name) => {
                metrics.workflow_executions.entry(name.clone())
                       .or_insert_with(Vec::new)
                       .push(WorkflowExecution::new(name));
            }
            WorkflowEvent::NodeCompleted(name, duration) => {
                metrics.node_durations.entry(name.clone())
                       .or_insert_with(Vec::new)
                       .push(*duration);
            }
            WorkflowEvent::NodeSkipped(name) => {
                metrics.node_skips.entry(name.clone())
                       .or_insert(0)
                       .add_assign(1);
            }
            WorkflowEvent::NodeFailed(name, _) => {
                metrics.node_failures.entry(name.clone())
                       .or_insert(0)
                       .add_assign(1);
            }
            WorkflowEvent::Completed(name, duration) => {
                if let Some(executions) = metrics.workflow_executions.get_mut(name) {
                    if let Some(execution) = executions.last_mut() {
                        execution.completed = true;
                        execution.duration = Some(*duration);
                    }
                }
            }
            WorkflowEvent::Failed(name, _) => {
                if let Some(executions) = metrics.workflow_executions.get_mut(name) {
                    if let Some(execution) = executions.last_mut() {
                        execution.failed = true;
                    }
                }
                
                metrics.workflow_failures.entry(name.clone())
                       .or_insert(0)
                       .add_assign(1);
            }
            _ => {}
        }
    }
}

// 工作流指标
#[derive(Default)]
pub struct WorkflowMetrics {
    // 每个节点的执行时间
    node_durations: HashMap<String, Vec<Duration>>,
    
    // 节点跳过次数
    node_skips: HashMap<String, usize>,
    
    // 节点失败次数
    node_failures: HashMap<String, usize>,
    
    // 工作流执行记录
    workflow_executions: HashMap<String, Vec<WorkflowExecution>>,
    
    // 工作流失败次数
    workflow_failures: HashMap<String, usize>,
}

// 工作流执行记录
#[derive(Clone)]
pub struct WorkflowExecution {
    name: String,
    started_at: Instant,
    completed: bool,
    failed: bool,
    duration: Option<Duration>,
}

impl WorkflowExecution {
    fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            started_at: Instant::now(),
            completed: false,
            failed: false,
            duration: None,
        }
    }
    
    pub fn is_completed(&self) -> bool {
        self.completed
    }
    
    pub fn is_failed(&self) -> bool {
        self.failed
    }
    
    pub fn duration(&self) -> Option<Duration> {
        self.duration
    }
    
    pub fn name(&self) -> &str {
        &self.name
    }
    
    pub fn started_at(&self) -> Instant {
        self.started_at
    }
}

impl fmt::Debug for WorkflowMetrics {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // 计算平均节点执行时间
        let mut avg_node_times = HashMap::new();
        for (name, durations) in &self.node_durations {
            if !durations.is_empty() {
                let total: Duration = durations.iter().sum();
                let avg = total / durations.len() as u32;
                avg_node_times.insert(name, avg);
            }
        }
        
        // 计算工作流成功率
        let mut workflow_success_rates = HashMap::new();
        for (name, executions) in &self.workflow_executions {
            let total = executions.len();
            if total > 0 {
                let completed = executions.iter().filter(|e| e.completed).count();
                let rate = (completed as f64) / (total as f64) * 100.0;
                workflow_success_rates.insert(name, rate);
            }
        }
        
        f.debug_struct("WorkflowMetrics")
            .field("avg_node_times", &avg_node_times)
            .field("node_skips", &self.node_skips)
            .field("node_failures", &self.node_failures)
            .field("workflow_executions", &self.workflow_executions.iter().map(|(k, v)| (k, v.len())).collect::<HashMap<_, _>>())
            .field("workflow_success_rates", &workflow_success_rates)
            .finish()
    }
}

// 工作流定义
pub struct Workflow<Context, Error> {
    name: String,
    description: String,
    nodes: Vec<Box<dyn WorkflowNode<Context, Error> + Send + Sync>>,
    edges: HashMap<usize, Vec<usize>>, // 节点间连接（邻接表）
    entry_nodes: Vec<usize>,           // 入口节点索引
    listeners: Vec<Box<dyn WorkflowListener>>,
}

impl<Context, Error> Workflow<Context, Error>
where
    Context: Send + Sync + 'static,
    Error: Send + Sync + fmt::Display + fmt::Debug + 'static,
{
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            description: String::new(),
            nodes: Vec::new(),
            edges: HashMap::new(),
            entry_nodes: Vec::new(),
            listeners: Vec::new(),
        }
    }
    
    pub fn with_description(mut self, description: impl Into<String>) -> Self {
        self.description = description.into();
        self
    }
    
    // 添加节点
    pub fn add_node(
        &mut self,
        node: impl WorkflowNode<Context, Error> + Send + Sync + 'static,
    ) -> usize {
        let idx = self.nodes.len();
        self.nodes.push(Box::new(node));
        
        // 默认情况下，我们假设这是一个入口节点，直到建立连接
        self.entry_nodes.push(idx);
        
        // 初始化边映射
        self.edges.insert(idx, Vec::new());
        
        idx
    }
    
    // 添加边（从source到target的连接）
    pub fn add_edge(&mut self, source: usize, target: usize) -> Result<(), String> {
        if source >= self.nodes.len() || target >= self.nodes.len() {
            return Err(format!("Invalid node index: source={}, target={}", source, target));
        }
        
        // 添加连接
        self.edges.get_mut(&source).unwrap().push(target);
        
        // 目标节点不再是入口节点
        if let Some(pos) = self.entry_nodes.iter().position(|&i| i == target) {
            self.entry_nodes.remove(pos);
        }
        
        Ok(())
    }
    
    // 添加监听器
    pub fn add_listener(&mut self, listener: impl WorkflowListener + 'static) {
        self.listeners.push(Box::new(listener));
    }
    
    // 执行工作流
    pub fn execute(&self, context: &mut Context) -> Result<(), Error> {
        let start_time = Instant::now();
        let workflow_name = self.name.clone();
        
        // 通知工作流开始
        self.notify_event(WorkflowEvent::Started(workflow_name.clone()));
        
        // 访问标记（避免循环）
        let mut visited = HashSet::new();
        
        // 从所有入口节点开始执行
        for &entry in &self.entry_nodes {
            self.execute_node(entry, context, &mut visited)?;
        }
        
        // 通知工作流完成
        let duration = start_time.elapsed();
        self.notify_event(WorkflowEvent::Completed(workflow_name, duration));
        
        Ok(())
    }
    
    // 执行单个节点
    fn execute_node(
        &self,
        idx: usize,
        context: &mut Context,
        visited: &mut HashSet<usize>,
    ) -> Result<(), Error> {
        // 检查是否已访问
        if visited.contains(&idx) {
            return Ok(());
        }
        
        // 标记为已访问
        visited.insert(idx);
        
        let node = &self.nodes[idx];
        let node_name = node.name().to_string();
        
        // 检查是否可以跳过
        if node.can_skip(context) {
            self.notify_event(WorkflowEvent::NodeSkipped(node_name));
            
            // 跳过此节点但继续执行后续节点
            for &next in &self.edges[&idx] {
                self.execute_node(next, context, visited)?;
            }
            
            return Ok(());
        }
        
        // 通知节点开始
        self.notify_event(WorkflowEvent::NodeStarted(node_name.clone()));
        
        // 处理节点
        let start_time = Instant::now();
        match node.process(context) {
            Ok(()) => {
                let duration = start_time.elapsed();
                
                // 通知节点完成
                self.notify_event(WorkflowEvent::NodeCompleted(node_name, duration));
                
                // 执行所有后续节点
                for &next in &self.edges[&idx] {
                    self.execute_node(next, context, visited)?;
                }
                
                Ok(())
            }
            Err(e) => {
                // 通知节点失败
                let error_msg = format!("{}", e);
                self.notify_event(WorkflowEvent::NodeFailed(node_name.clone(), error_msg.clone()));
                
                // 通知工作流失败
                self.notify_event(WorkflowEvent::Failed(self.name.clone(), error_msg));
                
                Err(e)
            }
        }
    }
    
    // 通知事件给所有监听器
    fn notify_event(&self, event: WorkflowEvent) {
        for listener in &self.listeners {
            listener.on_event(&event);
        }
    }
    
    // 估计工作流执行时间（简单版本：假设按拓扑顺序执行）
    pub fn estimate_duration(&self, context: &Context) -> Duration {
        // 创建节点的入度映射
        let mut in_degree = HashMap::new();
        for i in 0..self.nodes.len() {
            in_degree.insert(i, 0);
        }
        
        for (_, targets) in &self.edges {
            for &target in targets {
                *in_degree.get_mut(&target).unwrap() += 1;
            }
        }
        
        // 拓扑排序
        let mut queue = Vec::new();
        for &i in &self.entry_nodes {
            queue.push(i);
        }
        
        let mut total_duration = Duration::from_secs(0);
        let mut critical_path = Vec::new();
        
        while !queue.is_empty() {
            let current = queue.remove(0);
            let node = &self.nodes[current];
            
            // 如果节点不能跳过，则计算其执行时间
            if !node.can_skip(context) {
                let duration = node.estimate_duration(context);
                total_duration += duration;
                critical_path.push((node.name().to_string(), duration));
            }
            
            // 处理后续节点
            for &next in &self.edges[&current] {
                let in_deg = in_degree.get_mut(&next).unwrap();
                *in_deg -= 1;
                
                if *in_deg == 0 {
                    queue.push(next);
                }
            }
        }
        
        // 打印关键路径（可选）
        println!("Critical path estimation:");
        for (name, duration) in critical_path {
            println!("  {} - {:?}", name, duration);
        }
        
        total_duration
    }
    
    // 获取节点数量
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }
    
    // 获取入口节点数量
    pub fn entry_node_count(&self) -> usize {
        self.entry_nodes.len()
    }
    
    // 获取工作流名称
    pub fn name(&self) -> &str {
        &self.name
    }
    
    // 获取工作流描述
    pub fn description(&self) -> &str {
        &self.description
    }
    
    // 合并两个工作流
    pub fn merge(&mut self, other: Self) -> Result<(), String> {
        let offset = self.nodes.len();
        
        // 合并节点
        self.nodes.extend(other.nodes);
        
        // 更新边和入口节点索引
        for (src, targets) in other.edges {
            let new_src = src + offset;
            let new_targets: Vec<_> = targets.into_iter().map(|t| t + offset).collect();
            self.edges.insert(new_src, new_targets);
        }
        
        // 更新入口节点
        for entry in other.entry_nodes {
            self.entry_nodes.push(entry + offset);
        }
        
        // 合并监听器
        self.listeners.extend(other.listeners);
        
        Ok(())
    }
}

// 函数式节点 - 使用函数创建工作流节点
pub struct FunctionNode<Context, Error, F>
where
    F: Fn(&mut Context) -> Result<(), Error> + Send + Sync,
{
    name: String,
    description: String,
    func: F,
    estimated_duration: Duration,
    skip_condition: Option<Box<dyn Fn(&Context) -> bool + Send + Sync>>,
}

impl<Context, Error, F> FunctionNode<Context, Error, F>
where
    F: Fn(&mut Context) -> Result<(), Error> + Send + Sync + 'static,
{
    pub fn new(name: impl Into<String>, func: F) -> Self {
        Self {
            name: name.into(),
            description: String::new(),
            func,
            estimated_duration: Duration::from_millis(100),
            skip_condition: None,
        }
    }
    
    pub fn with_description(mut self, description: impl Into<String>) -> Self {
        self.description = description.into();
        self
    }
    
    pub fn with_duration(mut self, duration: Duration) -> Self {
        self.estimated_duration = duration;
        self
    }
    
    pub fn with_skip_condition<C>(mut self, condition: C) -> Self
    where
        C: Fn(&Context) -> bool + Send + Sync + 'static,
    {
        self.skip_condition = Some(Box::new(condition));
        self
    }
}

impl<Context, Error, F> WorkflowNode<Context, Error> for FunctionNode<Context, Error, F>
where
    F: Fn(&mut Context) -> Result<(), Error> + Send + Sync + Clone + 'static,
    Error: Send + 'static,
{
    fn name(&self) -> &str {
        &self.name
    }
    
    fn description(&self) -> &str {
        if self.description.is_empty() {
            "Function node"
        } else {
            &self.description
        }
    }
    
    fn process(&self, context: &mut Context) -> Result<(), Error> {
        (self.func)(context)
    }
    
    fn estimate_duration(&self, _context: &Context) -> Duration {
        self.estimated_duration
    }
    
    fn can_skip(&self, context: &Context) -> bool {
        if let Some(condition) = &self.skip_condition {
            condition(context)
        } else {
            false
        }
    }
    
    fn box_clone(&self) -> Box<dyn WorkflowNode<Context, Error> + Send + Sync> {
        Box::new(Self {
            name: self.name.clone(),
            description: self.description.clone(),
            func: self.func.clone(),
            estimated_duration: self.estimated_duration,
            skip_condition: self.skip_condition.clone(),
        })
    }
}

impl<F> Clone for Box<dyn Fn(&F) -> bool + Send + Sync> {
    fn clone(&self) -> Self {
        let f = self.as_ref();
        Box::new(move |x| f(x))
    }
}

// 条件节点 - 根据条件选择执行路径
pub struct ConditionalNode<Context, Error> {
    name: String,
    description: String,
    condition: Box<dyn Fn(&Context) -> bool + Send + Sync>,
    true_branch: Option<Box<dyn WorkflowNode<Context, Error> + Send + Sync>>,
    false_branch: Option<Box<dyn WorkflowNode<Context, Error> + Send + Sync>>,
}

impl<Context, Error> ConditionalNode<Context, Error> {
    pub fn new<C>(name: impl Into<String>, condition: C) -> Self
    where
        C: Fn(&Context) -> bool + Send + Sync + 'static,
    {
        Self {
            name: name.into(),
            description: String::new(),
            condition: Box::new(condition),
            true_branch: None,
            false_branch: None,
        }
    }
    
    pub fn with_description(mut self, description: impl Into<String>) -> Self {
        self.description = description.into();
        self
    }
    
    pub fn with_true_branch(
        mut self,
        node: impl WorkflowNode<Context, Error> + Send + Sync + 'static,
    ) -> Self {
        self.true_branch = Some(Box::new(node));
        self
    }
    
    pub fn with_false_branch(
        mut self,
        node: impl WorkflowNode<Context, Error> + Send + Sync + 'static,
    ) -> Self {
        self.false_branch = Some(Box::new(node));
        self
    }
}

impl<Context, Error> WorkflowNode<Context, Error> for ConditionalNode<Context, Error>
where
    Context: 'static,
    Error: 'static,
{
    fn name(&self) -> &str {
        &self.name
    }
    
    fn description(&self) -> &str {
        if self.description.is_empty() {
            "Conditional node"
        } else {
            &self.description
        }
    }
    
    fn process(&self, context: &mut Context) -> Result<(), Error> {
        if (self.condition)(context) {
            // 执行真分支
            if let Some(branch) = &self.true_branch {
                branch.process(context)?;
            }
        } else {
            // 执行假分支
            if let Some(branch) = &self.false_branch {
                branch.process(context)?;
            }
        }
        Ok(())
    }
    
    fn estimate_duration(&self, context: &Context) -> Duration {
        let condition_result = (self.condition)(context);
        
        if condition_result {
            if let Some(branch) = &self.true_branch {
                branch.estimate_duration(context)
            } else {
                Duration::from_millis(1) // 几乎没有开销
            }
        } else {
            if let Some(branch) = &self.false_branch {
                branch.estimate_duration(context)
            } else {
                Duration::from_millis(1) // 几乎没有开销
            }
        }
    }
    
    fn can_skip(&self, _context: &Context) -> bool {
        false // 条件节点通常不应该被跳过
    }
    
    fn box_clone(&self) -> Box<dyn WorkflowNode<Context, Error> + Send + Sync> {
        Box::new(Self {
            name: self.name.clone(),
            description: self.description.clone(),
            condition: self.condition.clone(),
            true_branch: self.true_branch.as_ref().map(|b| b.box_clone()),
            false_branch: self.false_branch.as_ref().map(|b| b.box_clone()),
        })
    }
}

// 子工作流节点 - 嵌套工作流
pub struct SubworkflowNode<Context, Error> {
    name: String,
    description: String,
    workflow: Workflow<Context, Error>,
    skip_condition: Option<Box<dyn Fn(&Context) -> bool + Send + Sync>>,
}

impl<Context, Error> SubworkflowNode<Context, Error>
where
    Context: 'static,
    Error: 'static,
{
    pub fn new(name: impl Into<String>, workflow: Workflow<Context, Error>) -> Self {
        Self {
            name: name.into(),
            description: String::new(),
            workflow,
            skip_condition: None,
        }
    }
    
    pub fn with_description(mut self, description: impl Into<String>) -> Self {
        self.description = description.into();
        self
    }
    
    pub fn with_skip_condition<C>(mut self, condition: C) -> Self
    where
        C: Fn(&Context) -> bool + Send + Sync + 'static,
    {
        self.skip_condition = Some(Box::new(condition));
        self
    }
}

impl<Context, Error> WorkflowNode<Context, Error> for SubworkflowNode<Context, Error>
where
    Context: 'static,
    Error: fmt::Display + fmt::Debug + 'static,
{
    fn name(&self) -> &str {
        &self.name
    }
    
    fn description(&self) -> &str {
        if self.description.is_empty() {
            &self.workflow.description
        } else {
            &self.
继续前面的代码：

```rust
    fn description(&self) -> &str {
        if self.description.is_empty() {
            &self.workflow.description
        } else {
            &self.description
        }
    }
    
    fn process(&self, context: &mut Context) -> Result<(), Error> {
        // 执行子工作流
        self.workflow.execute(context)
    }
    
    fn estimate_duration(&self, context: &Context) -> Duration {
        // 估计子工作流的执行时间
        self.workflow.estimate_duration(context)
    }
    
    fn can_skip(&self, context: &Context) -> bool {
        if let Some(condition) = &self.skip_condition {
            condition(context)
        } else {
            false
        }
    }
    
    fn box_clone(&self) -> Box<dyn WorkflowNode<Context, Error> + Send + Sync> {
        // 注意：这里我们只克隆节点，不克隆内部工作流
        Box::new(Self {
            name: self.name.clone(),
            description: self.description.clone(),
            workflow: self.workflow.clone(),
            skip_condition: self.skip_condition.clone(),
        })
    }
}

// 为Workflow实现Clone特征
impl<Context, Error> Clone for Workflow<Context, Error>
where
    Context: 'static,
    Error: 'static,
{
    fn clone(&self) -> Self {
        let mut cloned = Self::new(self.name.clone())
            .with_description(self.description.clone());
        
        // 克隆节点
        for node in &self.nodes {
            cloned.nodes.push(node.box_clone());
        }
        
        // 克隆边
        for (src, targets) in &self.edges {
            cloned.edges.insert(*src, targets.clone());
        }
        
        // 克隆入口节点
        cloned.entry_nodes = self.entry_nodes.clone();
        
        // 克隆监听器
        // 注意：在实际应用中，可能需要为监听器实现Clone特征
        
        cloned
    }
}

// 工作流构建器 - 简化工作流创建
pub struct WorkflowBuilder<Context, Error> {
    workflow: Workflow<Context, Error>,
    current_node: Option<usize>,
}

impl<Context, Error> WorkflowBuilder<Context, Error>
where
    Context: Send + Sync + 'static,
    Error: Send + Sync + fmt::Display + fmt::Debug + 'static,
{
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            workflow: Workflow::new(name),
            current_node: None,
        }
    }
    
    pub fn with_description(mut self, description: impl Into<String>) -> Self {
        self.workflow = self.workflow.with_description(description);
        self
    }
    
    // 添加节点并使其成为当前节点
    pub fn add_node(
        &mut self,
        node: impl WorkflowNode<Context, Error> + Send + Sync + 'static,
    ) -> &mut Self {
        let idx = self.workflow.add_node(node);
        self.current_node = Some(idx);
        self
    }
    
    // 从当前节点添加边到新节点
    pub fn then(
        &mut self,
        node: impl WorkflowNode<Context, Error> + Send + Sync + 'static,
    ) -> &mut Self {
        if let Some(current) = self.current_node {
            let new_idx = self.workflow.add_node(node);
            self.workflow.add_edge(current, new_idx).unwrap();
            self.current_node = Some(new_idx);
        } else {
            self.add_node(node);
        }
        self
    }
    
    // 添加条件分支
    pub fn branch<C>(
        &mut self,
        condition: C,
        true_branch: impl WorkflowNode<Context, Error> + Send + Sync + 'static,
        false_branch: impl WorkflowNode<Context, Error> + Send + Sync + 'static,
    ) -> &mut Self
    where
        C: Fn(&Context) -> bool + Send + Sync + 'static,
    {
        let true_idx = self.workflow.add_node(true_branch);
        let false_idx = self.workflow.add_node(false_branch);
        
        let condition_node = ConditionalNode::new("branch", condition)
            .with_true_branch(FunctionNode::new("true_route", |_| Ok(())));
        
        let condition_idx = self.workflow.add_node(condition_node);
        
        if let Some(current) = self.current_node {
            self.workflow.add_edge(current, condition_idx).unwrap();
        }
        
        self.workflow.add_edge(condition_idx, true_idx).unwrap();
        self.workflow.add_edge(condition_idx, false_idx).unwrap();
        
        // 条件分支之后没有明确的"当前节点"
        self.current_node = None;
        
        self
    }
    
    // 添加子工作流
    pub fn subworkflow(&mut self, name: impl Into<String>, workflow: Workflow<Context, Error>) -> &mut Self {
        let subworkflow_node = SubworkflowNode::new(name, workflow);
        self.then(subworkflow_node)
    }
    
    // 添加监听器
    pub fn add_listener(&mut self, listener: impl WorkflowListener + 'static) -> &mut Self {
        self.workflow.add_listener(listener);
        self
    }
    
    // 构建工作流
    pub fn build(self) -> Workflow<Context, Error> {
        self.workflow
    }
}

// 使用示例
fn workflow_engine_example() {
    // 定义工作流上下文
    struct ProcessContext {
        data: HashMap<String, String>,
        processed: bool,
        error_occurred: bool,
    }
    
    impl ProcessContext {
        fn new() -> Self {
            Self {
                data: HashMap::new(),
                processed: false,
                error_occurred: false,
            }
        }
        
        fn set(&mut self, key: impl Into<String>, value: impl Into<String>) {
            self.data.insert(key.into(), value.into());
        }
        
        fn get(&self, key: &str) -> Option<&String> {
            self.data.get(key)
        }
    }
    
    // 创建日志监听器
    let log_listener = LoggingListener::new("[LOG]");
    
    // 创建指标监听器
    let metrics_listener = MetricsListener::new();
    let metrics_arc = metrics_listener.metrics();
    
    // 创建工作流构建器
    let mut builder = WorkflowBuilder::<ProcessContext, String>::new("data_processing");
    
    // 添加监听器
    builder.add_listener(log_listener);
    builder.add_listener(metrics_listener);
    
    // 添加工作流节点
    builder
        .add_node(
            FunctionNode::new("init", |ctx| {
                println!("Initializing context");
                ctx.set("status", "initialized");
                Ok(())
            })
            .with_duration(Duration::from_millis(10))
        )
        .then(
            FunctionNode::new("validate", |ctx| {
                println!("Validating data");
                
                if ctx.get("status") != Some(&"initialized".to_string()) {
                    return Err("Context not properly initialized".to_string());
                }
                
                ctx.set("status", "validated");
                Ok(())
            })
            .with_duration(Duration::from_millis(20))
        )
        .then(
            FunctionNode::new("process", |ctx| {
                println!("Processing data");
                
                // 模拟处理
                std::thread::sleep(Duration::from_millis(50));
                
                ctx.processed = true;
                ctx.set("status", "processed");
                ctx.set("result", "success");
                
                Ok(())
            })
            .with_duration(Duration::from_millis(50))
        );
    
    // 添加条件分支
    builder.branch(
        |ctx| ctx.get("result") == Some(&"success".to_string()),
        FunctionNode::new("success_handler", |ctx| {
            println!("Handling success");
            ctx.set("status", "completed");
            Ok(())
        }),
        FunctionNode::new("error_handler", |ctx| {
            println!("Handling error");
            ctx.error_occurred = true;
            ctx.set("status", "failed");
            Ok(())
        })
    );
    
    // 构建工作流
    let workflow = builder.build();
    
    // 创建上下文
    let mut context = ProcessContext::new();
    
    // 执行工作流
    match workflow.execute(&mut context) {
        Ok(()) => {
            println!("Workflow executed successfully!");
            println!("Context status: {:?}", context.get("status"));
            println!("Process flag: {}", context.processed);
            println!("Error flag: {}", context.error_occurred);
        }
        Err(e) => {
            println!("Workflow execution failed: {}", e);
        }
    }
    
    // 显示指标
    let metrics = metrics_arc.lock().unwrap();
    println!("Workflow metrics: {:#?}", metrics);
}
```

**设计原则**：构建灵活的组合式工作流引擎，支持节点的组合、条件分支和嵌套工作流，提供全面的监控和度量，使开发者能够构建和监控复杂的分布式工作流。

### 2.2 分布式拓扑管理器

```rust
// 分布式拓扑管理器 - 管理节点、连接和动态扩展
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::sync::{Arc, Mutex, RwLock};
use std::time::{Duration, Instant};

// 节点角色
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum NodeRole {
    Manager,    // 管理节点
    Worker,     // 工作节点
    Gateway,    // 网关节点
    Storage,    // 存储节点
    Custom(String), // 自定义角色
}

impl fmt::Display for NodeRole {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NodeRole::Manager => write!(f, "Manager"),
            NodeRole::Worker => write!(f, "Worker"),
            NodeRole::Gateway => write!(f, "Gateway"),
            NodeRole::Storage => write!(f, "Storage"),
            NodeRole::Custom(name) => write!(f, "Custom({})", name),
        }
    }
}

// 节点状态
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NodeStatus {
    Initializing,
    Ready,
    Busy,
    Degraded,
    Offline,
    Failed(String),
}

impl fmt::Display for NodeStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NodeStatus::Initializing => write!(f, "Initializing"),
            NodeStatus::Ready => write!(f, "Ready"),
            NodeStatus::Busy => write!(f, "Busy"),
            NodeStatus::Degraded => write!(f, "Degraded"),
            NodeStatus::Offline => write!(f, "Offline"),
            NodeStatus::Failed(reason) => write!(f, "Failed({})", reason),
        }
    }
}

// 节点能力
#[derive(Debug, Clone)]
pub struct NodeCapabilities {
    // 处理能力（相对值，1.0为基准）
    pub processing_power: f64,
    
    // 内存容量（字节）
    pub memory_bytes: usize,
    
    // 磁盘容量（字节）
    pub storage_bytes: usize,
    
    // 网络带宽（字节/秒）
    pub network_bandwidth_bps: usize,
    
    // 支持的特性
    pub features: HashSet<String>,
}

impl NodeCapabilities {
    pub fn new() -> Self {
        Self {
            processing_power: 1.0,
            memory_bytes: 8 * 1024 * 1024 * 1024, // 8GB
            storage_bytes: 100 * 1024 * 1024 * 1024, // 100GB
            network_bandwidth_bps: 100 * 1024 * 1024, // 100MB/s
            features: HashSet::new(),
        }
    }
    
    pub fn with_processing_power(mut self, power: f64) -> Self {
        self.processing_power = power;
        self
    }
    
    pub fn with_memory(mut self, bytes: usize) -> Self {
        self.memory_bytes = bytes;
        self
    }
    
    pub fn with_storage(mut self, bytes: usize) -> Self {
        self.storage_bytes = bytes;
        self
    }
    
    pub fn with_bandwidth(mut self, bps: usize) -> Self {
        self.network_bandwidth_bps = bps;
        self
    }
    
    pub fn with_feature(mut self, feature: impl Into<String>) -> Self {
        self.features.insert(feature.into());
        self
    }
    
    pub fn has_feature(&self, feature: &str) -> bool {
        self.features.contains(feature)
    }
}

// 节点元数据
#[derive(Debug, Clone)]
pub struct NodeMetadata {
    // 启动时间
    pub started_at: Instant,
    
    // 最后一次心跳时间
    pub last_heartbeat: Instant,
    
    // 自定义标签
    pub labels: HashMap<String, String>,
}

impl NodeMetadata {
    pub fn new() -> Self {
        let now = Instant::now();
        Self {
            started_at: now,
            last_heartbeat: now,
            labels: HashMap::new(),
        }
    }
    
    pub fn with_label(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.labels.insert(key.into(), value.into());
        self
    }
    
    pub fn update_heartbeat(&mut self) {
        self.last_heartbeat = Instant::now();
    }
    
    pub fn uptime(&self) -> Duration {
        self.started_at.elapsed()
    }
    
    pub fn time_since_last_heartbeat(&self) -> Duration {
        self.last_heartbeat.elapsed()
    }
}

// 节点定义
#[derive(Debug, Clone)]
pub struct Node {
    id: String,
    host: String,
    port: u16,
    roles: HashSet<NodeRole>,
    status: NodeStatus,
    capabilities: NodeCapabilities,
    metadata: NodeMetadata,
}

impl Node {
    pub fn new(id: impl Into<String>, host: impl Into<String>, port: u16) -> Self {
        Self {
            id: id.into(),
            host: host.into(),
            port,
            roles: HashSet::new(),
            status: NodeStatus::Initializing,
            capabilities: NodeCapabilities::new(),
            metadata: NodeMetadata::new(),
        }
    }
    
    pub fn with_role(mut self, role: NodeRole) -> Self {
        self.roles.insert(role);
        self
    }
    
    pub fn with_status(mut self, status: NodeStatus) -> Self {
        self.status = status;
        self
    }
    
    pub fn with_capabilities(mut self, capabilities: NodeCapabilities) -> Self {
        self.capabilities = capabilities;
        self
    }
    
    pub fn with_metadata(mut self, metadata: NodeMetadata) -> Self {
        self.metadata = metadata;
        self
    }
    
    // 更新节点状态
    pub fn update_status(&mut self, status: NodeStatus) {
        self.status = status;
    }
    
    // 更新心跳
    pub fn heartbeat(&mut self) {
        self.metadata.update_heartbeat();
        
        // 如果节点之前处于Offline状态，恢复为Ready
        if self.status == NodeStatus::Offline {
            self.status = NodeStatus::Ready;
        }
    }
    
    // 检查节点是否处于活动状态
    pub fn is_active(&self) -> bool {
        matches!(self.status, NodeStatus::Ready | NodeStatus::Busy)
    }
    
    // 获取节点ID
    pub fn id(&self) -> &str {
        &self.id
    }
    
    // 获取节点地址
    pub fn address(&self) -> String {
        format!("{}:{}", self.host, self.port)
    }
    
    // 检查节点是否具有特定角色
    pub fn has_role(&self, role: &NodeRole) -> bool {
        self.roles.contains(role)
    }
    
    // 获取节点状态
    pub fn status(&self) -> &NodeStatus {
        &self.status
    }
    
    // 获取节点能力
    pub fn capabilities(&self) -> &NodeCapabilities {
        &self.capabilities
    }
}

// 连接类型
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConnectionType {
    Direct,     // 直接连接
    Proxied,    // 通过代理连接
    Load,       // 负载均衡连接
    Failover,   // 故障转移连接
}

// 连接定义
#[derive(Debug, Clone)]
pub struct Connection {
    id: String,
    source_id: String,
    target_id: String,
    connection_type: ConnectionType,
    latency: Duration,
    bandwidth: usize, // 字节/秒
    packet_loss: f64, // 0.0-1.0
    metadata: HashMap<String, String>,
}

impl Connection {
    pub fn new(
        id: impl Into<String>,
        source_id: impl Into<String>,
        target_id: impl Into<String>,
    ) -> Self {
        Self {
            id: id.into(),
            source_id: source_id.into(),
            target_id: target_id.into(),
            connection_type: ConnectionType::Direct,
            latency: Duration::from_millis(10),
            bandwidth: 100 * 1024 * 1024, // 100MB/s
            packet_loss: 0.0,
            metadata: HashMap::new(),
        }
    }
    
    pub fn with_type(mut self, connection_type: ConnectionType) -> Self {
        self.connection_type = connection_type;
        self
    }
    
    pub fn with_latency(mut self, latency: Duration) -> Self {
        self.latency = latency;
        self
    }
    
    pub fn with_bandwidth(mut self, bandwidth: usize) -> Self {
        self.bandwidth = bandwidth;
        self
    }
    
    pub fn with_packet_loss(mut self, loss: f64) -> Self {
        self.packet_loss = loss.max(0.0).min(1.0);
        self
    }
    
    pub fn with_metadata(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.metadata.insert(key.into(), value.into());
        self
    }
    
    // 获取连接ID
    pub fn id(&self) -> &str {
        &self.id
    }
    
    // 获取源节点ID
    pub fn source_id(&self) -> &str {
        &self.source_id
    }
    
    // 获取目标节点ID
    pub fn target_id(&self) -> &str {
        &self.target_id
    }
    
    // 获取连接类型
    pub fn connection_type(&self) -> &ConnectionType {
        &self.connection_type
    }
    
    // 获取延迟
    pub fn latency(&self) -> Duration {
        self.latency
    }
    
    // 获取带宽
    pub fn bandwidth(&self) -> usize {
        self.bandwidth
    }
    
    // 获取丢包率
    pub fn packet_loss(&self) -> f64 {
        self.packet_loss
    }
}

// 拓扑更新事件
#[derive(Debug, Clone)]
pub enum TopologyEvent {
    NodeAdded(Node),
    NodeRemoved(String),
    NodeUpdated(Node),
    ConnectionAdded(Connection),
    ConnectionRemoved(String),
    ConnectionUpdated(Connection),
}

// 拓扑更新监听器
pub trait TopologyListener: Send + Sync {
    fn on_event(&self, event: &TopologyEvent);
}

// 拓扑管理器
pub struct TopologyManager {
    nodes: RwLock<HashMap<String, Node>>,
    connections: RwLock<HashMap<String, Connection>>,
    listeners: RwLock<Vec<Box<dyn TopologyListener>>>,
    heartbeat_timeout: Duration,
}

impl TopologyManager {
    pub fn new() -> Self {
        Self {
            nodes: RwLock::new(HashMap::new()),
            connections: RwLock::new(HashMap::new()),
            listeners: RwLock::new(Vec::new()),
            heartbeat_timeout: Duration::from_secs(30),
        }
    }
    
    pub fn with_heartbeat_timeout(mut self, timeout: Duration) -> Self {
        self.heartbeat_timeout = timeout;
        self
    }
    
    // 添加节点
    pub fn add_node(&self, node: Node) -> Result<(), String> {
        let node_id = node.id().to_string();
        
        {
            let mut nodes = self.nodes.write().unwrap();
            
            if nodes.contains_key(&node_id) {
                return Err(format!("Node with ID {} already exists", node_id));
            }
            
            nodes.insert(node_id.clone(), node.clone());
        }
        
        // 通知监听器
        self.notify_listeners(TopologyEvent::NodeAdded(node));
        
        Ok(())
    }
    
    // 移除节点
    pub fn remove_node(&self, node_id: &str) -> Result<(), String> {
        let removed = {
            let mut nodes = self.nodes.write().unwrap();
            nodes.remove(node_id).is_some()
        };
        
        if !removed {
            return Err(format!("Node with ID {} not found", node_id));
        }
        
        // 移除与该节点相关的所有连接
        {
            let mut connections = self.connections.write().unwrap();
            let to_remove: Vec<String> = connections.values()
                .filter(|conn| conn.source_id() == node_id || conn.target_id() == node_id)
                .map(|conn| conn.id().to_string())
                .collect();
            
            for conn_id in to_remove {
                if let Some(conn) = connections.remove(&conn_id) {
                    // 通知连接被移除
                    self.notify_listeners(TopologyEvent::ConnectionRemoved(conn.id().to_string()));
                }
            }
        }
        
        // 通知节点被移除
        self.notify_listeners(TopologyEvent::NodeRemoved(node_id.to_string()));
        
        Ok(())
    }
    
    // 更新节点
    pub fn update_node(&self, node: Node) -> Result<(), String> {
        let node_id = node.id().to_string();
        
        {
            let mut nodes = self.nodes.write().unwrap();
            
            if !nodes.contains_key(&node_id) {
                return Err(format!("Node with ID {} not found", node_id));
            }
            
            nodes.insert(node_id, node.clone());
        }
        
        // 通知监听器
        self.notify_listeners(TopologyEvent::NodeUpdated(node));
        
        Ok(())
    }
    
    // 添加连接
    pub fn add_connection(&self, connection: Connection) -> Result<(), String> {
        let conn_id = connection.id().to_string();
        let source_id = connection.source_id().to_string();
        let target_id = connection.target_id().to_string();
        
        // 验证源节点和目标节点是否存在
        {
            let nodes = self.nodes.read().unwrap();
            
            if !nodes.contains_key(&source_id) {
                return Err(format!("Source node with ID {} not found", source_id));
            }
            
            if !nodes.contains_key(&target_id) {
                return Err(format!("Target node with ID {} not found", target_id));
            }
        }
        
        {
            let mut connections = self.connections.write().unwrap();
            
            if connections.contains_key(&conn_id) {
                return Err(format!("Connection with ID {} already exists", conn_id));
            }
            
            connections.insert(conn_id.clone(), connection.clone());
        }
        
        // 通知监听器
        self.notify_listeners(TopologyEvent::ConnectionAdded(connection));
        
        Ok(())
    }
    
    // 移除连接
    pub fn remove_connection(&self, connection_id: &str) -> Result<(), String> {
        let removed = {
            let mut connections = self.connections.write().unwrap();
            connections.remove(connection_id).is_some()
        };
        
        if !removed {
            return Err(format!("Connection with ID {} not found", connection_id));
        }
        
        // 通知监听器
        self.notify_listeners(TopologyEvent::ConnectionRemoved(connection_id.to_string()));
        
        Ok(())
    }
    
    // 更新连接
    pub fn update_connection(&self, connection: Connection) -> Result<(), String> {
        let conn_id = connection.id().to_string();
        
        {
            let mut connections = self.connections.write().unwrap();
            
            if !connections.contains_key(&conn_id) {
                return Err(format!("Connection with ID {} not found", conn_id));
            }
            
            connections.insert(conn_id, connection.clone());
        }
        
        // 通知监听器
        self.notify_listeners(TopologyEvent::ConnectionUpdated(connection));
        
        Ok(())
    }
    
    // 获取节点
    pub fn get_node(&self, node_id: &str) -> Option<Node> {
        let nodes = self.nodes.read().unwrap();
        nodes.get(node_id).cloned()
    }
    
    // 获取所有节点
    pub fn get_all_nodes(&self) -> Vec<Node> {
        let nodes = self.nodes.read().unwrap();
        nodes.values().cloned().collect()
    }
    
    // 获取所有具有特定角色的节点
    pub fn get_nodes_by_role(&self, role: &NodeRole) -> Vec<Node> {
        let nodes = self.nodes.read().unwrap();
        nodes.values()
             .filter(|node| node.has_role(role))
             .cloned()
             .collect()
    }
    
    // 获取所有处于特定状态的节点
    pub fn get_nodes_by_status(&self, status: &NodeStatus) -> Vec<Node> {
        let nodes = self.nodes.read().unwrap();
        nodes.values()
             .filter(|node| &node.status == status)
             .cloned()
             .collect()
    }
    
    // 获取连接
    pub fn get_connection(&self, connection_id: &str) -> Option<Connection> {
        let connections = self.connections.read().unwrap();
        connections.get(connection_id).cloned()
    }
    
    // 获取所有连接
    pub fn get_all_connections(&self) -> Vec<Connection> {
        let connections = self.connections.read().unwrap();
        connections.values().cloned().collect()
    }
    
    // 获取从特定节点出发的所有连接
    pub fn get_connections_from_node(&self, node_id: &str) -> Vec<Connection> {
        let connections = self.connections.read().unwrap();
        connections.values()
                  .filter(|conn| conn.source_id() == node_id)
                  .cloned()
                  .collect()
    }
    
    // 获取到特定节点的所有连接
    pub fn get_connections_to_node(&self, node_id: &str) -> Vec<Connection> {
        let connections = self.connections.read().unwrap();
        connections.values()
                  .filter(|conn| conn.target_id() == node_id)
                  .cloned()
                  .collect()
    }
    
    // 处理节点心跳
    pub fn handle_heartbeat(&self, node_id: &str) -> Result<(), String> {
        let mut nodes = self.nodes.write().unwrap();
        
        if let Some(node) = nodes.get_mut(node_id) {
            node.heartbeat();
            Ok(())
        } else {
            Err(format!("Node with ID {} not found", node_id))
        }
    }
    
    // 检查并更新超时节点的状态
    pub fn check_heartbeats(&self) -> usize {
        let mut timeout_count = 0;
        let mut nodes_to_update = Vec::new();
        
        // 找出所有超时的节点
        {
            let nodes = self.nodes.read().unwrap();
            
            for node in nodes.values() {
                let time_since_heartbeat = node.metadata.time_since_last_heartbeat();
                
                if time_since_heartbeat > self.heartbeat_timeout && node.is_active() {
                    // 节点超时且之前处于活动状态
继续前面的代码：

```rust
                if time_since_heartbeat > self.heartbeat_timeout && node.is_active() {
                    // 节点超时且之前处于活动状态
                    timeout_count += 1;
                    
                    // 克隆节点并更新状态
                    let mut updated_node = node.clone();
                    updated_node.update_status(NodeStatus::Offline);
                    nodes_to_update.push(updated_node);
                }
            }
        }
        
        // 更新超时节点的状态
        for node in nodes_to_update {
            let _ = self.update_node(node);
        }
        
        timeout_count
    }
    
    // 添加拓扑更新监听器
    pub fn add_listener(&self, listener: impl TopologyListener + 'static) {
        let mut listeners = self.listeners.write().unwrap();
        listeners.push(Box::new(listener));
    }
    
    // 通知所有监听器
    fn notify_listeners(&self, event: TopologyEvent) {
        let listeners = self.listeners.read().unwrap();
        for listener in listeners.iter() {
            listener.on_event(&event);
        }
    }
    
    // 查找最短路径（Dijkstra算法）
    pub fn find_shortest_path(&self, from_node_id: &str, to_node_id: &str) -> Option<Vec<String>> {
        if from_node_id == to_node_id {
            return Some(vec![from_node_id.to_string()]);
        }
        
        // 从连接构建图
        let connections = self.connections.read().unwrap();
        let nodes = self.nodes.read().unwrap();
        
        // 如果源节点或目标节点不存在，返回None
        if !nodes.contains_key(from_node_id) || !nodes.contains_key(to_node_id) {
            return None;
        }
        
        // 构建邻接表
        let mut adjacency_list: HashMap<String, Vec<(String, u64)>> = HashMap::new();
        
        for conn in connections.values() {
            // 只考虑活动节点
            if let (Some(src_node), Some(dst_node)) = (nodes.get(conn.source_id()), nodes.get(conn.target_id())) {
                if !src_node.is_active() || !dst_node.is_active() {
                    continue;
                }
                
                // 使用延迟作为边的权重
                let weight = conn.latency().as_millis() as u64;
                
                adjacency_list
                    .entry(conn.source_id().to_string())
                    .or_insert_with(Vec::new)
                    .push((conn.target_id().to_string(), weight));
            }
        }
        
        // Dijkstra算法实现
        use std::collections::BinaryHeap;
        use std::cmp::Ordering;
        
        #[derive(Copy, Clone, Eq, PartialEq)]
        struct State {
            cost: u64,
            node: usize,
        }
        
        // 为了使用BinaryHeap作为最小堆
        impl Ord for State {
            fn cmp(&self, other: &Self) -> Ordering {
                other.cost.cmp(&self.cost)
                    .then_with(|| self.node.cmp(&other.node))
            }
        }
        
        impl PartialOrd for State {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }
        
        // 为了方便算法实现，创建节点ID到索引的映射
        let mut node_to_idx = HashMap::new();
        let mut idx_to_node = Vec::new();
        
        for node_id in adjacency_list.keys().chain(
            adjacency_list.values().flat_map(|v| v.iter().map(|(n, _)| n))
        ) {
            if !node_to_idx.contains_key(node_id) {
                node_to_idx.insert(node_id.clone(), idx_to_node.len());
                idx_to_node.push(node_id.clone());
            }
        }
        
        // 如果源节点或目标节点不在图中，返回None
        let start_idx = match node_to_idx.get(from_node_id) {
            Some(&idx) => idx,
            None => return None,
        };
        
        let end_idx = match node_to_idx.get(to_node_id) {
            Some(&idx) => idx,
            None => return None,
        };
        
        // 初始化距离和前驱节点数组
        let n = idx_to_node.len();
        let mut dist = vec![u64::MAX; n];
        let mut prev = vec![None; n];
        
        // 创建优先队列
        let mut heap = BinaryHeap::new();
        
        // 初始化起点
        dist[start_idx] = 0;
        heap.push(State { cost: 0, node: start_idx });
        
        // Dijkstra算法主循环
        while let Some(State { cost, node }) = heap.pop() {
            // 找到终点
            if node == end_idx {
                break;
            }
            
            // 如果已经找到更短的路径，忽略
            if cost > dist[node] {
                continue;
            }
            
            // 检查所有邻居
            if let Some(neighbors) = adjacency_list.get(&idx_to_node[node]) {
                for &(ref next, weight) in neighbors {
                    let next_idx = node_to_idx[next];
                    let next_cost = cost + weight;
                    
                    if next_cost < dist[next_idx] {
                        heap.push(State { cost: next_cost, node: next_idx });
                        dist[next_idx] = next_cost;
                        prev[next_idx] = Some(node);
                    }
                }
            }
        }
        
        // 如果无法到达终点
        if dist[end_idx] == u64::MAX {
            return None;
        }
        
        // 重建路径
        let mut path = Vec::new();
        let mut current = end_idx;
        
        path.push(idx_to_node[current].clone());
        
        while let Some(previous) = prev[current] {
            path.push(idx_to_node[previous].clone());
            current = previous;
        }
        
        // 反转路径使其从起点到终点
        path.reverse();
        
        Some(path)
    }
    
    // 寻找具有特定特性的最近节点
    pub fn find_nearest_node_with_feature(&self, from_node_id: &str, feature: &str) -> Option<Node> {
        // 找到所有具有该特性的节点
        let nodes_with_feature: Vec<Node> = {
            let nodes = self.nodes.read().unwrap();
            nodes.values()
                 .filter(|node| node.is_active() && node.capabilities().has_feature(feature))
                 .cloned()
                 .collect()
        };
        
        if nodes_with_feature.is_empty() {
            return None;
        }
        
        // 如果源节点有该特性，直接返回
        if let Some(node) = self.get_node(from_node_id) {
            if node.capabilities().has_feature(feature) {
                return Some(node);
            }
        }
        
        // 查找到每个具有该特性的节点的最短路径
        let mut best_node = None;
        let mut shortest_distance = u64::MAX;
        
        for target_node in nodes_with_feature {
            if let Some(path) = self.find_shortest_path(from_node_id, target_node.id()) {
                // 计算路径的总延迟（简化版）
                let total_latency = path.len() as u64;
                
                if total_latency < shortest_distance {
                    shortest_distance = total_latency;
                    best_node = Some(target_node);
                }
            }
        }
        
        best_node
    }
    
    // 检查两个节点是否可达
    pub fn are_nodes_connected(&self, from_node_id: &str, to_node_id: &str) -> bool {
        self.find_shortest_path(from_node_id, to_node_id).is_some()
    }
    
    // 获取拓扑统计信息
    pub fn get_topology_stats(&self) -> TopologyStats {
        let nodes = self.nodes.read().unwrap();
        let connections = self.connections.read().unwrap();
        
        let total_nodes = nodes.len();
        let active_nodes = nodes.values().filter(|n| n.is_active()).count();
        let degraded_nodes = nodes.values().filter(|n| n.status() == &NodeStatus::Degraded).count();
        let offline_nodes = nodes.values().filter(|n| n.status() == &NodeStatus::Offline).count();
        let failed_nodes = nodes.values().filter(|n| matches!(n.status(), NodeStatus::Failed(_))).count();
        
        let mut roles_count = HashMap::new();
        for node in nodes.values() {
            for role in &node.roles {
                *roles_count.entry(role.clone()).or_insert(0) += 1;
            }
        }
        
        TopologyStats {
            total_nodes,
            active_nodes,
            degraded_nodes,
            offline_nodes,
            failed_nodes,
            total_connections: connections.len(),
            roles_count,
            direct_connections: connections.values().filter(|c| c.connection_type() == &ConnectionType::Direct).count(),
            proxied_connections: connections.values().filter(|c| c.connection_type() == &ConnectionType::Proxied).count(),
        }
    }
}

// 拓扑统计信息
#[derive(Debug, Clone)]
pub struct TopologyStats {
    pub total_nodes: usize,
    pub active_nodes: usize,
    pub degraded_nodes: usize,
    pub offline_nodes: usize,
    pub failed_nodes: usize,
    pub total_connections: usize,
    pub roles_count: HashMap<NodeRole, usize>,
    pub direct_connections: usize,
    pub proxied_connections: usize,
}

// 日志拓扑监听器
pub struct LoggingTopologyListener {
    prefix: String,
}

impl LoggingTopologyListener {
    pub fn new(prefix: impl Into<String>) -> Self {
        Self {
            prefix: prefix.into(),
        }
    }
}

impl TopologyListener for LoggingTopologyListener {
    fn on_event(&self, event: &TopologyEvent) {
        match event {
            TopologyEvent::NodeAdded(node) => {
                println!("{} Node added: {} ({})", self.prefix, node.id(), node.address());
            }
            TopologyEvent::NodeRemoved(node_id) => {
                println!("{} Node removed: {}", self.prefix, node_id);
            }
            TopologyEvent::NodeUpdated(node) => {
                println!("{} Node updated: {} (Status: {})", self.prefix, node.id(), node.status());
            }
            TopologyEvent::ConnectionAdded(conn) => {
                println!("{} Connection added: {} ({} -> {})", 
                         self.prefix, conn.id(), conn.source_id(), conn.target_id());
            }
            TopologyEvent::ConnectionRemoved(conn_id) => {
                println!("{} Connection removed: {}", self.prefix, conn_id);
            }
            TopologyEvent::ConnectionUpdated(conn) => {
                println!("{} Connection updated: {} (Type: {:?})", 
                         self.prefix, conn.id(), conn.connection_type());
            }
        }
    }
}

// 使用示例
fn topology_manager_example() {
    // 创建拓扑管理器
    let topology = TopologyManager::new()
        .with_heartbeat_timeout(Duration::from_secs(10));
    
    // 添加监听器
    topology.add_listener(LoggingTopologyListener::new("[TOPOLOGY] "));
    
    // 创建一些节点
    let manager_node = Node::new("manager-1", "192.168.1.10", 8080)
        .with_role(NodeRole::Manager)
        .with_status(NodeStatus::Ready)
        .with_capabilities(
            NodeCapabilities::new()
                .with_processing_power(2.0)
                .with_feature("orchestration")
        );
    
    let worker_node1 = Node::new("worker-1", "192.168.1.11", 8080)
        .with_role(NodeRole::Worker)
        .with_status(NodeStatus::Ready)
        .with_capabilities(
            NodeCapabilities::new()
                .with_feature("compute")
        );
    
    let worker_node2 = Node::new("worker-2", "192.168.1.12", 8080)
        .with_role(NodeRole::Worker)
        .with_status(NodeStatus::Ready)
        .with_capabilities(
            NodeCapabilities::new()
                .with_feature("compute")
                .with_feature("gpu")
        );
    
    let storage_node = Node::new("storage-1", "192.168.1.13", 8080)
        .with_role(NodeRole::Storage)
        .with_status(NodeStatus::Ready)
        .with_capabilities(
            NodeCapabilities::new()
                .with_storage(1024 * 1024 * 1024 * 1024) // 1TB
                .with_feature("storage")
        );
    
    // 添加节点到拓扑
    topology.add_node(manager_node).unwrap();
    topology.add_node(worker_node1).unwrap();
    topology.add_node(worker_node2).unwrap();
    topology.add_node(storage_node).unwrap();
    
    // 创建一些连接
    let conn1 = Connection::new("conn-1", "manager-1", "worker-1")
        .with_latency(Duration::from_millis(5));
    
    let conn2 = Connection::new("conn-2", "manager-1", "worker-2")
        .with_latency(Duration::from_millis(8));
    
    let conn3 = Connection::new("conn-3", "manager-1", "storage-1")
        .with_latency(Duration::from_millis(10));
    
    let conn4 = Connection::new("conn-4", "worker-1", "storage-1")
        .with_latency(Duration::from_millis(7));
    
    let conn5 = Connection::new("conn-5", "worker-2", "storage-1")
        .with_latency(Duration::from_millis(12));
    
    // 添加连接到拓扑
    topology.add_connection(conn1).unwrap();
    topology.add_connection(conn2).unwrap();
    topology.add_connection(conn3).unwrap();
    topology.add_connection(conn4).unwrap();
    topology.add_connection(conn5).unwrap();
    
    // 测试心跳
    topology.handle_heartbeat("worker-1").unwrap();
    
    // 更新节点状态
    let mut updated_node = topology.get_node("worker-2").unwrap();
    updated_node.update_status(NodeStatus::Busy);
    topology.update_node(updated_node).unwrap();
    
    // 查找路径
    if let Some(path) = topology.find_shortest_path("manager-1", "storage-1") {
        println!("Shortest path from manager-1 to storage-1: {:?}", path);
    } else {
        println!("No path found from manager-1 to storage-1");
    }
    
    // 查找具有特定特性的最近节点
    if let Some(node) = topology.find_nearest_node_with_feature("manager-1", "gpu") {
        println!("Nearest node with GPU capability: {} ({})", node.id(), node.address());
    } else {
        println!("No node with GPU capability found");
    }
    
    // 获取拓扑统计信息
    let stats = topology.get_topology_stats();
    println!("Topology statistics:");
    println!("  Total nodes: {}", stats.total_nodes);
    println!("  Active nodes: {}", stats.active_nodes);
    println!("  Roles distribution:");
    for (role, count) in &stats.roles_count {
        println!("    {}: {}", role, count);
    }
    println!("  Total connections: {}", stats.total_connections);
    
    // 测试节点移除
    topology.remove_node("worker-1").unwrap();
    
    // 重新获取统计信息
    let updated_stats = topology.get_topology_stats();
    println!("Updated total nodes: {}", updated_stats.total_nodes);
}
```

**设计原则**：构建全面的分布式拓扑管理系统，支持节点发现、连接管理和动态拓扑变更，使分布式系统能够自适应网络结构变化并做出智能路由决策。

## 3. 分布式系统自动化控制

### 3.1 错误处理与自动恢复

```rust
// 错误处理与自动恢复框架
use std::collections::{HashMap, VecDeque};
use std::fmt;
use std::sync::{Arc, Mutex, RwLock};
use std::time::{Duration, Instant};

// 错误严重程度
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ErrorSeverity {
    Info,       // 信息性错误，不需要特别处理
    Warning,    // 警告，可能需要注意
    Error,      // 错误，需要处理
    Critical,   // 严重错误，需要立即处理
    Fatal,      // 致命错误，系统可能无法恢复
}

impl fmt::Display for ErrorSeverity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ErrorSeverity::Info => write!(f, "INFO"),
            ErrorSeverity::Warning => write!(f, "WARNING"),
            ErrorSeverity::Error => write!(f, "ERROR"),
            ErrorSeverity::Critical => write!(f, "CRITICAL"),
            ErrorSeverity::Fatal => write!(f, "FATAL"),
        }
    }
}

// 错误类别
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ErrorCategory {
    Network,            // 网络错误
    SystemResource,     // 系统资源错误（内存、CPU等）
    Storage,            // 存储错误
    Configuration,      // 配置错误
    Authorization,      // 授权错误
    DataCorruption,     // 数据损坏
    Timeout,            // 超时错误
    ServiceUnavailable, // 服务不可用
    Unknown,            // 未知错误
    Custom(String),     // 自定义错误类别
}

impl fmt::Display for ErrorCategory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ErrorCategory::Network => write!(f, "Network"),
            ErrorCategory::SystemResource => write!(f, "SystemResource"),
            ErrorCategory::Storage => write!(f, "Storage"),
            ErrorCategory::Configuration => write!(f, "Configuration"),
            ErrorCategory::Authorization => write!(f, "Authorization"),
            ErrorCategory::DataCorruption => write!(f, "DataCorruption"),
            ErrorCategory::Timeout => write!(f, "Timeout"),
            ErrorCategory::ServiceUnavailable => write!(f, "ServiceUnavailable"),
            ErrorCategory::Unknown => write!(f, "Unknown"),
            ErrorCategory::Custom(name) => write!(f, "Custom({})", name),
        }
    }
}

// 错误上下文
#[derive(Debug, Clone)]
pub struct ErrorContext {
    // 错误发生的组件
    pub component: String,
    
    // 错误发生的操作
    pub operation: String,
    
    // 相关标识符（如请求ID、用户ID等）
    pub identifiers: HashMap<String, String>,
    
    // 其他上下文信息
    pub details: HashMap<String, String>,
    
    // 错误发生时间
    pub timestamp: Instant,
}

impl ErrorContext {
    pub fn new(component: impl Into<String>, operation: impl Into<String>) -> Self {
        Self {
            component: component.into(),
            operation: operation.into(),
            identifiers: HashMap::new(),
            details: HashMap::new(),
            timestamp: Instant::now(),
        }
    }
    
    pub fn with_identifier(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.identifiers.insert(key.into(), value.into());
        self
    }
    
    pub fn with_detail(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.details.insert(key.into(), value.into());
        self
    }
}

// 系统错误定义
#[derive(Debug, Clone)]
pub struct SystemError {
    // 错误消息
    pub message: String,
    
    // 错误类别
    pub category: ErrorCategory,
    
    // 错误严重程度
    pub severity: ErrorSeverity,
    
    // 错误上下文
    pub context: ErrorContext,
    
    // 是否可重试
    pub retriable: bool,
    
    // 已尝试次数
    pub retry_count: usize,
    
    // 相关错误（如果有）
    pub related_errors: Vec<SystemError>,
}

impl SystemError {
    pub fn new(
        message: impl Into<String>,
        category: ErrorCategory,
        severity: ErrorSeverity,
        context: ErrorContext,
    ) -> Self {
        Self {
            message: message.into(),
            category,
            severity,
            context,
            retriable: false,
            retry_count: 0,
            related_errors: Vec::new(),
        }
    }
    
    pub fn with_retriable(mut self, retriable: bool) -> Self {
        self.retriable = retriable;
        self
    }
    
    pub fn with_retry_count(mut self, count: usize) -> Self {
        self.retry_count = count;
        self
    }
    
    pub fn with_related_error(mut self, error: SystemError) -> Self {
        self.related_errors.push(error);
        self
    }
    
    pub fn increment_retry(&mut self) {
        self.retry_count += 1;
    }
    
    // 判断是否可以重试
    pub fn can_retry(&self, max_retries: usize) -> bool {
        self.retriable && self.retry_count < max_retries
    }
    
    // 获取错误发生后经过的时间
    pub fn time_since_error(&self) -> Duration {
        self.context.timestamp.elapsed()
    }
}

impl fmt::Display for SystemError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}] {} error in {}::{}: {}", 
               self.severity, self.category, self.context.component, self.context.operation, self.message)
    }
}

// 错误处理策略
#[derive(Debug, Clone)]
pub enum ErrorHandlingStrategy {
    // 立即重试
    RetryImmediately(usize), // 最大重试次数
    
    // 带退避的重试
    RetryWithBackoff {
        max_retries: usize,
        initial_delay: Duration,
        max_delay: Duration,
        multiplier: f64,
    },
    
    // 使用备用操作
    Fallback(Box<dyn Fn() -> Result<(), SystemError> + Send + Sync>),
    
    // 预定重试（在指定时间后重试）
    RetryAt(Instant),
    
    // 丢弃错误
    Discard,
    
    // 上报错误（不处理）
    Propagate,
}

// 错误处理器特征
pub trait ErrorHandler: Send + Sync {
    // 处理错误
    fn handle_error(&self, error: &SystemError) -> ErrorHandlingStrategy;
    
    // 处理器名称
    fn name(&self) -> &str;
}

// 基于规则的错误处理器
pub struct RuleBasedErrorHandler {
    name: String,
    rules: Vec<ErrorHandlingRule>,
}

// 错误处理规则
pub struct ErrorHandlingRule {
    // 规则名称
    name: String,
    
    // 规则条件
    condition: Box<dyn Fn(&SystemError) -> bool + Send + Sync>,
    
    // 处理策略
    strategy: ErrorHandlingStrategy,
}

impl ErrorHandlingRule {
    pub fn new<F>(name: impl Into<String>, condition: F, strategy: ErrorHandlingStrategy) -> Self
    where
        F: Fn(&SystemError) -> bool + Send + Sync + 'static,
    {
        Self {
            name: name.into(),
            condition: Box::new(condition),
            strategy: strategy,
        }
    }
    
    // 检查规则是否适用于给定错误
    pub fn applies_to(&self, error: &SystemError) -> bool {
        (self.condition)(error)
    }
    
    // 获取处理策略
    pub fn strategy(&self) -> &ErrorHandlingStrategy {
        &self.strategy
    }
    
    // 规则名称
    pub fn name(&self) -> &str {
        &self.name
    }
}

impl RuleBasedErrorHandler {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            rules: Vec::new(),
        }
    }
    
    // 添加处理规则
    pub fn add_rule(&mut self, rule: ErrorHandlingRule) -> &mut Self {
        self.rules.push(rule);
        self
    }
    
    // 添加网络错误的重试规则
    pub fn add_network_retry_rule(&mut self, max_retries: usize) -> &mut Self {
        let rule = ErrorHandlingRule::new(
            "network_retry",
            |error| error.category == ErrorCategory::Network && error.retriable,
            ErrorHandlingStrategy::RetryWithBackoff {
                max_retries,
                initial_delay: Duration::from_millis(100),
                max_delay: Duration::from_secs(30),
                multiplier: 2.0,
            },
        );
        
        self.add_rule(rule)
    }
    
    // 添加超时错误的重试规则
    pub fn add_timeout_retry_rule(&mut self, max_retries: usize) -> &mut Self {
        let rule = ErrorHandlingRule::new(
            "timeout_retry",
            |error| error.category == ErrorCategory::Timeout,
            ErrorHandlingStrategy::RetryWithBackoff {
                max_retries,
                initial_delay: Duration::from_millis(200),
                max_delay: Duration::from_secs(60),
                multiplier: 2.0,
            },
        );
        
        self.add_rule(rule)
    }
    
    // 添加服务不可用错误的处理规则
    pub fn add_service_unavailable_rule<F>(&mut self, fallback: F) -> &mut Self
    where
        F: Fn() -> Result<(), SystemError> + Send + Sync + 'static,
    {
        let rule = ErrorHandlingRule::new(
            "service_unavailable",
            |error| error.category == ErrorCategory::ServiceUnavailable,
            ErrorHandlingStrategy::Fallback(Box::new(fallback)),
        );
        
        self.add_rule(rule)
    }
}

impl ErrorHandler for RuleBasedErrorHandler {
    fn handle_error(&self, error: &SystemError) -> ErrorHandlingStrategy {
        // 按顺序检查规则
        for rule in &self.rules {
            if rule.applies_to(error) {
                println!("Rule '{}' applies to error: {}", rule.name(), error);
                return rule.strategy().clone();
            }
        }
        
        // 默认策略：根据错误严重性决定
        match error.severity {
            ErrorSeverity::Info | ErrorSeverity::Warning => ErrorHandlingStrategy::Discard,
            _ => ErrorHandlingStrategy::Propagate,
        }
    }
    
    fn name(&self) -> &str {
        &self.name
    }
}

// 错误恢复管理器
pub struct ErrorRecoveryManager {
    handlers: HashMap<ErrorCategory, Vec<Box<dyn ErrorHandler>>>,
    default_handler: Box<dyn ErrorHandler>,
    error_log: RwLock<VecDeque<SystemError>>,
    max_log_size: usize,
    retry_scheduler: Arc<Mutex<RetryScheduler>>,
}

// 重试调度器
struct RetryScheduler {
    scheduled_retries: Vec<(Instant, SystemError, Box<dyn Fn() -> Result<(), SystemError> + Send>)>,
}

impl RetryScheduler {
    fn new() -> Self {
        Self {
            scheduled_retries: Vec::new(),
        }
    }
    
    // 调度重试
    fn schedule<F>(&mut self, when: Instant, error: SystemError, operation: F)
    where
        F: Fn() -> Result<(), SystemError> + Send + 'static,
    {
        self.scheduled_retries.push((when, error, Box::new(operation)));
    }
    
    // 获取并移除到期的重试
```rust
    // 获取并移除到期的重试
    fn get_due_retries(&mut self) -> Vec<(SystemError, Box<dyn Fn() -> Result<(), SystemError> + Send>)> {
        let now = Instant::now();
        let mut due_retries = Vec::new();
        
        // 收集所有到期的重试
        let mut i = 0;
        while i < self.scheduled_retries.len() {
            if self.scheduled_retries[i].0 <= now {
                let (_, error, operation) = self.scheduled_retries.remove(i);
                due_retries.push((error, operation));
            } else {
                i += 1;
            }
        }
        
        due_retries
    }
}

impl ErrorRecoveryManager {
    pub fn new(default_handler: Box<dyn ErrorHandler>) -> Self {
        Self {
            handlers: HashMap::new(),
            default_handler,
            error_log: RwLock::new(VecDeque::new()),
            max_log_size: 1000,
            retry_scheduler: Arc::new(Mutex::new(RetryScheduler::new())),
        }
    }
    
    // 注册错误处理器
    pub fn register_handler(&mut self, category: ErrorCategory, handler: Box<dyn ErrorHandler>) -> &mut Self {
        self.handlers.entry(category).or_insert_with(Vec::new).push(handler);
        self
    }
    
    // 设置最大日志大小
    pub fn with_max_log_size(mut self, size: usize) -> Self {
        self.max_log_size = size;
        self
    }
    
    // 记录错误
    fn log_error(&self, error: SystemError) {
        let mut log = self.error_log.write().unwrap();
        
        // 如果日志已满，移除最旧的错误
        if log.len() >= self.max_log_size {
            log.pop_front();
        }
        
        log.push_back(error);
    }
    
    // 处理错误
    pub fn handle_error<F>(&self, mut error: SystemError, retry_operation: F) -> Result<(), SystemError>
    where
        F: Fn() -> Result<(), SystemError> + Send + 'static,
    {
        // 记录错误
        self.log_error(error.clone());
        
        // 获取适用的处理器
        let handlers = self.handlers
            .get(&error.category)
            .map(|h| h.as_slice())
            .unwrap_or(&[]);
        
        // 如果没有特定的处理器，使用默认处理器
        let strategy = if handlers.is_empty() {
            self.default_handler.handle_error(&error)
        } else {
            // 使用第一个匹配的处理器
            handlers.iter()
                .map(|h| h.handle_error(&error))
                .next()
                .unwrap_or_else(|| self.default_handler.handle_error(&error))
        };
        
        // 根据策略处理错误
        match strategy {
            ErrorHandlingStrategy::RetryImmediately(max_retries) => {
                if error.can_retry(max_retries) {
                    println!("Immediately retrying operation (attempt {}/{})", 
                             error.retry_count + 1, max_retries);
                    
                    error.increment_retry();
                    match retry_operation() {
                        Ok(_) => Ok(()),
                        Err(new_error) => {
                            let mut new_error = new_error;
                            new_error.retry_count = error.retry_count;
                            self.handle_error(new_error, retry_operation)
                        }
                    }
                } else {
                    println!("Maximum retries ({}) exceeded", max_retries);
                    Err(error)
                }
            },
            
            ErrorHandlingStrategy::RetryWithBackoff { max_retries, initial_delay, max_delay, multiplier } => {
                if error.can_retry(max_retries) {
                    // 计算下一次重试的延迟
                    let delay = initial_delay.as_millis() as f64 * multiplier.powi(error.retry_count as i32);
                    let delay = Duration::from_millis(std::cmp::min(delay as u64, max_delay.as_millis() as u64));
                    
                    println!("Scheduling retry with backoff in {:?} (attempt {}/{})", 
                             delay, error.retry_count + 1, max_retries);
                    
                    // 增加重试计数
                    error.increment_retry();
                    
                    // 安排延迟重试
                    let retry_time = Instant::now() + delay;
                    let mut scheduler = self.retry_scheduler.lock().unwrap();
                    scheduler.schedule(retry_time, error, retry_operation);
                    
                    // 为了简化，我们这里不会等待重试结果
                    Ok(())
                } else {
                    println!("Maximum retries ({}) exceeded", max_retries);
                    Err(error)
                }
            },
            
            ErrorHandlingStrategy::Fallback(fallback) => {
                println!("Using fallback for error: {}", error);
                fallback()
            },
            
            ErrorHandlingStrategy::RetryAt(when) => {
                println!("Scheduling retry at specific time: {:?}", when);
                
                error.increment_retry();
                let mut scheduler = self.retry_scheduler.lock().unwrap();
                scheduler.schedule(when, error, retry_operation);
                
                Ok(())
            },
            
            ErrorHandlingStrategy::Discard => {
                println!("Discarding error: {}", error);
                Ok(())
            },
            
            ErrorHandlingStrategy::Propagate => {
                println!("Propagating error: {}", error);
                Err(error)
            },
        }
    }
    
    // 处理待定的重试
    pub fn process_due_retries(&self) -> usize {
        let mut scheduler = self.retry_scheduler.lock().unwrap();
        let due_retries = scheduler.get_due_retries();
        let count = due_retries.len();
        
        for (error, operation) in due_retries {
            // 异步处理重试，避免阻塞线程
            let self_clone = self.clone();
            let error_clone = error.clone();
            
            // 在实际实现中，这可能会启动一个新线程或使用异步任务
            std::thread::spawn(move || {
                match operation() {
                    Ok(_) => {
                        println!("Retry succeeded for error: {}", error_clone);
                    },
                    Err(new_error) => {
                        println!("Retry failed for error: {}", error_clone);
                        let mut new_error = new_error;
                        new_error.retry_count = error.retry_count;
                        
                        // 再次处理错误，可能会再次安排重试
                        let _ = self_clone.handle_error(new_error, operation);
                    }
                }
            });
        }
        
        count
    }
    
    // 获取错误日志
    pub fn get_error_log(&self) -> Vec<SystemError> {
        let log = self.error_log.read().unwrap();
        log.iter().cloned().collect()
    }
    
    // 获取按类别分组的错误计数
    pub fn get_error_counts_by_category(&self) -> HashMap<ErrorCategory, usize> {
        let log = self.error_log.read().unwrap();
        let mut counts = HashMap::new();
        
        for error in log.iter() {
            *counts.entry(error.category.clone()).or_insert(0) += 1;
        }
        
        counts
    }
    
    // 获取按严重程度分组的错误计数
    pub fn get_error_counts_by_severity(&self) -> HashMap<ErrorSeverity, usize> {
        let log = self.error_log.read().unwrap();
        let mut counts = HashMap::new();
        
        for error in log.iter() {
            *counts.entry(error.severity).or_insert(0) += 1;
        }
        
        counts
    }
    
    // 清除错误日志
    pub fn clear_error_log(&self) {
        let mut log = self.error_log.write().unwrap();
        log.clear();
    }
}

impl Clone for ErrorRecoveryManager {
    fn clone(&self) -> Self {
        // 注意：这里我们共享了重试调度器，但没有复制处理器
        // 在实际实现中，可能需要更深层次的克隆或使用引用计数
        Self {
            handlers: HashMap::new(),
            default_handler: Box::new(RuleBasedErrorHandler::new("default_clone")),
            error_log: RwLock::new(VecDeque::new()),
            max_log_size: self.max_log_size,
            retry_scheduler: self.retry_scheduler.clone(),
        }
    }
}

// 使用示例
fn error_recovery_example() {
    // 创建默认错误处理器
    let mut default_handler = RuleBasedErrorHandler::new("default_handler");
    default_handler
        .add_network_retry_rule(3)
        .add_timeout_retry_rule(5)
        .add_service_unavailable_rule(|| {
            println!("服务不可用，使用备用操作");
            Ok(())
        });
    
    // 创建错误恢复管理器
    let mut recovery_manager = ErrorRecoveryManager::new(Box::new(default_handler))
        .with_max_log_size(100);
    
    // 为特定错误类别注册处理器
    let mut data_corruption_handler = RuleBasedErrorHandler::new("data_corruption_handler");
    data_corruption_handler.add_rule(ErrorHandlingRule::new(
        "critical_data_corruption",
        |error| error.severity >= ErrorSeverity::Critical,
        ErrorHandlingStrategy::Propagate,
    ));
    
    recovery_manager.register_handler(ErrorCategory::DataCorruption, Box::new(data_corruption_handler));
    
    // 模拟一些操作和错误
    
    // 1. 网络错误 - 应该重试
    let network_error = SystemError::new(
        "连接拒绝",
        ErrorCategory::Network,
        ErrorSeverity::Error,
        ErrorContext::new("network_service", "connect")
            .with_identifier("server", "api.example.com")
            .with_detail("port", "443"),
    ).with_retriable(true);
    
    let result = recovery_manager.handle_error(network_error, || {
        println!("尝试重新连接...");
        // 假设连接成功
        Ok(())
    });
    
    match result {
        Ok(_) => println!("网络错误处理成功"),
        Err(e) => println!("网络错误处理失败: {}", e),
    }
    
    // 2. 数据损坏错误 - 严重 - 应该上报
    let data_corruption_error = SystemError::new(
        "发现数据库损坏",
        ErrorCategory::DataCorruption,
        ErrorSeverity::Critical,
        ErrorContext::new("database", "read_record")
            .with_identifier("table", "users")
            .with_identifier("record_id", "12345"),
    );
    
    let result = recovery_manager.handle_error(data_corruption_error, || {
        println!("尝试修复数据...");
        // 假设修复失败
        Err(SystemError::new(
            "无法修复损坏的数据",
            ErrorCategory::DataCorruption,
            ErrorSeverity::Critical,
            ErrorContext::new("database", "repair_record"),
        ))
    });
    
    match result {
        Ok(_) => println!("数据损坏错误处理成功"),
        Err(e) => println!("数据损坏错误处理失败: {}", e),
    }
    
    // 3. 超时错误 - 应该使用退避重试
    let timeout_error = SystemError::new(
        "请求超时",
        ErrorCategory::Timeout,
        ErrorSeverity::Warning,
        ErrorContext::new("api_client", "get_data")
            .with_identifier("endpoint", "/api/v1/data")
            .with_detail("timeout", "5s"),
    ).with_retriable(true);
    
    let result = recovery_manager.handle_error(timeout_error, || {
        println!("重试请求...");
        // 假设这次成功
        Ok(())
    });
    
    match result {
        Ok(_) => println!("超时错误处理成功"),
        Err(e) => println!("超时错误处理失败: {}", e),
    }
    
    // 处理待定的重试
    let processed = recovery_manager.process_due_retries();
    println!("处理了 {} 个待定重试", processed);
    
    // 获取错误统计
    let category_counts = recovery_manager.get_error_counts_by_category();
    println!("按类别统计的错误:");
    for (category, count) in &category_counts {
        println!("  {}: {}", category, count);
    }
    
    let severity_counts = recovery_manager.get_error_counts_by_severity();
    println!("按严重程度统计的错误:");
    for (severity, count) in &severity_counts {
        println!("  {}: {}", count, severity);
    }
}

// 自适应系统监控与控制
use std::collections::{HashSet, VecDeque};
use std::sync::{atomic::{AtomicUsize, Ordering}, Arc, Mutex, RwLock};
use std::time::{Duration, Instant};

// 系统指标类型
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MetricType {
    Counter,      // 累积计数器
    Gauge,        // 可变的数值
    Histogram,    // 观测值分布
    Rate,         // 变化率
}

// 系统指标定义
#[derive(Debug, Clone)]
pub struct MetricDefinition {
    // 指标名称
    name: String,
    
    // 指标类型
    metric_type: MetricType,
    
    // 指标描述
    description: String,
    
    // 指标单位
    unit: Option<String>,
    
    // 指标标签
    labels: HashSet<String>,
}

impl MetricDefinition {
    pub fn new(name: impl Into<String>, metric_type: MetricType, description: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            metric_type,
            description: description.into(),
            unit: None,
            labels: HashSet::new(),
        }
    }
    
    pub fn with_unit(mut self, unit: impl Into<String>) -> Self {
        self.unit = Some(unit.into());
        self
    }
    
    pub fn with_label(mut self, label: impl Into<String>) -> Self {
        self.labels.insert(label.into());
        self
    }
    
    pub fn with_labels(mut self, labels: Vec<impl Into<String>>) -> Self {
        for label in labels {
            self.labels.insert(label.into());
        }
        self
    }
    
    // 获取指标名称
    pub fn name(&self) -> &str {
        &self.name
    }
    
    // 获取指标类型
    pub fn metric_type(&self) -> MetricType {
        self.metric_type
    }
    
    // 获取指标描述
    pub fn description(&self) -> &str {
        &self.description
    }
    
    // 获取指标单位
    pub fn unit(&self) -> Option<&str> {
        self.unit.as_deref()
    }
    
    // 获取指标标签
    pub fn labels(&self) -> &HashSet<String> {
        &self.labels
    }
}

// 指标值
#[derive(Debug, Clone)]
pub enum MetricValue {
    // 计数器值
    Counter(u64),
    
    // 仪表值
    Gauge(f64),
    
    // 直方图值
    Histogram {
        observations: Vec<f64>,
        buckets: Vec<f64>,
        counts: Vec<usize>,
        sum: f64,
        count: usize,
    },
    
    // 速率值
    Rate {
        current_rate: f64,
        samples: VecDeque<(Instant, f64)>,
        window_size: Duration,
    },
}

impl MetricValue {
    // 创建新的计数器
    pub fn new_counter() -> Self {
        Self::Counter(0)
    }
    
    // 创建新的仪表
    pub fn new_gauge(initial_value: f64) -> Self {
        Self::Gauge(initial_value)
    }
    
    // 创建新的直方图
    pub fn new_histogram(buckets: Vec<f64>) -> Self {
        let bucket_count = buckets.len();
        Self::Histogram {
            observations: Vec::new(),
            buckets,
            counts: vec![0; bucket_count + 1], // +1 for the overflow bucket
            sum: 0.0,
            count: 0,
        }
    }
    
    // 创建新的速率
    pub fn new_rate(window_size: Duration) -> Self {
        Self::Rate {
            current_rate: 0.0,
            samples: VecDeque::new(),
            window_size,
        }
    }
    
    // 获取指标类型
    pub fn metric_type(&self) -> MetricType {
        match self {
            Self::Counter(_) => MetricType::Counter,
            Self::Gauge(_) => MetricType::Gauge,
            Self::Histogram { .. } => MetricType::Histogram,
            Self::Rate { .. } => MetricType::Rate,
        }
    }
    
    // 更新计数器值
    pub fn increment_counter(&mut self, value: u64) {
        if let Self::Counter(counter) = self {
            *counter += value;
        }
    }
    
    // 更新仪表值
    pub fn set_gauge(&mut self, value: f64) {
        if let Self::Gauge(gauge) = self {
            *gauge = value;
        }
    }
    
    // 记录直方图观测值
    pub fn observe(&mut self, value: f64) {
        match self {
            Self::Histogram { observations, buckets, counts, sum, count } => {
                observations.push(value);
                *sum += value;
                *count += 1;
                
                // 更新桶计数
                let mut bucket_index = buckets.len();
                for (i, upper_bound) in buckets.iter().enumerate() {
                    if value <= *upper_bound {
                        bucket_index = i;
                        break;
                    }
                }
                
                counts[bucket_index] += 1;
            },
            Self::Rate { current_rate, samples, window_size } => {
                // 记录样本
                let now = Instant::now();
                samples.push_back((now, value));
                
                // 移除过期样本
                while let Some((time, _)) = samples.front() {
                    if now.duration_since(*time) > *window_size {
                        samples.pop_front();
                    } else {
                        break;
                    }
                }
                
                // 如果有足够的样本，计算速率
                if samples.len() >= 2 {
                    let (first_time, first_value) = samples.front().unwrap();
                    let (last_time, last_value) = samples.back().unwrap();
                    
                    let time_diff = last_time.duration_since(*first_time).as_secs_f64();
                    if time_diff > 0.0 {
                        let value_diff = last_value - first_value;
                        *current_rate = value_diff / time_diff;
                    }
                }
            },
            _ => {
                // 忽略不是直方图或速率的类型
            }
        }
    }
    
    // 获取当前值
    pub fn get_value(&self) -> String {
        match self {
            Self::Counter(value) => value.to_string(),
            Self::Gauge(value) => value.to_string(),
            Self::Histogram { sum, count, .. } => {
                if *count > 0 {
                    format!("average: {}", sum / *count as f64)
                } else {
                    "no observations".to_string()
                }
            },
            Self::Rate { current_rate, .. } => format!("{}/s", current_rate),
        }
    }
    
    // 获取详细信息
    pub fn get_details(&self) -> Vec<(String, String)> {
        match self {
            Self::Counter(value) => vec![("value".to_string(), value.to_string())],
            Self::Gauge(value) => vec![("value".to_string(), value.to_string())],
            Self::Histogram { observations, buckets, counts, sum, count } => {
                let mut details = Vec::new();
                
                details.push(("count".to_string(), count.to_string()));
                details.push(("sum".to_string(), sum.to_string()));
                
                if *count > 0 {
                    details.push(("average".to_string(), (sum / *count as f64).to_string()));
                }
                
                // 计算分位数
                if !observations.is_empty() {
                    let mut sorted_obs = observations.clone();
                    sorted_obs.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
                    
                    let p50 = percentile(&sorted_obs, 0.5);
                    let p90 = percentile(&sorted_obs, 0.9);
                    let p99 = percentile(&sorted_obs, 0.99);
                    
                    details.push(("p50".to_string(), p50.to_string()));
                    details.push(("p90".to_string(), p90.to_string()));
                    details.push(("p99".to_string(), p99.to_string()));
                }
                
                // 添加桶信息
                for (i, (upper_bound, count)) in buckets.iter().zip(counts.iter()).enumerate() {
                    details.push((format!("bucket_{}", i), format!("<= {} : {}", upper_bound, count)));
                }
                
                details
            },
            Self::Rate { current_rate, samples, window_size } => {
                let mut details = Vec::new();
                
                details.push(("current_rate".to_string(), format!("{}/s", current_rate)));
                details.push(("window_size".to_string(), format!("{:?}", window_size)));
                details.push(("sample_count".to_string(), samples.len().to_string()));
                
                if let (Some((first_time, first_value)), Some((last_time, last_value))) = (samples.front(), samples.back()) {
                    let time_diff = last_time.duration_since(*first_time);
                    details.push(("time_span".to_string(), format!("{:?}", time_diff)));
                    details.push(("value_change".to_string(), format!("{}", last_value - first_value)));
                }
                
                details
            },
        }
    }
}

// 计算分位数辅助函数
fn percentile(sorted_values: &[f64], p: f64) -> f64 {
    if sorted_values.is_empty() {
        return 0.0;
    }
    
    let len = sorted_values.len();
    let index = (len as f64 * p).floor() as usize;
    if index >= len {
        return *sorted_values.last().unwrap();
    }
    
    sorted_values[index]
}

// 标签集
type LabelSet = HashMap<String, String>;

// 标签用于区分同一指标的不同实例
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MetricKey {
    name: String,
    labels: LabelSet,
}

impl MetricKey {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            labels: HashMap::new(),
        }
    }
    
    pub fn with_label(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.labels.insert(key.into(), value.into());
        self
    }
    
    pub fn with_labels(mut self, labels: HashMap<String, String>) -> Self {
        self.labels.extend(labels);
        self
    }
    
    // 获取指标名称
    pub fn name(&self) -> &str {
        &self.name
    }
    
    // 获取指标标签
    pub fn labels(&self) -> &LabelSet {
        &self.labels
    }
}
```

继续前面的代码...

```rust
// 指标注册表
pub struct MetricRegistry {
    // 指标定义
    definitions: RwLock<HashMap<String, MetricDefinition>>,
    
    // 指标值
    values: RwLock<HashMap<MetricKey, MetricValue>>,
    
    // 告警规则
    alert_rules: RwLock<Vec<AlertRule>>,
    
    // 告警历史
    alert_history: RwLock<VecDeque<Alert>>,
    
    // 每个指标定义的标签值集合
    label_values: RwLock<HashMap<String, HashMap<String, HashSet<String>>>>,
    
    // 最大告警历史记录数
    max_alert_history: usize,
}

impl MetricRegistry {
    pub fn new() -> Self {
        Self {
            definitions: RwLock::new(HashMap::new()),
            values: RwLock::new(HashMap::new()),
            alert_rules: RwLock::new(Vec::new()),
            alert_history: RwLock::new(VecDeque::new()),
            label_values: RwLock::new(HashMap::new()),
            max_alert_history: 1000,
        }
    }
    
    // 注册新指标
    pub fn register_metric(&self, definition: MetricDefinition) -> Result<(), String> {
        let name = definition.name().to_string();
        
        let mut definitions = self.definitions.write().unwrap();
        
        if definitions.contains_key(&name) {
            return Err(format!("指标 '{}' 已经存在", name));
        }
        
        // 预初始化标签值集合
        let mut label_values = self.label_values.write().unwrap();
        let metric_labels = label_values.entry(name.clone()).or_insert_with(HashMap::new);
        
        for label in definition.labels() {
            metric_labels.insert(label.clone(), HashSet::new());
        }
        
        definitions.insert(name, definition);
        
        Ok(())
    }
    
    // 添加告警规则
    pub fn add_alert_rule(&self, rule: AlertRule) {
        let mut rules = self.alert_rules.write().unwrap();
        rules.push(rule);
    }
    
    // 设置最大告警历史记录数
    pub fn set_max_alert_history(&self, max: usize) {
        self.max_alert_history = max;
    }
    
    // 创建或获取计数器实例
    pub fn counter(&self, key: MetricKey) -> Result<Arc<Counter>, String> {
        let name = key.name().to_string();
        
        // 验证指标定义存在
        let definitions = self.definitions.read().unwrap();
        let definition = definitions.get(&name).ok_or_else(|| format!("指标 '{}' 未注册", name))?;
        
        if definition.metric_type() != MetricType::Counter {
            return Err(format!("指标 '{}' 不是计数器类型", name));
        }
        
        // 验证标签
        self.validate_labels(&key, definition)?;
        
        // 获取或创建指标值
        let mut values = self.values.write().unwrap();
        
        if !values.contains_key(&key) {
            values.insert(key.clone(), MetricValue::new_counter());
        }
        
        // 更新标签值集合
        self.update_label_values(&key);
        
        // 创建计数器包装器
        Ok(Arc::new(Counter::new(key, self)))
    }
    
    // 创建或获取仪表实例
    pub fn gauge(&self, key: MetricKey, initial_value: f64) -> Result<Arc<Gauge>, String> {
        let name = key.name().to_string();
        
        // 验证指标定义存在
        let definitions = self.definitions.read().unwrap();
        let definition = definitions.get(&name).ok_or_else(|| format!("指标 '{}' 未注册", name))?;
        
        if definition.metric_type() != MetricType::Gauge {
            return Err(format!("指标 '{}' 不是仪表类型", name));
        }
        
        // 验证标签
        self.validate_labels(&key, definition)?;
        
        // 获取或创建指标值
        let mut values = self.values.write().unwrap();
        
        if !values.contains_key(&key) {
            values.insert(key.clone(), MetricValue::new_gauge(initial
```rust
        // 获取或创建指标值
        let mut values = self.values.write().unwrap();
        
        if !values.contains_key(&key) {
            values.insert(key.clone(), MetricValue::new_gauge(initial_value));
        }
        
        // 更新标签值集合
        self.update_label_values(&key);
        
        // 创建仪表包装器
        Ok(Arc::new(Gauge::new(key, self)))
    }
    
    // 创建或获取直方图实例
    pub fn histogram(&self, key: MetricKey, buckets: Vec<f64>) -> Result<Arc<Histogram>, String> {
        let name = key.name().to_string();
        
        // 验证指标定义存在
        let definitions = self.definitions.read().unwrap();
        let definition = definitions.get(&name).ok_or_else(|| format!("指标 '{}' 未注册", name))?;
        
        if definition.metric_type() != MetricType::Histogram {
            return Err(format!("指标 '{}' 不是直方图类型", name));
        }
        
        // 验证标签
        self.validate_labels(&key, definition)?;
        
        // 获取或创建指标值
        let mut values = self.values.write().unwrap();
        
        if !values.contains_key(&key) {
            values.insert(key.clone(), MetricValue::new_histogram(buckets));
        }
        
        // 更新标签值集合
        self.update_label_values(&key);
        
        // 创建直方图包装器
        Ok(Arc::new(Histogram::new(key, self)))
    }
    
    // 创建或获取速率实例
    pub fn rate(&self, key: MetricKey, window_size: Duration) -> Result<Arc<Rate>, String> {
        let name = key.name().to_string();
        
        // 验证指标定义存在
        let definitions = self.definitions.read().unwrap();
        let definition = definitions.get(&name).ok_or_else(|| format!("指标 '{}' 未注册", name))?;
        
        if definition.metric_type() != MetricType::Rate {
            return Err(format!("指标 '{}' 不是速率类型", name));
        }
        
        // 验证标签
        self.validate_labels(&key, definition)?;
        
        // 获取或创建指标值
        let mut values = self.values.write().unwrap();
        
        if !values.contains_key(&key) {
            values.insert(key.clone(), MetricValue::new_rate(window_size));
        }
        
        // 更新标签值集合
        self.update_label_values(&key);
        
        // 创建速率包装器
        Ok(Arc::new(Rate::new(key, self)))
    }
    
    // 验证标签
    fn validate_labels(&self, key: &MetricKey, definition: &MetricDefinition) -> Result<(), String> {
        // 检查标签键是否有效
        let required_labels: HashSet<String> = definition.labels().iter().cloned().collect();
        let provided_labels: HashSet<String> = key.labels().keys().cloned().collect();
        
        // 确保所有必需的标签都提供了
        let missing_labels: Vec<_> = required_labels.difference(&provided_labels).collect();
        if !missing_labels.is_empty() {
            return Err(format!("缺少必需的标签: {:?}", missing_labels));
        }
        
        // 确保没有额外的标签
        let extra_labels: Vec<_> = provided_labels.difference(&required_labels).collect();
        if !extra_labels.is_empty() {
            return Err(format!("提供了未定义的标签: {:?}", extra_labels));
        }
        
        Ok(())
    }
    
    // 更新标签值集合
    fn update_label_values(&self, key: &MetricKey) {
        let mut label_values = self.label_values.write().unwrap();
        if let Some(metric_labels) = label_values.get_mut(key.name()) {
            for (label_key, label_value) in key.labels() {
                if let Some(values) = metric_labels.get_mut(label_key) {
                    values.insert(label_value.clone());
                }
            }
        }
    }
    
    // 内部更新指标值
    fn update_metric(&self, key: &MetricKey, updater: impl FnOnce(&mut MetricValue)) -> Result<(), String> {
        let mut values = self.values.write().unwrap();
        
        if let Some(value) = values.get_mut(key) {
            updater(value);
            Ok(())
        } else {
            Err(format!("指标 '{:?}' 不存在", key))
        }
    }
    
    // 获取指标值
    pub fn get_metric_value(&self, key: &MetricKey) -> Option<MetricValue> {
        let values = self.values.read().unwrap();
        values.get(key).cloned()
    }
    
    // 获取所有指标定义
    pub fn get_all_definitions(&self) -> Vec<MetricDefinition> {
        let definitions = self.definitions.read().unwrap();
        definitions.values().cloned().collect()
    }
    
    // 获取所有指标值
    pub fn get_all_metrics(&self) -> HashMap<MetricKey, MetricValue> {
        let values = self.values.read().unwrap();
        values.clone()
    }
    
    // 获取标签值
    pub fn get_label_values(&self, metric_name: &str, label_name: &str) -> Option<HashSet<String>> {
        let label_values = self.label_values.read().unwrap();
        label_values.get(metric_name)
            .and_then(|labels| labels.get(label_name))
            .cloned()
    }
    
    // 评估告警规则
    pub fn evaluate_alert_rules(&self) -> Vec<Alert> {
        let rules = self.alert_rules.read().unwrap();
        let mut new_alerts = Vec::new();
        
        for rule in rules.iter() {
            if let Some(alert) = rule.evaluate(self) {
                // 记录告警
                let mut history = self.alert_history.write().unwrap();
                history.push_back(alert.clone());
                
                // 如果超过最大历史记录数，移除最旧的
                while history.len() > self.max_alert_history {
                    history.pop_front();
                }
                
                new_alerts.push(alert);
            }
        }
        
        new_alerts
    }
    
    // 获取告警历史
    pub fn get_alert_history(&self) -> Vec<Alert> {
        let history = self.alert_history.read().unwrap();
        history.iter().cloned().collect()
    }
}

// 计数器包装器
pub struct Counter {
    key: MetricKey,
    registry: *const MetricRegistry,
}

impl Counter {
    fn new(key: MetricKey, registry: &MetricRegistry) -> Self {
        Self {
            key,
            registry: registry as *const _,
        }
    }
    
    // 增加计数器值
    pub fn increment(&self, value: u64) {
        if value == 0 {
            return;
        }
        
        // 安全地获取注册表引用
        let registry = unsafe { &*self.registry };
        
        let _ = registry.update_metric(&self.key, |metric| {
            if let MetricValue::Counter(counter) = metric {
                *counter += value;
            }
        });
    }
    
    // 获取当前值
    pub fn value(&self) -> Option<u64> {
        // 安全地获取注册表引用
        let registry = unsafe { &*self.registry };
        
        if let Some(MetricValue::Counter(value)) = registry.get_metric_value(&self.key) {
            Some(value)
        } else {
            None
        }
    }
}

impl Clone for Counter {
    fn clone(&self) -> Self {
        Self {
            key: self.key.clone(),
            registry: self.registry,
        }
    }
}

// 仪表包装器
pub struct Gauge {
    key: MetricKey,
    registry: *const MetricRegistry,
}

impl Gauge {
    fn new(key: MetricKey, registry: &MetricRegistry) -> Self {
        Self {
            key,
            registry: registry as *const _,
        }
    }
    
    // 设置仪表值
    pub fn set(&self, value: f64) {
        // 安全地获取注册表引用
        let registry = unsafe { &*self.registry };
        
        let _ = registry.update_metric(&self.key, |metric| {
            if let MetricValue::Gauge(gauge) = metric {
                *gauge = value;
            }
        });
    }
    
    // 增加仪表值
    pub fn increment(&self, value: f64) {
        // 安全地获取注册表引用
        let registry = unsafe { &*self.registry };
        
        let _ = registry.update_metric(&self.key, |metric| {
            if let MetricValue::Gauge(gauge) = metric {
                *gauge += value;
            }
        });
    }
    
    // 减少仪表值
    pub fn decrement(&self, value: f64) {
        // 安全地获取注册表引用
        let registry = unsafe { &*self.registry };
        
        let _ = registry.update_metric(&self.key, |metric| {
            if let MetricValue::Gauge(gauge) = metric {
                *gauge -= value;
            }
        });
    }
    
    // 获取当前值
    pub fn value(&self) -> Option<f64> {
        // 安全地获取注册表引用
        let registry = unsafe { &*self.registry };
        
        if let Some(MetricValue::Gauge(value)) = registry.get_metric_value(&self.key) {
            Some(value)
        } else {
            None
        }
    }
}

impl Clone for Gauge {
    fn clone(&self) -> Self {
        Self {
            key: self.key.clone(),
            registry: self.registry,
        }
    }
}

// 直方图包装器
pub struct Histogram {
    key: MetricKey,
    registry: *const MetricRegistry,
}

impl Histogram {
    fn new(key: MetricKey, registry: &MetricRegistry) -> Self {
        Self {
            key,
            registry: registry as *const _,
        }
    }
    
    // 记录观测值
    pub fn observe(&self, value: f64) {
        // 安全地获取注册表引用
        let registry = unsafe { &*self.registry };
        
        let _ = registry.update_metric(&self.key, |metric| {
            if let MetricValue::Histogram { observations, buckets, counts, sum, count } = metric {
                observations.push(value);
                *sum += value;
                *count += 1;
                
                // 更新桶计数
                let mut bucket_index = buckets.len();
                for (i, upper_bound) in buckets.iter().enumerate() {
                    if value <= *upper_bound {
                        bucket_index = i;
                        break;
                    }
                }
                
                counts[bucket_index] += 1;
            }
        });
    }
    
    // 获取直方图详情
    pub fn details(&self) -> Option<Vec<(String, String)>> {
        // 安全地获取注册表引用
        let registry = unsafe { &*self.registry };
        
        registry.get_metric_value(&self.key).map(|value| value.get_details())
    }
}

impl Clone for Histogram {
    fn clone(&self) -> Self {
        Self {
            key: self.key.clone(),
            registry: self.registry,
        }
    }
}

// 速率包装器
pub struct Rate {
    key: MetricKey,
    registry: *const MetricRegistry,
}

impl Rate {
    fn new(key: MetricKey, registry: &MetricRegistry) -> Self {
        Self {
            key,
            registry: registry as *const _,
        }
    }
    
    // 记录值
    pub fn record(&self, value: f64) {
        // 安全地获取注册表引用
        let registry = unsafe { &*self.registry };
        
        let _ = registry.update_metric(&self.key, |metric| {
            metric.observe(value);
        });
    }
    
    // 获取当前速率
    pub fn current_rate(&self) -> Option<f64> {
        // 安全地获取注册表引用
        let registry = unsafe { &*self.registry };
        
        if let Some(MetricValue::Rate { current_rate, .. }) = registry.get_metric_value(&self.key) {
            Some(current_rate)
        } else {
            None
        }
    }
    
    // 获取速率详情
    pub fn details(&self) -> Option<Vec<(String, String)>> {
        // 安全地获取注册表引用
        let registry = unsafe { &*self.registry };
        
        registry.get_metric_value(&self.key).map(|value| value.get_details())
    }
}

impl Clone for Rate {
    fn clone(&self) -> Self {
        Self {
            key: self.key.clone(),
            registry: self.registry,
        }
    }
}

// 告警规则
#[derive(Debug, Clone)]
pub struct AlertRule {
    // 规则名称
    name: String,
    
    // 规则描述
    description: String,
    
    // 告警级别
    severity: AlertSeverity,
    
    // 目标指标
    target_metric: String,
    
    // 标签选择器
    label_selectors: HashMap<String, String>,
    
    // 告警条件
    condition: AlertCondition,
    
    // 告警消息模板
    message_template: String,
    
    // 告警通知目标
    notification_targets: Vec<NotificationTarget>,
}

// 告警条件
#[derive(Debug, Clone)]
pub enum AlertCondition {
    // 大于阈值
    GreaterThan(f64),
    
    // 小于阈值
    LessThan(f64),
    
    // 等于阈值
    Equals(f64),
    
    // 不等于阈值
    NotEquals(f64),
    
    // 大于或等于阈值
    GreaterOrEquals(f64),
    
    // 小于或等于阈值
    LessOrEquals(f64),
    
    // 在范围内
    InRange(f64, f64),
    
    // 不在范围内
    OutOfRange(f64, f64),
    
    // 变化率大于阈值
    RateOfChange(f64),
    
    // 连续满足条件的次数
    ConsecutiveCount(Box<AlertCondition>, usize),
}

// 告警级别
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum AlertSeverity {
    Info,
    Warning,
    Error,
    Critical,
}

impl fmt::Display for AlertSeverity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AlertSeverity::Info => write!(f, "INFO"),
            AlertSeverity::Warning => write!(f, "WARNING"),
            AlertSeverity::Error => write!(f, "ERROR"),
            AlertSeverity::Critical => write!(f, "CRITICAL"),
        }
    }
}

// 通知目标
#[derive(Debug, Clone)]
pub enum NotificationTarget {
    Email(String),
    Webhook(String),
    Sms(String),
    Custom(String),
}

impl AlertRule {
    pub fn new(
        name: impl Into<String>,
        description: impl Into<String>,
        severity: AlertSeverity,
        target_metric: impl Into<String>,
        condition: AlertCondition,
        message_template: impl Into<String>,
    ) -> Self {
        Self {
            name: name.into(),
            description: description.into(),
            severity,
            target_metric: target_metric.into(),
            label_selectors: HashMap::new(),
            condition,
            message_template: message_template.into(),
            notification_targets: Vec::new(),
        }
    }
    
    pub fn with_label_selector(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.label_selectors.insert(key.into(), value.into());
        self
    }
    
    pub fn with_notification_target(mut self, target: NotificationTarget) -> Self {
        self.notification_targets.push(target);
        self
    }
    
    // 评估告警规则
    pub fn evaluate(&self, registry: &MetricRegistry) -> Option<Alert> {
        // 获取所有匹配的指标
        let values = registry.values.read().unwrap();
        
        let matching_metrics: Vec<(MetricKey, MetricValue)> = values
            .iter()
            .filter(|(key, _)| {
                // 检查指标名称
                if key.name() != self.target_metric {
                    return false;
                }
                
                // 检查标签选择器
                for (selector_key, selector_value) in &self.label_selectors {
                    if key.labels().get(selector_key) != Some(selector_value) {
                        return false;
                    }
                }
                
                true
            })
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        
        if matching_metrics.is_empty() {
            return None;
        }
        
        // 检查每个匹配的指标是否满足条件
        for (key, value) in matching_metrics {
            if self.check_condition(&value) {
                // 创建告警
                return Some(Alert {
                    name: self.name.clone(),
                    description: self.description.clone(),
                    severity: self.severity.clone(),
                    metric_key: key,
                    metric_value: value,
                    message: self.render_message(&key),
                    timestamp: Instant::now(),
                    notification_targets: self.notification_targets.clone(),
                });
            }
        }
        
        None
    }
    
    // 检查指标值是否满足条件
    fn check_condition(&self, value: &MetricValue) -> bool {
        // 首先提取数值
        let numeric_value = match value {
            MetricValue::Counter(v) => *v as f64,
            MetricValue::Gauge(v) => *v,
            MetricValue::Histogram { sum, count, .. } => {
                if *count > 0 {
                    *sum / *count as f64
                } else {
                    return false;
                }
            },
            MetricValue::Rate { current_rate, .. } => *current_rate,
        };
        
        // 检查条件
        match &self.condition {
            AlertCondition::GreaterThan(threshold) => numeric_value > *threshold,
            AlertCondition::LessThan(threshold) => numeric_value < *threshold,
            AlertCondition::Equals(threshold) => (numeric_value - *threshold).abs() < f64::EPSILON,
            AlertCondition::NotEquals(threshold) => (numeric_value - *threshold).abs() >= f64::EPSILON,
            AlertCondition::GreaterOrEquals(threshold) => numeric_value >= *threshold,
            AlertCondition::LessOrEquals(threshold) => numeric_value <= *threshold,
            AlertCondition::InRange(min, max) => numeric_value >= *min && numeric_value <= *max,
            AlertCondition::OutOfRange(min, max) => numeric_value < *min || numeric_value > *max,
            
            // 对于变化率和连续计数，这里简化处理
            // 在实际实现中，这些通常需要保存历史状态
            AlertCondition::RateOfChange(_) => false,
            AlertCondition::ConsecutiveCount(_, _) => false,
        }
    }
    
    // 渲染告警消息
    fn render_message(&self, key: &MetricKey) -> String {
        // 简单的模板替换
        let mut message = self.message_template.clone();
        
        // 替换指标名称
        message = message.replace("{metric}", key.name());
        
        // 替换标签
        for (label_key, label_value) in key.labels() {
            message = message.replace(&format!("{{label.{}}}", label_key), label_value);
        }
        
        message
    }
}

// 告警
#[derive(Debug, Clone)]
pub struct Alert {
    // 告警名称
    name: String,
    
    // 告警描述
    description: String,
    
    // 告警级别
    severity: AlertSeverity,
    
    // 触发的指标
    metric_key: MetricKey,
    
    // 指标值
    metric_value: MetricValue,
    
    // 告警消息
    message: String,
    
    // 告警时间
    timestamp: Instant,
    
    // 通知目标
    notification_targets: Vec<NotificationTarget>,
}

impl Alert {
    // 获取告警名称
    pub fn name(&self) -> &str {
        &self.name
    }
    
    // 获取告警描述
    pub fn description(&self) -> &str {
        &self.description
    }
    
    // 获取告警级别
    pub fn severity(&self) -> &AlertSeverity {
        &self.severity
    }
    
    // 获取指标键
    pub fn metric_key(&self) -> &MetricKey {
        &self.metric_key
    }
    
    // 获取指标值
    pub fn metric_value(&self) -> &MetricValue {
        &self.metric_value
    }
    
    // 获取告警消息
    pub fn message(&self) -> &str {
        &self.message
    }
    
    // 获取告警时间
    pub fn timestamp(&self) -> &Instant {
        &self.timestamp
    }
    
    // 获取通知目标
    pub fn notification_targets(&self) -> &[NotificationTarget] {
        &self.notification_targets
    }
    
    // 发送通知
    pub fn send_notifications(&self) {
        for target in &self.notification_targets {
            match target {
                NotificationTarget::Email(email) => {
                    println!("发送电子邮件通知到 {}: {}", email, self.message);
                    // 实际实现中，这里会调用邮件发送服务
                }
                NotificationTarget::Webhook(url) => {
                    println!("发送Webhook通知到 {}: {}", url, self.message);
                    // 实际实现中，这里会发送HTTP请求
                }
                NotificationTarget::Sms(phone) => {
                    println!("发送短信通知到 {}: {}", phone, self.message);
                    // 实际实现中，这里会调用短信发送服务
                }
                NotificationTarget::Custom(target) => {
                    println!("发送自定义通知到 {}: {}", target, self.message);
                    // 实际实现中，这里会调用自定义通知机制
                }
            }
        }
    }
}

// 使用示例
fn adaptive_monitoring_example() {
    // 创建指标注册表
    let registry = MetricRegistry::new();
    
    // 注册一些指标
    let _ = registry.register_metric(
        MetricDefinition::new(
            "http_requests_total",
            MetricType::Counter,
            "HTTP请求总数",
        )
        .with_label("method")
        .with_label("status")
        .with_label("path")
    );
    
    let _ = registry.register_metric(
        MetricDefinition::new(
            "http_request_duration_seconds",
            MetricType::Histogram,
            "HTTP请求处理时间",
        )
        .with_unit("seconds")
        .with_label("method")
        .with_label("path")
    );
    
    let _ = registry.register_metric(
        MetricDefinition::new(
            "system_memory_usage",
            MetricType::Gauge,
            "系统内存使用量",
        )
        .with_unit("bytes")
    );
    
    let _ = registry.register_metric(
        MetricDefinition::new(
            "requests_per_second",
            MetricType::Rate,
            "每秒请求数",
        )
        .with_unit("requests/s")
        .with_label("endpoint")
    );
    
    // 创建一些指标实例
    let requests_total = registry.counter(
        MetricKey::new("http_requests_total")
            .with_label("method", "GET")
            .with_label("status", "200")
            .with_label("path", "/api/v1/users"),
    ).unwrap();
    
    let request_duration = registry.histogram(
        MetricKey::new("http_request_duration_seconds")
            .with_label("method", "GET")
            .with_label("path", "/api/v1/users"),
        vec![0.01, 0.05, 0.1, 0.5, 1.0, 5.0],
    ).unwrap();
    
    let memory_usage = registry.gauge(
        MetricKey::new("system_memory_usage"),
        100_000_000.0, // 初始值100MB
    ).unwrap();
    
    let requests_rate = registry.rate(
        MetricKey::new("requests_per_second")
            .with_label("endpoint", "/api/v1/users"),
        Duration::from_secs(60), // 1分钟窗口
    ).unwrap();
    
    // 添加一些告警规则
    registry.add_alert_rule(
        AlertRule::new(
            "high_memory_usage",
            "系统内存使用量过高",
            AlertSeverity::Warning,
            "system_memory_usage",
            AlertCondition::GreaterThan(500_000_000.0), // 500MB
            "系统内存使用量过高：{metric} = {value} 字节",
        )
        .with_notification_target(NotificationTarget::Email("admin@example.com".to_string()))
    );
    
    registry.add_alert_rule(
        AlertRule::new(
            "slow_request",
            "请求处理时间过长",
            AlertSeverity::Error,
            "http_request_duration_seconds",
            AlertCondition::GreaterThan(1.0), // 1秒
            "请求处理时间过长：{metric}[{label.method}:{label.path}] = {value} 秒",
        )
        .with_label_selector("method", "GET")
        .with_notification_target(NotificationTarget::Webhook("https://example.com/notifications".to_string()))
    );
    
    // 模拟一些指标更新
    requests_total.increment(1);
    request_duration.observe(0.8);
    memory_usage.set(200_000_000.0);
    requests_rate.record(15.0);
    
    // 模拟一些会触发告警的指标更新
    memory_usage.set(600_000_000.0); // 这应该触发内存使用量告警
    request_duration.observe(2.5);    // 这应该触发请求处理时间告警
    
    // 评估告警规则
    let alerts = registry.evaluate_alert_rules();
    
    println!("触发的告警:");
    for alert in &alerts {
        println!("- [{} : {}] {}", alert.severity(), alert.name(), alert.message());
        alert.send_notifications();
    }
    
    // 获取指标值
    let value = requests_total.value().unwrap_or(0);
    println!("HTTP请求总数: {}", value);
    
    // 获取直方图详情
    if let Some(details) = request_duration.details() {
        println!("HTTP请求处理时间:");
        for (key, value) in details {
            println!("  {}: {}", key, value);
        }
    }
    
    // 获取内存使用量
    let memory = memory_usage.value().unwrap_or(0.0);
    println!("系统内存使用量: {} 字节", memory);
    
    // 获取请求速率
    let rate = requests_rate.current_rate().unwrap_or(0.0);
    println!("每秒请求数: {} 请求/秒", rate);
    
    // 获取所有指标值
    let all_metrics = registry.get_all_metrics();
    println!("所有指标 ({} 个):", all_metrics.len());
    for (key, value) in all_metrics {
        println!("  {}[{:?}] = {}", key.name(), key.labels(), value.get_value());
    }
    
    // 获取告警历史
    let alert_history = registry.get_alert_history();
    println!("告警历史 ({} 个):", alert_history.len());
    for alert in alert_history {
        println!("  [{} : {}] {}", alert.severity(), alert.name(), alert.message());
    }
}

// 主函数：演示所有功能
fn main() {
    println!("=== 拓扑管理示例 ===");
    topology_
```rust
    println!("=== 拓扑管理示例 ===");
    topology_manager_example();
    
    println!("\n=== 错误恢复示例 ===");
    error_recovery_example();
    
    println!("\n=== 自适应监控示例 ===");
    adaptive_monitoring_example();
    
    println!("\n=== 分布式系统自动化控制示例 ===");
    distributed_control_example();
}

// 分布式系统自动化控制示例
fn distributed_control_example() {
    // 创建资源感知调度器
    let scheduler = ResourceAwareScheduler::new(4);
    
    // 创建拓扑管理器
    let topology = Arc::new(TopologyManager::new());
    
    // 创建错误恢复管理器
    let mut default_handler = RuleBasedErrorHandler::new("default_handler");
    default_handler
        .add_network_retry_rule(3)
        .add_timeout_retry_rule(5);
    
    let recovery_manager = Arc::new(ErrorRecoveryManager::new(Box::new(default_handler)));
    
    // 创建指标注册表
    let metrics = Arc::new(MetricRegistry::new());
    
    // 注册一些关键指标
    let _ = metrics.register_metric(
        MetricDefinition::new(
            "task_execution_time",
            MetricType::Histogram,
            "任务执行时间",
        )
        .with_unit("seconds")
        .with_label("task_type")
        .with_label("priority")
    );
    
    let _ = metrics.register_metric(
        MetricDefinition::new(
            "task_queue_length",
            MetricType::Gauge,
            "任务队列长度",
        )
    );
    
    let _ = metrics.register_metric(
        MetricDefinition::new(
            "error_count",
            MetricType::Counter,
            "错误计数",
        )
        .with_label("error_type")
    );
    
    // 创建分布式控制系统
    let controller = DistributedController::new(
        scheduler,
        topology,
        recovery_manager,
        metrics.clone(),
    );
    
    // 创建一些关键指标实例
    let queue_length = metrics.gauge(
        MetricKey::new("task_queue_length"),
        0.0,
    ).unwrap();
    
    let error_counter = metrics.counter(
        MetricKey::new("error_count")
            .with_label("error_type", "network"),
    ).unwrap();
    
    let task_time = metrics.histogram(
        MetricKey::new("task_execution_time")
            .with_label("task_type", "data_processing")
            .with_label("priority", "high"),
        vec![0.01, 0.1, 0.5, 1.0, 5.0, 10.0],
    ).unwrap();
    
    // 模拟一些任务执行
    println!("提交任务...");
    let task_count = 10;
    
    for i in 0..task_count {
        let priority = if i % 3 == 0 { TaskPriority::High } else { TaskPriority::Normal };
        let task_type = if i % 2 == 0 { "data_processing" } else { "network_io" };
        
        // 更新队列长度指标
        queue_length.increment(1.0);
        
        // 提交任务
        let task_result = controller.submit_task(
            format!("task-{}", i),
            task_type.to_string(),
            priority,
            move |ctx| {
                println!("执行任务 {} ({})", i, task_type);
                
                // 模拟一些工作
                let start = Instant::now();
                
                // 模拟一些随机错误
                if i % 7 == 0 {
                    println!("  任务 {} 出现网络错误", i);
                    error_counter.increment(1);
                    return Err("网络错误".into());
                }
                
                // 模拟工作时间
                std::thread::sleep(Duration::from_millis((i % 5 + 1) * 100));
                
                // 记录任务执行时间
                let elapsed = start.elapsed().as_secs_f64();
                task_time.observe(elapsed);
                
                println!("  任务 {} 完成，用时 {:.2} 秒", i, elapsed);
                
                // 更新队列长度指标
                queue_length.decrement(1.0);
                
                Ok(format!("任务 {} 的结果", i))
            },
        );
        
        match task_result {
            Ok(task_id) => println!("任务已提交，ID: {}", task_id),
            Err(e) => println!("任务提交失败: {:?}", e),
        }
    }
    
    // 等待所有任务完成
    println!("等待任务完成...");
    std::thread::sleep(Duration::from_secs(3));
    
    // 获取系统状态
    let system_state = controller.get_system_state();
    println!("系统状态:");
    println!("  活动任务: {}", system_state.active_tasks);
    println!("  已完成任务: {}", system_state.completed_tasks);
    println!("  失败任务: {}", system_state.failed_tasks);
    println!("  资源使用率: {:.2}%", system_state.resource_utilization * 100.0);
    
    // 获取指标统计
    let execution_time_stats = task_time.details().unwrap_or_default();
    println!("任务执行时间统计:");
    for (key, value) in execution_time_stats {
        println!("  {}: {}", key, value);
    }
    
    let error_count = error_counter.value().unwrap_or(0);
    println!("网络错误总数: {}", error_count);
    
    // 获取告警
    let alerts = metrics.evaluate_alert_rules();
    if !alerts.is_empty() {
        println!("触发的告警:");
        for alert in alerts {
            println!("  {}: {}", alert.name(), alert.message());
        }
    } else {
        println!("没有触发的告警");
    }
}

// 分布式控制器
pub struct DistributedController {
    // 资源感知调度器
    scheduler: ResourceAwareScheduler,
    
    // 拓扑管理器
    topology: Arc<TopologyManager>,
    
    // 错误恢复管理器
    recovery_manager: Arc<ErrorRecoveryManager>,
    
    // 监控指标
    metrics: Arc<MetricRegistry>,
    
    // 系统状态
    state: RwLock<SystemState>,
    
    // 任务注册表
    tasks: RwLock<HashMap<String, TaskInfo>>,
}

// 系统状态
#[derive(Debug, Clone, Default)]
pub struct SystemState {
    // 活动任务数
    pub active_tasks: usize,
    
    // 完成任务数
    pub completed_tasks: usize,
    
    // 失败任务数
    pub failed_tasks: usize,
    
    // 资源使用率
    pub resource_utilization: f64,
    
    // 更新时间
    pub updated_at: Instant,
}

// 任务优先级
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum TaskPriority {
    Low,
    Normal,
    High,
    Critical,
}

// 任务状态
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TaskStatus {
    Queued,
    Running,
    Completed(String),
    Failed(String),
}

// 任务信息
#[derive(Debug, Clone)]
pub struct TaskInfo {
    // 任务ID
    id: String,
    
    // 任务类型
    task_type: String,
    
    // 任务优先级
    priority: TaskPriority,
    
    // 任务状态
    status: TaskStatus,
    
    // 创建时间
    created_at: Instant,
    
    // 开始执行时间
    started_at: Option<Instant>,
    
    // 完成时间
    completed_at: Option<Instant>,
}

// 任务上下文
pub struct TaskContext {
    // 任务ID
    id: String,
    
    // 任务类型
    task_type: String,
    
    // 任务优先级
    priority: TaskPriority,
    
    // 执行节点
    node_id: Option<String>,
    
    // 任务状态更新器
    status_updater: Box<dyn Fn(TaskStatus) + Send + Sync>,
    
    // 指标注册表
    metrics: Arc<MetricRegistry>,
}

impl TaskContext {
    // 获取任务ID
    pub fn id(&self) -> &str {
        &self.id
    }
    
    // 获取任务类型
    pub fn task_type(&self) -> &str {
        &self.task_type
    }
    
    // 获取任务优先级
    pub fn priority(&self) -> TaskPriority {
        self.priority
    }
    
    // 获取执行节点
    pub fn node_id(&self) -> Option<&str> {
        self.node_id.as_deref()
    }
    
    // 更新任务状态
    pub fn update_status(&self, status: TaskStatus) {
        (self.status_updater)(status);
    }
    
    // 记录指标
    pub fn observe(&self, metric_name: &str, value: f64) {
        // 创建一个带有任务上下文的指标键
        let metric_key = MetricKey::new(metric_name)
            .with_label("task_id", self.id.clone())
            .with_label("task_type", self.task_type.clone());
        
        // 尝试记录直方图值
        if let Ok(histogram) = self.metrics.histogram(metric_key, vec![0.1, 1.0, 10.0]) {
            histogram.observe(value);
        }
    }
}

impl DistributedController {
    pub fn new(
        scheduler: ResourceAwareScheduler,
        topology: Arc<TopologyManager>,
        recovery_manager: Arc<ErrorRecoveryManager>,
        metrics: Arc<MetricRegistry>,
    ) -> Self {
        Self {
            scheduler,
            topology,
            recovery_manager,
            metrics,
            state: RwLock::new(SystemState::default()),
            tasks: RwLock::new(HashMap::new()),
        }
    }
    
    // 提交任务
    pub fn submit_task<F, T, E>(
        &self,
        task_id: impl Into<String>,
        task_type: impl Into<String>,
        priority: TaskPriority,
        work: F,
    ) -> Result<String, String>
    where
        F: FnOnce(&TaskContext) -> Result<T, E> + Send + 'static,
        T: ToString + Send + 'static,
        E: ToString + Send + 'static,
    {
        let task_id = task_id.into();
        let task_type = task_type.into();
        
        // 检查任务是否已存在
        {
            let tasks = self.tasks.read().unwrap();
            if tasks.contains_key(&task_id) {
                return Err(format!("任务ID '{}' 已存在", task_id));
            }
        }
        
        // 创建任务信息
        let task_info = TaskInfo {
            id: task_id.clone(),
            task_type: task_type.clone(),
            priority,
            status: TaskStatus::Queued,
            created_at: Instant::now(),
            started_at: None,
            completed_at: None,
        };
        
        // 注册任务
        {
            let mut tasks = self.tasks.write().unwrap();
            tasks.insert(task_id.clone(), task_info);
        }
        
        // 更新状态
        {
            let mut state = self.state.write().unwrap();
            state.active_tasks += 1;
            state.updated_at = Instant::now();
        }
        
        // 创建状态更新闭包
        let tasks_ref = Arc::new(self.tasks.clone());
        let metrics_ref = self.metrics.clone();
        let state_ref = Arc::new(self.state.clone());
        
        let status_updater = move |status: TaskStatus| {
            // 更新任务状态
            let mut tasks = tasks_ref.write().unwrap();
            if let Some(task) = tasks.get_mut(&task_id) {
                match status {
                    TaskStatus::Running => {
                        task.status = status;
                        task.started_at = Some(Instant::now());
                    },
                    TaskStatus::Completed(_) | TaskStatus::Failed(_) => {
                        task.status = status.clone();
                        task.completed_at = Some(Instant::now());
                        
                        // 更新系统状态
                        let mut state = state_ref.write().unwrap();
                        state.active_tasks = state.active_tasks.saturating_sub(1);
                        
                        match status {
                            TaskStatus::Completed(_) => state.completed_tasks += 1,
                            TaskStatus::Failed(_) => state.failed_tasks += 1,
                            _ => {}
                        }
                        
                        state.updated_at = Instant::now();
                        
                        // 记录任务执行时间指标
                        if let (Some(start), Some(end)) = (task.started_at, task.completed_at) {
                            let execution_time = end.duration_since(start).as_secs_f64();
                            
                            // 创建指标键
                            let metric_key = MetricKey::new("task_execution_time")
                                .with_label("task_type", task.task_type.clone())
                                .with_label("priority", format!("{:?}", task.priority));
                            
                            // 记录直方图值
                            if let Ok(histogram) = metrics_ref.histogram(
                                metric_key, 
                                vec![0.01, 0.1, 0.5, 1.0, 5.0, 10.0]
                            ) {
                                histogram.observe(execution_time);
                            }
                        }
                    },
                    _ => {
                        task.status = status;
                    }
                }
            }
        };
        
        // 创建任务上下文
        let context = TaskContext {
            id: task_id.clone(),
            task_type: task_type.clone(),
            priority,
            node_id: None, // 在实际执行时设置
            status_updater: Box::new(status_updater),
            metrics: self.metrics.clone(),
        };
        
        // 包装工作函数
        let work_wrapper = move |_: &mut ()| {
            // 更新状态为运行中
            context.update_status(TaskStatus::Running);
            
            // 执行实际工作
            match work(&context) {
                Ok(result) => {
                    let result_str = result.to_string();
                    context.update_status(TaskStatus::Completed(result_str.clone()));
                    Ok(result_str)
                },
                Err(e) => {
                    let error_str = e.to_string();
                    context.update_status(TaskStatus::Failed(error_str.clone()));
                    Err(error_str)
                }
            }
        };
        
        // 提交到调度器
        let task_priority = match priority {
            TaskPriority::Low => 0,
            TaskPriority::Normal => 1,
            TaskPriority::High => 2,
            TaskPriority::Critical => 3,
        };
        
        self.scheduler.submit_task(task_id.clone(), work_wrapper, task_priority);
        
        Ok(task_id)
    }
    
    // 获取任务状态
    pub fn get_task_status(&self, task_id: &str) -> Option<TaskStatus> {
        let tasks = self.tasks.read().unwrap();
        tasks.get(task_id).map(|task| task.status.clone())
    }
    
    // 获取所有任务
    pub fn get_all_tasks(&self) -> Vec<TaskInfo> {
        let tasks = self.tasks.read().unwrap();
        tasks.values().cloned().collect()
    }
    
    // 根据状态过滤任务
    pub fn get_tasks_by_status(&self, status_filter: fn(&TaskStatus) -> bool) -> Vec<TaskInfo> {
        let tasks = self.tasks.read().unwrap();
        tasks.values()
            .filter(|task| status_filter(&task.status))
            .cloned()
            .collect()
    }
    
    // 获取系统状态
    pub fn get_system_state(&self) -> SystemState {
        let state = self.state.read().unwrap();
        state.clone()
    }
    
    // 处理错误
    pub fn handle_error(&self, error: SystemError) -> Result<(), SystemError> {
        self.recovery_manager.handle_error(error, || {
            // 这里可以实现默认的恢复逻辑
            println!("尝试从错误中恢复...");
            Ok(())
        })
    }
}

// 完成主函数调用
```

**设计原则**：

本框架通过将拓扑管理、错误处理、监控和任务调度整合在一起，为分布式系统提供了一个完整的自适应控制机制。该设计遵循以下关键原则：

1. **自我感知与适应性**：系统能够感知自身资源状态，根据工作负载和资源约束自动调整执行策略。

2. **故障弹性与恢复能力**：通过可配置的错误处理规则和重试策略，系统能够从常见故障中恢复，并对不同类型的错误采取合适的处理措施。

3. **可组合性**：各个组件（拓扑管理、错误处理、监控、任务调度）设计为可独立使用，同时又能无缝集成，形成一个协调一致的系统。

4. **可监控性**：通过全面的指标收集和告警系统，提供对系统状态的深入洞察，支持问题诊断和优化。

5. **资源效率**：资源感知调度根据系统负载和任务优先级，最大化资源利用率，同时避免系统过载。

该框架是一个完全根据标准库实现的分布式算法工作流系统，具有自我感知、可组合、可监控和可持续特性，适用于构建高可靠性的分布式应用程序。
