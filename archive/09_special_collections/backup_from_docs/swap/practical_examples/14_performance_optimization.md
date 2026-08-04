# C07-14. 性能优化实战示例 (Rust 1.90 增强版)

## 目录

- [C07-14. 性能优化实战示例 (Rust 1.90 增强版)](#c07-14-性能优化实战示例-rust-190-增强版)
  - [目录](#目录)
  - [1. 进程启动优化](#1-进程启动优化)
    - [1.1 进程启动优化器](#11-进程启动优化器)
  - [2. 内存使用优化](#2-内存使用优化)
    - [2.1 内存池管理器](#21-内存池管理器)
  - [3. CPU 使用优化](#3-cpu-使用优化)
    - [3.1 CPU 负载均衡器](#31-cpu-负载均衡器)
  - [4. I/O 性能优化](#4-io-性能优化)
    - [4.1 I/O 优化器](#41-io-优化器)
  - [5. 并发性能优化](#5-并发性能优化)
    - [5.1 并发优化器](#51-并发优化器)
  - [6. 缓存优化策略](#6-缓存优化策略)
    - [6.1 多级缓存系统](#61-多级缓存系统)
  - [总结](#总结)

本章提供性能优化实战示例，涵盖进程启动、内存使用、CPU 使用、I/O 性能、并发性能和缓存优化等方面。

## 1. 进程启动优化

### 1.1 进程启动优化器

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

// 进程启动优化器
pub struct ProcessStartupOptimizer {
    startup_cache: Arc<RwLock<HashMap<String, CachedProcess>>>,
    preloader: Arc<ProcessPreloader>,
    config: StartupConfig,
}

#[derive(Debug, Clone)]
pub struct StartupConfig {
    pub max_cached_processes: usize,
    pub cache_ttl: Duration,
    pub preload_enabled: bool,
    pub preload_count: usize,
    pub warmup_timeout: Duration,
}

#[derive(Debug)]
pub struct CachedProcess {
    pub command: String,
    pub args: Vec<String>,
    pub process: std::process::Child,
    pub created_at: Instant,
    pub last_used: Instant,
    pub usage_count: u64,
    pub startup_time: Duration,
}

impl ProcessStartupOptimizer {
    pub fn new(config: StartupConfig) -> Self {
        Self {
            startup_cache: Arc::new(RwLock::new(HashMap::new())),
            preloader: Arc::new(ProcessPreloader::new()),
            config,
        }
    }

    // 优化进程启动
    pub async fn optimized_spawn(
        &self,
        command: String,
        args: Vec<String>,
    ) -> Result<std::process::Child, StartupError> {
        let cache_key = format!("{}:{}", command, args.join(" "));
        
        // 检查缓存
        if let Some(cached_process) = self.get_cached_process(&cache_key).await {
            return Ok(cached_process);
        }

        // 启动新进程
        let start_time = Instant::now();
        let child = self.spawn_process(&command, &args).await?;
        let startup_time = start_time.elapsed();

        // 缓存进程
        self.cache_process(cache_key, command, args, child, startup_time).await;

        Ok(child)
    }

    // 获取缓存的进程
    async fn get_cached_process(&self, cache_key: &str) -> Option<std::process::Child> {
        let mut cache = self.startup_cache.write().await;
        
        if let Some(cached_process) = cache.get_mut(cache_key) {
            // 检查是否过期
            if cached_process.created_at.elapsed() > self.config.cache_ttl {
                cache.remove(cache_key);
                return None;
            }

            cached_process.last_used = Instant::now();
            cached_process.usage_count += 1;

            // 返回进程的克隆
            cached_process.process.try_clone().ok()
        } else {
            None
        }
    }

    // 缓存进程
    async fn cache_process(
        &self,
        cache_key: String,
        command: String,
        args: Vec<String>,
        mut process: std::process::Child,
        startup_time: Duration,
    ) {
        let cached_process = CachedProcess {
            command,
            args,
            process,
            created_at: Instant::now(),
            last_used: Instant::now(),
            usage_count: 1,
            startup_time,
        };

        let mut cache = self.startup_cache.write().await;
        
        // 检查缓存大小限制
        if cache.len() >= self.config.max_cached_processes {
            // 移除最久未使用的进程
            let oldest_key = cache.iter()
                .min_by_key(|(_, p)| p.last_used)
                .map(|(k, _)| k.clone());
            
            if let Some(key) = oldest_key {
                cache.remove(&key);
            }
        }

        cache.insert(cache_key, cached_process);
    }

    // 启动进程
    async fn spawn_process(
        &self,
        command: &str,
        args: &[String],
    ) -> Result<std::process::Child, StartupError> {
        let mut cmd = std::process::Command::new(command);
        cmd.args(args);
        cmd.stdout(std::process::Stdio::piped());
        cmd.stderr(std::process::Stdio::piped());

        // 优化进程启动参数
        self.optimize_command(&mut cmd);

        let child = cmd.spawn()
            .map_err(|e| StartupError::SpawnFailed(e.to_string()))?;

        Ok(child)
    }

    // 优化命令参数
    fn optimize_command(&self, cmd: &mut std::process::Command) {
        // 设置环境变量优化
        cmd.env("RUST_LOG", "warn");
        cmd.env("RUST_BACKTRACE", "0");
        
        // 设置进程优先级
        #[cfg(unix)]
        {
            use std::os::unix::process::CommandExt;
            cmd.process_group(0);
        }
    }

    // 预热进程
    pub async fn warmup_processes(&self, commands: Vec<(String, Vec<String>)>) -> Result<(), StartupError> {
        if !self.config.preload_enabled {
            return Ok(());
        }

        let mut handles = Vec::new();
        
        for (command, args) in commands.into_iter().take(self.config.preload_count) {
            let optimizer = self.clone();
            let handle = tokio::spawn(async move {
                optimizer.optimized_spawn(command, args).await
            });
            handles.push(handle);
        }

        // 等待所有预热进程完成
        for handle in handles {
            let _ = handle.await;
        }

        Ok(())
    }

    // 获取启动统计
    pub async fn get_startup_stats(&self) -> StartupStats {
        let cache = self.startup_cache.read().await;
        
        let total_cached = cache.len();
        let total_usage: u64 = cache.values().map(|p| p.usage_count).sum();
        let average_startup_time: Duration = if total_cached > 0 {
            let total_time: Duration = cache.values().map(|p| p.startup_time).sum();
            Duration::from_nanos(total_time.as_nanos() as u64 / total_cached as u64)
        } else {
            Duration::ZERO
        };

        StartupStats {
            total_cached_processes: total_cached,
            total_usage_count: total_usage,
            average_startup_time,
            cache_hit_rate: if total_usage > 0 {
                cache.values().filter(|p| p.usage_count > 1).count() as f64 / total_cached as f64
            } else {
                0.0
            },
        }
    }
}

// 进程预加载器
pub struct ProcessPreloader {
    preloaded_processes: Arc<Mutex<Vec<PreloadedProcess>>>,
}

#[derive(Debug)]
pub struct PreloadedProcess {
    pub command: String,
    pub args: Vec<String>,
    pub process: std::process::Child,
    pub created_at: Instant,
}

impl ProcessPreloader {
    pub fn new() -> Self {
        Self {
            preloaded_processes: Arc::new(Mutex::new(Vec::new())),
        }
    }

    pub async fn preload_process(
        &self,
        command: String,
        args: Vec<String>,
    ) -> Result<(), StartupError> {
        let mut cmd = std::process::Command::new(&command);
        cmd.args(&args);
        cmd.stdout(std::process::Stdio::piped());
        cmd.stderr(std::process::Stdio::piped());

        let child = cmd.spawn()
            .map_err(|e| StartupError::SpawnFailed(e.to_string()))?;

        let preloaded_process = PreloadedProcess {
            command,
            args,
            process: child,
            created_at: Instant::now(),
        };

        {
            let mut processes = self.preloaded_processes.lock().unwrap();
            processes.push(preloaded_process);
        }

        Ok(())
    }
}

#[derive(Debug)]
pub struct StartupStats {
    pub total_cached_processes: usize,
    pub total_usage_count: u64,
    pub average_startup_time: Duration,
    pub cache_hit_rate: f64,
}

#[derive(Debug, thiserror::Error)]
pub enum StartupError {
    #[error("进程启动失败: {0}")]
    SpawnFailed(String),
    
    #[error("缓存操作失败: {0}")]
    CacheOperationFailed(String),
    
    #[error("预热失败: {0}")]
    WarmupFailed(String),
}
```

## 2. 内存使用优化

### 2.1 内存池管理器

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

// 内存池管理器
pub struct MemoryPoolManager {
    pools: Arc<RwLock<HashMap<String, MemoryPool>>>,
    config: MemoryConfig,
    allocator: Arc<MemoryAllocator>,
}

#[derive(Debug, Clone)]
pub struct MemoryConfig {
    pub max_pool_size: usize,
    pub default_chunk_size: usize,
    pub cleanup_interval: Duration,
    pub auto_cleanup: bool,
    pub memory_limit: usize,
}

#[derive(Debug)]
pub struct MemoryPool {
    pub name: String,
    pub chunk_size: usize,
    pub total_chunks: usize,
    pub available_chunks: usize,
    pub allocated_chunks: usize,
    pub chunks: Vec<MemoryChunk>,
    pub created_at: Instant,
    pub last_accessed: Instant,
}

#[derive(Debug)]
pub struct MemoryChunk {
    pub id: String,
    pub data: Vec<u8>,
    pub in_use: bool,
    pub allocated_at: Option<Instant>,
    pub last_used: Option<Instant>,
}

impl MemoryPoolManager {
    pub fn new(config: MemoryConfig) -> Self {
        let manager = Self {
            pools: Arc::new(RwLock::new(HashMap::new())),
            config,
            allocator: Arc::new(MemoryAllocator::new()),
        };

        // 启动自动清理
        if config.auto_cleanup {
            manager.start_cleanup_task();
        }

        manager
    }

    // 创建内存池
    pub async fn create_pool(
        &self,
        name: String,
        chunk_size: Option<usize>,
        initial_chunks: Option<usize>,
    ) -> Result<(), MemoryError> {
        let chunk_size = chunk_size.unwrap_or(self.config.default_chunk_size);
        let initial_chunks = initial_chunks.unwrap_or(10);

        let mut chunks = Vec::new();
        for i in 0..initial_chunks {
            let chunk = MemoryChunk {
                id: format!("{}-{}", name, i),
                data: vec![0; chunk_size],
                in_use: false,
                allocated_at: None,
                last_used: None,
            };
            chunks.push(chunk);
        }

        let pool = MemoryPool {
            name: name.clone(),
            chunk_size,
            total_chunks: initial_chunks,
            available_chunks: initial_chunks,
            allocated_chunks: 0,
            chunks,
            created_at: Instant::now(),
            last_accessed: Instant::now(),
        };

        {
            let mut pools = self.pools.write().await;
            pools.insert(name, pool);
        }

        Ok(())
    }

    // 分配内存
    pub async fn allocate(
        &self,
        pool_name: &str,
        size: Option<usize>,
    ) -> Result<MemoryHandle, MemoryError> {
        let mut pools = self.pools.write().await;
        
        if let Some(pool) = pools.get_mut(pool_name) {
            pool.last_accessed = Instant::now();

            // 查找可用的块
            if let Some(chunk_index) = pool.chunks.iter().position(|c| !c.in_use) {
                let chunk = &mut pool.chunks[chunk_index];
                chunk.in_use = true;
                chunk.allocated_at = Some(Instant::now());
                chunk.last_used = Some(Instant::now());

                pool.available_chunks -= 1;
                pool.allocated_chunks += 1;

                Ok(MemoryHandle {
                    pool_name: pool_name.to_string(),
                    chunk_id: chunk.id.clone(),
                    data: chunk.data.as_mut_ptr(),
                    size: chunk.data.len(),
                })
            } else {
                // 扩展池
                self.expand_pool(pool, 1).await?;
                
                // 重试分配
                let chunk_index = pool.chunks.len() - 1;
                let chunk = &mut pool.chunks[chunk_index];
                chunk.in_use = true;
                chunk.allocated_at = Some(Instant::now());
                chunk.last_used = Some(Instant::now());

                pool.available_chunks -= 1;
                pool.allocated_chunks += 1;

                Ok(MemoryHandle {
                    pool_name: pool_name.to_string(),
                    chunk_id: chunk.id.clone(),
                    data: chunk.data.as_mut_ptr(),
                    size: chunk.data.len(),
                })
            }
        } else {
            Err(MemoryError::PoolNotFound(pool_name.to_string()))
        }
    }

    // 释放内存
    pub async fn deallocate(&self, handle: MemoryHandle) -> Result<(), MemoryError> {
        let mut pools = self.pools.write().await;
        
        if let Some(pool) = pools.get_mut(&handle.pool_name) {
            if let Some(chunk) = pool.chunks.iter_mut().find(|c| c.id == handle.chunk_id) {
                chunk.in_use = false;
                chunk.allocated_at = None;
                chunk.last_used = Some(Instant::now());

                pool.available_chunks += 1;
                pool.allocated_chunks -= 1;
            }
        }

        Ok(())
    }

    // 扩展内存池
    async fn expand_pool(&self, pool: &mut MemoryPool, additional_chunks: usize) -> Result<(), MemoryError> {
        for i in 0..additional_chunks {
            let chunk = MemoryChunk {
                id: format!("{}-{}", pool.name, pool.total_chunks + i),
                data: vec![0; pool.chunk_size],
                in_use: false,
                allocated_at: None,
                last_used: None,
            };
            pool.chunks.push(chunk);
        }

        pool.total_chunks += additional_chunks;
        pool.available_chunks += additional_chunks;

        Ok(())
    }

    // 获取内存统计
    pub async fn get_memory_stats(&self) -> MemoryStats {
        let pools = self.pools.read().await;
        
        let total_pools = pools.len();
        let total_chunks: usize = pools.values().map(|p| p.total_chunks).sum();
        let allocated_chunks: usize = pools.values().map(|p| p.allocated_chunks).sum();
        let available_chunks: usize = pools.values().map(|p| p.available_chunks).sum();
        let total_memory: usize = pools.values().map(|p| p.total_chunks * p.chunk_size).sum();
        let allocated_memory: usize = pools.values().map(|p| p.allocated_chunks * p.chunk_size).sum();

        MemoryStats {
            total_pools,
            total_chunks,
            allocated_chunks,
            available_chunks,
            total_memory,
            allocated_memory,
            utilization_rate: if total_memory > 0 {
                allocated_memory as f64 / total_memory as f64
            } else {
                0.0
            },
        }
    }

    // 启动清理任务
    fn start_cleanup_task(&self) {
        let pools = self.pools.clone();
        let config = self.config.clone();

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(config.cleanup_interval);
            
            loop {
                interval.tick().await;
                
                let mut pools_guard = pools.write().await;
                let now = Instant::now();
                
                // 清理长时间未使用的块
                for pool in pools_guard.values_mut() {
                    for chunk in &mut pool.chunks {
                        if !chunk.in_use {
                            if let Some(last_used) = chunk.last_used {
                                if now.duration_since(last_used) > Duration::from_secs(3600) {
                                    // 重置块
                                    chunk.data.fill(0);
                                }
                            }
                        }
                    }
                }
            }
        });
    }
}

// 内存句柄
pub struct MemoryHandle {
    pub pool_name: String,
    pub chunk_id: String,
    pub data: *mut u8,
    pub size: usize,
}

unsafe impl Send for MemoryHandle {}
unsafe impl Sync for MemoryHandle {}

impl Drop for MemoryHandle {
    fn drop(&mut self) {
        // 在实际实现中，这里会调用 deallocate
        // 为了简化示例，这里只是标记
    }
}

// 内存分配器
pub struct MemoryAllocator {
    allocated_memory: Arc<Mutex<usize>>,
    allocation_count: Arc<Mutex<u64>>,
}

impl MemoryAllocator {
    pub fn new() -> Self {
        Self {
            allocated_memory: Arc::new(Mutex::new(0)),
            allocation_count: Arc::new(Mutex::new(0)),
        }
    }

    pub fn allocate(&self, size: usize) -> Result<*mut u8, MemoryError> {
        let mut allocated = self.allocated_memory.lock().unwrap();
        let mut count = self.allocation_count.lock().unwrap();

        *allocated += size;
        *count += 1;

        // 实际的内存分配
        let ptr = unsafe { std::alloc::alloc(std::alloc::Layout::from_size_align(size, 8).unwrap()) };
        
        if ptr.is_null() {
            Err(MemoryError::AllocationFailed)
        } else {
            Ok(ptr)
        }
    }

    pub fn deallocate(&self, ptr: *mut u8, size: usize) {
        let mut allocated = self.allocated_memory.lock().unwrap();
        *allocated -= size;

        unsafe {
            std::alloc::dealloc(ptr, std::alloc::Layout::from_size_align(size, 8).unwrap());
        }
    }
}

#[derive(Debug)]
pub struct MemoryStats {
    pub total_pools: usize,
    pub total_chunks: usize,
    pub allocated_chunks: usize,
    pub available_chunks: usize,
    pub total_memory: usize,
    pub allocated_memory: usize,
    pub utilization_rate: f64,
}

#[derive(Debug, thiserror::Error)]
pub enum MemoryError {
    #[error("内存池未找到: {0}")]
    PoolNotFound(String),
    
    #[error("内存分配失败")]
    AllocationFailed,
    
    #[error("内存不足")]
    OutOfMemory,
    
    #[error("操作失败: {0}")]
    OperationFailed(String),
}
```

## 3. CPU 使用优化

### 3.1 CPU 负载均衡器

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

// CPU 负载均衡器
pub struct CPULoadBalancer {
    workers: Arc<RwLock<HashMap<String, CPUWorker>>>,
    task_queue: Arc<Mutex<VecDeque<CPUTask>>>,
    config: CPUConfig,
}

#[derive(Debug, Clone)]
pub struct CPUConfig {
    pub max_workers: usize,
    pub cpu_threshold: f64,
    pub load_check_interval: Duration,
    pub auto_scaling: bool,
    pub scaling_factor: f64,
}

#[derive(Debug)]
pub struct CPUWorker {
    pub id: String,
    pub cpu_usage: f64,
    pub memory_usage: u64,
    pub active_tasks: u32,
    pub completed_tasks: u64,
    pub failed_tasks: u64,
    pub last_activity: Instant,
    pub status: WorkerStatus,
}

#[derive(Debug, Clone)]
pub enum WorkerStatus {
    Idle,
    Busy,
    Overloaded,
    Offline,
}

#[derive(Debug)]
pub struct CPUTask {
    pub id: String,
    pub priority: TaskPriority,
    pub estimated_cpu_time: Duration,
    pub data: Vec<u8>,
    pub created_at: Instant,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum TaskPriority {
    Low = 1,
    Normal = 2,
    High = 3,
    Critical = 4,
}

impl CPULoadBalancer {
    pub fn new(config: CPUConfig) -> Self {
        Self {
            workers: Arc::new(RwLock::new(HashMap::new())),
            task_queue: Arc::new(Mutex::new(VecDeque::new())),
            config,
        }
    }

    // 添加工作节点
    pub async fn add_worker(&self, worker_id: String) -> Result<(), CPULoadError> {
        let worker = CPUWorker {
            id: worker_id.clone(),
            cpu_usage: 0.0,
            memory_usage: 0,
            active_tasks: 0,
            completed_tasks: 0,
            failed_tasks: 0,
            last_activity: Instant::now(),
            status: WorkerStatus::Idle,
        };

        {
            let mut workers = self.workers.write().await;
            if workers.len() >= self.config.max_workers {
                return Err(CPULoadError::MaxWorkersExceeded);
            }
            workers.insert(worker_id, worker);
        }

        // 启动工作节点监控
        self.start_worker_monitoring(worker_id).await;

        Ok(())
    }

    // 提交任务
    pub async fn submit_task(&self, task: CPUTask) -> Result<String, CPULoadError> {
        let task_id = task.id.clone();
        
        {
            let mut queue = self.task_queue.lock().unwrap();
            queue.push_back(task);
        }

        // 尝试分配任务
        self.schedule_tasks().await?;

        Ok(task_id)
    }

    // 调度任务
    pub async fn schedule_tasks(&self) -> Result<(), CPULoadError> {
        let mut queue = self.task_queue.lock().unwrap();
        let mut workers = self.workers.write().await;

        while let Some(task) = queue.pop_front() {
            // 选择最佳工作节点
            if let Some(worker_id) = self.select_best_worker(&workers) {
                if let Some(worker) = workers.get_mut(&worker_id) {
                    worker.active_tasks += 1;
                    worker.status = WorkerStatus::Busy;
                    worker.last_activity = Instant::now();

                    // 异步执行任务
                    let workers_clone = self.workers.clone();
                    let worker_id_clone = worker_id.clone();
                    tokio::spawn(async move {
                        Self::execute_task(workers_clone, worker_id_clone, task).await;
                    });
                }
            } else {
                // 没有可用工作节点，重新加入队列
                queue.push_front(task);
                break;
            }
        }

        Ok(())
    }

    // 选择最佳工作节点
    fn select_best_worker(&self, workers: &HashMap<String, CPUWorker>) -> Option<String> {
        let mut best_worker = None;
        let mut best_score = f64::MAX;

        for (worker_id, worker) in workers {
            if matches!(worker.status, WorkerStatus::Idle | WorkerStatus::Busy) {
                // 计算负载分数（CPU使用率 + 任务数量权重）
                let cpu_score = worker.cpu_usage;
                let task_score = worker.active_tasks as f64 * 10.0;
                let total_score = cpu_score + task_score;

                if total_score < best_score {
                    best_score = total_score;
                    best_worker = Some(worker_id.clone());
                }
            }
        }

        best_worker
    }

    // 执行任务
    async fn execute_task(
        workers: Arc<RwLock<HashMap<String, CPUWorker>>>,
        worker_id: String,
        task: CPUTask,
    ) {
        // 模拟任务执行
        tokio::time::sleep(task.estimated_cpu_time).await;

        // 更新工作节点状态
        {
            let mut workers = workers.write().await;
            if let Some(worker) = workers.get_mut(&worker_id) {
                worker.active_tasks -= 1;
                worker.completed_tasks += 1;
                worker.last_activity = Instant::now();

                if worker.active_tasks == 0 {
                    worker.status = WorkerStatus::Idle;
                }
            }
        }
    }

    // 启动工作节点监控
    async fn start_worker_monitoring(&self, worker_id: String) {
        let workers = self.workers.clone();
        let config = self.config.clone();

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(config.load_check_interval);
            
            loop {
                interval.tick().await;
                
                let mut workers_guard = workers.write().await;
                if let Some(worker) = workers_guard.get_mut(&worker_id) {
                    // 更新CPU使用率
                    worker.cpu_usage = Self::get_cpu_usage().await;
                    
                    // 更新工作节点状态
                    if worker.cpu_usage > config.cpu_threshold {
                        worker.status = WorkerStatus::Overloaded;
                    } else if worker.active_tasks == 0 {
                        worker.status = WorkerStatus::Idle;
                    } else {
                        worker.status = WorkerStatus::Busy;
                    }
                } else {
                    break;
                }
            }
        });
    }

    // 获取CPU使用率
    async fn get_cpu_usage() -> f64 {
        // 模拟CPU使用率获取
        tokio::time::sleep(Duration::from_millis(10)).await;
        25.0 // 模拟25%的CPU使用率
    }

    // 自动扩缩容
    pub async fn auto_scale(&self) -> Result<(), CPULoadError> {
        if !self.config.auto_scaling {
            return Ok(());
        }

        let workers = self.workers.read().await;
        let queue = self.task_queue.lock().unwrap();

        let total_cpu_usage: f64 = workers.values().map(|w| w.cpu_usage).sum();
        let average_cpu_usage = total_cpu_usage / workers.len() as f64;
        let pending_tasks = queue.len();

        // 扩容条件：平均CPU使用率超过阈值且有待处理任务
        if average_cpu_usage > self.config.cpu_threshold && pending_tasks > 0 {
            let additional_workers = (pending_tasks as f64 * self.config.scaling_factor) as usize;
            
            for i in 0..additional_workers {
                let worker_id = format!("worker-{}", workers.len() + i);
                self.add_worker(worker_id).await?;
            }
        }

        Ok(())
    }

    // 获取负载统计
    pub async fn get_load_stats(&self) -> LoadStats {
        let workers = self.workers.read().await;
        let queue = self.task_queue.lock().unwrap();

        let total_workers = workers.len();
        let idle_workers = workers.values().filter(|w| matches!(w.status, WorkerStatus::Idle)).count();
        let busy_workers = workers.values().filter(|w| matches!(w.status, WorkerStatus::Busy)).count();
        let overloaded_workers = workers.values().filter(|w| matches!(w.status, WorkerStatus::Overloaded)).count();
        
        let total_cpu_usage: f64 = workers.values().map(|w| w.cpu_usage).sum();
        let average_cpu_usage = if total_workers > 0 {
            total_cpu_usage / total_workers as f64
        } else {
            0.0
        };

        let total_tasks: u64 = workers.values().map(|w| w.completed_tasks + w.failed_tasks).sum();
        let completed_tasks: u64 = workers.values().map(|w| w.completed_tasks).sum();
        let failed_tasks: u64 = workers.values().map(|w| w.failed_tasks).sum();

        LoadStats {
            total_workers,
            idle_workers,
            busy_workers,
            overloaded_workers,
            average_cpu_usage,
            pending_tasks: queue.len(),
            total_tasks,
            completed_tasks,
            failed_tasks,
            success_rate: if total_tasks > 0 {
                completed_tasks as f64 / total_tasks as f64
            } else {
                0.0
            },
        }
    }
}

#[derive(Debug)]
pub struct LoadStats {
    pub total_workers: usize,
    pub idle_workers: usize,
    pub busy_workers: usize,
    pub overloaded_workers: usize,
    pub average_cpu_usage: f64,
    pub pending_tasks: usize,
    pub total_tasks: u64,
    pub completed_tasks: u64,
    pub failed_tasks: u64,
    pub success_rate: f64,
}

#[derive(Debug, thiserror::Error)]
pub enum CPULoadError {
    #[error("超过最大工作节点数")]
    MaxWorkersExceeded,
    
    #[error("工作节点未找到: {0}")]
    WorkerNotFound(String),
    
    #[error("任务调度失败: {0}")]
    TaskSchedulingFailed(String),
    
    #[error("负载均衡失败: {0}")]
    LoadBalancingFailed(String),
}
```

## 4. I/O 性能优化

### 4.1 I/O 优化器

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::RwLock;
use tokio::io::{AsyncRead, AsyncWrite};

// I/O 优化器
pub struct IOOptimizer {
    buffers: Arc<RwLock<HashMap<String, IOBuffer>>>,
    config: IOConfig,
    stats: Arc<Mutex<IOStats>>,
}

#[derive(Debug, Clone)]
pub struct IOConfig {
    pub buffer_size: usize,
    pub max_buffers: usize,
    pub flush_interval: Duration,
    pub auto_flush: bool,
    pub compression_enabled: bool,
    pub batch_size: usize,
}

#[derive(Debug)]
pub struct IOBuffer {
    pub id: String,
    pub data: Vec<u8>,
    pub size: usize,
    pub last_write: Instant,
    pub write_count: u64,
    pub read_count: u64,
    pub compression_ratio: f64,
}

#[derive(Debug)]
pub struct IOStats {
    pub total_reads: u64,
    pub total_writes: u64,
    pub total_bytes_read: u64,
    pub total_bytes_written: u64,
    pub average_read_time: Duration,
    pub average_write_time: Duration,
    pub cache_hits: u64,
    pub cache_misses: u64,
}

impl IOOptimizer {
    pub fn new(config: IOConfig) -> Self {
        let optimizer = Self {
            buffers: Arc::new(RwLock::new(HashMap::new())),
            config,
            stats: Arc::new(Mutex::new(IOStats {
                total_reads: 0,
                total_writes: 0,
                total_bytes_read: 0,
                total_bytes_written: 0,
                average_read_time: Duration::ZERO,
                average_write_time: Duration::ZERO,
                cache_hits: 0,
                cache_misses: 0,
            })),
        };

        // 启动自动刷新
        if config.auto_flush {
            optimizer.start_flush_task();
        }

        optimizer
    }

    // 优化读取操作
    pub async fn optimized_read<R: AsyncRead + Unpin>(
        &self,
        reader: &mut R,
        buffer_id: &str,
        size: usize,
    ) -> Result<Vec<u8>, IOError> {
        let start_time = Instant::now();

        // 检查缓冲区
        if let Some(cached_data) = self.get_cached_data(buffer_id, size).await {
            self.update_stats(true, 0, start_time.elapsed());
            return Ok(cached_data);
        }

        // 执行实际读取
        let mut buffer = vec![0; size];
        let bytes_read = reader.read(&mut buffer).await
            .map_err(|e| IOError::ReadFailed(e.to_string()))?;

        buffer.truncate(bytes_read);

        // 缓存数据
        self.cache_data(buffer_id, buffer.clone()).await;

        // 更新统计
        self.update_stats(false, bytes_read, start_time.elapsed());

        Ok(buffer)
    }

    // 优化写入操作
    pub async fn optimized_write<W: AsyncWrite + Unpin>(
        &self,
        writer: &mut W,
        buffer_id: &str,
        data: &[u8],
    ) -> Result<usize, IOError> {
        let start_time = Instant::now();

        // 批量写入
        let written = if data.len() > self.config.batch_size {
            self.batch_write(writer, data).await?
        } else {
            writer.write(data).await
                .map_err(|e| IOError::WriteFailed(e.to_string()))?
        };

        // 缓存数据
        self.cache_data(buffer_id, data.to_vec()).await;

        // 更新统计
        self.update_stats(false, written, start_time.elapsed());

        Ok(written)
    }

    // 批量写入
    async fn batch_write<W: AsyncWrite + Unpin>(
        &self,
        writer: &mut W,
        data: &[u8],
    ) -> Result<usize, IOError> {
        let mut total_written = 0;
        let chunk_size = self.config.batch_size;

        for chunk in data.chunks(chunk_size) {
            let written = writer.write(chunk).await
                .map_err(|e| IOError::WriteFailed(e.to_string()))?;
            total_written += written;
        }

        writer.flush().await
            .map_err(|e| IOError::FlushFailed(e.to_string()))?;

        Ok(total_written)
    }

    // 获取缓存数据
    async fn get_cached_data(&self, buffer_id: &str, size: usize) -> Option<Vec<u8>> {
        let buffers = self.buffers.read().await;
        
        if let Some(buffer) = buffers.get(buffer_id) {
            if buffer.size >= size {
                Some(buffer.data[..size].to_vec())
            } else {
                None
            }
        } else {
            None
        }
    }

    // 缓存数据
    async fn cache_data(&self, buffer_id: &str, data: Vec<u8>) {
        let buffer = IOBuffer {
            id: buffer_id.to_string(),
            data: data.clone(),
            size: data.len(),
            last_write: Instant::now(),
            write_count: 1,
            read_count: 0,
            compression_ratio: 1.0,
        };

        {
            let mut buffers = self.buffers.write().await;
            
            // 检查缓冲区数量限制
            if buffers.len() >= self.config.max_buffers {
                // 移除最久未使用的缓冲区
                let oldest_key = buffers.iter()
                    .min_by_key(|(_, b)| b.last_write)
                    .map(|(k, _)| k.clone());
                
                if let Some(key) = oldest_key {
                    buffers.remove(&key);
                }
            }

            buffers.insert(buffer_id.to_string(), buffer);
        }
    }

    // 更新统计信息
    fn update_stats(&self, cache_hit: bool, bytes: usize, duration: Duration) {
        let mut stats = self.stats.lock().unwrap();
        
        if cache_hit {
            stats.cache_hits += 1;
        } else {
            stats.cache_misses += 1;
            stats.total_bytes_read += bytes as u64;
        }

        // 更新平均时间
        let total_operations = stats.cache_hits + stats.cache_misses;
        if total_operations > 0 {
            stats.average_read_time = Duration::from_nanos(
                (stats.average_read_time.as_nanos() * (total_operations - 1) as u128 + duration.as_nanos()) / total_operations as u128
            );
        }
    }

    // 启动刷新任务
    fn start_flush_task(&self) {
        let buffers = self.buffers.clone();
        let config = self.config.clone();

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(config.flush_interval);
            
            loop {
                interval.tick().await;
                
                let mut buffers_guard = buffers.write().await;
                let now = Instant::now();
                
                // 清理过期缓冲区
                buffers_guard.retain(|_, buffer| {
                    now.duration_since(buffer.last_write) < Duration::from_secs(300)
                });
            }
        });
    }

    // 获取I/O统计
    pub fn get_io_stats(&self) -> IOStats {
        self.stats.lock().unwrap().clone()
    }

    // 压缩数据
    pub fn compress_data(&self, data: &[u8]) -> Result<Vec<u8>, IOError> {
        if !self.config.compression_enabled {
            return Ok(data.to_vec());
        }

        // 简单的压缩实现（实际应用中会使用更高效的压缩算法）
        let compressed = data.iter()
            .filter(|&&b| b != 0)
            .cloned()
            .collect();

        Ok(compressed)
    }

    // 解压数据
    pub fn decompress_data(&self, compressed_data: &[u8], original_size: usize) -> Result<Vec<u8>, IOError> {
        if !self.config.compression_enabled {
            return Ok(compressed_data.to_vec());
        }

        // 简单的解压实现
        let mut decompressed = vec![0; original_size];
        let mut pos = 0;
        
        for &byte in compressed_data {
            if pos < original_size {
                decompressed[pos] = byte;
                pos += 1;
            }
        }

        Ok(decompressed)
    }
}

#[derive(Debug, Clone)]
pub struct IOStats {
    pub total_reads: u64,
    pub total_writes: u64,
    pub total_bytes_read: u64,
    pub total_bytes_written: u64,
    pub average_read_time: Duration,
    pub average_write_time: Duration,
    pub cache_hits: u64,
    pub cache_misses: u64,
}

#[derive(Debug, thiserror::Error)]
pub enum IOError {
    #[error("读取失败: {0}")]
    ReadFailed(String),
    
    #[error("写入失败: {0}")]
    WriteFailed(String),
    
    #[error("刷新失败: {0}")]
    FlushFailed(String),
    
    #[error("压缩失败: {0}")]
    CompressionFailed(String),
    
    #[error("解压失败: {0}")]
    DecompressionFailed(String),
}
```

## 5. 并发性能优化

### 5.1 并发优化器

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::{RwLock, Semaphore};

// 并发优化器
pub struct ConcurrencyOptimizer {
    thread_pools: Arc<RwLock<HashMap<String, ThreadPool>>>,
    task_scheduler: Arc<TaskScheduler>,
    config: ConcurrencyConfig,
}

#[derive(Debug, Clone)]
pub struct ConcurrencyConfig {
    pub max_thread_pools: usize,
    pub default_pool_size: usize,
    pub max_pool_size: usize,
    pub min_pool_size: usize,
    pub task_timeout: Duration,
    pub auto_scaling: bool,
    pub load_balancing: bool,
}

#[derive(Debug)]
pub struct ThreadPool {
    pub name: String,
    pub size: usize,
    pub active_tasks: u32,
    pub completed_tasks: u64,
    pub failed_tasks: u64,
    pub average_task_time: Duration,
    pub last_activity: Instant,
    pub semaphore: Arc<Semaphore>,
}

impl ConcurrencyOptimizer {
    pub fn new(config: ConcurrencyConfig) -> Self {
        Self {
            thread_pools: Arc::new(RwLock::new(HashMap::new())),
            task_scheduler: Arc::new(TaskScheduler::new()),
            config,
        }
    }

    // 创建线程池
    pub async fn create_thread_pool(
        &self,
        name: String,
        size: Option<usize>,
    ) -> Result<(), ConcurrencyError> {
        let pool_size = size.unwrap_or(self.config.default_pool_size);
        let semaphore = Arc::new(Semaphore::new(pool_size));

        let pool = ThreadPool {
            name: name.clone(),
            size: pool_size,
            active_tasks: 0,
            completed_tasks: 0,
            failed_tasks: 0,
            average_task_time: Duration::ZERO,
            last_activity: Instant::now(),
            semaphore,
        };

        {
            let mut pools = self.thread_pools.write().await;
            if pools.len() >= self.config.max_thread_pools {
                return Err(ConcurrencyError::MaxPoolsExceeded);
            }
            pools.insert(name, pool);
        }

        Ok(())
    }

    // 提交任务
    pub async fn submit_task<F, R>(
        &self,
        pool_name: &str,
        task: F,
    ) -> Result<R, ConcurrencyError>
    where
        F: FnOnce() -> R + Send + 'static,
        R: Send + 'static,
    {
        let pools = self.thread_pools.read().await;
        
        if let Some(pool) = pools.get(pool_name) {
            let semaphore = pool.semaphore.clone();
            let _permit = semaphore.acquire().await
                .map_err(|_| ConcurrencyError::TaskSubmissionFailed)?;

            // 更新池状态
            {
                let mut pools = self.thread_pools.write().await;
                if let Some(pool) = pools.get_mut(pool_name) {
                    pool.active_tasks += 1;
                    pool.last_activity = Instant::now();
                }
            }

            // 执行任务
            let start_time = Instant::now();
            let result = task();
            let task_time = start_time.elapsed();

            // 更新统计
            {
                let mut pools = self.thread_pools.write().await;
                if let Some(pool) = pools.get_mut(pool_name) {
                    pool.active_tasks -= 1;
                    pool.completed_tasks += 1;
                    
                    // 更新平均任务时间
                    let total_tasks = pool.completed_tasks + pool.failed_tasks;
                    if total_tasks > 0 {
                        pool.average_task_time = Duration::from_nanos(
                            (pool.average_task_time.as_nanos() * (total_tasks - 1) as u128 + task_time.as_nanos()) / total_tasks as u128
                        );
                    }
                }
            }

            Ok(result)
        } else {
            Err(ConcurrencyError::PoolNotFound(pool_name.to_string()))
        }
    }

    // 异步提交任务
    pub async fn submit_async_task<F, Fut>(
        &self,
        pool_name: &str,
        task: F,
    ) -> Result<tokio::task::JoinHandle<Result<(), ConcurrencyError>>, ConcurrencyError>
    where
        F: FnOnce() -> Fut + Send + 'static,
        Fut: std::future::Future<Output = Result<(), ConcurrencyError>> + Send + 'static,
    {
        let pools = self.thread_pools.read().await;
        
        if let Some(pool) = pools.get(pool_name) {
            let semaphore = pool.semaphore.clone();
            let pools_clone = self.thread_pools.clone();
            let pool_name = pool_name.to_string();

            let handle = tokio::spawn(async move {
                let _permit = semaphore.acquire().await
                    .map_err(|_| ConcurrencyError::TaskSubmissionFailed)?;

                // 更新池状态
                {
                    let mut pools = pools_clone.write().await;
                    if let Some(pool) = pools.get_mut(&pool_name) {
                        pool.active_tasks += 1;
                        pool.last_activity = Instant::now();
                    }
                }

                // 执行任务
                let start_time = Instant::now();
                let result = task().await;
                let task_time = start_time.elapsed();

                // 更新统计
                {
                    let mut pools = pools_clone.write().await;
                    if let Some(pool) = pools.get_mut(&pool_name) {
                        pool.active_tasks -= 1;
                        
                        match result {
                            Ok(_) => pool.completed_tasks += 1,
                            Err(_) => pool.failed_tasks += 1,
                        }
                        
                        // 更新平均任务时间
                        let total_tasks = pool.completed_tasks + pool.failed_tasks;
                        if total_tasks > 0 {
                            pool.average_task_time = Duration::from_nanos(
                                (pool.average_task_time.as_nanos() * (total_tasks - 1) as u128 + task_time.as_nanos()) / total_tasks as u128
                            );
                        }
                    }
                }

                result
            });

            Ok(handle)
        } else {
            Err(ConcurrencyError::PoolNotFound(pool_name.to_string()))
        }
    }

    // 自动扩缩容
    pub async fn auto_scale(&self) -> Result<(), ConcurrencyError> {
        if !self.config.auto_scaling {
            return Ok(());
        }

        let mut pools = self.thread_pools.write().await;
        
        for pool in pools.values_mut() {
            let utilization = pool.active_tasks as f64 / pool.size as f64;
            
            // 扩容条件：利用率超过80%
            if utilization > 0.8 && pool.size < self.config.max_pool_size {
                pool.size += 1;
                // 在实际实现中，这里会动态调整信号量大小
            }
            // 缩容条件：利用率低于20%且池大小大于最小值
            else if utilization < 0.2 && pool.size > self.config.min_pool_size {
                pool.size -= 1;
            }
        }

        Ok(())
    }

    // 获取并发统计
    pub async fn get_concurrency_stats(&self) -> ConcurrencyStats {
        let pools = self.thread_pools.read().await;
        
        let total_pools = pools.len();
        let total_threads: usize = pools.values().map(|p| p.size).sum();
        let active_threads: u32 = pools.values().map(|p| p.active_tasks).sum();
        let total_tasks: u64 = pools.values().map(|p| p.completed_tasks + p.failed_tasks).sum();
        let completed_tasks: u64 = pools.values().map(|p| p.completed_tasks).sum();
        let failed_tasks: u64 = pools.values().map(|p| p.failed_tasks).sum();
        
        let average_task_time: Duration = if total_tasks > 0 {
            let total_time: Duration = pools.values().map(|p| p.average_task_time).sum();
            Duration::from_nanos(total_time.as_nanos() as u64 / total_tasks as u64)
        } else {
            Duration::ZERO
        };

        ConcurrencyStats {
            total_pools,
            total_threads,
            active_threads,
            total_tasks,
            completed_tasks,
            failed_tasks,
            average_task_time,
            success_rate: if total_tasks > 0 {
                completed_tasks as f64 / total_tasks as f64
            } else {
                0.0
            },
            utilization_rate: if total_threads > 0 {
                active_threads as f64 / total_threads as f64
            } else {
                0.0
            },
        }
    }
}

// 任务调度器
pub struct TaskScheduler {
    // 任务调度器实现
}

impl TaskScheduler {
    pub fn new() -> Self {
        Self {}
    }
}

#[derive(Debug)]
pub struct ConcurrencyStats {
    pub total_pools: usize,
    pub total_threads: usize,
    pub active_threads: u32,
    pub total_tasks: u64,
    pub completed_tasks: u64,
    pub failed_tasks: u64,
    pub average_task_time: Duration,
    pub success_rate: f64,
    pub utilization_rate: f64,
}

#[derive(Debug, thiserror::Error)]
pub enum ConcurrencyError {
    #[error("超过最大线程池数")]
    MaxPoolsExceeded,
    
    #[error("线程池未找到: {0}")]
    PoolNotFound(String),
    
    #[error("任务提交失败")]
    TaskSubmissionFailed,
    
    #[error("任务执行失败: {0}")]
    TaskExecutionFailed(String),
    
    #[error("并发操作失败: {0}")]
    ConcurrencyOperationFailed(String),
}
```

## 6. 缓存优化策略

### 6.1 多级缓存系统

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

// 多级缓存系统
pub struct MultiLevelCache {
    l1_cache: Arc<RwLock<L1Cache>>,
    l2_cache: Arc<RwLock<L2Cache>>,
    l3_cache: Arc<RwLock<L3Cache>>,
    config: CacheConfig,
    stats: Arc<Mutex<CacheStats>>,
}

#[derive(Debug, Clone)]
pub struct CacheConfig {
    pub l1_size: usize,
    pub l2_size: usize,
    pub l3_size: usize,
    pub default_ttl: Duration,
    pub cleanup_interval: Duration,
    pub auto_cleanup: bool,
    pub compression_enabled: bool,
}

#[derive(Debug)]
pub struct L1Cache {
    pub data: HashMap<String, CacheEntry>,
    pub size: usize,
    pub max_size: usize,
}

#[derive(Debug)]
pub struct L2Cache {
    pub data: HashMap<String, CacheEntry>,
    pub size: usize,
    pub max_size: usize,
}

#[derive(Debug)]
pub struct L3Cache {
    pub data: HashMap<String, CacheEntry>,
    pub size: usize,
    pub max_size: usize,
}

#[derive(Debug, Clone)]
pub struct CacheEntry {
    pub key: String,
    pub value: Vec<u8>,
    pub created_at: Instant,
    pub last_accessed: Instant,
    pub access_count: u64,
    pub ttl: Duration,
    pub compressed: bool,
}

impl MultiLevelCache {
    pub fn new(config: CacheConfig) -> Self {
        let cache = Self {
            l1_cache: Arc::new(RwLock::new(L1Cache {
                data: HashMap::new(),
                size: 0,
                max_size: config.l1_size,
            })),
            l2_cache: Arc::new(RwLock::new(L2Cache {
                data: HashMap::new(),
                size: 0,
                max_size: config.l2_size,
            })),
            l3_cache: Arc::new(RwLock::new(L3Cache {
                data: HashMap::new(),
                size: 0,
                max_size: config.l3_size,
            })),
            config,
            stats: Arc::new(Mutex::new(CacheStats {
                l1_hits: 0,
                l2_hits: 0,
                l3_hits: 0,
                misses: 0,
                total_requests: 0,
                evictions: 0,
                compressions: 0,
            })),
        };

        // 启动自动清理
        if config.auto_cleanup {
            cache.start_cleanup_task();
        }

        cache
    }

    // 获取缓存值
    pub async fn get(&self, key: &str) -> Option<Vec<u8>> {
        let mut stats = self.stats.lock().unwrap();
        stats.total_requests += 1;

        // L1 缓存查找
        {
            let mut l1 = self.l1_cache.write().await;
            if let Some(entry) = l1.data.get_mut(key) {
                if !self.is_expired(entry) {
                    entry.last_accessed = Instant::now();
                    entry.access_count += 1;
                    stats.l1_hits += 1;
                    return Some(entry.value.clone());
                } else {
                    l1.data.remove(key);
                    l1.size -= 1;
                }
            }
        }

        // L2 缓存查找
        {
            let mut l2 = self.l2_cache.write().await;
            if let Some(entry) = l2.data.get_mut(key) {
                if !self.is_expired(entry) {
                    entry.last_accessed = Instant::now();
                    entry.access_count += 1;
                    stats.l2_hits += 1;
                    
                    // 提升到 L1 缓存
                    self.promote_to_l1(key, entry.clone()).await;
                    
                    return Some(entry.value.clone());
                } else {
                    l2.data.remove(key);
                    l2.size -= 1;
                }
            }
        }

        // L3 缓存查找
        {
            let mut l3 = self.l3_cache.write().await;
            if let Some(entry) = l3.data.get_mut(key) {
                if !self.is_expired(entry) {
                    entry.last_accessed = Instant::now();
                    entry.access_count += 1;
                    stats.l3_hits += 1;
                    
                    // 提升到 L2 缓存
                    self.promote_to_l2(key, entry.clone()).await;
                    
                    return Some(entry.value.clone());
                } else {
                    l3.data.remove(key);
                    l3.size -= 1;
                }
            }
        }

        stats.misses += 1;
        None
    }

    // 设置缓存值
    pub async fn set(&self, key: String, value: Vec<u8>, ttl: Option<Duration>) -> Result<(), CacheError> {
        let ttl = ttl.unwrap_or(self.config.default_ttl);
        let mut value = value;

        // 压缩数据
        if self.config.compression_enabled && value.len() > 1024 {
            value = self.compress_data(&value)?;
        }

        let entry = CacheEntry {
            key: key.clone(),
            value,
            created_at: Instant::now(),
            last_accessed: Instant::now(),
            access_count: 1,
            ttl,
            compressed: self.config.compression_enabled,
        };

        // 存储到 L1 缓存
        self.store_in_l1(key, entry).await;

        Ok(())
    }

    // 存储到 L1 缓存
    async fn store_in_l1(&self, key: String, entry: CacheEntry) {
        let mut l1 = self.l1_cache.write().await;
        
        // 检查容量
        if l1.size >= l1.max_size {
            self.evict_from_l1(&mut l1).await;
        }

        l1.data.insert(key, entry);
        l1.size += 1;
    }

    // 提升到 L1 缓存
    async fn promote_to_l1(&self, key: &str, entry: CacheEntry) {
        let mut l1 = self.l1_cache.write().await;
        
        // 检查容量
        if l1.size >= l1.max_size {
            self.evict_from_l1(&mut l1).await;
        }

        l1.data.insert(key.to_string(), entry);
        l1.size += 1;
    }

    // 提升到 L2 缓存
    async fn promote_to_l2(&self, key: &str, entry: CacheEntry) {
        let mut l2 = self.l2_cache.write().await;
        
        // 检查容量
        if l2.size >= l2.max_size {
            self.evict_from_l2(&mut l2).await;
        }

        l2.data.insert(key.to_string(), entry);
        l2.size += 1;
    }

    // 从 L1 缓存驱逐
    async fn evict_from_l1(&self, l1: &mut L1Cache) {
        if let Some((key, entry)) = l1.data.iter()
            .min_by_key(|(_, e)| e.last_accessed)
            .map(|(k, v)| (k.clone(), v.clone())) {
            
            l1.data.remove(&key);
            l1.size -= 1;
            
            // 降级到 L2 缓存
            self.demote_to_l2(key, entry).await;
            
            let mut stats = self.stats.lock().unwrap();
            stats.evictions += 1;
        }
    }

    // 从 L2 缓存驱逐
    async fn evict_from_l2(&self, l2: &mut L2Cache) {
        if let Some((key, entry)) = l2.data.iter()
            .min_by_key(|(_, e)| e.last_accessed)
            .map(|(k, v)| (k.clone(), v.clone())) {
            
            l2.data.remove(&key);
            l2.size -= 1;
            
            // 降级到 L3 缓存
            self.demote_to_l3(key, entry).await;
            
            let mut stats = self.stats.lock().unwrap();
            stats.evictions += 1;
        }
    }

    // 降级到 L2 缓存
    async fn demote_to_l2(&self, key: String, entry: CacheEntry) {
        let mut l2 = self.l2_cache.write().await;
        
        if l2.size >= l2.max_size {
            self.evict_from_l2(&mut l2).await;
        }

        l2.data.insert(key, entry);
        l2.size += 1;
    }

    // 降级到 L3 缓存
    async fn demote_to_l3(&self, key: String, entry: CacheEntry) {
        let mut l3 = self.l3_cache.write().await;
        
        if l3.size >= l3.max_size {
            // 从 L3 缓存移除最久未使用的条目
            if let Some((old_key, _)) = l3.data.iter()
                .min_by_key(|(_, e)| e.last_accessed)
                .map(|(k, _)| k.clone()) {
                l3.data.remove(&old_key);
                l3.size -= 1;
            }
        }

        l3.data.insert(key, entry);
        l3.size += 1;
    }

    // 检查是否过期
    fn is_expired(&self, entry: &CacheEntry) -> bool {
        entry.created_at.elapsed() > entry.ttl
    }

    // 压缩数据
    fn compress_data(&self, data: &[u8]) -> Result<Vec<u8>, CacheError> {
        // 简单的压缩实现
        let compressed = data.iter()
            .filter(|&&b| b != 0)
            .cloned()
            .collect();
        
        let mut stats = self.stats.lock().unwrap();
        stats.compressions += 1;
        
        Ok(compressed)
    }

    // 启动清理任务
    fn start_cleanup_task(&self) {
        let l1_cache = self.l1_cache.clone();
        let l2_cache = self.l2_cache.clone();
        let l3_cache = self.l3_cache.clone();
        let config = self.config.clone();

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(config.cleanup_interval);
            
            loop {
                interval.tick().await;
                
                // 清理 L1 缓存
                {
                    let mut l1 = l1_cache.write().await;
                    l1.data.retain(|_, entry| !Self::is_expired_static(entry));
                    l1.size = l1.data.len();
                }

                // 清理 L2 缓存
                {
                    let mut l2 = l2_cache.write().await;
                    l2.data.retain(|_, entry| !Self::is_expired_static(entry));
                    l2.size = l2.data.len();
                }

                // 清理 L3 缓存
                {
                    let mut l3 = l3_cache.write().await;
                    l3.data.retain(|_, entry| !Self::is_expired_static(entry));
                    l3.size = l3.data.len();
                }
            }
        });
    }

    // 静态方法检查过期
    fn is_expired_static(entry: &CacheEntry) -> bool {
        entry.created_at.elapsed() > entry.ttl
    }

    // 获取缓存统计
    pub fn get_cache_stats(&self) -> CacheStats {
        self.stats.lock().unwrap().clone()
    }

    // 清空缓存
    pub async fn clear(&self) {
        {
            let mut l1 = self.l1_cache.write().await;
            l1.data.clear();
            l1.size = 0;
        }

        {
            let mut l2 = self.l2_cache.write().await;
            l2.data.clear();
            l2.size = 0;
        }

        {
            let mut l3 = self.l3_cache.write().await;
            l3.data.clear();
            l3.size = 0;
        }
    }
}

#[derive(Debug, Clone)]
pub struct CacheStats {
    pub l1_hits: u64,
    pub l2_hits: u64,
    pub l3_hits: u64,
    pub misses: u64,
    pub total_requests: u64,
    pub evictions: u64,
    pub compressions: u64,
}

#[derive(Debug, thiserror::Error)]
pub enum CacheError {
    #[error("缓存操作失败: {0}")]
    CacheOperationFailed(String),
    
    #[error("压缩失败: {0}")]
    CompressionFailed(String),
    
    #[error("解压失败: {0}")]
    DecompressionFailed(String),
}
```

## 总结

本章提供了性能优化的完整示例，包括：

1. **进程启动优化** - 进程缓存和预热机制
2. **内存使用优化** - 内存池管理和分配优化
3. **CPU 使用优化** - 负载均衡和任务调度
4. **I/O 性能优化** - 缓冲区和批量操作
5. **并发性能优化** - 线程池和任务调度
6. **缓存优化策略** - 多级缓存系统

这些示例展示了如何在 Rust 1.90 中实现各种性能优化技术，提供了完整的监控、统计和自动优化功能。
