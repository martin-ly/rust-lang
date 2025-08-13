# 高级模式与跨平台

## 概述

在实际的系统编程中，进程管理需要处理复杂的场景和跨平台兼容性。本章深入探讨高级进程模式，包括进程池、微服务架构、跨平台兼容性以及性能优化策略，为构建生产级的进程管理系统提供实践指导。

## 进程池模式

### 基础进程池

进程池通过预创建和复用进程来提高性能，减少进程创建和销毁的开销。

```rust
use std::sync::{Arc, Mutex, Condvar};
use std::collections::VecDeque;
use std::process::{Child, Command};
use std::thread;

struct ProcessPool {
    processes: Arc<Mutex<VecDeque<Child>>>,
    max_size: usize,
    current_size: Arc<Mutex<usize>>,
    not_empty: Arc<Condvar>,
    not_full: Arc<Condvar>,
}

impl ProcessPool {
    fn new(max_size: usize) -> Self {
        ProcessPool {
            processes: Arc::new(Mutex::new(VecDeque::new())),
            max_size,
            current_size: Arc::new(Mutex::new(0)),
            not_empty: Arc::new(Condvar::new()),
            not_full: Arc::new(Condvar::new()),
        }
    }
    
    fn acquire(&self, command: &str, args: &[&str]) -> Result<Child, std::io::Error> {
        let mut processes = self.processes.lock().unwrap();
        
        // 等待可用进程
        while processes.is_empty() {
            let mut current_size = self.current_size.lock().unwrap();
            if *current_size < self.max_size {
                // 创建新进程
                let child = Command::new(command)
                    .args(args)
                    .spawn()?;
                *current_size += 1;
                return Ok(child);
            } else {
                // 等待进程可用
                processes = self.not_empty.wait(processes).unwrap();
            }
        }
        
        // 复用现有进程
        Ok(processes.pop_front().unwrap())
    }
    
    fn release(&self, mut child: Child) {
        // 检查进程是否仍然活跃
        match child.try_wait() {
            Ok(Some(_)) => {
                // 进程已结束，减少计数
                let mut current_size = self.current_size.lock().unwrap();
                *current_size -= 1;
                self.not_full.notify_one();
            }
            Ok(None) => {
                // 进程仍在运行，放回池中
                let mut processes = self.processes.lock().unwrap();
                processes.push_back(child);
                self.not_empty.notify_one();
            }
            Err(_) => {
                // 进程出错，减少计数
                let mut current_size = self.current_size.lock().unwrap();
                *current_size -= 1;
                self.not_full.notify_one();
            }
        }
    }
}

fn process_pool_example() {
    let pool = Arc::new(ProcessPool::new(5));
    let mut handles = vec![];
    
    for i in 0..10 {
        let pool_clone = pool.clone();
        let handle = thread::spawn(move || {
            // 获取进程
            let child = pool_clone.acquire("echo", &["Hello", "World"]).unwrap();
            
            // 使用进程
            let output = child.wait_with_output().unwrap();
            println!("Task {}: {}", i, String::from_utf8_lossy(&output.stdout));
            
            // 释放进程（在实际应用中，这里会重新初始化进程）
            // pool_clone.release(child);
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
}
```

### 智能进程池

```rust
use std::time::{Duration, Instant};
use std::collections::HashMap;

struct SmartProcessPool {
    processes: Arc<Mutex<HashMap<u64, ProcessInfo>>>,
    max_size: usize,
    idle_timeout: Duration,
    health_check_interval: Duration,
}

#[derive(Debug)]
struct ProcessInfo {
    child: Child,
    created_at: Instant,
    last_used: Instant,
    use_count: u32,
    status: ProcessStatus,
}

#[derive(Debug)]
enum ProcessStatus {
    Idle,
    Busy,
    Unhealthy,
}

impl SmartProcessPool {
    fn new(max_size: usize, idle_timeout: Duration) -> Self {
        let pool = SmartProcessPool {
            processes: Arc::new(Mutex::new(HashMap::new())),
            max_size,
            idle_timeout,
            health_check_interval: Duration::from_secs(30),
        };
        
        // 启动健康检查线程
        let processes_clone = pool.processes.clone();
        let idle_timeout_clone = pool.idle_timeout;
        thread::spawn(move || {
            loop {
                thread::sleep(Duration::from_secs(30));
                pool.cleanup_idle_processes();
            }
        });
        
        pool
    }
    
    fn acquire(&self, command: &str, args: &[&str]) -> Result<u64, std::io::Error> {
        let mut processes = self.processes.lock().unwrap();
        
        // 查找空闲进程
        for (id, info) in processes.iter_mut() {
            if matches!(info.status, ProcessStatus::Idle) {
                info.status = ProcessStatus::Busy;
                info.last_used = Instant::now();
                info.use_count += 1;
                return Ok(*id);
            }
        }
        
        // 创建新进程
        if processes.len() < self.max_size {
            let child = Command::new(command)
                .args(args)
                .spawn()?;
            
            let id = rand::random::<u64>();
            let process_info = ProcessInfo {
                child,
                created_at: Instant::now(),
                last_used: Instant::now(),
                use_count: 1,
                status: ProcessStatus::Busy,
            };
            
            processes.insert(id, process_info);
            Ok(id)
        } else {
            Err(std::io::Error::new(
                std::io::ErrorKind::WouldBlock,
                "Pool is full",
            ))
        }
    }
    
    fn release(&self, id: u64) {
        let mut processes = self.processes.lock().unwrap();
        if let Some(info) = processes.get_mut(&id) {
            info.status = ProcessStatus::Idle;
            info.last_used = Instant::now();
        }
    }
    
    fn cleanup_idle_processes(&self) {
        let mut processes = self.processes.lock().unwrap();
        let now = Instant::now();
        let mut to_remove = vec![];
        
        for (id, info) in processes.iter() {
            if matches!(info.status, ProcessStatus::Idle) 
                && now.duration_since(info.last_used) > self.idle_timeout {
                to_remove.push(*id);
            }
        }
        
        for id in to_remove {
            processes.remove(&id);
        }
    }
}
```

## 微服务架构

### 服务发现与注册

```rust
use std::collections::HashMap;
use std::net::{TcpListener, TcpStream};
use std::io::{self, Read, Write};

#[derive(Debug, Clone)]
struct ServiceInfo {
    id: String,
    name: String,
    address: String,
    port: u16,
    health_check_url: String,
    metadata: HashMap<String, String>,
}

struct ServiceRegistry {
    services: Arc<Mutex<HashMap<String, ServiceInfo>>>,
    health_checker: Arc<HealthChecker>,
}

struct HealthChecker {
    check_interval: Duration,
}

impl ServiceRegistry {
    fn new() -> Self {
        let registry = ServiceRegistry {
            services: Arc::new(Mutex::new(HashMap::new())),
            health_checker: Arc::new(HealthChecker {
                check_interval: Duration::from_secs(30),
            }),
        };
        
        // 启动健康检查
        let services_clone = registry.services.clone();
        let health_checker = registry.health_checker.clone();
        thread::spawn(move || {
            loop {
                thread::sleep(health_checker.check_interval);
                registry.perform_health_checks();
            }
        });
        
        registry
    }
    
    fn register(&self, service: ServiceInfo) -> Result<(), String> {
        let mut services = self.services.lock().unwrap();
        services.insert(service.id.clone(), service);
        Ok(())
    }
    
    fn deregister(&self, service_id: &str) -> Result<(), String> {
        let mut services = self.services.lock().unwrap();
        services.remove(service_id);
        Ok(())
    }
    
    fn discover(&self, service_name: &str) -> Vec<ServiceInfo> {
        let services = self.services.lock().unwrap();
        services.values()
            .filter(|service| service.name == service_name)
            .cloned()
            .collect()
    }
    
    fn perform_health_checks(&self) {
        let mut services = self.services.lock().unwrap();
        let mut to_remove = vec![];
        
        for (id, service) in services.iter() {
            if !self.is_service_healthy(service) {
                to_remove.push(id.clone());
            }
        }
        
        for id in to_remove {
            services.remove(&id);
        }
    }
    
    fn is_service_healthy(&self, service: &ServiceInfo) -> bool {
        // 简化的健康检查
        match TcpStream::connect(format!("{}:{}", service.address, service.port)) {
            Ok(_) => true,
            Err(_) => false,
        }
    }
}
```

### 负载均衡器

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

enum LoadBalancingStrategy {
    RoundRobin,
    LeastConnections,
    Weighted,
}

struct LoadBalancer {
    services: Arc<Mutex<Vec<ServiceInfo>>>,
    strategy: LoadBalancingStrategy,
    current_index: AtomicUsize,
    connection_counts: Arc<Mutex<HashMap<String, u32>>>,
}

impl LoadBalancer {
    fn new(strategy: LoadBalancingStrategy) -> Self {
        LoadBalancer {
            services: Arc::new(Mutex::new(Vec::new())),
            strategy,
            current_index: AtomicUsize::new(0),
            connection_counts: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    fn add_service(&self, service: ServiceInfo) {
        let mut services = self.services.lock().unwrap();
        services.push(service);
    }
    
    fn select_service(&self) -> Option<ServiceInfo> {
        let services = self.services.lock().unwrap();
        if services.is_empty() {
            return None;
        }
        
        match self.strategy {
            LoadBalancingStrategy::RoundRobin => {
                let index = self.current_index.fetch_add(1, Ordering::SeqCst);
                Some(services[index % services.len()].clone())
            }
            LoadBalancingStrategy::LeastConnections => {
                let connection_counts = self.connection_counts.lock().unwrap();
                services.iter()
                    .min_by_key(|service| connection_counts.get(&service.id).unwrap_or(&0))
                    .cloned()
            }
            LoadBalancingStrategy::Weighted => {
                // 简化的加权轮询
                let index = self.current_index.fetch_add(1, Ordering::SeqCst);
                Some(services[index % services.len()].clone())
            }
        }
    }
    
    fn increment_connection_count(&self, service_id: &str) {
        let mut counts = self.connection_counts.lock().unwrap();
        *counts.entry(service_id.to_string()).or_insert(0) += 1;
    }
    
    fn decrement_connection_count(&self, service_id: &str) {
        let mut counts = self.connection_counts.lock().unwrap();
        if let Some(count) = counts.get_mut(service_id) {
            *count = count.saturating_sub(1);
        }
    }
}
```

## 跨平台兼容性

### 平台抽象层

```rust
use std::io;

#[cfg(target_os = "windows")]
mod windows {
    use super::*;
    
    pub struct ProcessManager;
    
    impl ProcessManager {
        pub fn create_process(&self, command: &str, args: &[&str]) -> io::Result<Child> {
            use std::process::Command;
            Command::new(command)
                .args(args)
                .spawn()
        }
        
        pub fn kill_process(&self, pid: u32) -> io::Result<()> {
            // Windows 特定的进程终止逻辑
            Ok(())
        }
    }
}

#[cfg(target_os = "linux")]
mod linux {
    use super::*;
    
    pub struct ProcessManager;
    
    impl ProcessManager {
        pub fn create_process(&self, command: &str, args: &[&str]) -> io::Result<Child> {
            use std::process::Command;
            Command::new(command)
                .args(args)
                .spawn()
        }
        
        pub fn kill_process(&self, pid: u32) -> io::Result<()> {
            // Linux 特定的进程终止逻辑
            Ok(())
        }
    }
}

#[cfg(target_os = "macos")]
mod macos {
    use super::*;
    
    pub struct ProcessManager;
    
    impl ProcessManager {
        pub fn create_process(&self, command: &str, args: &[&str]) -> io::Result<Child> {
            use std::process::Command;
            Command::new(command)
                .args(args)
                .spawn()
        }
        
        pub fn kill_process(&self, pid: u32) -> io::Result<()> {
            // macOS 特定的进程终止逻辑
            Ok(())
        }
    }
}

// 统一的平台抽象
pub struct CrossPlatformProcessManager {
    #[cfg(target_os = "windows")]
    manager: windows::ProcessManager,
    #[cfg(target_os = "linux")]
    manager: linux::ProcessManager,
    #[cfg(target_os = "macos")]
    manager: macos::ProcessManager,
}

impl CrossPlatformProcessManager {
    pub fn new() -> Self {
        CrossPlatformProcessManager {
            #[cfg(target_os = "windows")]
            manager: windows::ProcessManager,
            #[cfg(target_os = "linux")]
            manager: linux::ProcessManager,
            #[cfg(target_os = "macos")]
            manager: macos::ProcessManager,
        }
    }
    
    pub fn create_process(&self, command: &str, args: &[&str]) -> io::Result<Child> {
        self.manager.create_process(command, args)
    }
    
    pub fn kill_process(&self, pid: u32) -> io::Result<()> {
        self.manager.kill_process(pid)
    }
}
```

### 条件编译与特征检测

```rust
#[cfg(feature = "process_pool")]
mod process_pool {
    use super::*;
    
    pub struct AdvancedProcessPool {
        // 高级进程池实现
    }
}

#[cfg(feature = "health_check")]
mod health_check {
    use super::*;
    
    pub struct HealthChecker {
        // 健康检查实现
    }
}

#[cfg(feature = "metrics")]
mod metrics {
    use super::*;
    
    pub struct ProcessMetrics {
        // 指标收集实现
    }
}

// 根据编译时特征提供不同的功能
pub struct ProcessManager {
    #[cfg(feature = "process_pool")]
    pool: Option<process_pool::AdvancedProcessPool>,
    #[cfg(feature = "health_check")]
    health_checker: Option<health_check::HealthChecker>,
    #[cfg(feature = "metrics")]
    metrics: Option<metrics::ProcessMetrics>,
}

impl ProcessManager {
    pub fn new() -> Self {
        ProcessManager {
            #[cfg(feature = "process_pool")]
            pool: Some(process_pool::AdvancedProcessPool::new()),
            #[cfg(feature = "health_check")]
            health_checker: Some(health_check::HealthChecker::new()),
            #[cfg(feature = "metrics")]
            metrics: Some(metrics::ProcessMetrics::new()),
        }
    }
}
```

## 性能优化策略

### 异步进程管理

```rust
use tokio::process::{Command, Child};
use tokio::sync::mpsc;
use futures::future::{self, FutureExt};

struct AsyncProcessManager {
    command_tx: mpsc::Sender<ProcessCommand>,
}

enum ProcessCommand {
    Create { command: String, args: Vec<String>, response_tx: oneshot::Sender<io::Result<Child>> },
    Kill { pid: u32, response_tx: oneshot::Sender<io::Result<()>> },
}

impl AsyncProcessManager {
    fn new() -> Self {
        let (command_tx, mut command_rx) = mpsc::channel(100);
        
        // 启动异步处理循环
        tokio::spawn(async move {
            while let Some(command) = command_rx.recv().await {
                match command {
                    ProcessCommand::Create { command, args, response_tx } => {
                        let result = Command::new(&command)
                            .args(&args)
                            .spawn();
                        let _ = response_tx.send(result);
                    }
                    ProcessCommand::Kill { pid, response_tx } => {
                        // 异步进程终止逻辑
                        let result = Ok(());
                        let _ = response_tx.send(result);
                    }
                }
            }
        });
        
        AsyncProcessManager { command_tx }
    }
    
    async fn create_process(&self, command: String, args: Vec<String>) -> io::Result<Child> {
        let (response_tx, response_rx) = oneshot::channel();
        let _ = self.command_tx.send(ProcessCommand::Create {
            command,
            args,
            response_tx,
        }).await;
        
        response_rx.await.unwrap()
    }
    
    async fn kill_process(&self, pid: u32) -> io::Result<()> {
        let (response_tx, response_rx) = oneshot::channel();
        let _ = self.command_tx.send(ProcessCommand::Kill {
            pid,
            response_tx,
        }).await;
        
        response_rx.await.unwrap()
    }
}
```

### 内存池优化

```rust
use std::sync::Arc;
use std::collections::VecDeque;

struct MemoryPool {
    buffers: Arc<Mutex<VecDeque<Vec<u8>>>>,
    buffer_size: usize,
    max_buffers: usize,
}

impl MemoryPool {
    fn new(buffer_size: usize, max_buffers: usize) -> Self {
        MemoryPool {
            buffers: Arc::new(Mutex::new(VecDeque::new())),
            buffer_size,
            max_buffers,
        }
    }
    
    fn acquire_buffer(&self) -> Vec<u8> {
        let mut buffers = self.buffers.lock().unwrap();
        if let Some(buffer) = buffers.pop_front() {
            buffer
        } else {
            vec![0; self.buffer_size]
        }
    }
    
    fn release_buffer(&self, mut buffer: Vec<u8>) {
        let mut buffers = self.buffers.lock().unwrap();
        if buffers.len() < self.max_buffers {
            buffer.clear();
            buffers.push_back(buffer);
        }
    }
}

struct OptimizedProcessManager {
    memory_pool: MemoryPool,
    process_pool: ProcessPool,
}

impl OptimizedProcessManager {
    fn new() -> Self {
        OptimizedProcessManager {
            memory_pool: MemoryPool::new(4096, 100),
            process_pool: ProcessPool::new(10),
        }
    }
    
    fn execute_with_optimization(&self, command: &str, args: &[&str]) -> io::Result<Vec<u8>> {
        // 使用内存池优化数据传输
        let buffer = self.memory_pool.acquire_buffer();
        
        // 执行进程操作
        let result = self.process_pool.acquire(command, args)
            .and_then(|child| child.wait_with_output());
        
        // 释放缓冲区
        self.memory_pool.release_buffer(buffer);
        
        result.map(|output| output.stdout)
    }
}
```

## 监控与诊断

### 进程监控

```rust
use std::time::{Duration, Instant};
use std::collections::HashMap;

#[derive(Debug)]
struct ProcessMetrics {
    cpu_usage: f64,
    memory_usage: u64,
    start_time: Instant,
    last_activity: Instant,
    total_requests: u64,
    failed_requests: u64,
}

struct ProcessMonitor {
    metrics: Arc<Mutex<HashMap<u32, ProcessMetrics>>>,
    alert_thresholds: AlertThresholds,
}

#[derive(Debug)]
struct AlertThresholds {
    max_cpu_usage: f64,
    max_memory_usage: u64,
    max_response_time: Duration,
}

impl ProcessMonitor {
    fn new() -> Self {
        ProcessMonitor {
            metrics: Arc::new(Mutex::new(HashMap::new())),
            alert_thresholds: AlertThresholds {
                max_cpu_usage: 80.0,
                max_memory_usage: 1024 * 1024 * 100, // 100MB
                max_response_time: Duration::from_secs(5),
            },
        }
    }
    
    fn record_metrics(&self, pid: u32, metrics: ProcessMetrics) {
        let mut all_metrics = self.metrics.lock().unwrap();
        all_metrics.insert(pid, metrics);
    }
    
    fn check_alerts(&self) -> Vec<Alert> {
        let mut alerts = Vec::new();
        let metrics = self.metrics.lock().unwrap();
        
        for (pid, metric) in metrics.iter() {
            if metric.cpu_usage > self.alert_thresholds.max_cpu_usage {
                alerts.push(Alert {
                    pid: *pid,
                    alert_type: AlertType::HighCpuUsage,
                    message: format!("CPU usage: {}%", metric.cpu_usage),
                });
            }
            
            if metric.memory_usage > self.alert_thresholds.max_memory_usage {
                alerts.push(Alert {
                    pid: *pid,
                    alert_type: AlertType::HighMemoryUsage,
                    message: format!("Memory usage: {} bytes", metric.memory_usage),
                });
            }
        }
        
        alerts
    }
}

#[derive(Debug)]
struct Alert {
    pid: u32,
    alert_type: AlertType,
    message: String,
}

#[derive(Debug)]
enum AlertType {
    HighCpuUsage,
    HighMemoryUsage,
    ProcessHang,
    ProcessCrash,
}
```

## 总结

高级进程模式和跨平台兼容性是构建生产级系统的关键要素。通过进程池、微服务架构、跨平台抽象和性能优化，Rust 提供了强大的进程管理能力。

### 关键要点

1. **进程池模式** - 通过复用进程提高性能和资源利用率
2. **微服务架构** - 服务发现、负载均衡和健康检查
3. **跨平台兼容** - 条件编译和平台抽象层
4. **性能优化** - 异步处理、内存池和监控诊断

### 下一步

在下一章中，我们将总结模块的核心概念，回顾最佳实践，并探讨技术发展趋势。

"

---

<!-- 以下为按标准模板自动补全的占位章节，待后续填充 -->
"
## 技术背景
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 核心概念
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 技术实现
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 形式化分析
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 应用案例
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 性能分析
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 最佳实践
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 常见问题
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n
## 未来值值展望
(待补充，参考 STANDARD_DOCUMENT_TEMPLATE_2025.md)\n


