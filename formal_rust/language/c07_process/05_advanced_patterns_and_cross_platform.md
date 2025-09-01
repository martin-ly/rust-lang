# 高级模式与跨平台

## 概述

本章深入探讨 Rust 进程管理的高级模式，包括进程池、微服务架构、跨平台兼容性以及性能优化策略。这些模式为构建大规模、高性能的分布式系统提供了理论基础和实践指导。

## 进程池模式

### 基础进程池

```rust
use std::process::{Command, Child};
use std::sync::{Arc, Mutex, Condvar};
use std::collections::VecDeque;
use std::thread;
use std::time::Duration;

struct ProcessPool {
    workers: Vec<Worker>,
    task_queue: Arc<Mutex<VecDeque<Task>>>,
    notifier: Arc<Condvar>,
    max_processes: usize,
    active_processes: Arc<Mutex<usize>>,
}

struct Worker {
    id: usize,
    handle: Option<thread::JoinHandle<()>>,
}

struct Task {
    command: String,
    args: Vec<String>,
    callback: Box<dyn FnOnce(Result<String, String>) + Send>,
}

impl ProcessPool {
    fn new(max_processes: usize) -> Self {
        let task_queue = Arc::new(Mutex::new(VecDeque::new()));
        let notifier = Arc::new(Condvar::new());
        let active_processes = Arc::new(Mutex::new(0));
        
        let mut workers = Vec::new();
        for i in 0..max_processes {
            let worker = Worker {
                id: i,
                handle: None,
            };
            workers.push(worker);
        }
        
        ProcessPool {
            workers,
            task_queue,
            notifier,
            max_processes,
            active_processes,
        }
    }
    
    fn start(&mut self) {
        for worker in &mut self.workers {
            let task_queue = self.task_queue.clone();
            let notifier = self.notifier.clone();
            let active_processes = self.active_processes.clone();
            
            let handle = thread::spawn(move || {
                loop {
                    let task = {
                        let mut queue = task_queue.lock().unwrap();
                        while queue.is_empty() {
                            queue = notifier.wait(queue).unwrap();
                        }
                        queue.pop_front()
                    };
                    
                    if let Some(task) = task {
                        let mut active = active_processes.lock().unwrap();
                        *active += 1;
                        drop(active);
                        
                        let result = Self::execute_task(&task.command, &task.args);
                        (task.callback)(result);
                        
                        let mut active = active_processes.lock().unwrap();
                        *active -= 1;
                    }
                }
            });
            
            worker.handle = Some(handle);
        }
    }
    
    fn submit<F>(&self, command: String, args: Vec<String>, callback: F)
    where
        F: FnOnce(Result<String, String>) + Send + 'static,
    {
        let task = Task {
            command,
            args,
            callback: Box::new(callback),
        };
        
        {
            let mut queue = self.task_queue.lock().unwrap();
            queue.push_back(task);
        }
        
        self.notifier.notify_one();
    }
    
    fn execute_task(command: &str, args: &[String]) -> Result<String, String> {
        match Command::new(command)
            .args(args)
            .output()
        {
            Ok(output) => {
                if output.status.success() {
                    Ok(String::from_utf8_lossy(&output.stdout).to_string())
                } else {
                    Err(String::from_utf8_lossy(&output.stderr).to_string())
                }
            }
            Err(e) => Err(e.to_string()),
        }
    }
    
    fn wait_for_completion(&self) {
        loop {
            let active = *self.active_processes.lock().unwrap();
            let queue_len = self.task_queue.lock().unwrap().len();
            
            if active == 0 && queue_len == 0 {
                break;
            }
            
            thread::sleep(Duration::from_millis(100));
        }
    }
}
```

### 动态进程池

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

struct DynamicProcessPool {
    base_pool: ProcessPool,
    min_processes: usize,
    max_processes: usize,
    current_processes: AtomicUsize,
    load_threshold: f64,
}

impl DynamicProcessPool {
    fn new(min_processes: usize, max_processes: usize, load_threshold: f64) -> Self {
        DynamicProcessPool {
            base_pool: ProcessPool::new(min_processes),
            min_processes,
            max_processes,
            current_processes: AtomicUsize::new(min_processes),
            load_threshold,
        }
    }
    
    fn adjust_pool_size(&mut self) {
        let current = self.current_processes.load(Ordering::Relaxed);
        let active = *self.base_pool.active_processes.lock().unwrap();
        let queue_len = self.base_pool.task_queue.lock().unwrap().len();
        
        let load = if current > 0 {
            (active as f64) / (current as f64)
        } else {
            0.0
        };
        
        if load > self.load_threshold && current < self.max_processes {
            // 增加进程
            self.scale_up();
        } else if load < self.load_threshold / 2.0 && current > self.min_processes {
            // 减少进程
            self.scale_down();
        }
    }
    
    fn scale_up(&mut self) {
        let current = self.current_processes.load(Ordering::Relaxed);
        if current < self.max_processes {
            self.current_processes.fetch_add(1, Ordering::Relaxed);
            // 添加新的工作进程
        }
    }
    
    fn scale_down(&mut self) {
        let current = self.current_processes.load(Ordering::Relaxed);
        if current > self.min_processes {
            self.current_processes.fetch_sub(1, Ordering::Relaxed);
            // 移除工作进程
        }
    }
}
```

## 微服务架构

### 服务发现

```rust
use std::collections::HashMap;
use std::net::{IpAddr, SocketAddr};
use std::sync::{Arc, RwLock};
use std::time::{Duration, Instant};

#[derive(Debug, Clone)]
struct ServiceInstance {
    id: String,
    address: SocketAddr,
    health_check_url: String,
    last_heartbeat: Instant,
    metadata: HashMap<String, String>,
}

struct ServiceRegistry {
    services: Arc<RwLock<HashMap<String, Vec<ServiceInstance>>>>,
    health_check_interval: Duration,
}

impl ServiceRegistry {
    fn new() -> Self {
        ServiceRegistry {
            services: Arc::new(RwLock::new(HashMap::new())),
            health_check_interval: Duration::from_secs(30),
        }
    }
    
    fn register(&self, service_name: String, instance: ServiceInstance) {
        let mut services = self.services.write().unwrap();
        services.entry(service_name)
            .or_insert_with(Vec::new)
            .push(instance);
    }
    
    fn discover(&self, service_name: &str) -> Option<Vec<ServiceInstance>> {
        let services = self.services.read().unwrap();
        services.get(service_name).cloned()
    }
    
    fn heartbeat(&self, service_id: &str) {
        let mut services = self.services.write().unwrap();
        for service_instances in services.values_mut() {
            for instance in service_instances.iter_mut() {
                if instance.id == service_id {
                    instance.last_heartbeat = Instant::now();
                    break;
                }
            }
        }
    }
    
    fn health_check(&self) {
        let mut services = self.services.write().unwrap();
        for service_instances in services.values_mut() {
            service_instances.retain(|instance| {
                instance.last_heartbeat.elapsed() < self.health_check_interval * 2
            });
        }
    }
}
```

### 负载均衡

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

trait LoadBalancer {
    fn select_instance(&self, instances: &[ServiceInstance]) -> Option<&ServiceInstance>;
}

struct RoundRobinBalancer {
    current: AtomicUsize,
}

impl RoundRobinBalancer {
    fn new() -> Self {
        RoundRobinBalancer {
            current: AtomicUsize::new(0),
        }
    }
}

impl LoadBalancer for RoundRobinBalancer {
    fn select_instance(&self, instances: &[ServiceInstance]) -> Option<&ServiceInstance> {
        if instances.is_empty() {
            return None;
        }
        
        let current = self.current.fetch_add(1, Ordering::Relaxed);
        Some(&instances[current % instances.len()])
    }
}

struct LeastConnectionsBalancer {
    connections: Arc<RwLock<HashMap<String, usize>>>,
}

impl LeastConnectionsBalancer {
    fn new() -> Self {
        LeastConnectionsBalancer {
            connections: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    fn increment_connections(&self, instance_id: &str) {
        let mut connections = self.connections.write().unwrap();
        *connections.entry(instance_id.to_string()).or_insert(0) += 1;
    }
    
    fn decrement_connections(&self, instance_id: &str) {
        let mut connections = self.connections.write().unwrap();
        if let Some(count) = connections.get_mut(instance_id) {
            if *count > 0 {
                *count -= 1;
            }
        }
    }
}

impl LoadBalancer for LeastConnectionsBalancer {
    fn select_instance(&self, instances: &[ServiceInstance]) -> Option<&ServiceInstance> {
        if instances.is_empty() {
            return None;
        }
        
        let connections = self.connections.read().unwrap();
        instances.iter()
            .min_by_key(|instance| connections.get(&instance.id).unwrap_or(&0))
    }
}
```

### 服务网格

```rust
use std::sync::mpsc;

struct ServiceMesh {
    registry: ServiceRegistry,
    load_balancer: Box<dyn LoadBalancer + Send + Sync>,
    proxy_channels: HashMap<String, mpsc::Sender<ProxyMessage>>,
}

#[derive(Debug)]
enum ProxyMessage {
    ForwardRequest(String, Vec<u8>),
    Response(String, Vec<u8>),
    HealthCheck,
}

struct ServiceProxy {
    service_name: String,
    mesh: Arc<ServiceMesh>,
    request_sender: mpsc::Sender<ProxyMessage>,
    response_receiver: mpsc::Receiver<ProxyMessage>,
}

impl ServiceProxy {
    fn new(service_name: String, mesh: Arc<ServiceMesh>) -> Self {
        let (request_sender, request_receiver) = mpsc::channel();
        let (response_sender, response_receiver) = mpsc::channel();
        
        ServiceProxy {
            service_name,
            mesh,
            request_sender,
            response_receiver,
        }
    }
    
    fn forward_request(&self, request: Vec<u8>) -> Result<Vec<u8>, String> {
        // 选择服务实例
        let instances = self.mesh.registry.discover(&self.service_name)
            .ok_or("Service not found")?;
        
        let instance = self.mesh.load_balancer.select_instance(&instances)
            .ok_or("No available instances")?;
        
        // 转发请求
        self.request_sender.send(ProxyMessage::ForwardRequest(
            instance.id.clone(),
            request
        )).map_err(|e| e.to_string())?;
        
        // 等待响应
        match self.response_receiver.recv() {
            Ok(ProxyMessage::Response(_, response)) => Ok(response),
            Ok(_) => Err("Unexpected message type".to_string()),
            Err(e) => Err(e.to_string()),
        }
    }
}
```

## 跨平台兼容性

### 平台抽象层

```rust
use std::process::Command;
use std::io;

trait PlatformProcessManager {
    fn create_process(&self, command: &str, args: &[String]) -> io::Result<Child>;
    fn kill_process(&self, pid: u32) -> io::Result<()>;
    fn get_process_info(&self, pid: u32) -> io::Result<ProcessInfo>;
}

#[derive(Debug)]
struct ProcessInfo {
    pid: u32,
    parent_pid: Option<u32>,
    command_line: String,
    memory_usage: u64,
    cpu_usage: f64,
}

struct UnixProcessManager;

impl PlatformProcessManager for UnixProcessManager {
    fn create_process(&self, command: &str, args: &[String]) -> io::Result<Child> {
        Command::new(command)
            .args(args)
            .spawn()
    }
    
    fn kill_process(&self, pid: u32) -> io::Result<()> {
        unsafe {
            libc::kill(pid as i32, libc::SIGTERM);
        }
        Ok(())
    }
    
    fn get_process_info(&self, pid: u32) -> io::Result<ProcessInfo> {
        // Unix特定的进程信息获取
        Ok(ProcessInfo {
            pid,
            parent_pid: None,
            command_line: String::new(),
            memory_usage: 0,
            cpu_usage: 0.0,
        })
    }
}

struct WindowsProcessManager;

impl PlatformProcessManager for WindowsProcessManager {
    fn create_process(&self, command: &str, args: &[String]) -> io::Result<Child> {
        Command::new(command)
            .args(args)
            .spawn()
    }
    
    fn kill_process(&self, pid: u32) -> io::Result<()> {
        // Windows特定的进程终止
        Ok(())
    }
    
    fn get_process_info(&self, pid: u32) -> io::Result<ProcessInfo> {
        // Windows特定的进程信息获取
        Ok(ProcessInfo {
            pid,
            parent_pid: None,
            command_line: String::new(),
            memory_usage: 0,
            cpu_usage: 0.0,
        })
    }
}

struct CrossPlatformProcessManager {
    manager: Box<dyn PlatformProcessManager + Send + Sync>,
}

impl CrossPlatformProcessManager {
    fn new() -> Self {
        #[cfg(target_os = "windows")]
        let manager = Box::new(WindowsProcessManager);
        
        #[cfg(not(target_os = "windows"))]
        let manager = Box::new(UnixProcessManager);
        
        CrossPlatformProcessManager { manager }
    }
    
    fn create_process(&self, command: &str, args: &[String]) -> io::Result<Child> {
        self.manager.create_process(command, args)
    }
    
    fn kill_process(&self, pid: u32) -> io::Result<()> {
        self.manager.kill_process(pid)
    }
    
    fn get_process_info(&self, pid: u32) -> io::Result<ProcessInfo> {
        self.manager.get_process_info(pid)
    }
}
```

### 配置管理

```rust
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Serialize, Deserialize)]
struct ProcessConfig {
    name: String,
    command: String,
    args: Vec<String>,
    working_directory: Option<String>,
    environment: HashMap<String, String>,
    restart_policy: RestartPolicy,
    resource_limits: ResourceLimits,
}

#[derive(Debug, Serialize, Deserialize)]
enum RestartPolicy {
    Never,
    Always,
    OnFailure,
    UnlessStopped,
}

#[derive(Debug, Serialize, Deserialize)]
struct ResourceLimits {
    max_memory: Option<u64>,
    max_cpu: Option<f64>,
    max_file_descriptors: Option<u32>,
}

struct ConfigManager {
    configs: HashMap<String, ProcessConfig>,
    platform_overrides: HashMap<String, ProcessConfig>,
}

impl ConfigManager {
    fn new() -> Self {
        ConfigManager {
            configs: HashMap::new(),
            platform_overrides: HashMap::new(),
        }
    }
    
    fn load_config(&mut self, config: ProcessConfig) {
        self.configs.insert(config.name.clone(), config);
    }
    
    fn get_config(&self, name: &str) -> Option<&ProcessConfig> {
        // 首先检查平台特定的覆盖
        if let Some(override_config) = self.platform_overrides.get(name) {
            return Some(override_config);
        }
        
        self.configs.get(name)
    }
    
    fn apply_platform_overrides(&mut self, platform: &str) {
        // 根据平台应用特定的配置覆盖
        match platform {
            "windows" => {
                // Windows特定的配置
            }
            "linux" => {
                // Linux特定的配置
            }
            "macos" => {
                // macOS特定的配置
            }
            _ => {}
        }
    }
}
```

## 性能优化策略

### 进程预热

```rust
use std::time::{Duration, Instant};

struct ProcessWarmer {
    warmup_duration: Duration,
    warmup_requests: usize,
}

impl ProcessWarmer {
    fn new(warmup_duration: Duration, warmup_requests: usize) -> Self {
        ProcessWarmer {
            warmup_duration,
            warmup_requests,
        }
    }
    
    fn warmup_process(&self, process: &mut Child) -> Result<(), String> {
        let start_time = Instant::now();
        let mut request_count = 0;
        
        while start_time.elapsed() < self.warmup_duration && request_count < self.warmup_requests {
            // 发送预热请求
            self.send_warmup_request(process)?;
            request_count += 1;
            
            std::thread::sleep(Duration::from_millis(10));
        }
        
        Ok(())
    }
    
    fn send_warmup_request(&self, process: &mut Child) -> Result<(), String> {
        // 发送轻量级的预热请求
        Ok(())
    }
}
```

### 连接池

```rust
use std::sync::{Arc, Mutex, Condvar};
use std::collections::VecDeque;
use std::time::{Duration, Instant};

struct Connection {
    id: u64,
    created_at: Instant,
    last_used: Instant,
    is_active: bool,
}

struct ConnectionPool {
    connections: Arc<Mutex<VecDeque<Connection>>>,
    notifier: Arc<Condvar>,
    max_connections: usize,
    max_idle_time: Duration,
    cleanup_interval: Duration,
}

impl ConnectionPool {
    fn new(max_connections: usize, max_idle_time: Duration) -> Self {
        let pool = ConnectionPool {
            connections: Arc::new(Mutex::new(VecDeque::new())),
            notifier: Arc::new(Condvar::new()),
            max_connections,
            max_idle_time,
            cleanup_interval: Duration::from_secs(60),
        };
        
        // 启动清理线程
        pool.start_cleanup_thread();
        pool
    }
    
    fn get_connection(&self) -> Option<Connection> {
        let mut connections = self.connections.lock().unwrap();
        
        while connections.is_empty() {
            connections = self.notifier.wait(connections).unwrap();
        }
        
        connections.pop_front()
    }
    
    fn return_connection(&self, mut connection: Connection) {
        connection.last_used = Instant::now();
        connection.is_active = false;
        
        let mut connections = self.connections.lock().unwrap();
        if connections.len() < self.max_connections {
            connections.push_back(connection);
            self.notifier.notify_one();
        }
    }
    
    fn start_cleanup_thread(&self) {
        let connections = self.connections.clone();
        let max_idle_time = self.max_idle_time;
        let cleanup_interval = self.cleanup_interval;
        
        std::thread::spawn(move || {
            loop {
                std::thread::sleep(cleanup_interval);
                
                let mut conns = connections.lock().unwrap();
                let now = Instant::now();
                
                conns.retain(|conn| {
                    now.duration_since(conn.last_used) < max_idle_time
                });
            }
        });
    }
}
```

### 缓存策略

```rust
use std::collections::HashMap;
use std::sync::{Arc, RwLock};
use std::time::{Duration, Instant};

struct CacheEntry<T> {
    value: T,
    created_at: Instant,
    ttl: Duration,
}

struct ProcessCache<T> {
    cache: Arc<RwLock<HashMap<String, CacheEntry<T>>>>>,
    max_size: usize,
    default_ttl: Duration,
}

impl<T: Clone> ProcessCache<T> {
    fn new(max_size: usize, default_ttl: Duration) -> Self {
        ProcessCache {
            cache: Arc::new(RwLock::new(HashMap::new())),
            max_size,
            default_ttl,
        }
    }
    
    fn get(&self, key: &str) -> Option<T> {
        let cache = self.cache.read().unwrap();
        if let Some(entry) = cache.get(key) {
            if Instant::now().duration_since(entry.created_at) < entry.ttl {
                return Some(entry.value.clone());
            }
        }
        None
    }
    
    fn set(&self, key: String, value: T) {
        let mut cache = self.cache.write().unwrap();
        
        // 检查缓存大小限制
        if cache.len() >= self.max_size {
            self.evict_oldest(&mut cache);
        }
        
        let entry = CacheEntry {
            value,
            created_at: Instant::now(),
            ttl: self.default_ttl,
        };
        
        cache.insert(key, entry);
    }
    
    fn evict_oldest(&self, cache: &mut HashMap<String, CacheEntry<T>>) {
        if let Some((oldest_key, _)) = cache.iter()
            .min_by_key(|(_, entry)| entry.created_at)
        {
            cache.remove(oldest_key);
        }
    }
    
    fn cleanup_expired(&self) {
        let mut cache = self.cache.write().unwrap();
        let now = Instant::now();
        
        cache.retain(|_, entry| {
            now.duration_since(entry.created_at) < entry.ttl
        });
    }
}
```

## 监控与诊断

### 性能监控

```rust
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

struct PerformanceMetrics {
    total_requests: AtomicU64,
    successful_requests: AtomicU64,
    failed_requests: AtomicU64,
    total_response_time: AtomicU64,
    start_time: Instant,
}

impl PerformanceMetrics {
    fn new() -> Self {
        PerformanceMetrics {
            total_requests: AtomicU64::new(0),
            successful_requests: AtomicU64::new(0),
            failed_requests: AtomicU64::new(0),
            total_response_time: AtomicU64::new(0),
            start_time: Instant::now(),
        }
    }
    
    fn record_request(&self, success: bool, response_time: Duration) {
        self.total_requests.fetch_add(1, Ordering::Relaxed);
        
        if success {
            self.successful_requests.fetch_add(1, Ordering::Relaxed);
        } else {
            self.failed_requests.fetch_add(1, Ordering::Relaxed);
        }
        
        self.total_response_time.fetch_add(
            response_time.as_millis() as u64,
            Ordering::Relaxed
        );
    }
    
    fn get_stats(&self) -> PerformanceStats {
        let total = self.total_requests.load(Ordering::Relaxed);
        let successful = self.successful_requests.load(Ordering::Relaxed);
        let failed = self.failed_requests.load(Ordering::Relaxed);
        let total_time = self.total_response_time.load(Ordering::Relaxed);
        
        let uptime = self.start_time.elapsed();
        let requests_per_second = if uptime.as_secs() > 0 {
            total as f64 / uptime.as_secs() as f64
        } else {
            0.0
        };
        
        let average_response_time = if total > 0 {
            Duration::from_millis(total_time / total)
        } else {
            Duration::from_millis(0)
        };
        
        PerformanceStats {
            total_requests: total,
            successful_requests: successful,
            failed_requests: failed,
            success_rate: if total > 0 { successful as f64 / total as f64 } else { 0.0 },
            requests_per_second,
            average_response_time,
            uptime,
        }
    }
}

#[derive(Debug)]
struct PerformanceStats {
    total_requests: u64,
    successful_requests: u64,
    failed_requests: u64,
    success_rate: f64,
    requests_per_second: f64,
    average_response_time: Duration,
    uptime: Duration,
}
```

## 总结

高级模式与跨平台兼容性是构建大规模分布式系统的关键。通过进程池、微服务架构、跨平台抽象和性能优化策略，Rust 提供了强大的工具来构建高性能、可扩展的系统。

### 关键要点

1. **进程池模式** - 高效的进程管理和任务调度
2. **微服务架构** - 服务发现、负载均衡和服务网格
3. **跨平台兼容** - 统一的API适配不同操作系统
4. **性能优化** - 预热、连接池和缓存策略
5. **监控诊断** - 全面的性能监控和诊断工具

### 下一步

在下一章中，我们将总结整个模块的核心概念，回顾最佳实践，并展望技术发展趋势。

---

*本章为 Rust 进程管理的高级应用提供了完整的理论基础和实践指导，为构建企业级分布式系统奠定了坚实基础。*
