//! 微服务设计机制和架构模型
//! 
//! 本模块实现了微服务架构的设计模式和建模，包括：
//! - 服务发现机制
//! - 负载均衡策略
//! - 熔断器模式
//! - API网关
//! - 服务网格
//! - 配置管理
//! - 健康检查
//! - 分布式追踪
//! - 服务治理
//! 
//! 充分利用 Rust 1.90 的异步和并发特性

use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::{Arc, RwLock, atomic::{AtomicBool, AtomicUsize, Ordering}};
use std::time::{Duration, Instant, SystemTime};
use std::net::SocketAddr;
use std::fmt;
use serde::{Deserialize, Serialize};
use crate::error::ModelError;

#[cfg(feature = "tokio-adapter")]
use tokio::time::{sleep, timeout};

/// 微服务模型结果类型
pub type MicroserviceResult<T> = Result<T, ModelError>;

/// 服务标识符
pub type ServiceId = String;

/// 实例标识符
pub type InstanceId = String;

/// 请求标识符
pub type RequestId = String;

/// 服务实例
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServiceInstance {
    pub id: InstanceId,
    pub service_id: ServiceId,
    pub address: SocketAddr,
    pub metadata: HashMap<String, String>,
    pub health_status: HealthStatus,
    pub last_heartbeat: SystemTime,
    pub weight: u32,
    pub version: String,
    pub tags: HashSet<String>,
}

impl ServiceInstance {
    pub fn new(id: InstanceId, service_id: ServiceId, address: SocketAddr) -> Self {
        Self {
            id,
            service_id,
            address,
            metadata: HashMap::new(),
            health_status: HealthStatus::Healthy,
            last_heartbeat: SystemTime::now(),
            weight: 100,
            version: "1.0.0".to_string(),
            tags: HashSet::new(),
        }
    }
    
    pub fn with_metadata(mut self, key: String, value: String) -> Self {
        self.metadata.insert(key, value);
        self
    }
    
    pub fn with_weight(mut self, weight: u32) -> Self {
        self.weight = weight;
        self
    }
    
    pub fn with_version(mut self, version: String) -> Self {
        self.version = version;
        self
    }
    
    pub fn with_tag(mut self, tag: String) -> Self {
        self.tags.insert(tag);
        self
    }
    
    pub fn update_heartbeat(&mut self) {
        self.last_heartbeat = SystemTime::now();
        if self.health_status == HealthStatus::Unhealthy {
            self.health_status = HealthStatus::Healthy;
        }
    }
    
    pub fn is_healthy(&self) -> bool {
        matches!(self.health_status, HealthStatus::Healthy)
    }
    
    pub fn is_timeout(&self, timeout: Duration) -> bool {
        self.last_heartbeat.elapsed().unwrap_or(Duration::MAX) > timeout
    }
}

/// 健康状态
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum HealthStatus {
    Healthy,
    Unhealthy,
    Unknown,
    Starting,
    Stopping,
}

/// 服务发现注册中心
#[derive(Debug)]
pub struct ServiceRegistry {
    services: Arc<RwLock<HashMap<ServiceId, Vec<ServiceInstance>>>>,
    instances: Arc<RwLock<HashMap<InstanceId, ServiceInstance>>>,
    watchers: Arc<RwLock<HashMap<ServiceId, Vec<ServiceWatcherWrapper>>>>,
    health_check_interval: Duration,
    instance_timeout: Duration,
    is_running: AtomicBool,
}

impl ServiceRegistry {
    pub fn new(health_check_interval: Duration, instance_timeout: Duration) -> Self {
        Self {
            services: Arc::new(RwLock::new(HashMap::new())),
            instances: Arc::new(RwLock::new(HashMap::new())),
            watchers: Arc::new(RwLock::new(HashMap::new())),
            health_check_interval,
            instance_timeout,
            is_running: AtomicBool::new(false),
        }
    }
    
    /// 注册服务实例
    pub fn register(&self, instance: ServiceInstance) -> MicroserviceResult<()> {
        let service_id = instance.service_id.clone();
        let instance_id = instance.id.clone();
        
        // 添加到服务列表
        {
            let mut services = self.services.write().unwrap();
            services.entry(service_id.clone())
                .or_insert_with(Vec::new)
                .push(instance.clone());
        }
        
        // 添加到实例映射
        self.instances.write().unwrap().insert(instance_id.clone(), instance);
        
        // 通知观察者
        self.notify_watchers(&service_id, ServiceEvent::InstanceRegistered(instance_id.clone()));
        
        println!("Service instance registered: {} -> {}", service_id, instance_id);
        Ok(())
    }
    
    /// 注销服务实例
    pub fn deregister(&self, instance_id: &InstanceId) -> MicroserviceResult<()> {
        let instance = self.instances.write().unwrap().remove(instance_id);
        
        if let Some(instance) = instance {
            let service_id = instance.service_id.clone();
            
            // 从服务列表中移除
            {
                let mut services = self.services.write().unwrap();
                if let Some(instances) = services.get_mut(&service_id) {
                    instances.retain(|i| i.id != *instance_id);
                    if instances.is_empty() {
                        services.remove(&service_id);
                    }
                }
            }
            
            // 通知观察者
            self.notify_watchers(&service_id, ServiceEvent::InstanceDeregistered(instance_id.clone()));
            
            println!("Service instance deregistered: {} -> {}", service_id, instance_id);
        }
        
        Ok(())
    }
    
    /// 发现服务实例
    pub fn discover(&self, service_id: &ServiceId) -> Vec<ServiceInstance> {
        self.services.read().unwrap()
            .get(service_id)
            .map(|instances| instances.iter().filter(|i| i.is_healthy()).cloned().collect())
            .unwrap_or_default()
    }
    
    /// 获取所有服务
    pub fn get_all_services(&self) -> HashMap<ServiceId, Vec<ServiceInstance>> {
        self.services.read().unwrap().clone()
    }
    
    /// 添加服务观察者
    pub fn watch(&self, service_id: ServiceId, watcher: ServiceWatcherWrapper) {
        self.watchers.write().unwrap()
            .entry(service_id)
            .or_insert_with(Vec::new)
            .push(watcher);
    }
    
    /// 启动健康检查
    pub fn start_health_check(&self) {
        self.is_running.store(true, Ordering::SeqCst);
        
        let _services = Arc::clone(&self.services);
        let instances = Arc::clone(&self.instances);
        let watchers = Arc::clone(&self.watchers);
        let interval = self.health_check_interval;
        let timeout = self.instance_timeout;
        let is_running = Arc::new(AtomicBool::new(true));
        
        std::thread::spawn(move || {
            while is_running.load(Ordering::SeqCst) {
                // 检查实例健康状态
                let mut unhealthy_instances = Vec::new();
                
                {
                    let mut instances_guard = instances.write().unwrap();
                    for (instance_id, instance) in instances_guard.iter_mut() {
                        if instance.is_timeout(timeout) {
                            instance.health_status = HealthStatus::Unhealthy;
                            unhealthy_instances.push((instance.service_id.clone(), instance_id.clone()));
                        }
                    }
                }
                
                // 通知不健康的实例
                for (service_id, instance_id) in unhealthy_instances {
                    let watchers_guard = watchers.read().unwrap();
                    if let Some(service_watchers) = watchers_guard.get(&service_id) {
                        for watcher in service_watchers {
                            watcher.on_event(ServiceEvent::InstanceUnhealthy(instance_id.clone()));
                        }
                    }
                }
                
                std::thread::sleep(interval);
            }
        });
        
        println!("Service registry health check started");
    }
    
    /// 停止健康检查
    pub fn stop(&self) {
        self.is_running.store(false, Ordering::SeqCst);
        println!("Service registry stopped");
    }
    
    fn notify_watchers(&self, service_id: &ServiceId, event: ServiceEvent) {
        let watchers = self.watchers.read().unwrap();
        if let Some(service_watchers) = watchers.get(service_id) {
            for watcher in service_watchers {
                watcher.on_event(event.clone());
            }
        }
    }
}

/// 服务事件
#[derive(Debug, Clone)]
pub enum ServiceEvent {
    InstanceRegistered(InstanceId),
    InstanceDeregistered(InstanceId),
    InstanceHealthy(InstanceId),
    InstanceUnhealthy(InstanceId),
}

/// 服务观察者
pub trait ServiceWatcher: Send + Sync {
    fn on_event(&self, event: ServiceEvent);
}

/// 简单的服务观察者实现
#[derive(Debug)]
pub struct SimpleServiceWatcher {
    pub name: String,
}

impl ServiceWatcher for SimpleServiceWatcher {
    fn on_event(&self, event: ServiceEvent) {
        println!("Watcher {}: {:?}", self.name, event);
    }
}

/// 服务观察者包装器（解决trait object问题）
#[derive(Debug)]
pub enum ServiceWatcherWrapper {
    Simple(SimpleServiceWatcher),
}

impl ServiceWatcherWrapper {
    pub fn on_event(&self, event: ServiceEvent) {
        match self {
            ServiceWatcherWrapper::Simple(w) => w.on_event(event),
        }
    }
}

/// 负载均衡器
#[derive(Debug)]
pub struct LoadBalancer {
    strategy: LoadBalancingStrategy,
    service_registry: Arc<ServiceRegistry>,
    round_robin_counters: Arc<RwLock<HashMap<ServiceId, AtomicUsize>>>,
    connection_counts: Arc<RwLock<HashMap<InstanceId, AtomicUsize>>>,
}

/// 负载均衡策略
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum LoadBalancingStrategy {
    RoundRobin,
    WeightedRoundRobin,
    LeastConnections,
    Random,
    ConsistentHashing,
    IpHash,
}

impl LoadBalancer {
    pub fn new(strategy: LoadBalancingStrategy, service_registry: Arc<ServiceRegistry>) -> Self {
        Self {
            strategy,
            service_registry,
            round_robin_counters: Arc::new(RwLock::new(HashMap::new())),
            connection_counts: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    /// 选择服务实例
    pub fn select_instance(&self, service_id: &ServiceId, client_info: Option<&ClientInfo>) -> MicroserviceResult<ServiceInstance> {
        let instances = self.service_registry.discover(service_id);
        
        if instances.is_empty() {
            return Err(ModelError::ValidationError(format!("No healthy instances for service: {}", service_id)));
        }
        
        match self.strategy {
            LoadBalancingStrategy::RoundRobin => self.round_robin_select(service_id, &instances),
            LoadBalancingStrategy::WeightedRoundRobin => self.weighted_round_robin_select(&instances),
            LoadBalancingStrategy::LeastConnections => self.least_connections_select(&instances),
            LoadBalancingStrategy::Random => self.random_select(&instances),
            LoadBalancingStrategy::ConsistentHashing => self.consistent_hash_select(&instances, client_info),
            LoadBalancingStrategy::IpHash => self.ip_hash_select(&instances, client_info),
        }
    }
    
    fn round_robin_select(&self, service_id: &ServiceId, instances: &[ServiceInstance]) -> MicroserviceResult<ServiceInstance> {
        let mut counters = self.round_robin_counters.write().unwrap();
        let counter = counters.entry(service_id.clone()).or_insert_with(|| AtomicUsize::new(0));
        
        let index = counter.fetch_add(1, Ordering::SeqCst) % instances.len();
        Ok(instances[index].clone())
    }
    
    fn weighted_round_robin_select(&self, instances: &[ServiceInstance]) -> MicroserviceResult<ServiceInstance> {
        let total_weight: u32 = instances.iter().map(|i| i.weight).sum();
        if total_weight == 0 {
            return self.random_select(instances);
        }
        
        let random_weight = fastrand::u32(0..total_weight);
        let mut current_weight = 0;
        
        for instance in instances {
            current_weight += instance.weight;
            if random_weight < current_weight {
                return Ok(instance.clone());
            }
        }
        
        // 备用方案
        Ok(instances[0].clone())
    }
    
    fn least_connections_select(&self, instances: &[ServiceInstance]) -> MicroserviceResult<ServiceInstance> {
        let connection_counts = self.connection_counts.read().unwrap();
        
        let mut min_connections = usize::MAX;
        let mut selected_instance = None;
        
        for instance in instances {
            let connections = connection_counts.get(&instance.id)
                .map(|c| c.load(Ordering::SeqCst))
                .unwrap_or(0);
            
            if connections < min_connections {
                min_connections = connections;
                selected_instance = Some(instance.clone());
            }
        }
        
        selected_instance.ok_or_else(|| ModelError::ValidationError("No instance selected".to_string()))
    }
    
    fn random_select(&self, instances: &[ServiceInstance]) -> MicroserviceResult<ServiceInstance> {
        let index = fastrand::usize(0..instances.len());
        Ok(instances[index].clone())
    }
    
    fn consistent_hash_select(&self, instances: &[ServiceInstance], client_info: Option<&ClientInfo>) -> MicroserviceResult<ServiceInstance> {
        let default_key = "default".to_string();
        let hash_key = client_info
            .and_then(|info| info.session_id.as_ref())
            .or_else(|| client_info.and_then(|info| info.user_id.as_ref()))
            .unwrap_or(&default_key);
        
        let hash = self.simple_hash(hash_key);
        let index = hash as usize % instances.len();
        Ok(instances[index].clone())
    }
    
    fn ip_hash_select(&self, instances: &[ServiceInstance], client_info: Option<&ClientInfo>) -> MicroserviceResult<ServiceInstance> {
        let default_ip = "127.0.0.1".to_string();
        let ip = client_info
            .and_then(|info| info.client_ip.as_ref())
            .unwrap_or(&default_ip);
        
        let hash = self.simple_hash(ip);
        let index = hash as usize % instances.len();
        Ok(instances[index].clone())
    }
    
    fn simple_hash(&self, s: &str) -> u32 {
        s.bytes().fold(0u32, |acc, b| acc.wrapping_mul(31).wrapping_add(b as u32))
    }
    
    /// 增加连接计数
    pub fn increment_connections(&self, instance_id: &InstanceId) {
        let mut counts = self.connection_counts.write().unwrap();
        counts.entry(instance_id.clone())
            .or_insert_with(|| AtomicUsize::new(0))
            .fetch_add(1, Ordering::SeqCst);
    }
    
    /// 减少连接计数
    pub fn decrement_connections(&self, instance_id: &InstanceId) {
        let counts = self.connection_counts.read().unwrap();
        if let Some(counter) = counts.get(instance_id) {
            counter.fetch_sub(1, Ordering::SeqCst);
        }
    }
}

/// 客户端信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ClientInfo {
    pub client_ip: Option<String>,
    pub user_id: Option<String>,
    pub session_id: Option<String>,
    pub user_agent: Option<String>,
}

/// 熔断器状态
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum CircuitBreakerState {
    Closed,
    Open,
    HalfOpen,
}

/// 熔断器配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CircuitBreakerConfig {
    pub failure_threshold: usize,
    pub success_threshold: usize,
    pub timeout: Duration,
    pub reset_timeout: Duration,
    pub max_concurrent_requests: usize,
}

impl Default for CircuitBreakerConfig {
    fn default() -> Self {
        Self {
            failure_threshold: 5,
            success_threshold: 3,
            timeout: Duration::from_secs(1),
            reset_timeout: Duration::from_secs(60),
            max_concurrent_requests: 10,
        }
    }
}

/// 熔断器
#[derive(Debug, Clone)]
pub struct CircuitBreaker {
    config: CircuitBreakerConfig,
    state: Arc<RwLock<CircuitBreakerState>>,
    failure_count: Arc<AtomicUsize>,
    success_count: Arc<AtomicUsize>,
    last_failure_time: Arc<RwLock<Option<Instant>>>,
    concurrent_requests: Arc<AtomicUsize>,
    metrics: Arc<RwLock<CircuitBreakerMetrics>>,
}

impl CircuitBreaker {
    pub fn new(config: CircuitBreakerConfig) -> Self {
        Self {
            config,
            state: Arc::new(RwLock::new(CircuitBreakerState::Closed)),
            failure_count: Arc::new(AtomicUsize::new(0)),
            success_count: Arc::new(AtomicUsize::new(0)),
            last_failure_time: Arc::new(RwLock::new(None)),
            concurrent_requests: Arc::new(AtomicUsize::new(0)),
            metrics: Arc::new(RwLock::new(CircuitBreakerMetrics::default())),
        }
    }
    
    /// 执行请求
    pub async fn execute<F, Fut, T>(&self, request: F) -> MicroserviceResult<T>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = MicroserviceResult<T>>,
    {
        // 检查熔断器状态
        if !self.can_execute() {
            self.metrics.write().unwrap().rejected_requests += 1;
            return Err(ModelError::ValidationError("Circuit breaker is open".to_string()));
        }
        
        // 增加并发请求计数
        let concurrent = self.concurrent_requests.fetch_add(1, Ordering::SeqCst);
        if concurrent >= self.config.max_concurrent_requests {
            self.concurrent_requests.fetch_sub(1, Ordering::SeqCst);
            return Err(ModelError::ValidationError("Too many concurrent requests".to_string()));
        }
        
        let start_time = Instant::now();
        
        // 执行请求
        let result = if let Some(timeout_duration) = Some(self.config.timeout) {
            #[cfg(feature = "tokio-adapter")]
            {
                match timeout(timeout_duration, request()).await {
                    Ok(result) => result,
                    Err(_) => Err(ModelError::TimeoutError("Request timeout".to_string())),
                }
            }
            #[cfg(not(feature = "tokio-adapter"))]
            {
                request().await
            }
        } else {
            request().await
        };
        
        // 减少并发请求计数
        self.concurrent_requests.fetch_sub(1, Ordering::SeqCst);
        
        // 更新统计和状态
        let execution_time = start_time.elapsed();
        self.update_metrics_and_state(&result, execution_time);
        
        result
    }
    
    fn can_execute(&self) -> bool {
        let state = self.state.read().unwrap();
        match *state {
            CircuitBreakerState::Closed => true,
            CircuitBreakerState::Open => {
                // 检查是否可以尝试重置
                if let Some(last_failure) = *self.last_failure_time.read().unwrap() {
                    if last_failure.elapsed() >= self.config.reset_timeout {
                        // 转换到半开状态
                        drop(state);
                        *self.state.write().unwrap() = CircuitBreakerState::HalfOpen;
                        self.success_count.store(0, Ordering::SeqCst);
                        return true;
                    }
                }
                false
            }
            CircuitBreakerState::HalfOpen => {
                self.concurrent_requests.load(Ordering::SeqCst) == 0
            }
        }
    }
    
    fn update_metrics_and_state<T>(&self, result: &MicroserviceResult<T>, execution_time: Duration) {
        let mut metrics = self.metrics.write().unwrap();
        metrics.total_requests += 1;
        metrics.total_execution_time += execution_time;
        
        match result {
            Ok(_) => {
                metrics.successful_requests += 1;
                self.on_success();
            }
            Err(_) => {
                metrics.failed_requests += 1;
                self.on_failure();
            }
        }
    }
    
    fn on_success(&self) {
        let state = self.state.read().unwrap();
        match *state {
            CircuitBreakerState::HalfOpen => {
                let success_count = self.success_count.fetch_add(1, Ordering::SeqCst) + 1;
                if success_count >= self.config.success_threshold {
                    drop(state);
                    *self.state.write().unwrap() = CircuitBreakerState::Closed;
                    self.failure_count.store(0, Ordering::SeqCst);
                    println!("Circuit breaker reset to CLOSED");
                }
            }
            CircuitBreakerState::Closed => {
                self.failure_count.store(0, Ordering::SeqCst);
            }
            _ => {}
        }
    }
    
    fn on_failure(&self) {
        *self.last_failure_time.write().unwrap() = Some(Instant::now());
        
        let state = self.state.read().unwrap();
        match *state {
            CircuitBreakerState::Closed => {
                let failure_count = self.failure_count.fetch_add(1, Ordering::SeqCst) + 1;
                if failure_count >= self.config.failure_threshold {
                    drop(state);
                    *self.state.write().unwrap() = CircuitBreakerState::Open;
                    println!("Circuit breaker opened due to failures");
                }
            }
            CircuitBreakerState::HalfOpen => {
                drop(state);
                *self.state.write().unwrap() = CircuitBreakerState::Open;
                println!("Circuit breaker reopened due to failure in half-open state");
            }
            _ => {}
        }
    }
    
    /// 获取当前状态
    pub fn get_state(&self) -> CircuitBreakerState {
        self.state.read().unwrap().clone()
    }
    
    /// 获取指标
    pub fn get_metrics(&self) -> CircuitBreakerMetrics {
        self.metrics.read().unwrap().clone()
    }
    
    /// 手动重置熔断器
    pub fn reset(&self) {
        *self.state.write().unwrap() = CircuitBreakerState::Closed;
        self.failure_count.store(0, Ordering::SeqCst);
        self.success_count.store(0, Ordering::SeqCst);
        *self.last_failure_time.write().unwrap() = None;
        println!("Circuit breaker manually reset");
    }
}

/// 熔断器指标
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CircuitBreakerMetrics {
    pub total_requests: u64,
    pub successful_requests: u64,
    pub failed_requests: u64,
    pub rejected_requests: u64,
    pub total_execution_time: Duration,
}

impl CircuitBreakerMetrics {
    pub fn success_rate(&self) -> f64 {
        if self.total_requests > 0 {
            self.successful_requests as f64 / self.total_requests as f64
        } else {
            0.0
        }
    }
    
    pub fn failure_rate(&self) -> f64 {
        if self.total_requests > 0 {
            self.failed_requests as f64 / self.total_requests as f64
        } else {
            0.0
        }
    }
    
    pub fn average_execution_time(&self) -> Duration {
        if self.total_requests > 0 {
            self.total_execution_time / self.total_requests as u32
        } else {
            Duration::ZERO
        }
    }
}

/// API网关
#[allow(dead_code)]
#[derive(Debug)]
pub struct ApiGateway {
    service_registry: Arc<ServiceRegistry>,
    load_balancer: LoadBalancer,
    circuit_breakers: Arc<RwLock<HashMap<ServiceId, CircuitBreaker>>>,
    rate_limiters: Arc<RwLock<HashMap<String, RateLimiter>>>,
    request_router: RequestRouter,
    middleware_chain: Vec<MiddlewareWrapper>,
}

impl ApiGateway {
    pub fn new(service_registry: Arc<ServiceRegistry>) -> Self {
        let load_balancer = LoadBalancer::new(
            LoadBalancingStrategy::RoundRobin,
            Arc::clone(&service_registry),
        );
        
        Self {
            service_registry,
            load_balancer,
            circuit_breakers: Arc::new(RwLock::new(HashMap::new())),
            rate_limiters: Arc::new(RwLock::new(HashMap::new())),
            request_router: RequestRouter::new(),
            middleware_chain: Vec::new(),
        }
    }
    
    /// 添加中间件
    pub fn add_middleware(&mut self, middleware: MiddlewareWrapper) {
        self.middleware_chain.push(middleware);
    }
    
    /// 处理请求
    pub async fn handle_request(&self, request: ApiRequest) -> MicroserviceResult<ApiResponse> {
        let mut context = RequestContext::new(request);
        
        // 执行中间件链
        for middleware in &self.middleware_chain {
            middleware.process(&mut context).await?;
        }
        
        // 路由请求
        let service_id = self.request_router.route(&context.request)?;
        
        // 检查限流
        self.check_rate_limit(&service_id, &context)?;
        
        // 获取熔断器
        let circuit_breaker = self.get_or_create_circuit_breaker(&service_id);
        
        // 通过熔断器执行请求
        circuit_breaker.execute(|| async {
            // 选择服务实例
            let instance = self.load_balancer.select_instance(&service_id, context.client_info.as_ref())?;
            
            // 执行实际请求
            self.execute_request(&instance, &context.request).await
        }).await
    }
    
    fn check_rate_limit(&self, service_id: &ServiceId, context: &RequestContext) -> MicroserviceResult<()> {
        let rate_limiters = self.rate_limiters.read().unwrap();
        if let Some(rate_limiter) = rate_limiters.get(service_id) {
            let default_key = "default".to_string();
            let client_key = context.client_info.as_ref()
                .and_then(|info| info.client_ip.as_ref())
                .unwrap_or(&default_key);
            
            if !rate_limiter.allow_request(client_key) {
                return Err(ModelError::ValidationError("Rate limit exceeded".to_string()));
            }
        }
        Ok(())
    }
    
    fn get_or_create_circuit_breaker(&self, service_id: &ServiceId) -> CircuitBreaker {
        let mut breakers = self.circuit_breakers.write().unwrap();
        breakers.entry(service_id.clone())
            .or_insert_with(|| CircuitBreaker::new(CircuitBreakerConfig::default()))
            .clone()
    }
    
    async fn execute_request(&self, instance: &ServiceInstance, request: &ApiRequest) -> MicroserviceResult<ApiResponse> {
        // 简化实现：模拟HTTP请求
        println!("Executing request to {}:{} - {}", instance.address.ip(), instance.address.port(), request.path);
        
        // 模拟网络延迟
        #[cfg(feature = "tokio-adapter")]
        sleep(Duration::from_millis(fastrand::u64(10..100))).await;
        
        // 模拟成功/失败
        if fastrand::f64() < 0.9 {
            Ok(ApiResponse {
                status_code: 200,
                headers: HashMap::new(),
                body: format!("Response from {}", instance.id),
            })
        } else {
            Err(ModelError::ValidationError("Service error".to_string()))
        }
    }
}

/// API请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ApiRequest {
    pub method: String,
    pub path: String,
    pub headers: HashMap<String, String>,
    pub body: String,
    pub query_params: HashMap<String, String>,
}

/// API响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ApiResponse {
    pub status_code: u16,
    pub headers: HashMap<String, String>,
    pub body: String,
}

/// 请求上下文
#[derive(Debug)]
pub struct RequestContext {
    pub request: ApiRequest,
    pub client_info: Option<ClientInfo>,
    pub start_time: Instant,
    pub metadata: HashMap<String, String>,
}

impl RequestContext {
    pub fn new(request: ApiRequest) -> Self {
        Self {
            request,
            client_info: None,
            start_time: Instant::now(),
            metadata: HashMap::new(),
        }
    }
}

/// 中间件trait
#[async_trait::async_trait]
pub trait Middleware: Send + Sync {
    async fn process(&self, context: &mut RequestContext) -> MicroserviceResult<()>;
}

/// 认证中间件
#[derive(Debug)]
pub struct AuthenticationMiddleware {
    pub required_headers: Vec<String>,
}

#[async_trait::async_trait]
impl Middleware for AuthenticationMiddleware {
    async fn process(&self, context: &mut RequestContext) -> MicroserviceResult<()> {
        for header in &self.required_headers {
            if !context.request.headers.contains_key(header) {
                return Err(ModelError::ValidationError(format!("Missing required header: {}", header)));
            }
        }
        
        // 提取客户端信息
        context.client_info = Some(ClientInfo {
            client_ip: context.request.headers.get("X-Real-IP").cloned(),
            user_id: context.request.headers.get("X-User-ID").cloned(),
            session_id: context.request.headers.get("X-Session-ID").cloned(),
            user_agent: context.request.headers.get("User-Agent").cloned(),
        });
        
        Ok(())
    }
}

/// 日志中间件
#[derive(Debug)]
pub struct LoggingMiddleware;

#[async_trait::async_trait]
impl Middleware for LoggingMiddleware {
    async fn process(&self, context: &mut RequestContext) -> MicroserviceResult<()> {
        println!("Request: {} {} - Headers: {:?}", 
                context.request.method, 
                context.request.path, 
                context.request.headers.keys().collect::<Vec<_>>());
        Ok(())
    }
}

/// 中间件包装器（解决trait object安全性问题）
#[derive(Debug)]
pub enum MiddlewareWrapper {
    Authentication(AuthenticationMiddleware),
    Logging(LoggingMiddleware),
}

impl MiddlewareWrapper {
    pub async fn process(&self, context: &mut RequestContext) -> MicroserviceResult<()> {
        match self {
            MiddlewareWrapper::Authentication(m) => m.process(context).await,
            MiddlewareWrapper::Logging(m) => m.process(context).await,
        }
    }
}

/// 请求路由器
#[derive(Debug)]
pub struct RequestRouter {
    routes: HashMap<String, ServiceId>,
    path_patterns: Vec<(String, ServiceId)>,
}

impl RequestRouter {
    pub fn new() -> Self {
        Self {
            routes: HashMap::new(),
            path_patterns: Vec::new(),
        }
    }
    
    /// 添加路由规则
    pub fn add_route(&mut self, path_pattern: String, service_id: ServiceId) {
        self.path_patterns.push((path_pattern, service_id));
    }
    
    /// 路由请求
    pub fn route(&self, request: &ApiRequest) -> MicroserviceResult<ServiceId> {
        // 精确匹配
        if let Some(service_id) = self.routes.get(&request.path) {
            return Ok(service_id.clone());
        }
        
        // 模式匹配
        for (pattern, service_id) in &self.path_patterns {
            if self.matches_pattern(pattern, &request.path) {
                return Ok(service_id.clone());
            }
        }
        
        Err(ModelError::ValidationError(format!("No route found for path: {}", request.path)))
    }
    
    fn matches_pattern(&self, pattern: &str, path: &str) -> bool {
        // 简化的模式匹配实现
        if pattern.contains('*') {
            let prefix = pattern.split('*').next().unwrap_or("");
            path.starts_with(prefix)
        } else {
            pattern == path
        }
    }
}

impl Default for RequestRouter {
    fn default() -> Self {
        Self::new()
    }
}

/// 限流器
#[derive(Debug)]
pub struct RateLimiter {
    max_requests: usize,
    time_window: Duration,
    requests: Arc<RwLock<HashMap<String, VecDeque<Instant>>>>,
}

impl RateLimiter {
    pub fn new(max_requests: usize, time_window: Duration) -> Self {
        Self {
            max_requests,
            time_window,
            requests: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    /// 检查是否允许请求
    pub fn allow_request(&self, client_key: &str) -> bool {
        let now = Instant::now();
        let mut requests = self.requests.write().unwrap();
        let client_requests = requests.entry(client_key.to_string()).or_insert_with(VecDeque::new);
        
        // 清理过期请求
        while let Some(&front_time) = client_requests.front() {
            if now.duration_since(front_time) > self.time_window {
                client_requests.pop_front();
            } else {
                break;
            }
        }
        
        // 检查是否超过限制
        if client_requests.len() >= self.max_requests {
            false
        } else {
            client_requests.push_back(now);
            true
        }
    }
    
    /// 获取当前请求数
    pub fn current_requests(&self, client_key: &str) -> usize {
        let requests = self.requests.read().unwrap();
        requests.get(client_key).map(|q| q.len()).unwrap_or(0)
    }
}

/// 配置管理器
#[derive(Debug)]
pub struct ConfigurationManager {
    configs: Arc<RwLock<HashMap<String, ConfigValue>>>,
    watchers: Arc<RwLock<HashMap<String, Vec<ConfigWatcherWrapper>>>>,
}

impl ConfigurationManager {
    pub fn new() -> Self {
        Self {
            configs: Arc::new(RwLock::new(HashMap::new())),
            watchers: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    /// 设置配置值
    pub fn set_config(&self, key: String, value: ConfigValue) {
        let old_value = self.configs.write().unwrap().insert(key.clone(), value.clone());
        
        // 通知观察者
        if old_value.as_ref() != Some(&value) {
            self.notify_watchers(&key, &value);
        }
    }
    
    /// 获取配置值
    pub fn get_config(&self, key: &str) -> Option<ConfigValue> {
        self.configs.read().unwrap().get(key).cloned()
    }
    
    /// 添加配置观察者
    pub fn add_watcher(&self, key: String, watcher: ConfigWatcherWrapper) {
        self.watchers.write().unwrap()
            .entry(key)
            .or_insert_with(Vec::new)
            .push(watcher);
    }
    
    fn notify_watchers(&self, key: &str, value: &ConfigValue) {
        let watchers = self.watchers.read().unwrap();
        if let Some(key_watchers) = watchers.get(key) {
            for watcher in key_watchers {
                watcher.on_config_change(key, value);
            }
        }
    }
}

impl Default for ConfigurationManager {
    fn default() -> Self {
        Self::new()
    }
}

/// 配置值
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ConfigValue {
    String(String),
    Integer(i64),
    Float(f64),
    Boolean(bool),
    Array(Vec<ConfigValue>),
    Object(HashMap<String, ConfigValue>),
}

impl fmt::Display for ConfigValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ConfigValue::String(s) => write!(f, "{}", s),
            ConfigValue::Integer(i) => write!(f, "{}", i),
            ConfigValue::Float(fl) => write!(f, "{}", fl),
            ConfigValue::Boolean(b) => write!(f, "{}", b),
            ConfigValue::Array(arr) => write!(f, "{:?}", arr),
            ConfigValue::Object(obj) => write!(f, "{:?}", obj),
        }
    }
}

/// 配置观察者
pub trait ConfigWatcher: Send + Sync {
    fn on_config_change(&self, key: &str, value: &ConfigValue);
}

/// 简单配置观察者
#[derive(Debug)]
pub struct SimpleConfigWatcher {
    pub name: String,
}

impl ConfigWatcher for SimpleConfigWatcher {
    fn on_config_change(&self, key: &str, value: &ConfigValue) {
        println!("Config watcher {}: {} = {}", self.name, key, value);
    }
}

/// 配置观察者包装器（解决trait object问题）
#[derive(Debug)]
pub enum ConfigWatcherWrapper {
    Simple(SimpleConfigWatcher),
}

impl ConfigWatcherWrapper {
    pub fn on_config_change(&self, key: &str, value: &ConfigValue) {
        match self {
            ConfigWatcherWrapper::Simple(w) => w.on_config_change(key, value),
        }
    }
}

/// 微服务系统管理器
#[allow(dead_code)]
#[derive(Debug)]
pub struct MicroserviceSystemManager {
    service_registry: Arc<ServiceRegistry>,
    api_gateway: ApiGateway,
    config_manager: ConfigurationManager,
    metrics_collector: MetricsCollector,
}

impl MicroserviceSystemManager {
    pub fn new() -> Self {
        let service_registry = Arc::new(ServiceRegistry::new(
            Duration::from_secs(5),
            Duration::from_secs(30),
        ));
        
        let api_gateway = ApiGateway::new(Arc::clone(&service_registry));
        
        Self {
            service_registry,
            api_gateway,
            config_manager: ConfigurationManager::new(),
            metrics_collector: MetricsCollector::new(),
        }
    }
    
    /// 启动系统
    pub fn start(&self) -> MicroserviceResult<()> {
        self.service_registry.start_health_check();
        self.metrics_collector.start();
        println!("Microservice system started");
        Ok(())
    }
    
    /// 停止系统
    pub fn stop(&self) -> MicroserviceResult<()> {
        self.service_registry.stop();
        self.metrics_collector.stop();
        println!("Microservice system stopped");
        Ok(())
    }
    
    /// 注册服务
    pub fn register_service(&self, instance: ServiceInstance) -> MicroserviceResult<()> {
        self.service_registry.register(instance)
    }
    
    /// 处理API请求
    pub async fn handle_api_request(&self, request: ApiRequest) -> MicroserviceResult<ApiResponse> {
        self.api_gateway.handle_request(request).await
    }
    
    /// 获取系统状态
    pub fn get_system_status(&self) -> MicroserviceSystemStatus {
        let services = self.service_registry.get_all_services();
        let total_instances = services.values().map(|instances| instances.len()).sum();
        let healthy_instances = services.values()
            .flat_map(|instances| instances.iter())
            .filter(|instance| instance.is_healthy())
            .count();
        
        MicroserviceSystemStatus {
            total_services: services.len(),
            total_instances,
            healthy_instances,
            services,
            metrics: self.metrics_collector.get_metrics(),
        }
    }
}

impl Default for MicroserviceSystemManager {
    fn default() -> Self {
        Self::new()
    }
}

/// 微服务系统状态
#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)]
pub struct MicroserviceSystemStatus {
    pub total_services: usize,
    pub total_instances: usize,
    pub healthy_instances: usize,
    pub services: HashMap<ServiceId, Vec<ServiceInstance>>,
    pub metrics: SystemMetrics,
}

/// 指标收集器
#[derive(Debug)]
pub struct MetricsCollector {
    metrics: Arc<RwLock<SystemMetrics>>,
    is_running: AtomicBool,
}

impl MetricsCollector {
    pub fn new() -> Self {
        Self {
            metrics: Arc::new(RwLock::new(SystemMetrics::default())),
            is_running: AtomicBool::new(false),
        }
    }
    
    pub fn start(&self) {
        self.is_running.store(true, Ordering::SeqCst);
        println!("Metrics collector started");
    }
    
    pub fn stop(&self) {
        self.is_running.store(false, Ordering::SeqCst);
        println!("Metrics collector stopped");
    }
    
    pub fn get_metrics(&self) -> SystemMetrics {
        self.metrics.read().unwrap().clone()
    }
    
    pub fn record_request(&self, service_id: &ServiceId, execution_time: Duration, success: bool) {
        let mut metrics = self.metrics.write().unwrap();
        metrics.total_requests += 1;
        metrics.total_execution_time += execution_time;
        
        if success {
            metrics.successful_requests += 1;
        } else {
            metrics.failed_requests += 1;
        }
        
        // 更新服务级别指标
        let service_metrics = metrics.service_metrics.entry(service_id.clone()).or_insert_with(ServiceMetrics::default);
        service_metrics.total_requests += 1;
        service_metrics.total_execution_time += execution_time;
        
        if success {
            service_metrics.successful_requests += 1;
        } else {
            service_metrics.failed_requests += 1;
        }
    }
}

impl Default for MetricsCollector {
    fn default() -> Self {
        Self::new()
    }
}

/// 系统指标
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct SystemMetrics {
    pub total_requests: u64,
    pub successful_requests: u64,
    pub failed_requests: u64,
    pub total_execution_time: Duration,
    pub service_metrics: HashMap<ServiceId, ServiceMetrics>,
}

impl SystemMetrics {
    pub fn success_rate(&self) -> f64 {
        if self.total_requests > 0 {
            self.successful_requests as f64 / self.total_requests as f64
        } else {
            0.0
        }
    }
    
    pub fn average_execution_time(&self) -> Duration {
        if self.total_requests > 0 {
            self.total_execution_time / self.total_requests as u32
        } else {
            Duration::ZERO
        }
    }
}

/// 服务指标
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ServiceMetrics {
    pub total_requests: u64,
    pub successful_requests: u64,
    pub failed_requests: u64,
    pub total_execution_time: Duration,
}

impl ServiceMetrics {
    pub fn success_rate(&self) -> f64 {
        if self.total_requests > 0 {
            self.successful_requests as f64 / self.total_requests as f64
        } else {
            0.0
        }
    }
    
    pub fn average_execution_time(&self) -> Duration {
        if self.total_requests > 0 {
            self.total_execution_time / self.total_requests as u32
        } else {
            Duration::ZERO
        }
    }
}

/// 服务网格 (Service Mesh)
/// 
/// 为微服务提供透明的网络通信、负载均衡、服务发现、
/// 安全、监控等基础设施功能
#[derive(Debug)]
pub struct ServiceMesh {
    /// 网格名称
    name: String,
    /// 注册的服务代理
    proxies: Arc<RwLock<HashMap<ServiceId, SidecarProxy>>>,
    /// 流量管理规则
    traffic_rules: Arc<RwLock<Vec<TrafficRule>>>,
    /// 安全策略
    security_policies: Arc<RwLock<HashMap<ServiceId, SecurityPolicy>>>,
    /// 可观测性配置
    observability_config: Arc<RwLock<ObservabilityConfig>>,
}

/// Sidecar代理
#[derive(Debug, Clone)]
pub struct SidecarProxy {
    /// 服务ID
    service_id: ServiceId,
    /// 代理地址
    proxy_address: SocketAddr,
    /// 服务地址
    service_address: SocketAddr,
    /// 启用的功能
    enabled_features: HashSet<ProxyFeature>,
    /// 统计信息
    stats: ProxyStats,
}

/// 代理功能
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ProxyFeature {
    /// 负载均衡
    LoadBalancing,
    /// 熔断器
    CircuitBreaking,
    /// 重试
    Retry,
    /// 超时
    Timeout,
    /// TLS终止
    TlsTermination,
    /// 请求追踪
    Tracing,
    /// 指标收集
    Metrics,
}

/// 代理统计信息
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ProxyStats {
    pub total_requests: u64,
    pub successful_requests: u64,
    pub failed_requests: u64,
    pub average_latency_ms: f64,
    pub p95_latency_ms: f64,
    pub p99_latency_ms: f64,
}

/// 流量规则
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TrafficRule {
    /// 规则ID
    pub id: String,
    /// 源服务
    pub source_service: ServiceId,
    /// 目标服务
    pub destination_service: ServiceId,
    /// 流量分配
    pub traffic_split: Vec<TrafficSplit>,
    /// 重试策略
    pub retry_policy: Option<RetryPolicy>,
    /// 超时设置
    pub timeout: Option<Duration>,
}

/// 流量分配
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TrafficSplit {
    /// 目标版本
    pub version: String,
    /// 流量权重 (0-100)
    pub weight: u32,
}

/// 重试策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RetryPolicy {
    /// 最大重试次数
    pub max_attempts: u32,
    /// 重试间隔
    pub retry_interval: Duration,
    /// 可重试的错误码
    pub retryable_status_codes: Vec<u16>,
}

/// 安全策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SecurityPolicy {
    /// 启用mTLS
    pub enable_mtls: bool,
    /// 允许的服务列表
    pub allowed_services: HashSet<ServiceId>,
    /// JWT验证
    pub jwt_validation: Option<JwtValidation>,
    /// 访问控制
    pub access_control: Vec<AccessRule>,
}

/// JWT验证配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct JwtValidation {
    pub issuer: String,
    pub audience: String,
    pub public_key: String,
}

/// 访问控制规则
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AccessRule {
    pub path_pattern: String,
    pub allowed_methods: Vec<String>,
    pub required_roles: Vec<String>,
}

/// 可观测性配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ObservabilityConfig {
    /// 启用追踪
    pub enable_tracing: bool,
    /// 采样率 (0.0-1.0)
    pub tracing_sample_rate: f64,
    /// 启用指标
    pub enable_metrics: bool,
    /// 指标导出端点
    pub metrics_endpoint: Option<String>,
    /// 启用日志
    pub enable_logging: bool,
    /// 日志级别
    pub log_level: LogLevel,
}

/// 日志级别
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum LogLevel {
    Trace,
    Debug,
    Info,
    Warn,
    Error,
}

impl ServiceMesh {
    /// 创建新的服务网格
    pub fn new(name: String) -> Self {
        Self {
            name,
            proxies: Arc::new(RwLock::new(HashMap::new())),
            traffic_rules: Arc::new(RwLock::new(Vec::new())),
            security_policies: Arc::new(RwLock::new(HashMap::new())),
            observability_config: Arc::new(RwLock::new(ObservabilityConfig {
                enable_tracing: true,
                tracing_sample_rate: 0.1,
                enable_metrics: true,
                metrics_endpoint: None,
                enable_logging: true,
                log_level: LogLevel::Info,
            })),
        }
    }
    
    /// 注册Sidecar代理
    pub fn register_proxy(&self, proxy: SidecarProxy) -> MicroserviceResult<()> {
        let mut proxies = self.proxies.write()
            .map_err(|e| ModelError::LockError(format!("无法获取代理写锁: {}", e)))?;
        
        proxies.insert(proxy.service_id.clone(), proxy);
        Ok(())
    }
    
    /// 获取代理
    pub fn get_proxy(&self, service_id: &ServiceId) -> MicroserviceResult<Option<SidecarProxy>> {
        let proxies = self.proxies.read()
            .map_err(|e| ModelError::LockError(format!("无法获取代理读锁: {}", e)))?;
        
        Ok(proxies.get(service_id).cloned())
    }
    
    /// 添加流量规则
    pub fn add_traffic_rule(&self, rule: TrafficRule) -> MicroserviceResult<()> {
        let mut rules = self.traffic_rules.write()
            .map_err(|e| ModelError::LockError(format!("无法获取流量规则写锁: {}", e)))?;
        
        rules.push(rule);
        Ok(())
    }
    
    /// 设置安全策略
    pub fn set_security_policy(&self, service_id: ServiceId, policy: SecurityPolicy) -> MicroserviceResult<()> {
        let mut policies = self.security_policies.write()
            .map_err(|e| ModelError::LockError(format!("无法获取安全策略写锁: {}", e)))?;
        
        policies.insert(service_id, policy);
        Ok(())
    }
    
    /// 更新可观测性配置
    pub fn update_observability_config(&self, config: ObservabilityConfig) -> MicroserviceResult<()> {
        let mut obs_config = self.observability_config.write()
            .map_err(|e| ModelError::LockError(format!("无法获取可观测性配置写锁: {}", e)))?;
        
        *obs_config = config;
        Ok(())
    }
    
    /// 获取网格统计
    pub fn get_mesh_stats(&self) -> MicroserviceResult<MeshStats> {
        let proxies = self.proxies.read()
            .map_err(|e| ModelError::LockError(format!("无法获取代理读锁: {}", e)))?;
        
        let total_services = proxies.len();
        let total_requests: u64 = proxies.values().map(|p| p.stats.total_requests).sum();
        let successful_requests: u64 = proxies.values().map(|p| p.stats.successful_requests).sum();
        let failed_requests: u64 = proxies.values().map(|p| p.stats.failed_requests).sum();
        
        let avg_latency = if total_services > 0 {
            proxies.values().map(|p| p.stats.average_latency_ms).sum::<f64>() / total_services as f64
        } else {
            0.0
        };
        
        Ok(MeshStats {
            total_services,
            total_requests,
            successful_requests,
            failed_requests,
            average_latency_ms: avg_latency,
        })
    }
    
    /// 获取网格名称
    pub fn name(&self) -> &str {
        &self.name
    }
}

/// 网格统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MeshStats {
    pub total_services: usize,
    pub total_requests: u64,
    pub successful_requests: u64,
    pub failed_requests: u64,
    pub average_latency_ms: f64,
}

impl SidecarProxy {
    /// 创建新的Sidecar代理
    pub fn new(service_id: ServiceId, proxy_address: SocketAddr, service_address: SocketAddr) -> Self {
        Self {
            service_id,
            proxy_address,
            service_address,
            enabled_features: HashSet::new(),
            stats: ProxyStats::default(),
        }
    }
    
    /// 启用功能
    pub fn enable_feature(&mut self, feature: ProxyFeature) {
        self.enabled_features.insert(feature);
    }
    
    /// 检查功能是否启用
    pub fn is_feature_enabled(&self, feature: &ProxyFeature) -> bool {
        self.enabled_features.contains(feature)
    }
    
    /// 更新统计信息
    pub fn update_stats(&mut self, success: bool, latency_ms: f64) {
        self.stats.total_requests += 1;
        if success {
            self.stats.successful_requests += 1;
        } else {
            self.stats.failed_requests += 1;
        }
        
        // 简化的平均延迟计算
        self.stats.average_latency_ms = 
            (self.stats.average_latency_ms * (self.stats.total_requests - 1) as f64 + latency_ms) 
            / self.stats.total_requests as f64;
    }
    
    /// 获取代理地址
    pub fn proxy_address(&self) -> &SocketAddr {
        &self.proxy_address
    }
    
    /// 获取服务地址
    pub fn service_address(&self) -> &SocketAddr {
        &self.service_address
    }
}

/// 分布式追踪系统
/// 
/// 实现分布式追踪功能，用于追踪跨服务的请求链路
#[derive(Debug)]
pub struct DistributedTracing {
    /// 追踪系统名称
    name: String,
    /// 活动的追踪
    active_traces: Arc<RwLock<HashMap<String, Trace>>>,
    /// 已完成的追踪
    completed_traces: Arc<RwLock<VecDeque<Trace>>>,
    /// 采样率
    sample_rate: Arc<RwLock<f64>>,
    /// 最大保存的追踪数量
    max_traces: usize,
}

/// 追踪
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Trace {
    /// 追踪ID
    pub trace_id: String,
    /// 根Span
    pub root_span: Span,
    /// 所有Span
    pub spans: Vec<Span>,
    /// 开始时间
    pub start_time: SystemTime,
    /// 结束时间
    pub end_time: Option<SystemTime>,
    /// 状态
    pub status: TraceStatus,
}

/// 追踪状态
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum TraceStatus {
    Active,
    Completed,
    Failed,
}

/// Span (追踪片段)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Span {
    /// Span ID
    pub span_id: String,
    /// 父Span ID
    pub parent_span_id: Option<String>,
    /// 追踪ID
    pub trace_id: String,
    /// 服务名称
    pub service_name: String,
    /// 操作名称
    pub operation_name: String,
    /// 开始时间
    pub start_time: SystemTime,
    /// 结束时间
    pub end_time: Option<SystemTime>,
    /// 持续时间(毫秒)
    pub duration_ms: Option<f64>,
    /// 标签
    pub tags: HashMap<String, String>,
    /// 日志
    pub logs: Vec<SpanLog>,
    /// 状态
    pub status: SpanStatus,
}

/// Span状态
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum SpanStatus {
    Running,
    Ok,
    Error,
}

/// Span日志
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SpanLog {
    pub timestamp: SystemTime,
    pub message: String,
    pub fields: HashMap<String, String>,
}

impl DistributedTracing {
    /// 创建新的分布式追踪系统
    pub fn new(name: String, sample_rate: f64) -> Self {
        Self {
            name,
            active_traces: Arc::new(RwLock::new(HashMap::new())),
            completed_traces: Arc::new(RwLock::new(VecDeque::new())),
            sample_rate: Arc::new(RwLock::new(sample_rate)),
            max_traces: 1000,
        }
    }
    
    /// 开始新的追踪
    pub fn start_trace(&self, trace_id: String, service_name: String, operation_name: String) -> MicroserviceResult<Span> {
        // 检查采样率
        let sample_rate = *self.sample_rate.read()
            .map_err(|e| ModelError::LockError(format!("无法获取采样率读锁: {}", e)))?;
        
        // 简化：总是采样（实际应该使用随机数）
        if sample_rate <= 0.0 {
            return Err(ModelError::ComputationError("采样率过低，跳过追踪".to_string()));
        }
        
        let span_id = format!("{}-root", trace_id);
        let span = Span {
            span_id: span_id.clone(),
            parent_span_id: None,
            trace_id: trace_id.clone(),
            service_name,
            operation_name,
            start_time: SystemTime::now(),
            end_time: None,
            duration_ms: None,
            tags: HashMap::new(),
            logs: Vec::new(),
            status: SpanStatus::Running,
        };
        
        let trace = Trace {
            trace_id: trace_id.clone(),
            root_span: span.clone(),
            spans: vec![span.clone()],
            start_time: SystemTime::now(),
            end_time: None,
            status: TraceStatus::Active,
        };
        
        let mut traces = self.active_traces.write()
            .map_err(|e| ModelError::LockError(format!("无法获取活动追踪写锁: {}", e)))?;
        
        traces.insert(trace_id, trace);
        
        Ok(span)
    }
    
    /// 添加子Span
    pub fn add_span(&self, trace_id: &str, parent_span_id: &str, service_name: String, operation_name: String) -> MicroserviceResult<Span> {
        let span_id = format!("{}-{}", trace_id, uuid::Uuid::new_v4().to_string()[..8].to_string());
        
        let span = Span {
            span_id: span_id.clone(),
            parent_span_id: Some(parent_span_id.to_string()),
            trace_id: trace_id.to_string(),
            service_name,
            operation_name,
            start_time: SystemTime::now(),
            end_time: None,
            duration_ms: None,
            tags: HashMap::new(),
            logs: Vec::new(),
            status: SpanStatus::Running,
        };
        
        let mut traces = self.active_traces.write()
            .map_err(|e| ModelError::LockError(format!("无法获取活动追踪写锁: {}", e)))?;
        
        if let Some(trace) = traces.get_mut(trace_id) {
            trace.spans.push(span.clone());
        } else {
            return Err(ModelError::ValidationError(format!("追踪{}不存在", trace_id)));
        }
        
        Ok(span)
    }
    
    /// 结束Span
    pub fn end_span(&self, trace_id: &str, span_id: &str, status: SpanStatus) -> MicroserviceResult<()> {
        let mut traces = self.active_traces.write()
            .map_err(|e| ModelError::LockError(format!("无法获取活动追踪写锁: {}", e)))?;
        
        if let Some(trace) = traces.get_mut(trace_id) {
            if let Some(span) = trace.spans.iter_mut().find(|s| s.span_id == span_id) {
                let end_time = SystemTime::now();
                span.end_time = Some(end_time);
                span.status = status;
                
                if let Ok(duration) = end_time.duration_since(span.start_time) {
                    span.duration_ms = Some(duration.as_secs_f64() * 1000.0);
                }
            }
        }
        
        Ok(())
    }
    
    /// 完成追踪
    pub fn finish_trace(&self, trace_id: &str) -> MicroserviceResult<()> {
        let mut active_traces = self.active_traces.write()
            .map_err(|e| ModelError::LockError(format!("无法获取活动追踪写锁: {}", e)))?;
        
        if let Some(mut trace) = active_traces.remove(trace_id) {
            trace.end_time = Some(SystemTime::now());
            trace.status = TraceStatus::Completed;
            
            let mut completed_traces = self.completed_traces.write()
                .map_err(|e| ModelError::LockError(format!("无法获取已完成追踪写锁: {}", e)))?;
            
            // 限制保存的追踪数量
            if completed_traces.len() >= self.max_traces {
                completed_traces.pop_front();
            }
            
            completed_traces.push_back(trace);
        }
        
        Ok(())
    }
    
    /// 获取追踪
    pub fn get_trace(&self, trace_id: &str) -> MicroserviceResult<Option<Trace>> {
        let active_traces = self.active_traces.read()
            .map_err(|e| ModelError::LockError(format!("无法获取活动追踪读锁: {}", e)))?;
        
        if let Some(trace) = active_traces.get(trace_id) {
            return Ok(Some(trace.clone()));
        }
        
        let completed_traces = self.completed_traces.read()
            .map_err(|e| ModelError::LockError(format!("无法获取已完成追踪读锁: {}", e)))?;
        
        Ok(completed_traces.iter().find(|t| t.trace_id == trace_id).cloned())
    }
    
    /// 获取追踪统计
    pub fn get_stats(&self) -> MicroserviceResult<TracingStats> {
        let active_traces = self.active_traces.read()
            .map_err(|e| ModelError::LockError(format!("无法获取活动追踪读锁: {}", e)))?;
        
        let completed_traces = self.completed_traces.read()
            .map_err(|e| ModelError::LockError(format!("无法获取已完成追踪读锁: {}", e)))?;
        
        let total_spans: usize = completed_traces.iter().map(|t| t.spans.len()).sum();
        
        let avg_span_duration = if total_spans > 0 {
            let total_duration: f64 = completed_traces.iter()
                .flat_map(|t| &t.spans)
                .filter_map(|s| s.duration_ms)
                .sum();
            total_duration / total_spans as f64
        } else {
            0.0
        };
        
        Ok(TracingStats {
            active_traces: active_traces.len(),
            completed_traces: completed_traces.len(),
            total_spans,
            average_span_duration_ms: avg_span_duration,
        })
    }
    
    /// 设置采样率
    pub fn set_sample_rate(&self, rate: f64) -> MicroserviceResult<()> {
        let mut sample_rate = self.sample_rate.write()
            .map_err(|e| ModelError::LockError(format!("无法获取采样率写锁: {}", e)))?;
        
        *sample_rate = rate.max(0.0).min(1.0);
        Ok(())
    }
    
    /// 获取追踪系统名称
    pub fn name(&self) -> &str {
        &self.name
    }
}

/// 追踪统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TracingStats {
    pub active_traces: usize,
    pub completed_traces: usize,
    pub total_spans: usize,
    pub average_span_duration_ms: f64,
}

impl Span {
    /// 添加标签
    pub fn add_tag(&mut self, key: String, value: String) {
        self.tags.insert(key, value);
    }
    
    /// 添加日志
    pub fn add_log(&mut self, message: String, fields: HashMap<String, String>) {
        self.logs.push(SpanLog {
            timestamp: SystemTime::now(),
            message,
            fields,
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::net::{IpAddr, Ipv4Addr};
    
    #[test]
    fn test_service_registry() {
        let registry = ServiceRegistry::new(Duration::from_secs(1), Duration::from_secs(5));
        
        let instance = ServiceInstance::new(
            "instance1".to_string(),
            "user-service".to_string(),
            SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8080),
        );
        
        registry.register(instance).unwrap();
        
        let instances = registry.discover(&"user-service".to_string());
        assert_eq!(instances.len(), 1);
        assert_eq!(instances[0].id, "instance1");
    }
    
    #[test]
    fn test_load_balancer() {
        let registry = Arc::new(ServiceRegistry::new(Duration::from_secs(1), Duration::from_secs(5)));
        let lb = LoadBalancer::new(LoadBalancingStrategy::RoundRobin, Arc::clone(&registry));
        
        // 注册多个实例
        for i in 0..3 {
            let instance = ServiceInstance::new(
                format!("instance{}", i),
                "test-service".to_string(),
                SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8080 + i),
            );
            registry.register(instance).unwrap();
        }
        
        // 测试轮询
        let mut selected_instances = HashSet::new();
        for _ in 0..6 {
            let instance = lb.select_instance(&"test-service".to_string(), None).unwrap();
            selected_instances.insert(instance.id);
        }
        
        assert_eq!(selected_instances.len(), 3);
    }
    
    #[tokio::test]
    #[cfg(feature = "tokio-adapter")]
    async fn test_circuit_breaker() {
        let config = CircuitBreakerConfig {
            failure_threshold: 2,
            success_threshold: 1,
            timeout: Duration::from_millis(100),
            reset_timeout: Duration::from_millis(500),
            max_concurrent_requests: 5,
        };
        
        let circuit_breaker = CircuitBreaker::new(config);
        
        // 测试成功请求
        let result = circuit_breaker.execute(|| async {
            Ok::<_, ModelError>("success".to_string())
        }).await;
        assert!(result.is_ok());
        assert_eq!(circuit_breaker.get_state(), CircuitBreakerState::Closed);
        
        // 测试失败请求
        for _ in 0..2 {
            let _ = circuit_breaker.execute(|| async {
                Err::<String, _>(ModelError::ValidationError("error".to_string()))
            }).await;
        }
        
        assert_eq!(circuit_breaker.get_state(), CircuitBreakerState::Open);
        
        // 测试熔断器打开时的请求
        let result = circuit_breaker.execute(|| async {
            Ok::<_, ModelError>("should be rejected".to_string())
        }).await;
        assert!(result.is_err());
    }
    
    #[test]
    fn test_rate_limiter() {
        let rate_limiter = RateLimiter::new(3, Duration::from_secs(1));
        
        // 前3个请求应该被允许
        for _ in 0..3 {
            assert!(rate_limiter.allow_request("client1"));
        }
        
        // 第4个请求应该被拒绝
        assert!(!rate_limiter.allow_request("client1"));
        
        // 不同客户端应该有独立的限制
        assert!(rate_limiter.allow_request("client2"));
    }
    
    #[test]
    fn test_request_router() {
        let mut router = RequestRouter::new();
        router.add_route("/api/users/*".to_string(), "user-service".to_string());
        router.add_route("/api/orders/*".to_string(), "order-service".to_string());
        
        let user_request = ApiRequest {
            method: "GET".to_string(),
            path: "/api/users/123".to_string(),
            headers: HashMap::new(),
            body: String::new(),
            query_params: HashMap::new(),
        };
        
        let service_id = router.route(&user_request).unwrap();
        assert_eq!(service_id, "user-service");
    }
    
    #[test]
    fn test_configuration_manager() {
        let config_manager = ConfigurationManager::new();
        
        config_manager.set_config("database.url".to_string(), ConfigValue::String("localhost:5432".to_string()));
        config_manager.set_config("cache.ttl".to_string(), ConfigValue::Integer(3600));
        
        let db_url = config_manager.get_config("database.url");
        assert_eq!(db_url, Some(ConfigValue::String("localhost:5432".to_string())));
        
        let cache_ttl = config_manager.get_config("cache.ttl");
        assert_eq!(cache_ttl, Some(ConfigValue::Integer(3600)));
    }
    
    #[test]
    fn test_microservice_system_manager() {
        let manager = MicroserviceSystemManager::new();
        
        let instance = ServiceInstance::new(
            "instance1".to_string(),
            "test-service".to_string(),
            SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8080),
        );
        
        manager.register_service(instance).unwrap();
        
        let status = manager.get_system_status();
        assert_eq!(status.total_services, 1);
        assert_eq!(status.total_instances, 1);
        assert_eq!(status.healthy_instances, 1);
    }
    
    #[test]
    fn test_service_mesh() {
        let mesh = ServiceMesh::new("test-mesh".to_string());
        
        // 创建并注册Sidecar代理
        let mut proxy = SidecarProxy::new(
            "service-a".to_string(),
            SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 9000),
            SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8080),
        );
        
        proxy.enable_feature(ProxyFeature::LoadBalancing);
        proxy.enable_feature(ProxyFeature::CircuitBreaking);
        proxy.enable_feature(ProxyFeature::Tracing);
        
        mesh.register_proxy(proxy).unwrap();
        
        // 验证代理注册
        let retrieved_proxy = mesh.get_proxy(&"service-a".to_string()).unwrap();
        assert!(retrieved_proxy.is_some());
        
        let proxy = retrieved_proxy.unwrap();
        assert!(proxy.is_feature_enabled(&ProxyFeature::LoadBalancing));
        assert!(proxy.is_feature_enabled(&ProxyFeature::Tracing));
        
        // 添加流量规则
        let rule = TrafficRule {
            id: "rule1".to_string(),
            source_service: "service-a".to_string(),
            destination_service: "service-b".to_string(),
            traffic_split: vec![
                TrafficSplit { version: "v1".to_string(), weight: 80 },
                TrafficSplit { version: "v2".to_string(), weight: 20 },
            ],
            retry_policy: Some(RetryPolicy {
                max_attempts: 3,
                retry_interval: Duration::from_millis(100),
                retryable_status_codes: vec![500, 502, 503],
            }),
            timeout: Some(Duration::from_secs(5)),
        };
        
        mesh.add_traffic_rule(rule).unwrap();
        
        // 设置安全策略
        let mut allowed_services = HashSet::new();
        allowed_services.insert("service-b".to_string());
        allowed_services.insert("service-c".to_string());
        
        let policy = SecurityPolicy {
            enable_mtls: true,
            allowed_services,
            jwt_validation: Some(JwtValidation {
                issuer: "https://auth.example.com".to_string(),
                audience: "service-a".to_string(),
                public_key: "-----BEGIN PUBLIC KEY-----".to_string(),
            }),
            access_control: vec![
                AccessRule {
                    path_pattern: "/api/*".to_string(),
                    allowed_methods: vec!["GET".to_string(), "POST".to_string()],
                    required_roles: vec!["user".to_string()],
                },
            ],
        };
        
        mesh.set_security_policy("service-a".to_string(), policy).unwrap();
        
        // 验证网格统计
        let stats = mesh.get_mesh_stats().unwrap();
        assert_eq!(stats.total_services, 1);
    }
    
    #[test]
    fn test_sidecar_proxy_stats() {
        let mut proxy = SidecarProxy::new(
            "service-a".to_string(),
            SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 9000),
            SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8080),
        );
        
        // 模拟请求
        proxy.update_stats(true, 10.0);
        proxy.update_stats(true, 20.0);
        proxy.update_stats(false, 15.0);
        
        assert_eq!(proxy.stats.total_requests, 3);
        assert_eq!(proxy.stats.successful_requests, 2);
        assert_eq!(proxy.stats.failed_requests, 1);
        assert_eq!(proxy.stats.average_latency_ms, 15.0);
    }
    
    #[test]
    fn test_distributed_tracing() {
        let tracing = DistributedTracing::new("test-tracer".to_string(), 1.0);
        
        // 开始追踪
        let root_span = tracing.start_trace(
            "trace-123".to_string(),
            "api-gateway".to_string(),
            "handle_request".to_string(),
        ).unwrap();
        
        assert_eq!(root_span.service_name, "api-gateway");
        assert_eq!(root_span.status, SpanStatus::Running);
        
        // 添加子Span
        let child_span = tracing.add_span(
            "trace-123",
            &root_span.span_id,
            "user-service".to_string(),
            "get_user".to_string(),
        ).unwrap();
        
        assert_eq!(child_span.parent_span_id, Some(root_span.span_id.clone()));
        
        // 结束Span
        tracing.end_span("trace-123", &child_span.span_id, SpanStatus::Ok).unwrap();
        tracing.end_span("trace-123", &root_span.span_id, SpanStatus::Ok).unwrap();
        
        // 完成追踪
        tracing.finish_trace("trace-123").unwrap();
        
        // 验证追踪
        let trace = tracing.get_trace("trace-123").unwrap();
        assert!(trace.is_some());
        
        let trace = trace.unwrap();
        assert_eq!(trace.status, TraceStatus::Completed);
        assert_eq!(trace.spans.len(), 2);
        
        // 验证统计
        let stats = tracing.get_stats().unwrap();
        assert_eq!(stats.active_traces, 0);
        assert_eq!(stats.completed_traces, 1);
        assert_eq!(stats.total_spans, 2);
    }
    
    #[test]
    fn test_span_operations() {
        let mut span = Span {
            span_id: "span-1".to_string(),
            parent_span_id: None,
            trace_id: "trace-1".to_string(),
            service_name: "test-service".to_string(),
            operation_name: "test-op".to_string(),
            start_time: SystemTime::now(),
            end_time: None,
            duration_ms: None,
            tags: HashMap::new(),
            logs: Vec::new(),
            status: SpanStatus::Running,
        };
        
        // 添加标签
        span.add_tag("http.method".to_string(), "GET".to_string());
        span.add_tag("http.status_code".to_string(), "200".to_string());
        
        assert_eq!(span.tags.len(), 2);
        assert_eq!(span.tags.get("http.method"), Some(&"GET".to_string()));
        
        // 添加日志
        let mut fields = HashMap::new();
        fields.insert("event".to_string(), "cache_miss".to_string());
        span.add_log("Cache miss occurred".to_string(), fields);
        
        assert_eq!(span.logs.len(), 1);
        assert_eq!(span.logs[0].message, "Cache miss occurred");
    }
    
    #[test]
    fn test_tracing_sample_rate() {
        let tracing = DistributedTracing::new("test-tracer".to_string(), 0.5);
        
        // 设置采样率
        tracing.set_sample_rate(0.8).unwrap();
        
        // 采样率边界测试
        tracing.set_sample_rate(-0.1).unwrap(); // 应该被限制为0.0
        tracing.set_sample_rate(1.5).unwrap();  // 应该被限制为1.0
    }
}
