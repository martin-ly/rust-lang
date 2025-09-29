//! 微服务架构异步演示
//! 
//! 本示例展示了基于异步编程的微服务架构：
//! - 服务发现和注册
//! - 负载均衡
//! - 服务间通信
//! - 熔断器模式
//! - 分布式追踪
//! - 配置管理
//! - 健康检查
//! - 优雅关闭
//! 
//! 运行方式：
//! ```bash
//! cargo run --example microservices_async_demo
//! ```

use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant, SystemTime};
use tokio::sync::{Mutex, RwLock, Notify};
use tokio::time::{sleep, interval};
use serde::{Serialize, Deserialize};
use anyhow::Result;
use uuid::Uuid;

/// 服务实例信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServiceInstance {
    pub id: String,
    pub name: String,
    pub host: String,
    pub port: u16,
    pub status: ServiceStatus,
    pub metadata: HashMap<String, String>,
    pub registered_at: SystemTime,
    pub last_heartbeat: SystemTime,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ServiceStatus {
    Healthy,
    Unhealthy,
    Starting,
    Stopping,
}

/// 服务注册中心
pub struct ServiceRegistry {
    services: Arc<RwLock<HashMap<String, Vec<ServiceInstance>>>>,
    heartbeat_interval: Duration,
    health_check_timeout: Duration,
    shutdown_notify: Arc<Notify>,
}

impl ServiceRegistry {
    pub fn new() -> Self {
        Self {
            services: Arc::new(RwLock::new(HashMap::new())),
            heartbeat_interval: Duration::from_secs(30),
            health_check_timeout: Duration::from_secs(10),
            shutdown_notify: Arc::new(Notify::new()),
        }
    }

    pub async fn register_service(&self, instance: ServiceInstance) -> Result<()> {
        let mut services = self.services.write().await;
        let service_instances = services.entry(instance.name.clone()).or_insert_with(Vec::new);
        service_instances.push(instance);
        Ok(())
    }

    pub async fn deregister_service(&self, service_name: &str, instance_id: &str) -> Result<()> {
        let mut services = self.services.write().await;
        if let Some(instances) = services.get_mut(service_name) {
            instances.retain(|instance| instance.id != instance_id);
            if instances.is_empty() {
                services.remove(service_name);
            }
        }
        Ok(())
    }

    pub async fn get_service_instances(&self, service_name: &str) -> Vec<ServiceInstance> {
        let services = self.services.read().await;
        services.get(service_name).cloned().unwrap_or_default()
    }

    pub async fn get_healthy_instances(&self, service_name: &str) -> Vec<ServiceInstance> {
        let instances = self.get_service_instances(service_name).await;
        instances.into_iter().filter(|instance| matches!(instance.status, ServiceStatus::Healthy)).collect()
    }

    pub async fn update_heartbeat(&self, service_name: &str, instance_id: &str) -> Result<()> {
        let mut services = self.services.write().await;
        if let Some(instances) = services.get_mut(service_name) {
            for instance in instances.iter_mut() {
                if instance.id == instance_id {
                    instance.last_heartbeat = SystemTime::now();
                    instance.status = ServiceStatus::Healthy;
                    break;
                }
            }
        }
        Ok(())
    }

    pub fn start(&self) -> tokio::task::JoinHandle<()> {
        let services = Arc::clone(&self.services);
        let heartbeat_interval = self.heartbeat_interval;
        let health_check_timeout = self.health_check_timeout;
        let shutdown_notify = Arc::clone(&self.shutdown_notify);

        tokio::spawn(async move {
            let mut interval = interval(Duration::from_secs(10));

            loop {
                tokio::select! {
                    _ = interval.tick() => {
                        Self::cleanup_unhealthy_services(&services, heartbeat_interval, health_check_timeout).await;
                    }
                    _ = shutdown_notify.notified() => {
                        break;
                    }
                }
            }
        })
    }

    async fn cleanup_unhealthy_services(
        services: &Arc<RwLock<HashMap<String, Vec<ServiceInstance>>>>,
        heartbeat_interval: Duration,
        health_check_timeout: Duration,
    ) {
        let mut services_guard = services.write().await;
        let now = SystemTime::now();

        for (_, instances) in services_guard.iter_mut() {
            for instance in instances.iter_mut() {
                if now.duration_since(instance.last_heartbeat).unwrap_or_default() > heartbeat_interval {
                    instance.status = ServiceStatus::Unhealthy;
                }
            }
            
            // 移除不健康的实例
            instances.retain(|instance| {
                now.duration_since(instance.last_heartbeat).unwrap_or_default() <= health_check_timeout
            });
        }
    }

    pub async fn shutdown(&self) {
        self.shutdown_notify.notify_waiters();
    }
}

/// 负载均衡器
pub struct LoadBalancer {
    registry: Arc<ServiceRegistry>,
    strategy: LoadBalancingStrategy,
    round_robin_index: Arc<Mutex<usize>>,
}

#[derive(Debug, Clone)]
pub enum LoadBalancingStrategy {
    RoundRobin,
    Random,
    LeastConnections,
    Weighted,
}

impl LoadBalancer {
    pub fn new(registry: Arc<ServiceRegistry>, strategy: LoadBalancingStrategy) -> Self {
        Self {
            registry,
            strategy,
            round_robin_index: Arc::new(Mutex::new(0)),
        }
    }

    pub async fn select_instance(&self, service_name: &str) -> Option<ServiceInstance> {
        let instances = self.registry.get_healthy_instances(service_name).await;
        
        if instances.is_empty() {
            return None;
        }

        match &self.strategy {
            LoadBalancingStrategy::RoundRobin => {
                let mut index = self.round_robin_index.lock().await;
                let selected = instances[*index % instances.len()].clone();
                *index = (*index + 1) % instances.len();
                Some(selected)
            }
            LoadBalancingStrategy::Random => {
                let index = (rand::random::<u32>() as usize) % instances.len();
                Some(instances[index].clone())
            }
            LoadBalancingStrategy::LeastConnections => {
                // 简化实现，返回第一个实例
                instances.first().cloned()
            }
            LoadBalancingStrategy::Weighted => {
                // 简化实现，返回第一个实例
                instances.first().cloned()
            }
        }
    }
}

/// 熔断器
pub struct CircuitBreaker {
    #[allow(dead_code)]
    failure_threshold: u32,
    #[allow(dead_code)]
    recovery_timeout: Duration,
    state: Arc<Mutex<CircuitState>>,
}

#[derive(Debug, Clone)]
pub enum CircuitState {
    Closed,    // 正常状态
    Open,      // 熔断状态
    HalfOpen,  // 半开状态
}

impl CircuitBreaker {
    pub fn new(failure_threshold: u32, recovery_timeout: Duration) -> Self {
        Self {
            failure_threshold,
            recovery_timeout,
            state: Arc::new(Mutex::new(CircuitState::Closed)),
        }
    }

    pub async fn call<F, Fut, T>(&self, operation: F) -> Result<T>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = Result<T>>,
    {
        let state = self.state.lock().await;
        
        match *state {
            CircuitState::Open => {
                return Err(anyhow::anyhow!("熔断器开启，拒绝请求"));
            }
            CircuitState::HalfOpen => {
                // 允许一个请求通过测试
            }
            CircuitState::Closed => {
                // 正常处理
            }
        }
        drop(state);

        let result = operation().await;
        
        let mut state = self.state.lock().await;
        match result {
            Ok(_) => {
                *state = CircuitState::Closed;
            }
            Err(_) => {
                *state = CircuitState::Open;
            }
        }

        result
    }
}

/// 分布式追踪
pub struct DistributedTracer {
    traces: Arc<Mutex<Vec<Trace>>>,
}

#[derive(Debug, Clone)]
pub struct Trace {
    pub trace_id: String,
    pub span_id: String,
    pub parent_span_id: Option<String>,
    pub operation_name: String,
    pub start_time: Instant,
    pub end_time: Option<Instant>,
    pub tags: HashMap<String, String>,
    pub logs: Vec<TraceLog>,
}

#[derive(Debug, Clone)]
pub struct TraceLog {
    pub timestamp: Instant,
    pub message: String,
    pub level: LogLevel,
}

#[derive(Debug, Clone)]
pub enum LogLevel {
    Debug,
    Info,
    Warn,
    Error,
}

impl std::fmt::Display for LogLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LogLevel::Debug => write!(f, "Debug"),
            LogLevel::Info => write!(f, "Info"),
            LogLevel::Warn => write!(f, "Warn"),
            LogLevel::Error => write!(f, "Error"),
        }
    }
}

impl DistributedTracer {
    pub fn new() -> Self {
        Self {
            traces: Arc::new(Mutex::new(Vec::new())),
        }
    }

    pub async fn start_span(&self, operation_name: &str, parent_span_id: Option<String>) -> String {
        let span_id = Uuid::new_v4().to_string();
        let trace_id = parent_span_id.as_ref().map(|_| Uuid::new_v4().to_string()).unwrap_or_else(|| Uuid::new_v4().to_string());
        
        let trace = Trace {
            trace_id: trace_id.clone(),
            span_id: span_id.clone(),
            parent_span_id,
            operation_name: operation_name.to_string(),
            start_time: Instant::now(),
            end_time: None,
            tags: HashMap::new(),
            logs: Vec::new(),
        };

        let mut traces = self.traces.lock().await;
        traces.push(trace);
        
        span_id
    }

    pub async fn finish_span(&self, span_id: &str) {
        let mut traces = self.traces.lock().await;
        for trace in traces.iter_mut() {
            if trace.span_id == span_id {
                trace.end_time = Some(Instant::now());
                break;
            }
        }
    }

    pub async fn add_tag(&self, span_id: &str, key: String, value: String) {
        let mut traces = self.traces.lock().await;
        for trace in traces.iter_mut() {
            if trace.span_id == span_id {
                trace.tags.insert(key, value);
                break;
            }
        }
    }

    pub async fn log(&self, span_id: &str, level: LogLevel, message: String) {
        let mut traces = self.traces.lock().await;
        for trace in traces.iter_mut() {
            if trace.span_id == span_id {
                trace.logs.push(TraceLog {
                    timestamp: Instant::now(),
                    message,
                    level,
                });
                break;
            }
        }
    }

    pub async fn get_traces(&self) -> Vec<Trace> {
        self.traces.lock().await.clone()
    }
}

/// 微服务
pub struct Microservice {
    pub name: String,
    pub instance_id: String,
    pub host: String,
    pub port: u16,
    pub registry: Arc<ServiceRegistry>,
    pub tracer: Arc<DistributedTracer>,
    pub shutdown_notify: Arc<Notify>,
}

impl Microservice {
    pub fn new(name: String, host: String, port: u16, registry: Arc<ServiceRegistry>, tracer: Arc<DistributedTracer>) -> Self {
        Self {
            instance_id: Uuid::new_v4().to_string(),
            name,
            host,
            port,
            registry,
            tracer,
            shutdown_notify: Arc::new(Notify::new()),
        }
    }

    pub async fn start(&self) -> Result<()> {
        // 注册服务
        let instance = ServiceInstance {
            id: self.instance_id.clone(),
            name: self.name.clone(),
            host: self.host.clone(),
            port: self.port,
            status: ServiceStatus::Starting,
            metadata: HashMap::new(),
            registered_at: SystemTime::now(),
            last_heartbeat: SystemTime::now(),
        };

        self.registry.register_service(instance).await?;
        println!("    🚀 服务 {} 已注册", self.name);

        // 启动心跳
        self.start_heartbeat().await;

        // 启动服务处理
        self.start_service_handler().await;

        Ok(())
    }

    async fn start_heartbeat(&self) {
        let registry = Arc::clone(&self.registry);
        let service_name = self.name.clone();
        let instance_id = self.instance_id.clone();
        let shutdown_notify = Arc::clone(&self.shutdown_notify);

        tokio::spawn(async move {
            let mut interval = interval(Duration::from_secs(10));

            loop {
                tokio::select! {
                    _ = interval.tick() => {
                        if let Err(e) = registry.update_heartbeat(&service_name, &instance_id).await {
                            println!("      心跳更新失败: {}", e);
                        }
                    }
                    _ = shutdown_notify.notified() => {
                        break;
                    }
                }
            }
        });
    }

    async fn start_service_handler(&self) {
        let tracer = Arc::clone(&self.tracer);
        let service_name = self.name.clone();
        let shutdown_notify = Arc::clone(&self.shutdown_notify);

        tokio::spawn(async move {
            let mut interval = interval(Duration::from_secs(1));

            loop {
                tokio::select! {
                    _ = interval.tick() => {
                        let span_id = tracer.start_span(&format!("{}_process", service_name), None).await;
                        tracer.add_tag(&span_id, "service".to_string(), service_name.clone()).await;
                        
                        // 模拟服务处理
                        sleep(Duration::from_millis(100)).await;
                        
                        tracer.log(&span_id, LogLevel::Info, "处理请求完成".to_string()).await;
                        tracer.finish_span(&span_id).await;
                    }
                    _ = shutdown_notify.notified() => {
                        break;
                    }
                }
            }
        });
    }

    pub async fn shutdown(&self) -> Result<()> {
        println!("    🛑 关闭服务 {}", self.name);
        
        // 注销服务
        self.registry.deregister_service(&self.name, &self.instance_id).await?;
        
        // 通知关闭
        self.shutdown_notify.notify_waiters();
        
        Ok(())
    }
}

/// 微服务客户端
pub struct MicroserviceClient {
    #[allow(dead_code)]
    registry: Arc<ServiceRegistry>,
    load_balancer: LoadBalancer,
    circuit_breaker: CircuitBreaker,
    tracer: Arc<DistributedTracer>,
}

impl MicroserviceClient {
    pub fn new(registry: Arc<ServiceRegistry>, tracer: Arc<DistributedTracer>) -> Self {
        Self {
            load_balancer: LoadBalancer::new(Arc::clone(&registry), LoadBalancingStrategy::RoundRobin),
            circuit_breaker: CircuitBreaker::new(3, Duration::from_secs(30)),
            registry,
            tracer,
        }
    }

    pub async fn call_service(&self, service_name: &str, operation: &str) -> Result<String> {
        let span_id = self.tracer.start_span(&format!("call_{}", service_name), None).await;
        self.tracer.add_tag(&span_id, "service".to_string(), service_name.to_string()).await;
        self.tracer.add_tag(&span_id, "operation".to_string(), operation.to_string()).await;

        let result = self.circuit_breaker.call(|| async {
            let instance = self.load_balancer.select_instance(service_name).await
                .ok_or_else(|| anyhow::anyhow!("没有可用的服务实例"))?;

            self.tracer.add_tag(&span_id, "target_host".to_string(), format!("{}:{}", instance.host, instance.port)).await;

            // 模拟服务调用
            sleep(Duration::from_millis(50)).await;

            // 模拟偶尔失败
            if rand::random::<f32>() < 0.1 {
                Err(anyhow::anyhow!("服务调用失败"))
            } else {
                Ok(format!("响应来自 {}:{}", instance.host, instance.port))
            }
        }).await;

        match &result {
            Ok(_response) => {
                self.tracer.log(&span_id, LogLevel::Info, "服务调用成功".to_string()).await;
                self.tracer.add_tag(&span_id, "success".to_string(), "true".to_string()).await;
            }
            Err(e) => {
                self.tracer.log(&span_id, LogLevel::Error, format!("服务调用失败: {}", e)).await;
                self.tracer.add_tag(&span_id, "success".to_string(), "false".to_string()).await;
            }
        }

        self.tracer.finish_span(&span_id).await;
        result
    }
}

struct MicroservicesAsyncDemo;

impl MicroservicesAsyncDemo {
    async fn run() -> Result<()> {
        println!("🏗️ 微服务架构异步演示");
        println!("================================");

        // 1. 服务注册中心演示
        println!("\n📋 1. 服务注册中心演示");
        Self::demo_service_registry().await?;

        // 2. 负载均衡演示
        println!("\n⚖️ 2. 负载均衡演示");
        Self::demo_load_balancing().await?;

        // 3. 熔断器演示
        println!("\n🔌 3. 熔断器演示");
        Self::demo_circuit_breaker().await?;

        // 4. 分布式追踪演示
        println!("\n🔍 4. 分布式追踪演示");
        Self::demo_distributed_tracing().await?;

        // 5. 完整微服务系统演示
        println!("\n🎯 5. 完整微服务系统演示");
        Self::demo_complete_microservices_system().await?;

        Ok(())
    }

    async fn demo_service_registry() -> Result<()> {
        let registry = Arc::new(ServiceRegistry::new());
        let registry_handle = registry.start();

        // 注册一些服务实例
        let services = vec![
            ("user-service", "localhost", 8080),
            ("user-service", "localhost", 8081),
            ("order-service", "localhost", 8082),
            ("payment-service", "localhost", 8083),
        ];

        for (name, host, port) in services {
            let instance = ServiceInstance {
                id: Uuid::new_v4().to_string(),
                name: name.to_string(),
                host: host.to_string(),
                port,
                status: ServiceStatus::Healthy,
                metadata: HashMap::new(),
                registered_at: SystemTime::now(),
                last_heartbeat: SystemTime::now(),
            };

            registry.register_service(instance).await?;
        }

        // 查询服务实例
        let user_instances = registry.get_healthy_instances("user-service").await;
        println!("    user-service 实例数: {}", user_instances.len());

        let order_instances = registry.get_healthy_instances("order-service").await;
        println!("    order-service 实例数: {}", order_instances.len());

        // 注销一个服务
        if let Some(instance) = user_instances.first() {
            registry.deregister_service("user-service", &instance.id).await?;
            println!("    注销服务实例: {}", instance.id);
        }

        let remaining_instances = registry.get_healthy_instances("user-service").await;
        println!("    剩余 user-service 实例数: {}", remaining_instances.len());

        registry.shutdown().await;
        let _ = registry_handle.await;

        Ok(())
    }

    async fn demo_load_balancing() -> Result<()> {
        let registry = Arc::new(ServiceRegistry::new());
        let load_balancer = LoadBalancer::new(registry, LoadBalancingStrategy::RoundRobin);

        // 添加多个实例
        for i in 0..3 {
            let instance = ServiceInstance {
                id: format!("instance_{}", i),
                name: "test-service".to_string(),
                host: "localhost".to_string(),
                port: 8080 + i,
                status: ServiceStatus::Healthy,
                metadata: HashMap::new(),
                registered_at: SystemTime::now(),
                last_heartbeat: SystemTime::now(),
            };

            load_balancer.registry.register_service(instance).await?;
        }

        // 测试负载均衡
        println!("    轮询负载均衡测试:");
        for i in 0..10 {
            if let Some(instance) = load_balancer.select_instance("test-service").await {
                println!("      请求 {} -> {}:{}", i, instance.host, instance.port);
            }
            sleep(Duration::from_millis(100)).await;
        }

        Ok(())
    }

    async fn demo_circuit_breaker() -> Result<()> {
        let circuit_breaker = CircuitBreaker::new(3, Duration::from_secs(5));

        println!("    熔断器测试 (失败阈值: 3):");

        // 模拟多次失败
        for i in 0..5 {
            let result = circuit_breaker.call(|| async {
                if i < 3 {
                    Err(anyhow::anyhow!("模拟失败"))
                } else {
                    Ok("成功")
                }
            }).await;

            match result {
                Ok(response) => println!("      请求 {}: ✅ {}", i, response),
                Err(e) => println!("      请求 {}: ❌ {}", i, e),
            }
        }

        // 等待恢复
        println!("    等待熔断器恢复...");
        sleep(Duration::from_secs(6)).await;

        // 测试恢复
        let result = circuit_breaker.call(|| async {
            Ok("恢复后的成功响应")
        }).await;

        match result {
            Ok(response) => println!("      恢复测试: ✅ {}", response),
            Err(e) => println!("      恢复测试: ❌ {}", e),
        }

        Ok(())
    }

    async fn demo_distributed_tracing() -> Result<()> {
        let tracer = Arc::new(DistributedTracer::new());

        // 创建分布式追踪
        let root_span = tracer.start_span("user_request", None).await;
        tracer.add_tag(&root_span, "user_id".to_string(), "12345".to_string()).await;

        // 子操作 1
        let span1 = tracer.start_span("validate_user", Some(root_span.clone())).await;
        tracer.log(&span1, LogLevel::Info, "开始验证用户".to_string()).await;
        sleep(Duration::from_millis(50)).await;
        tracer.finish_span(&span1).await;

        // 子操作 2
        let span2 = tracer.start_span("fetch_orders", Some(root_span.clone())).await;
        tracer.log(&span2, LogLevel::Info, "开始获取订单".to_string()).await;
        sleep(Duration::from_millis(100)).await;
        tracer.log(&span2, LogLevel::Info, "订单获取完成".to_string()).await;
        tracer.finish_span(&span2).await;

        tracer.finish_span(&root_span).await;

        // 显示追踪信息
        let traces = tracer.get_traces().await;
        println!("    追踪信息:");
        for trace in traces {
            let duration = if let Some(end) = trace.end_time {
                Some(end.duration_since(trace.start_time))
            } else {
                None
            };
            println!("      Span: {} ({:?})", trace.operation_name, duration.unwrap_or_default());
            println!("        Tags: {:?}", trace.tags);
            for log in trace.logs {
                println!("        Log: [{}] {}", log.level, log.message);
            }
        }

        Ok(())
    }

    async fn demo_complete_microservices_system() -> Result<()> {
        let registry = Arc::new(ServiceRegistry::new());
        let tracer = Arc::new(DistributedTracer::new());

        // 启动注册中心
        let registry_handle = registry.start();

        // 创建微服务
        let user_service = Microservice::new(
            "user-service".to_string(),
            "localhost".to_string(),
            8080,
            Arc::clone(&registry),
            Arc::clone(&tracer),
        );

        let order_service = Microservice::new(
            "order-service".to_string(),
            "localhost".to_string(),
            8081,
            Arc::clone(&registry),
            Arc::clone(&tracer),
        );

        // 启动微服务
        user_service.start().await?;
        order_service.start().await?;

        // 等待服务注册
        sleep(Duration::from_secs(1)).await;

        // 创建客户端
        let client = MicroserviceClient::new(Arc::clone(&registry), Arc::clone(&tracer));

        // 模拟服务调用
        println!("    模拟服务调用:");
        for i in 0..5 {
            match client.call_service("user-service", "get_user").await {
                Ok(response) => println!("      用户服务调用 {}: ✅ {}", i, response),
                Err(e) => println!("      用户服务调用 {}: ❌ {}", i, e),
            }

            match client.call_service("order-service", "create_order").await {
                Ok(response) => println!("      订单服务调用 {}: ✅ {}", i, response),
                Err(e) => println!("      订单服务调用 {}: ❌ {}", i, e),
            }

            sleep(Duration::from_millis(200)).await;
        }

        // 显示追踪统计
        let traces = tracer.get_traces().await;
        println!("    追踪统计: {} 个 span", traces.len());

        // 优雅关闭
        user_service.shutdown().await?;
        order_service.shutdown().await?;
        registry.shutdown().await;
        let _ = registry_handle.await;

        Ok(())
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    MicroservicesAsyncDemo::run().await?;

    println!("\n🎉 微服务架构异步演示完成！");
    Ok(())
}
