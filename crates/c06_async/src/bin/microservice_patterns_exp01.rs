use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::RwLock;
use tokio::time::sleep;
use anyhow::{Result, anyhow};
use std::sync::atomic::{AtomicU32, AtomicU64, Ordering};

/// 服务实例信息
#[derive(Debug, Clone)]
struct ServiceInstance {
    id: String,
    health_status: HealthStatus,
    last_heartbeat: Instant,
    load: f64, // 负载指标 (0.0 - 1.0)
}

#[derive(Debug, Clone, PartialEq)]
enum HealthStatus {
    Healthy,
}

impl ServiceInstance {
    fn new(id: String) -> Self {
        Self {
            id,
            health_status: HealthStatus::Healthy,
            last_heartbeat: Instant::now(),
            load: 0.0,
        }
    }

    fn is_available(&self) -> bool {
        self.health_status == HealthStatus::Healthy && 
        self.last_heartbeat.elapsed() < Duration::from_secs(30)
    }
}

/// 服务注册中心
struct ServiceRegistry {
    services: Arc<RwLock<HashMap<String, Vec<ServiceInstance>>>>,
}

impl ServiceRegistry {
    fn new() -> Self {
        Self {
            services: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 注册服务实例
    async fn register_service(&self, service_name: &str, instance: ServiceInstance) {
        let mut services = self.services.write().await;
        let instance_id = instance.id.clone();
        services.entry(service_name.to_string())
            .or_insert_with(Vec::new)
            .push(instance);
        
        println!("📝 服务 {} 实例 {} 已注册", service_name, instance_id);
    }

    /// 获取服务实例列表
    async fn get_service_instances(&self, service_name: &str) -> Vec<ServiceInstance> {
        let services = self.services.read().await;
        services.get(service_name)
            .cloned()
            .unwrap_or_default()
            .into_iter()
            .filter(|i| i.is_available())
            .collect()
    }
}

/// 负载均衡器
struct LoadBalancer {
    strategy: LoadBalancingStrategy,
}

#[derive(Clone, Debug)]
enum LoadBalancingStrategy {
    RoundRobin,
    LeastConnections,
    Random,
}

impl LoadBalancer {
    fn new(strategy: LoadBalancingStrategy) -> Self {
        Self { strategy }
    }

    /// 选择服务实例
    fn select_instance<'a>(&self, instances: &'a [ServiceInstance]) -> Option<&'a ServiceInstance> {
        if instances.is_empty() {
            return None;
        }

        match self.strategy {
            LoadBalancingStrategy::RoundRobin => {
                // 简单的轮询实现
                static COUNTER: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
                let index = COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed) % instances.len();
                instances.get(index)
            }
            LoadBalancingStrategy::LeastConnections => {
                instances.iter().min_by(|a, b| a.load.partial_cmp(&b.load).unwrap())
            }
            LoadBalancingStrategy::Random => {
                use rand::{Rng, rngs::ThreadRng};
                let mut rng = ThreadRng::default();
                let index = rng.random_range(0..instances.len());
                instances.get(index)
            }
        }
    }
}

/// 熔断器
struct CircuitBreaker {
    failure_threshold: u32,
    recovery_timeout: Duration,
    failure_count: AtomicU32,
    last_failure_time: AtomicU64,
    state: AtomicU32, // 0: Closed, 1: Open, 2: HalfOpen
}

impl CircuitBreaker {
    fn new(failure_threshold: u32, recovery_timeout: Duration) -> Self {
        Self {
            failure_threshold,
            recovery_timeout,
            failure_count: AtomicU32::new(0),
            last_failure_time: AtomicU64::new(0),
            state: AtomicU32::new(0), // Closed
        }
    }

    /// 执行操作，应用熔断逻辑
    async fn call<F, Fut, T>(&self, operation: F) -> Result<T, anyhow::Error>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = Result<T, anyhow::Error>>,
    {
        // 检查是否允许执行
        if !self.can_execute() {
            return Err(anyhow!("熔断器打开中，请稍后重试"));
        }

        // 执行操作
        let result = operation().await;

        // 更新状态
        self.update_state(&result);

        result
    }

    /// 检查是否可以执行操作
    fn can_execute(&self) -> bool {
        let state = self.state.load(Ordering::Relaxed);
        match state {
            0 => true, // Closed
            1 => { // Open
                let last_failure = self.last_failure_time.load(Ordering::Relaxed);
                let now = std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap_or_default()
                    .as_secs();
                now - last_failure >= self.recovery_timeout.as_secs()
            }
            2 => true, // HalfOpen
            _ => false,
        }
    }

    /// 更新熔断器状态
    fn update_state<T>(&self, result: &Result<T, anyhow::Error>) {
        match result {
            Ok(_) => {
                // 成功操作
                self.failure_count.store(0, Ordering::Relaxed);
                self.state.store(0, Ordering::Relaxed); // Closed
                println!("🟢 熔断器关闭，服务恢复正常");
            }
            Err(_) => {
                // 失败操作
                let current_failures = self.failure_count.fetch_add(1, Ordering::Relaxed) + 1;
                let now = std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap_or_default()
                    .as_secs();
                self.last_failure_time.store(now, Ordering::Relaxed);

                if current_failures >= self.failure_threshold {
                    self.state.store(1, Ordering::Relaxed); // Open
                    println!("🔴 熔断器打开，失败次数: {}", current_failures);
                } else if self.state.load(Ordering::Relaxed) == 1 {
                    // 从 Open 状态进入 HalfOpen
                    self.state.store(2, Ordering::Relaxed); // HalfOpen
                    println!("🟡 熔断器进入半开状态");
                }
            }
        }
    }
}

/// 模拟微服务调用
async fn simulate_service_call(service_name: &str, instance: &ServiceInstance) -> Result<String> {
    // 模拟网络延迟
    let delay = Duration::from_millis(rand::random::<u64>() % 200 + 50);
    sleep(delay).await;
    
    // 模拟随机失败
    if rand::random::<f64>() < 0.1 { // 10% 失败率
        Err(anyhow!("服务调用失败"))
    } else {
        Ok(format!("服务 {} 实例 {} 响应成功", service_name, instance.id))
    }
}

/// 服务发现和负载均衡测试
async fn test_service_discovery_and_lb() {
    println!("🚀 服务发现和负载均衡测试");
    println!("{}", "=".repeat(50));
    
    let registry = Arc::new(ServiceRegistry::new());
    
    // 注册多个服务实例
    let service_name = "user-service";
    let instances = vec![
        ServiceInstance::new("user-1".to_string()),
        ServiceInstance::new("user-2".to_string()),
        ServiceInstance::new("user-3".to_string()),
    ];
    
    for instance in instances {
        registry.register_service(service_name, instance).await;
    }
    
    // 测试不同负载均衡策略
    let strategies = vec![
        LoadBalancingStrategy::RoundRobin,
        LoadBalancingStrategy::LeastConnections,
        LoadBalancingStrategy::Random,
    ];
    
    for strategy in strategies {
        println!("\n📊 测试负载均衡策略: {:?}", strategy);
        let lb = LoadBalancer::new(strategy);
        
        for i in 0..5 {
            let instances = registry.get_service_instances(service_name).await;
            if let Some(instance) = lb.select_instance(&instances) {
                println!("  请求 {}: 选择实例 {}", i + 1, instance.id);
                
                // 模拟调用
                match simulate_service_call(service_name, instance).await {
                    Ok(response) => println!("    ✅ {}", response),
                    Err(e) => println!("    ❌ {}", e),
                }
            }
        }
    }
}

/// 熔断器测试
async fn test_circuit_breaker() {
    println!("\n🚀 熔断器测试");
    println!("{}", "=".repeat(50));
    
    let breaker = Arc::new(CircuitBreaker::new(3, Duration::from_secs(5)));
    
    // 模拟多次失败
    for i in 0..5 {
        println!("  尝试 {}: ", i + 1);
        match breaker.call(|| async {
            // 模拟失败的操作
            sleep(Duration::from_millis(100)).await;
            Err::<String, _>(anyhow!("模拟失败"))
        }).await {
            Ok(result) => println!("    ✅ {}", result),
            Err(e) => println!("    ❌ {}", e),
        }
    }
    
    // 等待恢复
    println!("\n⏳ 等待熔断器恢复...");
    sleep(Duration::from_secs(6)).await;
    
    // 测试半开状态
    println!("  测试半开状态:");
    match breaker.call(|| async {
        Ok::<String, _>("服务恢复正常".to_string())
    }).await {
        Ok(result) => println!("    ✅ {}", result),
        Err(e) => println!("    ❌ {}", e),
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    println!("🚀 微服务模式示例启动");
    println!("{}", "=".repeat(60));
    
    // 测试服务发现和负载均衡
    test_service_discovery_and_lb().await;
    
    // 测试熔断器
    test_circuit_breaker().await;
    
    println!("\n{}", "=".repeat(60));
    println!("🎯 微服务模式示例完成");
    
    Ok(())
}
