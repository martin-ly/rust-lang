//! Rust 1.90 生产环境异步模式演示 (历史版本)
//!
//! ⚠️ **历史版本文件** - 本文件仅作为历史参考保留
//!
//! **当前推荐版本**: Rust 1.92.0+ | 最新特性请参考 `rust_192_features_demo.rs`
//! 
//! 本程序展示了在生产环境中使用 Rust 1.90 异步特性的最佳实践，
//! 包括错误处理、监控、重试、熔断器、限流等生产级模式

use std::sync::Arc;
use std::time::{Duration, Instant};
use std::collections::HashMap;
use anyhow::Result;
use tracing::{info, error, warn, debug, instrument};
use serde::{Deserialize, Serialize};
use tokio::sync::{Mutex, Semaphore, RwLock};
use tokio::time::sleep;
use std::sync::atomic::{AtomicU32, AtomicBool, Ordering};

/// 服务健康状态
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum HealthStatus {
    Healthy,
    Degraded,
    Unhealthy,
}

/// 服务指标
#[derive(Debug, Clone)]
pub struct ServiceMetrics {
    pub request_count: u64,
    pub success_count: u64,
    pub error_count: u64,
    pub average_latency_ms: f64,
    pub last_updated: Instant,
}

impl Default for ServiceMetrics {
    fn default() -> Self {
        Self {
            request_count: 0,
            success_count: 0,
            error_count: 0,
            average_latency_ms: 0.0,
            last_updated: Instant::now(),
        }
    }
}

/// 熔断器状态
#[derive(Debug, Clone, PartialEq)]
pub enum CircuitBreakerState {
    Closed,    // 正常状态
    Open,      // 熔断状态
    HalfOpen,  // 半开状态
}

/// 熔断器
pub struct CircuitBreaker {
    state: Arc<AtomicU32>, // 0: Closed, 1: Open, 2: HalfOpen
    failure_count: Arc<AtomicU32>,
    success_count: Arc<AtomicU32>,
    failure_threshold: u32,
    success_threshold: u32,
    timeout_duration: Duration,
    last_failure_time: Arc<Mutex<Option<Instant>>>,
}

impl CircuitBreaker {
    pub fn new(failure_threshold: u32, success_threshold: u32, timeout_duration: Duration) -> Self {
        Self {
            state: Arc::new(AtomicU32::new(0)), // Closed
            failure_count: Arc::new(AtomicU32::new(0)),
            success_count: Arc::new(AtomicU32::new(0)),
            failure_threshold,
            success_threshold,
            timeout_duration,
            last_failure_time: Arc::new(Mutex::new(None)),
        }
    }

    pub fn get_state(&self) -> CircuitBreakerState {
        match self.state.load(Ordering::Relaxed) {
            0 => CircuitBreakerState::Closed,
            1 => CircuitBreakerState::Open,
            2 => CircuitBreakerState::HalfOpen,
            _ => CircuitBreakerState::Closed,
        }
    }

    pub async fn can_execute(&self) -> bool {
        match self.get_state() {
            CircuitBreakerState::Closed => true,
            CircuitBreakerState::HalfOpen => true,
            CircuitBreakerState::Open => {
                // 检查是否应该尝试半开状态
                let last_failure = self.last_failure_time.lock().await;
                if let Some(last) = *last_failure {
                    if last.elapsed() >= self.timeout_duration {
                        self.state.store(2, Ordering::Relaxed); // HalfOpen
                        true
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
        }
    }

    pub fn record_success(&self) {
        match self.get_state() {
            CircuitBreakerState::Closed => {
                // 重置失败计数
                self.failure_count.store(0, Ordering::Relaxed);
            }
            CircuitBreakerState::HalfOpen => {
                let success_count = self.success_count.fetch_add(1, Ordering::Relaxed) + 1;
                if success_count >= self.success_threshold {
                    // 恢复到关闭状态
                    self.state.store(0, Ordering::Relaxed);
                    self.failure_count.store(0, Ordering::Relaxed);
                    self.success_count.store(0, Ordering::Relaxed);
                    info!("熔断器恢复到关闭状态");
                }
            }
            CircuitBreakerState::Open => {
                // 在开放状态下不应该有成功
            }
        }
    }

    pub async fn record_failure(&self) {
        let failure_count = self.failure_count.fetch_add(1, Ordering::Relaxed) + 1;
        
        // 更新最后失败时间
        {
            let mut last_failure = self.last_failure_time.lock().await;
            *last_failure = Some(Instant::now());
        }

        match self.get_state() {
            CircuitBreakerState::Closed => {
                if failure_count >= self.failure_threshold {
                    self.state.store(1, Ordering::Relaxed); // Open
                    warn!("熔断器开启，失败次数: {}", failure_count);
                }
            }
            CircuitBreakerState::HalfOpen => {
                // 半开状态下失败，立即回到开放状态
                self.state.store(1, Ordering::Relaxed);
                warn!("熔断器从半开状态回到开放状态");
            }
            CircuitBreakerState::Open => {
                // 已经在开放状态
            }
        }
    }
}

/// 限流器
#[allow(dead_code)]
pub struct RateLimiter {
    semaphore: Arc<Semaphore>,
    requests_per_second: u32,
    window_duration: Duration,
}

impl RateLimiter {
    pub fn new(requests_per_second: u32) -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(requests_per_second as usize)),
            requests_per_second,
            window_duration: Duration::from_secs(1),
        }
    }

    pub async fn acquire(&self) -> Result<()> {
        let _permit = self.semaphore.acquire().await
            .map_err(|_| anyhow::anyhow!("限流器已关闭"))?;
        Ok(())
    }

    pub fn get_capacity(&self) -> usize {
        self.semaphore.available_permits()
    }
}

/// 重试策略
pub struct RetryPolicy {
    max_retries: usize,
    base_delay: Duration,
    max_delay: Duration,
    backoff_multiplier: f64,
}

impl RetryPolicy {
    pub fn new(max_retries: usize, base_delay_ms: u64) -> Self {
        Self {
            max_retries,
            base_delay: Duration::from_millis(base_delay_ms),
            max_delay: Duration::from_secs(30),
            backoff_multiplier: 2.0,
        }
    }

    pub async fn execute_with_retry<F, T>(&self, operation: F) -> Result<T>
    where
        F: Fn() -> Result<T>,
    {
        let mut last_error = None;
        let mut delay = self.base_delay;

        for attempt in 1..=self.max_retries {
            match operation() {
                Ok(result) => {
                    if attempt > 1 {
                        info!("操作在第 {} 次尝试后成功", attempt);
                    }
                    return Ok(result);
                }
                Err(e) => {
                    last_error = Some(e);
                    if attempt < self.max_retries {
                        warn!("操作失败，第 {} 次重试，延迟: {:?}", attempt, delay);
                        sleep(delay).await;
                        delay = std::cmp::min(
                            Duration::from_millis((delay.as_millis() as f64 * self.backoff_multiplier) as u64),
                            self.max_delay
                        );
                    }
                }
            }
        }

        Err(last_error.unwrap_or_else(|| anyhow::anyhow!("未知错误")))
    }
}

/// 生产级服务
pub struct ProductionService {
    name: String,
    circuit_breaker: CircuitBreaker,
    rate_limiter: RateLimiter,
    retry_policy: RetryPolicy,
    metrics: Arc<RwLock<ServiceMetrics>>,
    health_status: Arc<AtomicU32>, // 0: Healthy, 1: Degraded, 2: Unhealthy
    is_shutdown: Arc<AtomicBool>,
}

impl ProductionService {
    pub fn new(name: String) -> Self {
        Self {
            name: name.clone(),
            circuit_breaker: CircuitBreaker::new(5, 3, Duration::from_secs(30)),
            rate_limiter: RateLimiter::new(100),
            retry_policy: RetryPolicy::new(3, 100),
            metrics: Arc::new(RwLock::new(ServiceMetrics::default())),
            health_status: Arc::new(AtomicU32::new(0)), // Healthy
            is_shutdown: Arc::new(AtomicBool::new(false)),
        }
    }

    /// 处理请求 - 生产级实现
    #[instrument(skip(self))]
    pub async fn handle_request(&self, request_id: &str) -> Result<String> {
        if self.is_shutdown.load(Ordering::Relaxed) {
            return Err(anyhow::anyhow!("服务已关闭"));
        }

        // 检查熔断器
        if !self.circuit_breaker.can_execute().await {
            warn!("熔断器开启，拒绝请求: {}", request_id);
            return Err(anyhow::anyhow!("服务暂时不可用"));
        }

        // 限流检查
        self.rate_limiter.acquire().await?;

        let start_time = Instant::now();
        let mut success = false;

        // 执行请求处理
        let result = self.retry_policy.execute_with_retry(|| {
            self.process_request_internal(request_id)
        }).await;

        let final_result = match result {
            Ok(response) => {
                success = true;
                self.circuit_breaker.record_success();
                self.update_health_status(HealthStatus::Healthy);
                Ok(response)
            }
            Err(e) => {
                self.circuit_breaker.record_failure().await;
                self.update_health_status(HealthStatus::Degraded);
                Err(e)
            }
        };

        // 更新指标
        let latency = start_time.elapsed().as_millis() as f64;
        self.update_metrics(success, latency).await;

        final_result
    }

    /// 内部请求处理逻辑
    fn process_request_internal(&self, request_id: &str) -> Result<String> {
        // 模拟处理逻辑
        if request_id.contains("error") {
            Err(anyhow::anyhow!("模拟处理错误"))
        } else if request_id.contains("slow") {
            // 模拟慢请求
            std::thread::sleep(Duration::from_millis(100));
            Ok(format!("处理完成: {}", request_id))
        } else {
            Ok(format!("处理完成: {}", request_id))
        }
    }

    /// 更新指标
    async fn update_metrics(&self, success: bool, latency_ms: f64) {
        let mut metrics = self.metrics.write().await;
        metrics.request_count += 1;
        
        if success {
            metrics.success_count += 1;
        } else {
            metrics.error_count += 1;
        }

        // 更新平均延迟
        metrics.average_latency_ms = 
            (metrics.average_latency_ms * (metrics.request_count - 1) as f64 + latency_ms) 
            / metrics.request_count as f64;
        
        metrics.last_updated = Instant::now();
    }

    /// 更新健康状态
    fn update_health_status(&self, status: HealthStatus) {
        let status_value = match status {
            HealthStatus::Healthy => 0,
            HealthStatus::Degraded => 1,
            HealthStatus::Unhealthy => 2,
        };
        self.health_status.store(status_value, Ordering::Relaxed);
    }

    /// 获取健康状态
    pub fn get_health_status(&self) -> HealthStatus {
        match self.health_status.load(Ordering::Relaxed) {
            0 => HealthStatus::Healthy,
            1 => HealthStatus::Degraded,
            2 => HealthStatus::Unhealthy,
            _ => HealthStatus::Unhealthy,
        }
    }

    /// 获取指标
    pub async fn get_metrics(&self) -> ServiceMetrics {
        let metrics = self.metrics.read().await;
        metrics.clone()
    }

    /// 优雅关闭
    pub async fn shutdown(&self) {
        info!("开始关闭服务: {}", self.name);
        self.is_shutdown.store(true, Ordering::Relaxed);
        
        // 等待所有请求完成
        sleep(Duration::from_secs(2)).await;
        
        info!("服务已关闭: {}", self.name);
    }

    /// 健康检查
    pub async fn health_check(&self) -> Result<HealthStatus> {
        let metrics = self.get_metrics().await;
        let health = self.get_health_status();
        
        debug!("健康检查 - 服务: {}, 状态: {:?}, 成功率: {:.2}%", 
            self.name, health, 
            (metrics.success_count as f64 / metrics.request_count as f64) * 100.0);
        
        Ok(health)
    }
}

/// 服务网格管理器
#[allow(dead_code)]
pub struct ServiceMeshManager {
    services: Arc<RwLock<HashMap<String, Arc<ProductionService>>>>,
    global_metrics: Arc<RwLock<ServiceMetrics>>,
}

impl ServiceMeshManager {
    pub fn new() -> Self {
        Self {
            services: Arc::new(RwLock::new(HashMap::new())),
            global_metrics: Arc::new(RwLock::new(ServiceMetrics::default())),
        }
    }

    pub async fn register_service(&self, name: String, service: Arc<ProductionService>) {
        let mut services = self.services.write().await;
        services.insert(name.clone(), service);
        info!("注册服务: {}", name);
    }

    pub async fn call_service(&self, service_name: &str, request_id: &str) -> Result<String> {
        let services = self.services.read().await;
        if let Some(service) = services.get(service_name) {
            service.handle_request(request_id).await
        } else {
            Err(anyhow::anyhow!("服务不存在: {}", service_name))
        }
    }

    pub async fn get_all_health_status(&self) -> HashMap<String, HealthStatus> {
        let services = self.services.read().await;
        let mut status_map = HashMap::new();
        
        for (name, service) in services.iter() {
            status_map.insert(name.clone(), service.get_health_status());
        }
        
        status_map
    }

    pub async fn generate_global_report(&self) -> String {
        let services = self.services.read().await;
        let health_statuses = self.get_all_health_status().await;
        
        let mut report = String::new();
        report.push_str("🌐 服务网格状态报告\n");
        report.push_str("==========================================\n\n");
        
        report.push_str("服务健康状态:\n");
        for (name, status) in &health_statuses {
            report.push_str(&format!("  {}: {:?}\n", name, status));
        }
        
        report.push_str("\n各服务指标:\n");
        for (name, service) in services.iter() {
            let metrics = service.get_metrics().await;
            report.push_str(&format!("  {}: 请求数 {}, 成功率 {:.2}%, 平均延迟 {:.2}ms\n",
                name, 
                metrics.request_count,
                (metrics.success_count as f64 / metrics.request_count as f64) * 100.0,
                metrics.average_latency_ms
            ));
        }
        
        report
    }
}

/// 主演示函数
#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    info!("🚀 开始 Rust 1.90 生产环境异步模式演示");
    info!("==========================================");

    // 创建服务网格管理器
    let mesh_manager = Arc::new(ServiceMeshManager::new());

    // 创建服务
    let user_service = Arc::new(ProductionService::new("user-service".to_string()));
    let order_service = Arc::new(ProductionService::new("order-service".to_string()));
    let payment_service = Arc::new(ProductionService::new("payment-service".to_string()));

    // 注册服务
    mesh_manager.register_service("user-service".to_string(), user_service.clone()).await;
    mesh_manager.register_service("order-service".to_string(), order_service.clone()).await;
    mesh_manager.register_service("payment-service".to_string(), payment_service.clone()).await;

    // 1. 正常请求处理演示
    info!("\n📋 正常请求处理演示:");
    let requests = vec![
        ("user-service", "user_001"),
        ("order-service", "order_002"),
        ("payment-service", "payment_003"),
    ];

    for (service_name, request_id) in requests {
        match mesh_manager.call_service(service_name, request_id).await {
            Ok(response) => info!("请求成功: {} -> {}", service_name, response),
            Err(e) => error!("请求失败: {} -> {}", service_name, e),
        }
    }

    // 2. 错误处理和重试演示
    info!("\n⚠️ 错误处理和重试演示:");
    let error_requests = vec![
        ("user-service", "user_error_001"),
        ("order-service", "order_error_002"),
        ("payment-service", "payment_error_003"),
    ];

    for (service_name, request_id) in error_requests {
        match mesh_manager.call_service(service_name, request_id).await {
            Ok(response) => info!("错误请求处理成功: {} -> {}", service_name, response),
            Err(e) => warn!("错误请求处理失败: {} -> {}", service_name, e),
        }
    }

    // 3. 负载测试演示
    info!("\n🔥 负载测试演示:");
    let mut handles = Vec::new();
    
    for i in 0..20 {
        let mesh_manager = Arc::clone(&mesh_manager);
        let handle = tokio::spawn(async move {
            let service_name = match i % 3 {
                0 => "user-service",
                1 => "order-service",
                _ => "payment-service",
            };
            let request_id = format!("load_test_{}", i);
            
            mesh_manager.call_service(service_name, &request_id).await
        });
        handles.push(handle);
    }

    // 等待所有负载测试完成
    let mut success_count = 0;
    for handle in handles {
        if let Ok(Ok(_)) = handle.await {
            success_count += 1;
        }
    }
    info!("负载测试完成，成功率: {}/20", success_count);

    // 4. 健康检查演示
    info!("\n🏥 健康检查演示:");
    let health_statuses = mesh_manager.get_all_health_status().await;
    for (service_name, status) in &health_statuses {
        info!("服务 {} 健康状态: {:?}", service_name, status);
    }

    // 5. 生成全局报告
    info!("\n📊 全局服务报告:");
    let report = mesh_manager.generate_global_report().await;
    println!("{}", report);

    // 6. 优雅关闭演示
    info!("\n🔒 优雅关闭演示:");
    user_service.shutdown().await;
    order_service.shutdown().await;
    payment_service.shutdown().await;

    info!("✅ Rust 1.90 生产环境异步模式演示完成!");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_circuit_breaker() {
        let cb = CircuitBreaker::new(3, 2, Duration::from_secs(1));
        
        // 测试正常状态
        assert_eq!(cb.get_state(), CircuitBreakerState::Closed);
        assert!(cb.can_execute().await);
        
        // 模拟失败
        for _ in 0..3 {
            cb.record_failure().await;
        }
        
        // 应该进入开放状态
        assert_eq!(cb.get_state(), CircuitBreakerState::Open);
        assert!(!cb.can_execute().await);
    }

    #[tokio::test]
    async fn test_rate_limiter() {
        let limiter = RateLimiter::new(5);
        
        // 应该能够获取许可
        assert!(limiter.acquire().await.is_ok());
        assert_eq!(limiter.get_capacity(), 4);
    }

    #[tokio::test]
    async fn test_retry_policy() {
        let policy = RetryPolicy::new(3, 10);
        
        let mut attempt_count = 0;
        let result = policy.execute_with_retry(|| {
            attempt_count += 1;
            if attempt_count < 3 {
                Err(anyhow::anyhow!("模拟错误"))
            } else {
                Ok("成功")
            }
        }).await;
        
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), "成功");
        assert_eq!(attempt_count, 3);
    }

    #[tokio::test]
    async fn test_production_service() {
        let service = ProductionService::new("test-service".to_string());
        
        // 测试正常请求
        let result = service.handle_request("test_request").await;
        assert!(result.is_ok());
        
        // 测试健康状态
        let health = service.health_check().await.unwrap();
        assert_eq!(health, HealthStatus::Healthy);
    }
}
