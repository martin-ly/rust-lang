//! Rust 1.90.0 生产级异步应用演示
//! 
//! 本程序演示一个完整的生产级异步应用
//! 包括微服务架构、负载均衡、监控、错误处理等

use std::sync::Arc;
use std::time::{Duration, Instant};
use std::collections::HashMap;
use anyhow::Result;
use tokio::sync::{Mutex, RwLock};
use tokio::time::{sleep, interval, timeout};
use tracing::{info, debug, warn, error, instrument};
use serde::{Deserialize, Serialize};

/// 生产级异步应用管理器
pub struct ProductionAsyncApp {
    pub app_id: String,
    pub version: String,
    pub config: Arc<RwLock<AppConfig>>,
    pub services: Arc<RwLock<HashMap<String, Arc<AsyncService>>>>,
    pub load_balancer: Arc<LoadBalancer>,
    pub metrics_collector: Arc<MetricsCollector>,
    pub health_checker: Arc<HealthChecker>,
    pub circuit_breaker: Arc<CircuitBreaker>,
    pub rate_limiter: Arc<RateLimiter>,
    pub graceful_shutdown: Arc<GracefulShutdown>,
}

/// 应用配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AppConfig {
    pub max_concurrent_requests: usize,
    pub request_timeout: Duration,
    pub health_check_interval: Duration,
    pub metrics_collection_interval: Duration,
    pub circuit_breaker_threshold: usize,
    pub rate_limit_per_second: usize,
}

/// 异步服务
pub struct AsyncService {
    pub service_id: String,
    pub service_type: ServiceType,
    pub endpoint: String,
    pub is_healthy: Arc<Mutex<bool>>,
    pub request_count: Arc<Mutex<usize>>,
    pub error_count: Arc<Mutex<usize>>,
    pub last_response_time: Arc<Mutex<Duration>>,
}

/// 服务类型
#[derive(Debug, Clone)]
pub enum ServiceType {
    ApiGateway,
    UserService,
    OrderService,
    PaymentService,
    NotificationService,
}

/// 负载均衡器
pub struct LoadBalancer {
    pub strategy: LoadBalanceStrategy,
    pub service_registry: Arc<RwLock<HashMap<String, Vec<String>>>>,
    pub round_robin_index: Arc<Mutex<usize>>,
}

/// 负载均衡策略
#[derive(Debug, Clone)]
pub enum LoadBalanceStrategy {
    RoundRobin,
    LeastConnections,
    WeightedRoundRobin,
    Random,
}

/// 指标收集器
pub struct MetricsCollector {
    pub metrics: Arc<RwLock<HashMap<String, MetricValue>>>,
    pub collection_interval: Duration,
    pub is_running: Arc<Mutex<bool>>,
}

/// 指标值
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MetricValue {
    Counter(usize),
    Gauge(f64),
    Histogram(Vec<f64>),
    Timer(Duration),
}

/// 健康检查器
pub struct HealthChecker {
    pub check_interval: Duration,
    pub is_running: Arc<Mutex<bool>>,
    pub failed_checks: Arc<RwLock<HashMap<String, usize>>>,
}

/// 熔断器
pub struct CircuitBreaker {
    pub failure_threshold: usize,
    pub recovery_timeout: Duration,
    pub state: Arc<Mutex<CircuitState>>,
    pub failure_count: Arc<Mutex<usize>>,
    pub last_failure_time: Arc<Mutex<Option<Instant>>>,
}

/// 熔断器状态
#[derive(Debug, Clone)]
pub enum CircuitState {
    Closed,   // 正常状态
    Open,     // 熔断状态
    HalfOpen, // 半开状态
}

/// 限流器
pub struct RateLimiter {
    pub requests_per_second: usize,
    pub tokens: Arc<Mutex<usize>>,
    pub last_refill: Arc<Mutex<Instant>>,
}

/// 优雅关闭管理器
pub struct GracefulShutdown {
    pub shutdown_signal: Arc<Mutex<bool>>,
    pub shutdown_timeout: Duration,
    pub active_connections: Arc<Mutex<usize>>,
}

/// HTTP 请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HttpRequest {
    pub method: String,
    pub path: String,
    pub headers: HashMap<String, String>,
    pub body: Option<String>,
}

/// HTTP 响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HttpResponse {
    pub status_code: u16,
    pub headers: HashMap<String, String>,
    pub body: Option<String>,
    pub processing_time: Duration,
}

impl ProductionAsyncApp {
    pub fn new(app_id: String, version: String) -> Self {
        let config = AppConfig {
            max_concurrent_requests: 1000,
            request_timeout: Duration::from_secs(30),
            health_check_interval: Duration::from_secs(10),
            metrics_collection_interval: Duration::from_secs(5),
            circuit_breaker_threshold: 10,
            rate_limit_per_second: 100,
        };

        Self {
            app_id: app_id.clone(),
            version: version.clone(),
            config: Arc::new(RwLock::new(config)),
            services: Arc::new(RwLock::new(HashMap::new())),
            load_balancer: Arc::new(LoadBalancer::new()),
            metrics_collector: Arc::new(MetricsCollector::new(Duration::from_secs(5))),
            health_checker: Arc::new(HealthChecker::new(Duration::from_secs(10))),
            circuit_breaker: Arc::new(CircuitBreaker::new(10, Duration::from_secs(60))),
            rate_limiter: Arc::new(RateLimiter::new(100)),
            graceful_shutdown: Arc::new(GracefulShutdown::new(Duration::from_secs(30))),
        }
    }

    /// 启动生产级应用
    #[instrument(skip(self))]
    pub async fn start(&self) -> Result<()> {
        info!("🚀 启动生产级异步应用: {} v{}", self.app_id, self.version);
        
        // 1. 初始化服务
        self.initialize_services().await?;
        
        // 2. 启动健康检查
        self.start_health_checking().await?;
        
        // 3. 启动指标收集
        self.start_metrics_collection().await?;
        
        // 4. 启动主服务循环
        self.start_main_service_loop().await?;
        
        info!("✅ 生产级异步应用启动完成");
        Ok(())
    }

    /// 初始化服务
    async fn initialize_services(&self) -> Result<()> {
        info!("🔧 初始化异步服务");
        
        let services = vec![
            ("api_gateway", ServiceType::ApiGateway, "http://localhost:8080"),
            ("user_service", ServiceType::UserService, "http://localhost:8081"),
            ("order_service", ServiceType::OrderService, "http://localhost:8082"),
            ("payment_service", ServiceType::PaymentService, "http://localhost:8083"),
            ("notification_service", ServiceType::NotificationService, "http://localhost:8084"),
        ];

        let mut service_map = self.services.write().await;
        for (id, service_type, endpoint) in services {
            let service = Arc::new(AsyncService {
                service_id: id.to_string(),
                service_type: service_type.clone(),
                endpoint: endpoint.to_string(),
                is_healthy: Arc::new(Mutex::new(true)),
                request_count: Arc::new(Mutex::new(0)),
                error_count: Arc::new(Mutex::new(0)),
                last_response_time: Arc::new(Mutex::new(Duration::from_millis(0))),
            });
            service_map.insert(id.to_string(), service);
            info!("  ✅ 服务 {} 初始化完成", id);
        }

        Ok(())
    }

    /// 启动健康检查
    async fn start_health_checking(&self) -> Result<()> {
        info!("🏥 启动健康检查服务");
        
        let health_checker = Arc::clone(&self.health_checker);
        let services = Arc::clone(&self.services);
        
        tokio::spawn(async move {
            let mut interval = interval(health_checker.check_interval);
            
            loop {
                interval.tick().await;
                
                let services = services.read().await;
                for (service_id, service) in services.iter() {
                    // 简单的健康检查逻辑
                    let error_count = *service.error_count.lock().await;
                    let request_count = *service.request_count.lock().await;
                    
                    let is_healthy = if request_count > 0 {
                        let error_rate = error_count as f64 / request_count as f64;
                        error_rate < 0.1 // 错误率低于10%认为健康
                    } else {
                        true
                    };
                    
                    let mut health = service.is_healthy.lock().await;
                    *health = is_healthy;
                    
                    if !is_healthy {
                        warn!("⚠️ 服务 {} 健康检查失败", service_id);
                    }
                }
            }
        });

        Ok(())
    }

    /// 启动指标收集
    async fn start_metrics_collection(&self) -> Result<()> {
        info!("📊 启动指标收集服务");
        
        let collector = Arc::clone(&self.metrics_collector);
        let services = Arc::clone(&self.services);
        
        tokio::spawn(async move {
            let mut interval = interval(collector.collection_interval);
            
            loop {
                interval.tick().await;
                
                let services = services.read().await;
                for (service_id, service) in services.iter() {
                    let request_count = *service.request_count.lock().await;
                    let error_count = *service.error_count.lock().await;
                    let response_time = *service.last_response_time.lock().await;
                    
                    let mut metrics = collector.metrics.write().await;
                    metrics.insert(
                        format!("{}_requests", service_id),
                        MetricValue::Counter(request_count),
                    );
                    metrics.insert(
                        format!("{}_errors", service_id),
                        MetricValue::Counter(error_count),
                    );
                    metrics.insert(
                        format!("{}_response_time", service_id),
                        MetricValue::Timer(response_time),
                    );
                }
                
                debug!("📈 指标收集完成，收集了 {} 个指标", services.len() * 3);
            }
        });

        Ok(())
    }

    /// 启动主服务循环
    async fn start_main_service_loop(&self) -> Result<()> {
        info!("🔄 启动主服务循环");
        
        // 模拟处理请求
        let mut request_counter = 0;
        let mut interval = interval(Duration::from_millis(100));
        
        loop {
            interval.tick().await;
            request_counter += 1;
            
            // 模拟接收请求
            let request = HttpRequest {
                method: "GET".to_string(),
                path: format!("/api/v1/request/{}", request_counter),
                headers: HashMap::new(),
                body: None,
            };
            
            // 处理请求
            if let Ok(response) = self.process_request(request).await {
                debug!("✅ 请求 {} 处理完成，状态码: {}", 
                       request_counter, response.status_code);
            }
            
            if request_counter >= 100 {
                info!("🎯 完成 {} 个请求的处理演示", request_counter);
                break;
            }
        }
        
        Ok(())
    }

    /// 处理HTTP请求
    #[instrument(skip(self, request))]
    async fn process_request(&self, request: HttpRequest) -> Result<HttpResponse> {
        let start_time = Instant::now();
        
        // 1. 限流检查
        if !self.rate_limiter.allow_request().await {
            return Ok(HttpResponse {
                status_code: 429,
                headers: HashMap::new(),
                body: Some("Rate limit exceeded".to_string()),
                processing_time: start_time.elapsed(),
            });
        }
        
        // 2. 熔断器检查
        if !self.circuit_breaker.allow_request().await {
            return Ok(HttpResponse {
                status_code: 503,
                headers: HashMap::new(),
                body: Some("Service unavailable".to_string()),
                processing_time: start_time.elapsed(),
            });
        }
        
        // 3. 负载均衡选择服务
        let service = self.load_balancer.select_service(&request.path).await?;
        
        // 4. 调用服务
        let response = timeout(
            self.config.read().await.request_timeout,
            self.call_service(&service, &request)
        ).await??;
        
        // 5. 更新指标
        self.update_metrics(&service, start_time.elapsed(), response.status_code == 200).await;
        
        Ok(response)
    }

    /// 调用服务
    async fn call_service(&self, service_id: &str, _request: &HttpRequest) -> Result<HttpResponse> {
        let services = self.services.read().await;
        if let Some(service) = services.get(service_id) {
            // 模拟服务调用
            sleep(Duration::from_millis(10)).await;
            
            let mut request_count = service.request_count.lock().await;
            *request_count += 1;
            
            Ok(HttpResponse {
                status_code: 200,
                headers: HashMap::new(),
                body: Some(format!("Response from {}", service_id)),
                processing_time: Duration::from_millis(10),
            })
        } else {
            Err(anyhow::anyhow!("Service not found: {}", service_id))
        }
    }

    /// 更新指标
    async fn update_metrics(&self, service_id: &str, response_time: Duration, success: bool) {
        let services = self.services.read().await;
        if let Some(service) = services.get(service_id) {
            let mut last_response_time = service.last_response_time.lock().await;
            *last_response_time = response_time;
            
            if !success {
                let mut error_count = service.error_count.lock().await;
                *error_count += 1;
            }
        }
    }

    /// 检查服务健康状态
    #[allow(dead_code)]
    async fn check_service_health(&self, service: &AsyncService) -> Result<bool> {
        // 模拟健康检查
        sleep(Duration::from_millis(5)).await;
        
        // 简单的健康检查逻辑
        let error_count = *service.error_count.lock().await;
        let request_count = *service.request_count.lock().await;
        
        if request_count > 0 {
            let error_rate = error_count as f64 / request_count as f64;
            Ok(error_rate < 0.1) // 错误率低于10%认为健康
        } else {
            Ok(true)
        }
    }

    /// 优雅关闭
    #[allow(dead_code)]
    pub async fn shutdown(&self) -> Result<()> {
        info!("🛑 开始优雅关闭");
        
        let mut shutdown_signal = self.graceful_shutdown.shutdown_signal.lock().await;
        *shutdown_signal = true;
        
        // 等待活跃连接完成
        let start_time = Instant::now();
        while *self.graceful_shutdown.active_connections.lock().await > 0 {
            if start_time.elapsed() > self.graceful_shutdown.shutdown_timeout {
                warn!("⚠️ 优雅关闭超时，强制关闭");
                break;
            }
            sleep(Duration::from_millis(100)).await;
        }
        
        info!("✅ 应用已优雅关闭");
        Ok(())
    }
}

impl LoadBalancer {
    pub fn new() -> Self {
        Self {
            strategy: LoadBalanceStrategy::RoundRobin,
            service_registry: Arc::new(RwLock::new(HashMap::new())),
            round_robin_index: Arc::new(Mutex::new(0)),
        }
    }

    pub async fn select_service(&self, path: &str) -> Result<String> {
        // 简单的路由逻辑
        let service_id = match path {
            path if path.starts_with("/api/users") => "user_service",
            path if path.starts_with("/api/orders") => "order_service",
            path if path.starts_with("/api/payments") => "payment_service",
            path if path.starts_with("/api/notifications") => "notification_service",
            _ => "api_gateway",
        };

        Ok(service_id.to_string())
    }
}

impl MetricsCollector {
    pub fn new(collection_interval: Duration) -> Self {
        Self {
            metrics: Arc::new(RwLock::new(HashMap::new())),
            collection_interval,
            is_running: Arc::new(Mutex::new(true)),
        }
    }
}

impl HealthChecker {
    pub fn new(check_interval: Duration) -> Self {
        Self {
            check_interval,
            is_running: Arc::new(Mutex::new(true)),
            failed_checks: Arc::new(RwLock::new(HashMap::new())),
        }
    }
}

impl CircuitBreaker {
    pub fn new(failure_threshold: usize, recovery_timeout: Duration) -> Self {
        Self {
            failure_threshold,
            recovery_timeout,
            state: Arc::new(Mutex::new(CircuitState::Closed)),
            failure_count: Arc::new(Mutex::new(0)),
            last_failure_time: Arc::new(Mutex::new(None)),
        }
    }

    pub async fn allow_request(&self) -> bool {
        let state = self.state.lock().await;
        match *state {
            CircuitState::Closed => true,
            CircuitState::Open => {
                // 检查是否可以进入半开状态
                let last_failure = *self.last_failure_time.lock().await;
                if let Some(last_failure) = last_failure {
                    if last_failure.elapsed() > self.recovery_timeout {
                        drop(state);
                        let mut new_state = self.state.lock().await;
                        *new_state = CircuitState::HalfOpen;
                        true
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
            CircuitState::HalfOpen => true,
        }
    }
}

impl RateLimiter {
    pub fn new(requests_per_second: usize) -> Self {
        Self {
            requests_per_second,
            tokens: Arc::new(Mutex::new(requests_per_second)),
            last_refill: Arc::new(Mutex::new(Instant::now())),
        }
    }

    pub async fn allow_request(&self) -> bool {
        let mut tokens = self.tokens.lock().await;
        let mut last_refill = self.last_refill.lock().await;
        
        // 令牌桶算法
        let now = Instant::now();
        let elapsed = now.duration_since(*last_refill);
        let tokens_to_add = (elapsed.as_secs_f64() * self.requests_per_second as f64) as usize;
        
        *tokens = (*tokens + tokens_to_add).min(self.requests_per_second);
        *last_refill = now;
        
        if *tokens > 0 {
            *tokens -= 1;
            true
        } else {
            false
        }
    }
}

impl GracefulShutdown {
    pub fn new(shutdown_timeout: Duration) -> Self {
        Self {
            shutdown_signal: Arc::new(Mutex::new(false)),
            shutdown_timeout,
            active_connections: Arc::new(Mutex::new(0)),
        }
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt()
        .with_target(false)
        .with_thread_ids(true)
        .with_thread_names(true)
        .with_max_level(tracing::Level::INFO)
        .init();

    info!("🚀 Rust 1.90.0 生产级异步应用演示");
    info!("==========================================");

    // 创建生产级应用
    let app = Arc::new(ProductionAsyncApp::new(
        "rust-190-production-app".to_string(),
        "1.0.0".to_string(),
    ));

    // 启动应用
    let app_clone = Arc::clone(&app);
    let app_handle = tokio::spawn(async move {
        app_clone.start().await
    });

    // 等待应用运行
    if let Err(e) = app_handle.await? {
        error!("❌ 应用运行错误: {}", e);
        return Err(e);
    }

    // 优雅关闭
    app.shutdown().await?;

    info!("🎉 生产级异步应用演示完成！");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_production_app_creation() {
        let app = ProductionAsyncApp::new(
            "test-app".to_string(),
            "1.0.0".to_string(),
        );
        
        assert_eq!(app.app_id, "test-app");
        assert_eq!(app.version, "1.0.0");
    }

    #[tokio::test]
    async fn test_load_balancer() {
        let lb = LoadBalancer::new();
        let service = lb.select_service("/api/users/123").await.unwrap();
        assert_eq!(service, "user_service");
    }

    #[tokio::test]
    async fn test_rate_limiter() {
        let limiter = RateLimiter::new(10);
        
        // 应该允许前10个请求
        for _ in 0..10 {
            assert!(limiter.allow_request().await);
        }
    }

    #[tokio::test]
    async fn test_circuit_breaker() {
        let cb = CircuitBreaker::new(5, Duration::from_secs(1));
        
        // 初始状态应该是关闭的，允许请求
        assert!(cb.allow_request().await);
    }

    #[tokio::test]
    async fn test_graceful_shutdown() {
        let shutdown = GracefulShutdown::new(Duration::from_secs(1));
        
        // 初始状态应该是运行中
        assert!(!*shutdown.shutdown_signal.lock().await);
    }
}
