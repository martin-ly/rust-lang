use anyhow::Result;
use c06_async::utils::metrics;
use std::sync::LazyLock;
use prometheus::{Histogram, HistogramOpts, IntCounter, IntCounterVec, Opts, Registry};
use rand::Rng;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{RwLock, broadcast};
use tokio::time::sleep;
use tracing::{debug, error, info, instrument, warn};
use uuid::Uuid;

/// 2025年异步API网关演示
/// 展示最新的异步API网关编程模式和最佳实践

/// 1. 异步API网关核心
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct AsyncAPIGateway {
    routes: Arc<RwLock<HashMap<String, Route>>>,
    services: Arc<RwLock<HashMap<String, BackendService>>>,
    middleware_stack: Arc<RwLock<Vec<Middleware>>>,
    gateway_stats: Arc<RwLock<GatewayStats>>,
    config: GatewayConfig,
    event_broadcaster: broadcast::Sender<GatewayEvent>,
}

#[derive(Debug, Clone)]
pub struct Route {
    pub id: String,
    pub path: String,
    pub methods: Vec<HttpMethod>,
    pub backend_service: String,
    pub timeout: Duration,
    pub retry_count: usize,
    pub rate_limit: Option<RateLimit>,
    pub auth_required: bool,
    pub middleware: Vec<String>,
    pub created_at: Instant,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum HttpMethod {
    GET,
    POST,
    PUT,
    DELETE,
    PATCH,
    HEAD,
    OPTIONS,
}

#[derive(Debug, Clone)]
pub struct RateLimit {
    pub requests_per_minute: usize,
    pub burst_size: usize,
    pub window_size: Duration,
}

#[derive(Debug, Clone)]
pub struct BackendService {
    pub id: String,
    pub name: String,
    pub base_url: String,
    pub health_check_url: String,
    pub instances: Vec<ServiceInstance>,
    pub load_balancer: LoadBalancerType,
    pub circuit_breaker: Option<CircuitBreakerConfig>,
    pub timeout: Duration,
    pub is_healthy: bool,
    pub last_health_check: Instant,
}

#[derive(Debug, Clone)]
pub struct ServiceInstance {
    pub id: String,
    pub url: String,
    pub weight: u32,
    pub is_healthy: bool,
    pub response_time: Duration,
    pub error_count: usize,
    pub request_count: usize,
}

#[derive(Debug, Clone, PartialEq)]
pub enum LoadBalancerType {
    RoundRobin,
    WeightedRoundRobin,
    LeastConnections,
    Random,
    ConsistentHash,
}

#[derive(Debug, Clone)]
pub struct CircuitBreakerConfig {
    pub failure_threshold: usize,
    pub success_threshold: usize,
    pub timeout: Duration,
    pub state: CircuitBreakerState,
    pub failure_count: usize,
    pub success_count: usize,
    pub last_failure_time: Option<Instant>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum CircuitBreakerState {
    Closed,
    Open,
    HalfOpen,
}

#[derive(Debug, Clone)]
pub struct Middleware {
    pub id: String,
    pub name: String,
    pub middleware_type: MiddlewareType,
    pub config: HashMap<String, String>,
    pub enabled: bool,
    pub order: usize,
}

#[derive(Debug, Clone, PartialEq)]
pub enum MiddlewareType {
    Authentication,
    Authorization,
    RateLimiting,
    Logging,
    Caching,
    Compression,
    CORS,
    RequestValidation,
    ResponseTransformation,
}

#[derive(Debug, Clone)]
pub struct GatewayConfig {
    pub listen_address: String,
    pub listen_port: u16,
    pub max_concurrent_requests: usize,
    pub request_timeout: Duration,
    pub enable_health_checks: bool,
    pub health_check_interval: Duration,
    pub enable_metrics: bool,
    pub enable_tracing: bool,
}

impl Default for GatewayConfig {
    fn default() -> Self {
        Self {
            listen_address: "0.0.0.0".to_string(),
            listen_port: 8080,
            max_concurrent_requests: 1000,
            request_timeout: Duration::from_secs(30),
            enable_health_checks: true,
            health_check_interval: Duration::from_secs(30),
            enable_metrics: true,
            enable_tracing: true,
        }
    }
}

#[derive(Debug, Clone)]
pub enum GatewayEvent {
    RequestReceived(String, String, HttpMethod),
    RequestCompleted(String, Duration, u16),
    RequestFailed(String, String),
    ServiceUnhealthy(String),
    ServiceHealthy(String),
    CircuitBreakerOpened(String),
    CircuitBreakerClosed(String),
}

#[derive(Debug, Clone, Default)]
pub struct GatewayStats {
    pub total_requests: usize,
    pub successful_requests: usize,
    pub failed_requests: usize,
    pub total_response_time: Duration,
    pub average_response_time: Duration,
    pub active_connections: usize,
    pub rate_limited_requests: usize,
    pub circuit_breaker_trips: usize,
}

impl AsyncAPIGateway {
    pub fn new(config: GatewayConfig) -> Self {
        let (event_broadcaster, _) = broadcast::channel(1000);

        Self {
            routes: Arc::new(RwLock::new(HashMap::new())),
            services: Arc::new(RwLock::new(HashMap::new())),
            middleware_stack: Arc::new(RwLock::new(Vec::new())),
            gateway_stats: Arc::new(RwLock::new(GatewayStats::default())),
            config,
            event_broadcaster,
        }
    }

    pub async fn add_route(&self, route: Route) -> Result<()> {
        let mut routes = self.routes.write().await;
        routes.insert(route.id.clone(), route.clone());

        // 广播事件
        let _ = self.event_broadcaster.send(GatewayEvent::RequestReceived(
            route.id.clone(),
            route.path.clone(),
            HttpMethod::GET, // 默认方法
        ));

        info!(
            "添加路由: {} -> {} ({})",
            route.path, route.backend_service, route.id
        );
        Ok(())
    }

    pub async fn register_service(&self, service: BackendService) -> Result<()> {
        let mut services = self.services.write().await;
        services.insert(service.id.clone(), service.clone());

        info!("注册服务: {} ({})", service.name, service.id);
        Ok(())
    }

    pub async fn add_middleware(&self, middleware: Middleware) -> Result<()> {
        let mut stack = self.middleware_stack.write().await;
        stack.push(middleware.clone());

        // 按顺序排序
        stack.sort_by_key(|m| m.order);

        info!(
            "添加中间件: {} (类型: {:?}, 顺序: {})",
            middleware.name, middleware.middleware_type, middleware.order
        );
        Ok(())
    }

    #[instrument(skip(self, request), fields(path=%request.path, method=?request.method))]
    pub async fn process_request(&self, request: GatewayRequest) -> Result<GatewayResponse> {
        let start_time = Instant::now();

        // 广播请求接收事件
        let _ = self.event_broadcaster.send(GatewayEvent::RequestReceived(
            request.id.clone(),
            request.path.clone(),
            request.method.clone(),
        ));

        // 查找路由
        let route = self.find_route(&request.path, &request.method).await?;

        // 执行中间件链
        let mut context = RequestContext::new(request.clone());

        for middleware in self.middleware_stack.read().await.iter() {
            if middleware.enabled {
                match self.execute_middleware(middleware, &mut context).await {
                    Ok(_) => continue,
                    Err(e) => {
                        let mut stats = self.gateway_stats.write().await;
                        stats.failed_requests += 1;

                        let _ = self.event_broadcaster.send(GatewayEvent::RequestFailed(
                            context.request.id.clone(),
                            e.to_string(),
                        ));

                        return Ok(GatewayResponse {
                            status_code: 500,
                            headers: HashMap::new(),
                            body: format!("中间件错误: {}", e),
                            response_time: start_time.elapsed(),
                        });
                    }
                }
            }
        }

        // 转发到后端服务
        let response = self.forward_to_backend(&route, &context).await?;

        let response_time = start_time.elapsed();

        // 更新统计
        let mut stats = self.gateway_stats.write().await;
        stats.total_requests += 1;
        stats.successful_requests += 1;
        stats.total_response_time += response_time;
        stats.average_response_time = Duration::from_millis(
            ((stats.average_response_time.as_millis() + response_time.as_millis()) / 2) as u64,
        );

        // 广播请求完成事件
        let _ = self.event_broadcaster.send(GatewayEvent::RequestCompleted(
            context.request.id.clone(),
            response_time,
            response.status_code,
        ));

        info!(
            "请求处理完成: {} -> {} (耗时: {:?})",
            context.request.path, response.status_code, response_time
        );

        Ok(response)
    }

    #[instrument(skip(self))]
    async fn find_route(&self, path: &str, method: &HttpMethod) -> Result<Route> {
        let routes = self.routes.read().await;

        for route in routes.values() {
            if route.path == path && route.methods.contains(method) {
                return Ok(route.clone());
            }
        }

        Err(anyhow::anyhow!("未找到匹配的路由: {:?} {}", method, path))
    }

    #[instrument(skip(self, middleware, context), fields(mw_name=%middleware.name, mw_type=?middleware.middleware_type))]
    async fn execute_middleware(
        &self,
        middleware: &Middleware,
        context: &mut RequestContext,
    ) -> Result<()> {
        match middleware.middleware_type {
            MiddlewareType::Authentication => self.execute_auth_middleware(context).await,
            MiddlewareType::RateLimiting => self.execute_rate_limiting_middleware(context).await,
            MiddlewareType::Logging => self.execute_logging_middleware(context).await,
            MiddlewareType::Caching => self.execute_caching_middleware(context).await,
            MiddlewareType::RequestValidation => self.execute_validation_middleware(context).await,
            _ => {
                // 其他中间件类型的默认实现
                debug!("执行中间件: {}", middleware.name);
                Ok(())
            }
        }
    }

    #[instrument(skip(self, context))]
    async fn execute_auth_middleware(&self, context: &mut RequestContext) -> Result<()> {
        // 模拟认证检查
        if let Some(auth_header) = context.request.headers.get("Authorization") {
            if auth_header.starts_with("Bearer ") {
                context.user_id = Some("user_123".to_string());
                debug!("用户认证成功: {}", context.user_id.as_ref().unwrap());
                return Ok(());
            }
        }

        Err(anyhow::anyhow!("认证失败"))
    }

    #[instrument(skip(self, context))]
    async fn execute_rate_limiting_middleware(&self, context: &mut RequestContext) -> Result<()> {
        // 简化的限流实现
        let default_ip = "127.0.0.1".to_string();
        let client_ip = context
            .request
            .headers
            .get("X-Forwarded-For")
            .or_else(|| context.request.headers.get("X-Real-IP"))
            .unwrap_or(&default_ip);

        // 模拟限流检查
        if rand::rng().random::<f64>() < 0.05 {
            let mut stats = self.gateway_stats.write().await;
            stats.rate_limited_requests += 1;
            RATE_LIMITED_TOTAL.with_label_values(&["burst"]).inc();

            return Err(anyhow::anyhow!("请求频率过高"));
        }

        debug!("限流检查通过: {}", client_ip);
        Ok(())
    }

    #[instrument(skip(self, context))]
    async fn execute_logging_middleware(&self, context: &mut RequestContext) -> Result<()> {
        info!(
            "请求日志: {:?} {} {} - 用户: {:?}",
            context.request.method, context.request.path, context.request.id, context.user_id
        );
        Ok(())
    }

    #[instrument(skip(self, context))]
    async fn execute_caching_middleware(&self, context: &mut RequestContext) -> Result<()> {
        // 模拟缓存检查
        if context.request.method == HttpMethod::GET {
            // 检查缓存
            if rand::rng().random::<f64>() < 0.3 {
                context.cached = true;
                debug!("缓存命中: {}", context.request.path);
                RATE_LIMITED_TOTAL.with_label_values(&["cache"]).inc();
            }
        }
        Ok(())
    }

    #[instrument(skip(self, context))]
    async fn execute_validation_middleware(&self, context: &mut RequestContext) -> Result<()> {
        // 模拟请求验证
        if context.request.body.len() > 1024 * 1024 {
            return Err(anyhow::anyhow!("请求体过大"));
        }

        debug!("请求验证通过: {}", context.request.path);
        Ok(())
    }

    #[instrument(skip(self, route, context), fields(backend=%route.backend_service))]
    async fn forward_to_backend(
        &self,
        route: &Route,
        context: &RequestContext,
    ) -> Result<GatewayResponse> {
        let services = self.services.read().await;
        let service = services
            .get(&route.backend_service)
            .ok_or_else(|| anyhow::anyhow!("后端服务 {} 不存在", route.backend_service))?;

        // 选择服务实例
        let instance = self.select_service_instance(service).await?;
        INSTANCE_PICK_TOTAL.with_label_values(&[&instance.id]).inc();

        // 模拟转发请求
        sleep(Duration::from_millis(50 + rand::rng().random_range(0..100))).await;

        // 模拟响应
        let status_code = if rand::rng().random::<f64>() < 0.95 {
            200
        } else {
            500
        };
        BACKEND_STATUS_TOTAL
            .with_label_values(&[if status_code == 200 { "200" } else { "500" }])
            .inc();
        let response_time = Duration::from_millis(50 + rand::rng().random_range(0..100));

        let mut headers = HashMap::new();
        headers.insert("Content-Type".to_string(), "application/json".to_string());
        headers.insert(
            "X-Response-Time".to_string(),
            response_time.as_millis().to_string(),
        );

        let body = if status_code == 200 {
            format!(
                "{{\"message\": \"响应来自 {}\", \"request_id\": \"{}\"}}",
                instance.url, context.request.id
            )
        } else {
            "{\"error\": \"内部服务器错误\"}".to_string()
        };

        Ok(GatewayResponse {
            status_code,
            headers,
            body,
            response_time,
        })
    }

    #[instrument(skip(self, service))]
    async fn select_service_instance<'a>(
        &self,
        service: &'a BackendService,
    ) -> Result<&'a ServiceInstance> {
        let healthy_instances: Vec<&ServiceInstance> = service
            .instances
            .iter()
            .filter(|instance| instance.is_healthy)
            .collect();

        if healthy_instances.is_empty() {
            return Err(anyhow::anyhow!("没有健康的服务实例"));
        }

        match service.load_balancer {
            LoadBalancerType::RoundRobin => {
                let index = rand::rng().random_range(0..healthy_instances.len());
                Ok(healthy_instances[index])
            }
            LoadBalancerType::Random => {
                let index = rand::rng().random_range(0..healthy_instances.len());
                Ok(healthy_instances[index])
            }
            LoadBalancerType::LeastConnections => {
                // 简化实现，返回第一个实例
                Ok(healthy_instances[0])
            }
            _ => Ok(healthy_instances[0]),
        }
    }

    pub async fn get_gateway_stats(&self) -> GatewayStats {
        self.gateway_stats.read().await.clone()
    }
}

#[derive(Debug, Clone)]
pub struct GatewayRequest {
    pub id: String,
    pub method: HttpMethod,
    pub path: String,
    pub headers: HashMap<String, String>,
    pub body: String,
    pub client_ip: String,
    pub timestamp: Instant,
}

#[derive(Debug, Clone)]
pub struct GatewayResponse {
    pub status_code: u16,
    pub headers: HashMap<String, String>,
    pub body: String,
    pub response_time: Duration,
}

#[derive(Debug, Clone)]
pub struct RequestContext {
    pub request: GatewayRequest,
    pub user_id: Option<String>,
    pub cached: bool,
    pub metadata: HashMap<String, String>,
}

impl RequestContext {
    pub fn new(request: GatewayRequest) -> Self {
        Self {
            request,
            user_id: None,
            cached: false,
            metadata: HashMap::new(),
        }
    }
}

/// 2. 异步健康检查系统
#[derive(Debug, Clone)]
pub struct AsyncHealthChecker {
    services: Arc<RwLock<HashMap<String, BackendService>>>,
    health_check_config: HealthCheckConfig,
    health_stats: Arc<RwLock<HealthStats>>,
}

#[derive(Debug, Clone)]
pub struct HealthCheckConfig {
    pub check_interval: Duration,
    pub timeout: Duration,
    pub failure_threshold: usize,
    pub success_threshold: usize,
    pub enable_auto_recovery: bool,
}

impl Default for HealthCheckConfig {
    fn default() -> Self {
        Self {
            check_interval: Duration::from_secs(30),
            timeout: Duration::from_secs(5),
            failure_threshold: 3,
            success_threshold: 2,
            enable_auto_recovery: true,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct HealthStats {
    pub total_checks: usize,
    pub healthy_services: usize,
    pub unhealthy_services: usize,
    pub service_recoveries: usize,
    pub check_errors: usize,
}

impl AsyncHealthChecker {
    pub fn new(config: HealthCheckConfig) -> Self {
        Self {
            services: Arc::new(RwLock::new(HashMap::new())),
            health_check_config: config,
            health_stats: Arc::new(RwLock::new(HealthStats::default())),
        }
    }

    pub async fn register_service(&self, service: BackendService) -> Result<()> {
        let mut services = self.services.write().await;
        services.insert(service.id.clone(), service);
        Ok(())
    }

    pub async fn start_health_checks(&self) -> Result<()> {
        let mut interval = tokio::time::interval(self.health_check_config.check_interval);

        loop {
            interval.tick().await;

            let services = self.services.read().await;
            let mut health_tasks = Vec::new();

            for service in services.values() {
                let checker_clone = self.clone();
                let service_clone = service.clone();

                let task = tokio::spawn(async move {
                    checker_clone.check_service_health(&service_clone).await;
                });

                health_tasks.push(task);
            }

            // 等待所有健康检查完成
            for task in health_tasks {
                let _ = task.await;
            }
        }
    }

    async fn check_service_health(&self, service: &BackendService) {
        let mut stats = self.health_stats.write().await;
        stats.total_checks += 1;

        // 模拟健康检查
        let is_healthy = rand::rng().random::<f64>() > 0.1; // 90% 健康率

        if is_healthy {
            stats.healthy_services += 1;
            info!("服务健康检查通过: {}", service.name);
        } else {
            stats.unhealthy_services += 1;
            stats.check_errors += 1;
            warn!("服务健康检查失败: {}", service.name);
        }
    }

    pub async fn get_health_stats(&self) -> HealthStats {
        self.health_stats.read().await.clone()
    }
}

/// 3. 异步监控和指标收集
#[derive(Debug, Clone)]
pub struct AsyncMetricsCollector {
    metrics: Arc<RwLock<HashMap<String, Metric>>>,
    #[allow(dead_code)]
    collector_config: MetricsConfig,
    metrics_stats: Arc<RwLock<MetricsStats>>,
}

#[derive(Debug, Clone)]
pub struct Metric {
    pub name: String,
    pub value: f64,
    pub metric_type: MetricType,
    pub labels: HashMap<String, String>,
    pub timestamp: Instant,
}

#[derive(Debug, Clone, PartialEq)]
pub enum MetricType {
    Counter,
    Gauge,
    Histogram,
    Summary,
}

#[derive(Debug, Clone)]
pub struct MetricsConfig {
    pub collection_interval: Duration,
    pub retention_period: Duration,
    pub enable_aggregation: bool,
    pub aggregation_window: Duration,
}

impl Default for MetricsConfig {
    fn default() -> Self {
        Self {
            collection_interval: Duration::from_secs(10),
            retention_period: Duration::from_secs(3600),
            aggregation_window: Duration::from_secs(60),
            enable_aggregation: true,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct MetricsStats {
    pub total_metrics_collected: usize,
    pub active_metrics: usize,
    pub aggregated_metrics: usize,
    pub collection_errors: usize,
}

impl AsyncMetricsCollector {
    pub fn new(config: MetricsConfig) -> Self {
        Self {
            metrics: Arc::new(RwLock::new(HashMap::new())),
            collector_config: config,
            metrics_stats: Arc::new(RwLock::new(MetricsStats::default())),
        }
    }

    pub async fn record_metric(
        &self,
        name: String,
        value: f64,
        metric_type: MetricType,
        labels: HashMap<String, String>,
    ) -> Result<()> {
        let metric = Metric {
            name: name.clone(),
            value,
            metric_type,
            labels,
            timestamp: Instant::now(),
        };

        let mut metrics = self.metrics.write().await;
        metrics.insert(name.clone(), metric);

        let mut stats = self.metrics_stats.write().await;
        stats.total_metrics_collected += 1;
        stats.active_metrics = metrics.len();

        debug!("记录指标: {} = {}", name, value);
        Ok(())
    }

    pub async fn get_metric(&self, name: &str) -> Option<Metric> {
        let metrics = self.metrics.read().await;
        metrics.get(name).cloned()
    }

    pub async fn get_all_metrics(&self) -> HashMap<String, Metric> {
        self.metrics.read().await.clone()
    }

    pub async fn get_metrics_stats(&self) -> MetricsStats {
        self.metrics_stats.read().await.clone()
    }
}

// 模块级指标（避免局部不可见）
static GW_REQ_TOTAL: LazyLock<IntCounter> = LazyLock::new(|| {
    IntCounter::with_opts(Opts::new("gateway_request_total", "网关请求总数")).unwrap()
});
static GW_REQ_SECONDS: LazyLock<Histogram> = LazyLock::new(|| {
    Histogram::with_opts(HistogramOpts::new(
        "gateway_request_seconds",
        "网关请求耗时(秒)",
    ))
    .unwrap()
});
static RATE_LIMITED_TOTAL: LazyLock<IntCounterVec> = LazyLock::new(|| {
    IntCounterVec::new(
        Opts::new("gateway_rate_limited_total", "限流命中次数"),
        &["reason"],
    )
    .unwrap()
});
static BACKEND_STATUS_TOTAL: LazyLock<IntCounterVec> = LazyLock::new(|| {
    IntCounterVec::new(
        Opts::new("gateway_backend_status_total", "后端响应状态计数"),
        &["status"],
    )
    .unwrap()
});
static INSTANCE_PICK_TOTAL: LazyLock<IntCounterVec> = LazyLock::new(|| {
    IntCounterVec::new(
        Opts::new("gateway_instance_pick_total", "后端实例选择分布"),
        &["instance"],
    )
    .unwrap()
});

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();
    // /metrics 暴露（网关演示：9897）
    let registry = Registry::new();
    let _ = registry.register(Box::new(GW_REQ_TOTAL.clone()));
    let _ = registry.register(Box::new(GW_REQ_SECONDS.clone()));
    let _ = registry.register(Box::new(RATE_LIMITED_TOTAL.clone()));
    let _ = registry.register(Box::new(BACKEND_STATUS_TOTAL.clone()));
    let _ = registry.register(Box::new(INSTANCE_PICK_TOTAL.clone()));
    let _metrics_handle = tokio::spawn(metrics::serve_metrics(registry.clone(), "127.0.0.1:9897"));

    info!("🚀 开始 2025 年异步API网关演示");

    // 1. 演示异步API网关核心
    info!("🌐 演示异步API网关核心");
    let config = GatewayConfig::default();
    let gateway = AsyncAPIGateway::new(config);

    // 注册后端服务
    let user_service = BackendService {
        id: "user-service".to_string(),
        name: "用户服务".to_string(),
        base_url: "http://localhost:3001".to_string(),
        health_check_url: "http://localhost:3001/health".to_string(),
        instances: vec![ServiceInstance {
            id: "user-instance-1".to_string(),
            url: "http://localhost:3001".to_string(),
            weight: 1,
            is_healthy: true,
            response_time: Duration::from_millis(100),
            error_count: 0,
            request_count: 0,
        }],
        load_balancer: LoadBalancerType::RoundRobin,
        circuit_breaker: Some(CircuitBreakerConfig {
            failure_threshold: 5,
            success_threshold: 3,
            timeout: Duration::from_secs(30),
            state: CircuitBreakerState::Closed,
            failure_count: 0,
            success_count: 0,
            last_failure_time: None,
        }),
        timeout: Duration::from_secs(30),
        is_healthy: true,
        last_health_check: Instant::now(),
    };

    gateway.register_service(user_service).await?;

    // 添加路由
    let user_route = Route {
        id: "user-route".to_string(),
        path: "/api/users".to_string(),
        methods: vec![HttpMethod::GET, HttpMethod::POST],
        backend_service: "user-service".to_string(),
        timeout: Duration::from_secs(30),
        retry_count: 3,
        rate_limit: Some(RateLimit {
            requests_per_minute: 100,
            burst_size: 20,
            window_size: Duration::from_secs(60),
        }),
        auth_required: true,
        middleware: vec!["auth".to_string(), "rate-limit".to_string()],
        created_at: Instant::now(),
    };

    gateway.add_route(user_route).await?;

    // 添加中间件
    let middleware_list = vec![
        Middleware {
            id: "auth-middleware".to_string(),
            name: "认证中间件".to_string(),
            middleware_type: MiddlewareType::Authentication,
            config: HashMap::new(),
            enabled: true,
            order: 1,
        },
        Middleware {
            id: "rate-limit-middleware".to_string(),
            name: "限流中间件".to_string(),
            middleware_type: MiddlewareType::RateLimiting,
            config: HashMap::new(),
            enabled: true,
            order: 2,
        },
        Middleware {
            id: "logging-middleware".to_string(),
            name: "日志中间件".to_string(),
            middleware_type: MiddlewareType::Logging,
            config: HashMap::new(),
            enabled: true,
            order: 3,
        },
    ];

    for middleware in middleware_list {
        gateway.add_middleware(middleware).await?;
    }

    // 处理一些请求
    for i in 0..10 {
        let t = std::time::Instant::now();
        let request = GatewayRequest {
            id: Uuid::new_v4().to_string(),
            method: HttpMethod::GET,
            path: "/api/users".to_string(),
            headers: [("Authorization".to_string(), "Bearer token123".to_string())]
                .iter()
                .cloned()
                .collect(),
            body: String::new(),
            client_ip: format!("192.168.1.{}", 100 + i),
            timestamp: Instant::now(),
        };

        match gateway.process_request(request).await {
            Ok(response) => {
                info!(
                    "请求处理成功: {} -> {} (耗时: {:?})",
                    i, response.status_code, response.response_time
                );
                GW_REQ_TOTAL.inc();
                GW_REQ_SECONDS.observe(t.elapsed().as_secs_f64());
            }
            Err(e) => {
                error!("请求处理失败: {} - {}", i, e);
                GW_REQ_TOTAL.inc();
                GW_REQ_SECONDS.observe(t.elapsed().as_secs_f64());
            }
        }
    }

    let gateway_stats = gateway.get_gateway_stats().await;
    info!(
        "网关统计: 总请求 {}, 成功 {}, 失败 {}, 平均响应时间 {:?}",
        gateway_stats.total_requests,
        gateway_stats.successful_requests,
        gateway_stats.failed_requests,
        gateway_stats.average_response_time
    );

    // 2. 演示异步健康检查系统
    info!("🏥 演示异步健康检查系统");
    let health_config = HealthCheckConfig::default();
    let health_checker = AsyncHealthChecker::new(health_config);

    // 注册服务到健康检查器
    let service_for_health = BackendService {
        id: "health-service".to_string(),
        name: "健康检查服务".to_string(),
        base_url: "http://localhost:3002".to_string(),
        health_check_url: "http://localhost:3002/health".to_string(),
        instances: vec![ServiceInstance {
            id: "health-instance-1".to_string(),
            url: "http://localhost:3002".to_string(),
            weight: 1,
            is_healthy: true,
            response_time: Duration::from_millis(50),
            error_count: 0,
            request_count: 0,
        }],
        load_balancer: LoadBalancerType::RoundRobin,
        circuit_breaker: None,
        timeout: Duration::from_secs(10),
        is_healthy: true,
        last_health_check: Instant::now(),
    };

    health_checker.register_service(service_for_health).await?;

    // 启动健康检查任务（短时间运行）
    let health_checker_clone = health_checker.clone();
    let health_task = tokio::spawn(async move { health_checker_clone.start_health_checks().await });

    // 让健康检查运行一段时间
    sleep(Duration::from_millis(2000)).await;

    health_task.abort();

    let health_stats = health_checker.get_health_stats().await;
    info!(
        "健康检查统计: 总检查 {}, 健康服务 {}, 不健康服务 {}",
        health_stats.total_checks, health_stats.healthy_services, health_stats.unhealthy_services
    );

    // 3. 演示异步监控和指标收集
    info!("📊 演示异步监控和指标收集");
    let metrics_config = MetricsConfig::default();
    let metrics_collector = AsyncMetricsCollector::new(metrics_config);

    // 记录一些指标
    for i in 0..20 {
        let labels = [
            ("service".to_string(), "api-gateway".to_string()),
            ("endpoint".to_string(), "/api/users".to_string()),
        ]
        .iter()
        .cloned()
        .collect();

        metrics_collector
            .record_metric(
                "request_count".to_string(),
                i as f64,
                MetricType::Counter,
                labels,
            )
            .await?;

        metrics_collector
            .record_metric(
                "response_time_ms".to_string(),
                (50 + i * 10) as f64,
                MetricType::Gauge,
                HashMap::new(),
            )
            .await?;
    }

    // 获取指标
    if let Some(metric) = metrics_collector.get_metric("request_count").await {
        info!(
            "指标: {} = {} ({:?})",
            metric.name, metric.value, metric.metric_type
        );
    }

    let metrics_stats = metrics_collector.get_metrics_stats().await;
    info!(
        "指标收集统计: 总收集 {}, 活跃指标 {}",
        metrics_stats.total_metrics_collected, metrics_stats.active_metrics
    );

    info!("✅ 2025 年异步API网关演示完成!");

    Ok(())
}
