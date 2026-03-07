# 服务网格语义 (Service Mesh Semantics)

## 目录

- [服务网格语义 (Service Mesh Semantics)](#服务网格语义-service-mesh-semantics)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 服务网格架构](#2-服务网格架构)
    - [2.1 Sidecar 模式](#21-sidecar-模式)
    - [2.2 数据平面与控制平面](#22-数据平面与控制平面)
    - [2.3 形式化定义](#23-形式化定义)
  - [3. 流量管理](#3-流量管理)
    - [3.1 流量分割与灰度发布](#31-流量分割与灰度发布)
    - [3.2 故障注入](#32-故障注入)
  - [4. Rust 实现](#4-rust-实现)
    - [4.1 Sidecar 代理核心](#41-sidecar-代理核心)
    - [4.2 mTLS 实现](#42-mtls-实现)
    - [4.3 可观测性集成](#43-可观测性集成)
  - [5. 形式化验证](#5-形式化验证)
    - [5.1 流量管理正确性](#51-流量管理正确性)
    - [5.2 安全属性](#52-安全属性)
  - [6. 性能考量](#6-性能考量)
  - [7. 总结](#7-总结)

## 1. 引言

服务网格是微服务架构中处理服务间通信的基础设施层。
本文档深入分析服务网格的架构语义、流量管理机制及其在 Rust 中的实现模式。

---

## 2. 服务网格架构

### 2.1 Sidecar 模式

```
服务网格架构:

┌──────────────────────────────────────────────────────────────────┐
│                        Kubernetes Pod                            │
│                                                                  │
│  ┌─────────────────────┐    ┌─────────────────────┐             │
│  │                     │    │                     │             │
│  │   Application       │◄──►│   Sidecar Proxy     │             │
│  │   (Microservice)    │    │   (Envoy/Linkerd)   │             │
│  │                     │    │                     │             │
│  │   • Business Logic  │    │   • Traffic Mgmt    │             │
│  │   • Domain Logic    │    │   • Load Balancing  │             │
│  │   • Data Processing │    │   • Security        │             │
│  │                     │    │   • Observability   │             │
│  └─────────────────────┘    └──────────┬──────────┘             │
│                                         │                        │
│                                         ▼                        │
│                              ┌─────────────────────┐             │
│                              │   Control Plane     │             │
│                              │   (Istiod/Linkerd)  │             │
│                              └─────────────────────┘             │
│                                                                  │
└──────────────────────────────────────────────────────────────────┘
                              │
                              ▼
                    ┌─────────────────┐
                    │  Other Services │
                    │  (via Sidecars) │
                    └─────────────────┘
```

### 2.2 数据平面与控制平面

```
服务网格平面分离:

┌──────────────────────────────────────────────────────────────────┐
│                        Control Plane                             │
├──────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐              │
│  │  API Server │  │  Config     │  │  Certificate│              │
│  │             │  │  Store      │  │  Manager    │              │
│  │ • xDS API   │  │ • CRD       │  │ • mTLS certs│              │
│  │ • Discovery │  │ • Policies  │  │ • Rotation  │              │
│  └─────────────┘  └─────────────┘  └─────────────┘              │
│                                                                  │
└──────────────────────────────────────────────────────────────────┘
                              │ xDS Protocol (ADS/CDS/RDS/EDS/LDS)
                              ▼
┌──────────────────────────────────────────────────────────────────┐
│                        Data Plane (Sidecars)                     │
├──────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐              │
│  │  Listener   │  │  Route      │  │  Cluster    │              │
│  │  (LDS)      │  │  (RDS)      │  │  (CDS)      │              │
│  │             │  │             │  │             │              │
│  │ Port binding│  │ Path match  │  │ Endpoint    │              │
│  │ Filter chain│  │ Retry/Timeout│ │ Load balance│              │
│  └─────────────┘  └─────────────┘  └─────────────┘              │
│                                                                  │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐              │
│  │  Transport  │  │  Metrics    │  │  mTLS       │              │
│  │  Socket     │  │  Stats      │  │  Handshake  │              │
│  │             │  │             │  │             │              │
│  │ TCP/HTTP2   │  │ Prometheus  │  │ Certificate │              │
│  │ gRPC/WebSock│  │ OpenTelemetry│ │ Validation  │              │
│  └─────────────┘  └─────────────┘  └─────────────┘              │
│                                                                  │
└──────────────────────────────────────────────────────────────────┘
```

### 2.3 形式化定义

```
服务网格形式化语义:

服务拓扑:
  Topology = (Services, Dependencies, Routes)

  Services = {s₁, s₂, ..., sₙ}
  Dependencies ⊆ Services × Services
  Routes: Services × Services → Path

流量管理:
  Route: Request × Source × Destination → Destination × Policy

  Policy = (Retry, Timeout, CircuitBreaker, RateLimit)

安全策略:
  AuthN: Identity × Certificate → {Valid, Invalid}
  AuthZ: Source × Destination × Action → {Allow, Deny}

可观测性:
  Metrics: Request → (Latency, Status, Bytes)
  Traces: Request → SpanContext
  Logs: Event → LogEntry

xDS 配置状态机:
  ConfigVersion: Resources → Version

  □ (ConfigUpdate → ◇ SidecarAck)
  □ (VersionMismatch → Resync)
```

---

## 3. 流量管理

### 3.1 流量分割与灰度发布

```
流量路由形式化:

权重路由:
  Route(destination, weight) =
    select_backend(destinations, weight_distribution)

金丝雀发布:
  TrafficSplit(version₁: 90%, version₂: 10%)

  Route(request) =
    if hash(request_id) < 0.9 then
      RouteTo(version₁)
    else
      RouteTo(version₂)

A/B 测试:
  Route(request) =
    match header(request, "X-Test-Group") of
      "A" → RouteTo(version_A)
      "B" → RouteTo(version_B)
      _   → RouteTo(default)

镜像流量:
  PrimaryRoute → service_v1 (100%)
  MirrorRoute → service_v2 (0% or shadow)
```

### 3.2 故障注入

```
混沌工程形式化:

延迟注入:
  InjectDelay(request, latency, probability) =
    if random() < probability then
      sleep(latency)
    process(request)

错误注入:
  InjectError(request, status_code, probability) =
    if random() < probability then
      return Error(status_code)
    else
      process(request)

中止注入:
  InjectAbort(request, probability) =
    if random() < probability then
      connection.reset()
```

---

## 4. Rust 实现

### 4.1 Sidecar 代理核心

```rust
use std::collections::HashMap;
use std::net::SocketAddr;
use std::sync::Arc;
use tokio::net::{TcpListener, TcpStream};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::sync::RwLock;
use async_trait::async_trait;
use hyper::{Body, Client, Request, Response, Server, StatusCode};
use hyper::service::{make_service_fn, service_fn};

/// 服务配置
#[derive(Debug, Clone)]
pub struct ServiceConfig {
    pub name: String,
    pub hosts: Vec<String>,
    pub ports: Vec<u16>,
    pub endpoints: Vec<Endpoint>,
    pub load_balancer: LoadBalancerType,
}

/// 端点
#[derive(Debug, Clone)]
pub struct Endpoint {
    pub address: SocketAddr,
    pub weight: u32,
    pub healthy: bool,
    pub metadata: HashMap<String, String>,
}

/// 路由规则
#[derive(Debug, Clone)]
pub struct RouteRule {
    pub match_criteria: MatchCriteria,
    pub destination: String,
    pub weight: u32,
    pub retries: Option<RetryPolicy>,
    pub timeout: Option<std::time::Duration>,
    pub fault: Option<FaultInjection>,
}

#[derive(Debug, Clone)]
pub struct MatchCriteria {
    pub path_prefix: Option<String>,
    pub headers: HashMap<String, String>,
    pub methods: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct RetryPolicy {
    pub attempts: u32,
    pub per_try_timeout: std::time::Duration,
    pub retry_on: Vec<String>, // 5xx, gateway-error, etc.
}

#[derive(Debug, Clone)]
pub struct FaultInjection {
    pub delay: Option<DelayFault>,
    pub abort: Option<AbortFault>,
}

#[derive(Debug, Clone)]
pub struct DelayFault {
    pub percentage: f64,
    pub fixed_delay: std::time::Duration,
}

#[derive(Debug, Clone)]
pub struct AbortFault {
    pub percentage: f64,
    pub http_status: u16,
}

/// Sidecar 代理
pub struct SidecarProxy {
    config: Arc<RwLock<ProxyConfig>>,
    client: Client<hyper::client::HttpConnector>,
    metrics: Arc<MetricsCollector>,
}

#[derive(Debug, Clone)]
pub struct ProxyConfig {
    pub listener_port: u16,
    pub admin_port: u16,
    pub services: HashMap<String, ServiceConfig>,
    pub routes: Vec<RouteRule>,
    pub tls_config: Option<TlsConfig>,
}

#[derive(Debug, Clone)]
pub struct TlsConfig {
    pub cert_path: String,
    pub key_path: String,
    pub ca_path: String,
    pub mtls_enabled: bool,
}

impl SidecarProxy {
    pub fn new(config: ProxyConfig) -> Self {
        let client = Client::new();

        Self {
            config: Arc::new(RwLock::new(config)),
            client,
            metrics: Arc::new(MetricsCollector::new()),
        }
    }

    /// 启动代理服务器
    pub async fn run(&self) -> Result<(), Box<dyn std::error::Error>> {
        let config = self.config.read().await;
        let addr = SocketAddr::from(([0, 0, 0, 0], config.listener_port));

        let proxy = self.clone();
        let make_svc = make_service_fn(move |_conn| {
            let proxy = proxy.clone();
            async move {
                Ok::<_, hyper::Error>(service_fn(move |req| {
                    let proxy = proxy.clone();
                    async move { proxy.handle_request(req).await }
                }))
            }
        });

        let server = Server::bind(&addr).serve(make_svc);

        tracing::info!("Sidecar proxy listening on {}", addr);

        server.await?;
        Ok(())
    }

    /// 处理传入请求
    async fn handle_request(
        &self,
        req: Request<Body>,
    ) -> Result<Response<Body>, hyper::Error> {
        let start = std::time::Instant::now();

        // 记录请求指标
        self.metrics.record_request_start(&req).await;

        // 匹配路由
        let route = match self.match_route(&req).await {
            Some(r) => r,
            None => {
                return Ok(Response::builder()
                    .status(StatusCode::NOT_FOUND)
                    .body(Body::from("No route matched"))
                    .unwrap());
            }
        };

        // 应用故障注入
        if let Some(ref fault) = route.fault {
            if let Some(response) = self.apply_fault(fault).await {
                return Ok(response);
            }
        }

        // 转发请求
        let result = self.forward_request(req, &route).await;

        // 记录响应指标
        let duration = start.elapsed();
        match &result {
            Ok(resp) => {
                self.metrics.record_response(resp.status(), duration).await;
            }
            Err(_) => {
                self.metrics.record_error("forward_error", duration).await;
            }
        }

        result
    }

    /// 匹配路由规则
    async fn match_route(&self, req: &Request<Body>) -> Option<RouteRule> {
        let config = self.config.read().await;

        config.routes.iter()
            .find(|rule| self.matches_criteria(req, &rule.match_criteria))
            .cloned()
    }

    fn matches_criteria(&self, req: &Request<Body>, criteria: &MatchCriteria) -> bool {
        // 检查路径前缀
        if let Some(ref prefix) = criteria.path_prefix {
            if !req.uri().path().starts_with(prefix) {
                return false;
            }
        }

        // 检查 HTTP 方法
        if !criteria.methods.is_empty() {
            let method = req.method().as_str();
            if !criteria.methods.iter().any(|m| m == method) {
                return false;
            }
        }

        // 检查请求头
        for (key, value) in &criteria.headers {
            match req.headers().get(key) {
                Some(header_value) => {
                    if header_value.to_str().unwrap_or("") != value {
                        return false;
                    }
                }
                None => return false,
            }
        }

        true
    }

    /// 应用故障注入
    async fn apply_fault(&self, fault: &FaultInjection) -> Option<Response<Body>> {
        use rand::Rng;
        let mut rng = rand::thread_rng();

        // 延迟注入
        if let Some(ref delay) = fault.delay {
            if rng.gen::<f64>() < delay.percentage {
                tokio::time::sleep(delay.fixed_delay).await;
            }
        }

        // 中止注入
        if let Some(ref abort) = fault.abort {
            if rng.gen::<f64>() < abort.percentage {
                return Some(Response::builder()
                    .status(abort.http_status)
                    .body(Body::from("Fault injected"))
                    .unwrap());
            }
        }

        None
    }

    /// 转发请求到目标服务
    async fn forward_request(
        &self,
        mut req: Request<Body>,
        route: &RouteRule,
    ) -> Result<Response<Body>, hyper::Error> {
        let config = self.config.read().await;

        // 获取目标服务配置
        let service = config.services.get(&route.destination)
            .ok_or_else(|| {
                hyper::Error::from(std::io::Error::new(
                    std::io::ErrorKind::NotFound,
                    "Service not found"
                ))
            })?;

        // 选择端点
        let endpoint = self.select_endpoint(service).await;

        // 构建目标 URI
        let uri = format!(
            "http://{}{}",
            endpoint.address,
            req.uri().path_and_query().map(|p| p.as_str()).unwrap_or("/")
        );

        *req.uri_mut() = uri.parse().unwrap();

        // 应用超时
        let timeout = route.timeout.unwrap_or(std::time::Duration::from_secs(30));

        match tokio::time::timeout(timeout, self.client.request(req)).await {
            Ok(Ok(response)) => Ok(response),
            Ok(Err(e)) => Err(e),
            Err(_) => Ok(Response::builder()
                .status(StatusCode::GATEWAY_TIMEOUT)
                .body(Body::from("Upstream timeout"))
                .unwrap()),
        }
    }

    /// 选择服务端点
    async fn select_endpoint(&self, service: &ServiceConfig) -> Endpoint {
        // 过滤健康端点
        let healthy: Vec<_> = service.endpoints.iter()
            .filter(|e| e.healthy)
            .cloned()
            .collect();

        if healthy.is_empty() {
            // 如果没有健康端点，返回第一个（可能失败）
            return service.endpoints.first().cloned().unwrap();
        }

        // 根据负载均衡策略选择
        match service.load_balancer {
            LoadBalancerType::RoundRobin => {
                // 简化实现，实际使用原子计数器
                healthy[0].clone()
            }
            LoadBalancerType::Random => {
                use rand::seq::SliceRandom;
                healthy.choose(&mut rand::thread_rng()).cloned().unwrap()
            }
            LoadBalancerType::LeastConnections => {
                // 简化实现
                healthy[0].clone()
            }
        }
    }

    /// 更新配置（xDS 推送）
    pub async fn update_config(&self, new_config: ProxyConfig) {
        let mut config = self.config.write().await;
        *config = new_config;
        tracing::info!("Proxy configuration updated");
    }
}

#[derive(Debug, Clone, Copy)]
pub enum LoadBalancerType {
    RoundRobin,
    Random,
    LeastConnections,
}

/// 指标收集器
pub struct MetricsCollector {
    request_count: AtomicU64,
    error_count: AtomicU64,
    latency_histogram: RwLock<Vec<u64>>, // in ms
}

impl MetricsCollector {
    pub fn new() -> Self {
        Self {
            request_count: AtomicU64::new(0),
            error_count: AtomicU64::new(0),
            latency_histogram: RwLock::new(Vec::new()),
        }
    }

    pub async fn record_request_start(&self, _req: &Request<Body>) {
        self.request_count.fetch_add(1, Ordering::Relaxed);
    }

    pub async fn record_response(&self, status: StatusCode, duration: std::time::Duration) {
        if !status.is_success() {
            self.error_count.fetch_add(1, Ordering::Relaxed);
        }

        let mut histogram = self.latency_histogram.write().await;
        histogram.push(duration.as_millis() as u64);
        if histogram.len() > 10000 {
            histogram.remove(0);
        }
    }

    pub async fn record_error(&self, _error_type: &str, _duration: std::time::Duration) {
        self.error_count.fetch_add(1, Ordering::Relaxed);
    }
}

impl Clone for SidecarProxy {
    fn clone(&self) -> Self {
        Self {
            config: Arc::clone(&self.config),
            client: self.client.clone(),
            metrics: Arc::clone(&self.metrics),
        }
    }
}
```

### 4.2 mTLS 实现

```rust
use rustls::{Certificate, PrivateKey, ServerConfig, ClientConfig};
use rustls::internal::msgs::enums::AlertDescription;
use std::sync::Arc;
use tokio_rustls::{TlsAcceptor, TlsConnector};

/// mTLS 管理器
pub struct MtlsManager {
    /// 服务器配置（用于接收连接）
    server_config: Arc<ServerConfig>,
    /// 客户端配置（用于发起连接）
    client_config: Arc<ClientConfig>,
    /// 证书存储
    cert_store: Arc<RwLock<CertificateStore>>,
}

#[derive(Debug, Clone)]
pub struct CertificateStore {
    /// 服务账户证书
    service_cert: Certificate,
    /// 私钥
    private_key: PrivateKey,
    /// CA 证书
    ca_cert: Certificate,
    /// 证书链
    cert_chain: Vec<Certificate>,
}

impl MtlsManager {
    pub fn new(cert_store: CertificateStore) -> Result<Self, Box<dyn std::error::Error>> {
        // 构建服务器配置
        let server_config = Self::build_server_config(&cert_store)?;

        // 构建客户端配置
        let client_config = Self::build_client_config(&cert_store)?;

        Ok(Self {
            server_config: Arc::new(server_config),
            client_config: Arc::new(client_config),
            cert_store: Arc::new(RwLock::new(cert_store)),
        })
    }

    fn build_server_config(store: &CertificateStore) -> Result<ServerConfig, rustls::Error> {
        let config = ServerConfig::builder()
            .with_safe_defaults()
            .with_client_cert_verifier(Arc::new(rustls::server::AllowAnyAuthenticatedClient::new(
                Self::build_root_store(&store.ca_cert)?
            )))
            .with_single_cert(
                store.cert_chain.clone(),
                store.private_key.clone()
            )?;

        Ok(config)
    }

    fn build_client_config(store: &CertificateStore) -> Result<ClientConfig, rustls::Error> {
        let config = ClientConfig::builder()
            .with_safe_defaults()
            .with_root_certificates(Self::build_root_store(&store.ca_cert)?)
            .with_single_cert(
                store.cert_chain.clone(),
                store.private_key.clone()
            )?;

        Ok(config)
    }

    fn build_root_store(ca_cert: &Certificate) -> Result<rustls::RootCertStore, rustls::Error> {
        let mut root_store = rustls::RootCertStore::empty();
        root_store.add(ca_cert)?;
        Ok(root_store)
    }

    /// 接受 mTLS 连接
    pub fn acceptor(&self) -> TlsAcceptor {
        TlsAcceptor::from(Arc::clone(&self.server_config))
    }

    /// 连接 mTLS 服务端
    pub fn connector(&self) -> TlsConnector {
        TlsConnector::from(Arc::clone(&self.client_config))
    }

    /// 获取对等身份
    pub fn peer_identity(connection: &tokio_rustls::server::TlsStream<TcpStream>) -> Option<String> {
        // 从 TLS 连接中提取客户端证书信息
        let (_io, session) = connection.get_ref();
        session.peer_certificates()
            .and_then(|certs| certs.first())
            .map(|cert| format!("{:?}", cert))
    }

    /// 轮换证书
    pub async fn rotate_certificates(&self, new_store: CertificateStore) -> Result<(), Box<dyn std::error::Error>> {
        // 构建新配置
        let server_config = Self::build_server_config(&new_store)?;
        let client_config = Self::build_client_config(&new_store)?;

        // 原子性更新
        let mut store = self.cert_store.write().await;
        *store = new_store;

        // 更新 TLS 配置（需要 Arc::make_mut 或重新创建）
        // 实际实现中可能需要更复杂的逻辑

        tracing::info!("Certificates rotated successfully");
        Ok(())
    }
}
```

### 4.3 可观测性集成

```rust
use opentelemetry::trace::{Span, SpanKind, Tracer};
use opentelemetry::KeyValue;
use tracing::{info, warn, error};

/// 分布式追踪集成
pub struct TracingIntegration {
    tracer: Arc<dyn Tracer + Send + Sync>,
}

impl TracingIntegration {
    /// 创建入站请求 span
    pub fn create_inbound_span(&self, req: &Request<Body>) -> Box<dyn Span> {
        let span = self.tracer
            .span_builder(format!("{} {}", req.method(), req.uri().path()))
            .with_kind(SpanKind::Server)
            .with_attributes(vec![
                KeyValue::new("http.method", req.method().as_str().to_string()),
                KeyValue::new("http.url", req.uri().to_string()),
                KeyValue::new("http.target", req.uri().path().to_string()),
            ])
            .start(&*self.tracer);

        span
    }

    /// 创建出站请求 span
    pub fn create_outbound_span(&self, req: &Request<Body>) -> Box<dyn Span> {
        let span = self.tracer
            .span_builder(format!("HTTP {}", req.method()))
            .with_kind(SpanKind::Client)
            .with_attributes(vec![
                KeyValue::new("http.method", req.method().as_str().to_string()),
                KeyValue::new("http.url", req.uri().to_string()),
            ])
            .start(&*self.tracer);

        span
    }
}

/// 指标导出器
pub struct MetricsExporter {
    registry: prometheus::Registry,
    request_total: prometheus::CounterVec,
    request_duration: prometheus::HistogramVec,
    active_connections: prometheus::Gauge,
}

impl MetricsExporter {
    pub fn new() -> Result<Self, prometheus::Error> {
        let registry = prometheus::Registry::new();

        let request_total = prometheus::CounterVec::new(
            prometheus::Opts::new("istio_requests_total", "Total requests"),
            &["source", "destination", "response_code"],
        )?;

        let request_duration = prometheus::HistogramVec::new(
            prometheus::HistogramOpts::new(
                "istio_request_duration_milliseconds",
                "Request duration in milliseconds"
            ),
            &["source", "destination"],
        )?;

        let active_connections = prometheus::Gauge::new(
            "istio_tcp_connections_open_total",
            "Current open connections"
        )?;

        registry.register(Box::new(request_total.clone()))?;
        registry.register(Box::new(request_duration.clone()))?;
        registry.register(Box::new(active_connections.clone()))?;

        Ok(Self {
            registry,
            request_total,
            request_duration,
            active_connections,
        })
    }

    pub fn record_request(&self, source: &str, destination: &str, status: u16) {
        self.request_total
            .with_label_values(&[source, destination, &status.to_string()])
            .inc();
    }

    pub fn record_duration(&self, source: &str, destination: &str, duration_ms: f64) {
        self.request_duration
            .with_label_values(&[source, destination])
            .observe(duration_ms);
    }

    pub fn inc_connections(&self) {
        self.active_connections.inc();
    }

    pub fn dec_connections(&self) {
        self.active_connections.dec();
    }

    pub fn gather(&self) -> Vec<prometheus::proto::MetricFamily> {
        self.registry.gather()
    }
}
```

---

## 5. 形式化验证

### 5.1 流量管理正确性

```
流量路由正确性:

1. 完备性:
   □ (RequestReceived → ◇ (Routed ∨ Rejected))

2. 一致性:
   □ (RouteMatched(rule) → RouteTo(rule.destination))

3. 权重公平性:
   lim_{n→∞} |requests(v₁)/weight(v₁) - requests(v₂)/weight(v₂)| ≤ ε

4. 超时保证:
   □ (RequestStarted → ◇ (Response ∨ Timeout))
   Time(Response) - Time(Request) ≤ timeout
```

### 5.2 安全属性

```
mTLS 安全保证:

1. 身份认证:
   □ (ConnectionEstablished → CertificateValidated)

   CertificateValidated = Valid(CA) ∧ NotExpired ∧ MatchesIdentity

2. 通信加密:
   □ (DataTransmitted → Encrypted(TLS1.3))

3. 授权:
   □ (RequestAllowed → AuthZ(identity, destination, action))
```

---

## 6. 性能考量

```
Sidecar 性能开销:

1. 延迟开销:
   - L3/L4 代理: ~0.5ms
   - L7 HTTP 代理: ~1-3ms
   - mTLS 握手: ~1-2ms (平摊)

2. 资源开销:
   - 内存: 50-100MB per sidecar
   - CPU: 0.1-0.5 vCPU per 1000 RPS

3. 网络开销:
   - 额外一跳: localhost → sidecar → network
   - 带宽: 增加 TLS 开销 (~5-10%)

优化策略:

1. eBPF 加速:
   - 使用 Cilium 等 eBPF 方案减少上下文切换
   - 延迟降低至 ~0.1ms

2. 共享代理:
   - 每个节点一个代理而非每个 Pod
   - 减少资源占用

3. 连接池:
   - 复用上游连接
   - 减少连接建立开销
```

---

## 7. 总结

| 特性 | Sidecar 模式 | 优势 | 挑战 |
|------|-------------|------|------|
| 流量管理 | 透明拦截 | 无代码侵入 | 延迟开销 |
| 安全 | 自动 mTLS | 统一安全策略 | 证书管理 |
| 可观测性 | 自动埋点 | 全链路追踪 | 数据量大 |
| 多语言 | 语言无关 | 统一治理 | 协议兼容 |

核心公式:

$$
\text{Route}(req) = \underset{r \in \text{rules}}{\arg\max} \text{MatchScore}(req, r)
$$

$$
\text{Canary}(req) = \begin{cases}
v_1 & \text{if } \text{hash}(req_{id}) < \theta \\
v_2 & \text{otherwise}
\end{cases}
$$

$$
\text{Latency}_{total} = \text{Latency}_{app} + \text{Latency}_{sidecar} + \text{Latency}_{network}
$$
