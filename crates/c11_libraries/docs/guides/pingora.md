# Pingora 高性能代理完整实战指南

> **适用版本**: Rust 1.75+ (推荐 1.90+)  
> **更新日期**: 2025-10-24  
> **难度级别**: 中级到高级

Pingora 是 Cloudflare 开源的高性能 HTTP 代理框架，基于 Rust 和 Tokio 构建，用于处理百万级并发连接。本指南提供从入门到生产的完整实战教程。

---

## 📊 目录

- [Pingora 高性能代理完整实战指南](#pingora-高性能代理完整实战指南)
  - [📊 目录](#-目录)
  - [Pingora 架构原理](#pingora-架构原理)
    - [核心特性](#核心特性)
  - [快速开始](#快速开始)
    - [环境准备](#环境准备)
  - [反向代理实现](#反向代理实现)
    - [基础反向代理](#基础反向代理)
    - [上游超时和重试](#上游超时和重试)
  - [路由与负载均衡](#路由与负载均衡)
    - [路径路由](#路径路由)
    - [负载均衡](#负载均衡)
    - [健康检查](#健康检查)
  - [中间件开发](#中间件开发)
    - [限流中间件](#限流中间件)
    - [缓存中间件](#缓存中间件)
    - [熔断中间件](#熔断中间件)
  - [TLS 与安全](#tls-与安全)
    - [TLS 终止](#tls-终止)
    - [上游 TLS](#上游-tls)
    - [安全头](#安全头)
  - [性能优化](#性能优化)
    - [配置优化](#配置优化)
    - [连接池优化](#连接池优化)
    - [零拷贝优化](#零拷贝优化)
  - [生产环境部署](#生产环境部署)
    - [Systemd 服务](#systemd-服务)
    - [Docker 部署](#docker-部署)
  - [监控与可观测性](#监控与可观测性)
    - [Prometheus 指标](#prometheus-指标)
    - [日志记录](#日志记录)
  - [高级特性](#高级特性)
    - [WebSocket 代理](#websocket-代理)
    - [HTTP/2 支持](#http2-支持)
  - [故障排查](#故障排查)
    - [常见问题](#常见问题)
  - [总结](#总结)
    - [核心功能](#核心功能)
    - [性能特点](#性能特点)
    - [生产就绪](#生产就绪)

---

## Pingora 架构原理

### 核心特性

**Pingora 的关键优势**:

1. **高性能**:
   - 零拷贝设计，最小化内存分配
   - 基于 Tokio 的完全异步架构
   - 处理百万级并发连接

2. **灵活性**:
   - 模块化设计，可插拔中间件
   - 自定义路由逻辑
   - 丰富的钩子函数

3. **生产就绪**:
   - Cloudflare 在生产环境验证
   - 完善的错误处理
   - 内置健康检查和故障转移

**架构图**:

```text
Client Request
      ↓
[Pingora Server]
      ↓
[ProxyHttp Trait]
      ├─ request_filter()     ← 请求预处理
      ├─ upstream_peer()      ← 选择上游
      ├─ upstream_request_filter() ← 修改上游请求
      ├─ response_filter()    ← 响应后处理
      └─ logging()            ← 日志记录
      ↓
[Upstream Server]
```

---

## 快速开始

### 环境准备

**依赖配置**:

```toml
[dependencies]
pingora = { version = "0.2", features = ["lb"] }
pingora-core = "0.2"
pingora-http = "0.2"
pingora-load-balancing = "0.2"
async-trait = "0.1"
tokio = { version = "1", features = ["full"] }
log = "0.4"
env_logger = "0.11"
```

**最简单的反向代理**:

```rust
use async_trait::async_trait;
use pingora::prelude::*;
use std::sync::Arc;

pub struct MyProxy {
    upstream_addr: String,
}

#[async_trait]
impl ProxyHttp for MyProxy {
    type CTX = ();
    
    fn new_ctx(&self) -> Self::CTX {
        ()
    }
    
    async fn upstream_peer(
        &self,
        _session: &mut Session,
        _ctx: &mut Self::CTX,
    ) -> Result<Box<HttpPeer>> {
        let peer = Box::new(HttpPeer::new(
            self.upstream_addr.parse()?,
            false,  // 不使用 TLS
            "".to_string(),  // SNI
        ));
        Ok(peer)
    }
}

fn main() {
    env_logger::init();
    
    // 创建服务器
    let mut server = Server::new(None).unwrap();
    server.bootstrap();
    
    // 创建代理服务
    let proxy = MyProxy {
        upstream_addr: "127.0.0.1:8080".to_string(),
    };
    
    let mut service = http_proxy_service(&server.configuration, proxy);
    service.add_tcp("0.0.0.0:6188");
    
    // 添加到服务器
    server.add_service(service);
    
    // 启动服务器
    server.run_forever();
}
```

**测试代码**:

```bash
# 终端1: 启动一个简单的上游服务器
python3 -m http.server 8080

# 终端2: 启动 Pingora 代理
cargo run --features proxy-pingora

# 终端3: 测试代理
curl http://localhost:6188/
```

---

## 反向代理实现

### 基础反向代理

**添加请求/响应修改**:

```rust
use async_trait::async_trait;
use pingora::prelude::*;
use pingora::proxy::Session;
use pingora::protocols::http::v1::server::HttpSession;

pub struct CustomProxy {
    upstream_addr: String,
}

#[async_trait]
impl ProxyHttp for CustomProxy {
    type CTX = ();
    
    fn new_ctx(&self) -> Self::CTX {
        ()
    }
    
    async fn upstream_peer(
        &self,
        _session: &mut Session,
        _ctx: &mut Self::CTX,
    ) -> Result<Box<HttpPeer>> {
        let peer = Box::new(HttpPeer::new(
            self.upstream_addr.parse()?,
            false,
            "".to_string(),
        ));
        Ok(peer)
    }
    
    // 请求过滤器：修改请求头
    async fn request_filter(
        &self,
        session: &mut Session,
        _ctx: &mut Self::CTX,
    ) -> Result<bool> {
        // 添加自定义请求头
        session
            .req_header_mut()
            .insert_header("X-Proxy-By", "Pingora")?;
        
        session
            .req_header_mut()
            .insert_header("X-Request-ID", &uuid::Uuid::new_v4().to_string())?;
        
        // 移除某些头
        session.req_header_mut().remove_header("Cookie");
        
        // 返回 false 继续处理，返回 true 中断请求
        Ok(false)
    }
    
    // 上游请求过滤器：修改发往上游的请求
    async fn upstream_request_filter(
        &self,
        _session: &mut Session,
        upstream_request: &mut RequestHeader,
        _ctx: &mut Self::CTX,
    ) -> Result<()> {
        // 添加上游特定的头
        upstream_request.insert_header("X-Forwarded-Proto", "http")?;
        Ok(())
    }
    
    // 响应过滤器：修改响应头
    async fn response_filter(
        &self,
        _session: &mut Session,
        upstream_response: &mut ResponseHeader,
        _ctx: &mut Self::CTX,
    ) -> Result<()> {
        // 添加响应头
        upstream_response.insert_header("X-Served-By", "Pingora")?;
        upstream_response.insert_header("X-Cache", "MISS")?;
        
        // 移除服务器信息（安全考虑）
        upstream_response.remove_header("Server");
        
        Ok(())
    }
    
    // 日志记录
    async fn logging(
        &self,
        session: &mut Session,
        _e: Option<&Error>,
        ctx: &mut Self::CTX,
    ) {
        let response_code = session
            .response_written()
            .map_or(0, |resp| resp.status.as_u16());
        
        log::info!(
            "{} {} {} - {}",
            session.client_addr().unwrap(),
            session.req_header().method,
            session.req_header().uri,
            response_code
        );
    }
}
```

---

### 上游超时和重试

**配置上游超时**:

```rust
use std::time::Duration;

#[async_trait]
impl ProxyHttp for TimeoutProxy {
    type CTX = ();
    
    fn new_ctx(&self) -> Self::CTX {
        ()
    }
    
    async fn upstream_peer(
        &self,
        _session: &mut Session,
        _ctx: &mut Self::CTX,
    ) -> Result<Box<HttpPeer>> {
        let mut peer = HttpPeer::new(
            "127.0.0.1:8080".parse()?,
            false,
            "".to_string(),
        );
        
        // 设置连接超时
        peer.options.connection_timeout = Some(Duration::from_secs(5));
        
        // 设置读超时
        peer.options.read_timeout = Some(Duration::from_secs(30));
        
        // 设置写超时
        peer.options.write_timeout = Some(Duration::from_secs(30));
        
        // 设置总超时
        peer.options.total_connection_timeout = Some(Duration::from_secs(10));
        
        Ok(Box::new(peer))
    }
}
```

**实现自动重试**:

```rust
use std::sync::atomic::{AtomicU32, Ordering};

pub struct RetryProxy {
    upstream_addr: String,
    retry_count: AtomicU32,
    max_retries: u32,
}

#[async_trait]
impl ProxyHttp for RetryProxy {
    type CTX = u32;  // 使用 CTX 存储当前重试次数
    
    fn new_ctx(&self) -> Self::CTX {
        0
    }
    
    async fn upstream_peer(
        &self,
        _session: &mut Session,
        ctx: &mut Self::CTX,
    ) -> Result<Box<HttpPeer>> {
        let peer = Box::new(HttpPeer::new(
            self.upstream_addr.parse()?,
            false,
            "".to_string(),
        ));
        Ok(peer)
    }
    
    async fn fail_to_connect(
        &self,
        _session: &mut Session,
        _peer: &HttpPeer,
        ctx: &mut Self::CTX,
        e: Box<Error>,
    ) -> Result<bool> {
        *ctx += 1;
        
        if *ctx < self.max_retries {
            log::warn!("连接失败，重试 {}/{}: {:?}", ctx, self.max_retries, e);
            // 返回 true 表示重试
            Ok(true)
        } else {
            log::error!("达到最大重试次数 {}", self.max_retries);
            // 返回 false 表示不再重试
            Ok(false)
        }
    }
    
    async fn fail_to_proxy(
        &self,
        _session: &mut Session,
        ctx: &mut Self::CTX,
        e: Box<Error>,
    ) -> Result<bool> {
        *ctx += 1;
        
        if *ctx < self.max_retries {
            log::warn!("代理失败，重试 {}/{}: {:?}", ctx, self.max_retries, e);
            Ok(true)
        } else {
            Ok(false)
        }
    }
}
```

---

## 路由与负载均衡

### 路径路由

**基于路径的路由**:

```rust
pub struct PathRoutingProxy {
    api_upstream: String,
    static_upstream: String,
    default_upstream: String,
}

#[async_trait]
impl ProxyHttp for PathRoutingProxy {
    type CTX = ();
    
    fn new_ctx(&self) -> Self::CTX {
        ()
    }
    
    async fn upstream_peer(
        &self,
        session: &mut Session,
        _ctx: &mut Self::CTX,
    ) -> Result<Box<HttpPeer>> {
        let path = session.req_header().uri.path();
        
        let upstream_addr = if path.starts_with("/api/") {
            &self.api_upstream
        } else if path.starts_with("/static/") {
            &self.static_upstream
        } else {
            &self.default_upstream
        };
        
        log::info!("路由 {} 到 {}", path, upstream_addr);
        
        let peer = Box::new(HttpPeer::new(
            upstream_addr.parse()?,
            false,
            "".to_string(),
        ));
        Ok(peer)
    }
}
```

**基于 Host 的路由**:

```rust
pub struct HostRoutingProxy {
    api_domain: String,
    api_upstream: String,
    web_domain: String,
    web_upstream: String,
    default_upstream: String,
}

#[async_trait]
impl ProxyHttp for HostRoutingProxy {
    type CTX = ();
    
    fn new_ctx(&self) -> Self::CTX {
        ()
    }
    
    async fn upstream_peer(
        &self,
        session: &mut Session,
        _ctx: &mut Self::CTX,
    ) -> Result<Box<HttpPeer>> {
        let host = session
            .req_header()
            .headers
            .get("Host")
            .and_then(|h| h.to_str().ok())
            .unwrap_or("");
        
        let upstream_addr = if host.contains(&self.api_domain) {
            &self.api_upstream
        } else if host.contains(&self.web_domain) {
            &self.web_upstream
        } else {
            &self.default_upstream
        };
        
        log::info!("路由 Host {} 到 {}", host, upstream_addr);
        
        let peer = Box::new(HttpPeer::new(
            upstream_addr.parse()?,
            false,
            "".to_string(),
        ));
        Ok(peer)
    }
}
```

---

### 负载均衡

**轮询负载均衡**:

```rust
use pingora_load_balancing::{LoadBalancer, RoundRobin, Backend};
use std::sync::Arc;

pub struct LoadBalancedProxy {
    lb: Arc<LoadBalancer<RoundRobin>>,
}

impl LoadBalancedProxy {
    pub fn new(upstream_addrs: Vec<&str>) -> Self {
        let backends: Vec<Backend> = upstream_addrs
            .iter()
            .map(|addr| Backend::new(addr).unwrap())
            .collect();
        
        let lb = LoadBalancer::from_backends(backends);
        
        Self {
            lb: Arc::new(lb),
        }
    }
}

#[async_trait]
impl ProxyHttp for LoadBalancedProxy {
    type CTX = ();
    
    fn new_ctx(&self) -> Self::CTX {
        ()
    }
    
    async fn upstream_peer(
        &self,
        session: &mut Session,
        _ctx: &mut Self::CTX,
    ) -> Result<Box<HttpPeer>> {
        // 使用请求的某个特征作为选择依据（如 IP）
        let client_ip = session.client_addr()
            .map(|addr| addr.to_string())
            .unwrap_or_default();
        
        let backend = self.lb
            .select(client_ip.as_bytes(), 256)
            .ok_or_else(|| Error::new(ErrorType::InternalError))?;
        
        log::info!("选择后端: {}", backend.addr);
        
        let peer = Box::new(HttpPeer::new(
            backend.addr,
            false,
            "".to_string(),
        ));
        Ok(peer)
    }
}

// 使用示例
fn main() {
    let proxy = LoadBalancedProxy::new(vec![
        "127.0.0.1:8080",
        "127.0.0.1:8081",
        "127.0.0.1:8082",
    ]);
    
    // ... 启动服务器
}
```

**加权轮询**:

```rust
use pingora_load_balancing::selection::weighted::Weighted;

pub struct WeightedLoadBalancer {
    lb: Arc<LoadBalancer<Weighted>>,
}

impl WeightedLoadBalancer {
    pub fn new() -> Self {
        let mut backends = vec![];
        
        // 添加不同权重的后端
        let mut backend1 = Backend::new("127.0.0.1:8080").unwrap();
        backend1.weight = 5;  // 权重 5
        backends.push(backend1);
        
        let mut backend2 = Backend::new("127.0.0.1:8081").unwrap();
        backend2.weight = 3;  // 权重 3
        backends.push(backend2);
        
        let mut backend3 = Backend::new("127.0.0.1:8082").unwrap();
        backend3.weight = 2;  // 权重 2
        backends.push(backend3);
        
        let lb = LoadBalancer::from_backends(backends);
        
        Self {
            lb: Arc::new(lb),
        }
    }
}

#[async_trait]
impl ProxyHttp for WeightedLoadBalancer {
    type CTX = ();
    
    fn new_ctx(&self) -> Self::CTX {
        ()
    }
    
    async fn upstream_peer(
        &self,
        _session: &mut Session,
        _ctx: &mut Self::CTX,
    ) -> Result<Box<HttpPeer>> {
        let backend = self.lb
            .select(b"", 256)
            .ok_or_else(|| Error::new(ErrorType::InternalError))?;
        
        let peer = Box::new(HttpPeer::new(
            backend.addr,
            false,
            "".to_string(),
        ));
        Ok(peer)
    }
}
```

---

### 健康检查

**HTTP 健康检查**:

```rust
use pingora_load_balancing::health_check;
use std::time::Duration;
use tokio::time::interval;

pub struct HealthCheckManager {
    lb: Arc<LoadBalancer<RoundRobin>>,
}

impl HealthCheckManager {
    pub fn start_health_checks(&self) {
        let lb = self.lb.clone();
        
        tokio::spawn(async move {
            let mut ticker = interval(Duration::from_secs(10));
            
            loop {
                ticker.tick().await;
                
                for backend in lb.backends().get_backend() {
                    let health_check_path = "/health";
                    
                    match health_check::http_health_check(
                        &backend.addr,
                        health_check_path,
                    ).await {
                        Ok(true) => {
                            log::info!("后端 {} 健康", backend.addr);
                            backend.set_healthy(true);
                        }
                        Ok(false) | Err(_) => {
                            log::warn!("后端 {} 不健康", backend.addr);
                            backend.set_healthy(false);
                        }
                    }
                }
            }
        });
    }
}
```

---

## 中间件开发

### 限流中间件

**令牌桶限流**:

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

pub struct RateLimiter {
    // IP -> (令牌数, 上次刷新时间)
    buckets: Arc<Mutex<HashMap<String, (f64, Instant)>>>,
    rate: f64,  // 每秒令牌数
    capacity: f64,  // 桶容量
}

impl RateLimiter {
    pub fn new(rate: f64, capacity: f64) -> Self {
        Self {
            buckets: Arc::new(Mutex::new(HashMap::new())),
            rate,
            capacity,
        }
    }
    
    fn try_acquire(&self, key: &str) -> bool {
        let mut buckets = self.buckets.lock().unwrap();
        let now = Instant::now();
        
        let (tokens, last_refill) = buckets
            .entry(key.to_string())
            .or_insert((self.capacity, now));
        
        // 补充令牌
        let elapsed = now.duration_since(*last_refill).as_secs_f64();
        *tokens = (*tokens + elapsed * self.rate).min(self.capacity);
        *last_refill = now;
        
        // 尝试消耗一个令牌
        if *tokens >= 1.0 {
            *tokens -= 1.0;
            true
        } else {
            false
        }
    }
}

pub struct RateLimitProxy {
    upstream_addr: String,
    limiter: RateLimiter,
}

#[async_trait]
impl ProxyHttp for RateLimitProxy {
    type CTX = ();
    
    fn new_ctx(&self) -> Self::CTX {
        ()
    }
    
    async fn request_filter(
        &self,
        session: &mut Session,
        _ctx: &mut Self::CTX,
    ) -> Result<bool> {
        let client_ip = session.client_addr()
            .map(|addr| addr.to_string())
            .unwrap_or_else(|| "unknown".to_string());
        
        if !self.limiter.try_acquire(&client_ip) {
            log::warn!("限流: {}", client_ip);
            
            // 返回 429 Too Many Requests
            let mut resp = ResponseHeader::build(429, None)?;
            resp.insert_header("Retry-After", "1")?;
            session.write_response_header(Box::new(resp)).await?;
            
            return Ok(true);  // 中断请求
        }
        
        Ok(false)  // 继续处理
    }
    
    async fn upstream_peer(
        &self,
        _session: &mut Session,
        _ctx: &mut Self::CTX,
    ) -> Result<Box<HttpPeer>> {
        let peer = Box::new(HttpPeer::new(
            self.upstream_addr.parse()?,
            false,
            "".to_string(),
        ));
        Ok(peer)
    }
}
```

---

### 缓存中间件

**简单的内存缓存**:

```rust
use std::collections::HashMap;
use std::sync::{Arc, RwLock};

pub struct CacheMiddleware {
    upstream_addr: String,
    cache: Arc<RwLock<HashMap<String, Vec<u8>>>>,
}

#[async_trait]
impl ProxyHttp for CacheMiddleware {
    type CTX = Option<Vec<u8>>;  // 存储缓存的响应
    
    fn new_ctx(&self) -> Self::CTX {
        None
    }
    
    async fn request_filter(
        &self,
        session: &mut Session,
        ctx: &mut Self::CTX,
    ) -> Result<bool> {
        // 只缓存 GET 请求
        if session.req_header().method != http::Method::GET {
            return Ok(false);
        }
        
        let cache_key = session.req_header().uri.to_string();
        
        // 检查缓存
        let cache = self.cache.read().unwrap();
        if let Some(cached_response) = cache.get(&cache_key) {
            log::info!("缓存命中: {}", cache_key);
            
            // 直接返回缓存的响应
            let resp = ResponseHeader::build(200, None)?;
            session.write_response_header(Box::new(resp)).await?;
            session.write_response_body(Some(cached_response.clone().into())).await?;
            
            return Ok(true);  // 中断请求，直接返回缓存
        }
        
        Ok(false)  // 缓存未命中，继续请求上游
    }
    
    async fn response_filter(
        &self,
        session: &mut Session,
        _upstream_response: &mut ResponseHeader,
        _ctx: &mut Self::CTX,
    ) -> Result<()> {
        // 存储响应到缓存
        if let Some(body) = session.response_body() {
            let cache_key = session.req_header().uri.to_string();
            let mut cache = self.cache.write().unwrap();
            cache.insert(cache_key, body.to_vec());
            log::info!("缓存存储: {}", session.req_header().uri);
        }
        
        Ok(())
    }
    
    async fn upstream_peer(
        &self,
        _session: &mut Session,
        _ctx: &mut Self::CTX,
    ) -> Result<Box<HttpPeer>> {
        let peer = Box::new(HttpPeer::new(
            self.upstream_addr.parse()?,
            false,
            "".to_string(),
        ));
        Ok(peer)
    }
}
```

---

### 熔断中间件

**熔断器实现**:

```rust
use std::sync::atomic::{AtomicU32, AtomicU64, Ordering};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

#[derive(Debug, Clone, Copy, PartialEq)]
enum CircuitState {
    Closed,   // 正常状态
    Open,     // 熔断打开
    HalfOpen, // 半开状态
}

pub struct CircuitBreaker {
    state: Arc<Mutex<CircuitState>>,
    failure_count: AtomicU32,
    success_count: AtomicU32,
    last_failure_time: AtomicU64,
    
    failure_threshold: u32,
    success_threshold: u32,
    timeout: Duration,
}

impl CircuitBreaker {
    pub fn new(
        failure_threshold: u32,
        success_threshold: u32,
        timeout: Duration,
    ) -> Self {
        Self {
            state: Arc::new(Mutex::new(CircuitState::Closed)),
            failure_count: AtomicU32::new(0),
            success_count: AtomicU32::new(0),
            last_failure_time: AtomicU64::new(0),
            failure_threshold,
            success_threshold,
            timeout,
        }
    }
    
    pub fn is_open(&self) -> bool {
        let state = *self.state.lock().unwrap();
        
        match state {
            CircuitState::Open => {
                // 检查是否应该进入半开状态
                let last_fail = self.last_failure_time.load(Ordering::Relaxed);
                let now = SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap()
                    .as_secs();
                
                if now - last_fail >= self.timeout.as_secs() {
                    *self.state.lock().unwrap() = CircuitState::HalfOpen;
                    false
                } else {
                    true
                }
            }
            CircuitState::HalfOpen => false,
            CircuitState::Closed => false,
        }
    }
    
    pub fn record_success(&self) {
        let mut state = self.state.lock().unwrap();
        
        match *state {
            CircuitState::HalfOpen => {
                self.success_count.fetch_add(1, Ordering::Relaxed);
                
                if self.success_count.load(Ordering::Relaxed) >= self.success_threshold {
                    *state = CircuitState::Closed;
                    self.failure_count.store(0, Ordering::Relaxed);
                    self.success_count.store(0, Ordering::Relaxed);
                    log::info!("熔断器关闭");
                }
            }
            _ => {}
        }
    }
    
    pub fn record_failure(&self) {
        self.failure_count.fetch_add(1, Ordering::Relaxed);
        
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        self.last_failure_time.store(now, Ordering::Relaxed);
        
        if self.failure_count.load(Ordering::Relaxed) >= self.failure_threshold {
            *self.state.lock().unwrap() = CircuitState::Open;
            log::warn!("熔断器打开");
        }
    }
}

pub struct CircuitBreakerProxy {
    upstream_addr: String,
    circuit_breaker: CircuitBreaker,
}

#[async_trait]
impl ProxyHttp for CircuitBreakerProxy {
    type CTX = ();
    
    fn new_ctx(&self) -> Self::CTX {
        ()
    }
    
    async fn request_filter(
        &self,
        session: &mut Session,
        _ctx: &mut Self::CTX,
    ) -> Result<bool> {
        if self.circuit_breaker.is_open() {
            log::warn!("熔断器打开，拒绝请求");
            
            let resp = ResponseHeader::build(503, None)?;
            session.write_response_header(Box::new(resp)).await?;
            
            return Ok(true);  // 中断请求
        }
        
        Ok(false)
    }
    
    async fn upstream_peer(
        &self,
        _session: &mut Session,
        _ctx: &mut Self::CTX,
    ) -> Result<Box<HttpPeer>> {
        let peer = Box::new(HttpPeer::new(
            self.upstream_addr.parse()?,
            false,
            "".to_string(),
        ));
        Ok(peer)
    }
    
    async fn fail_to_proxy(
        &self,
        _session: &mut Session,
        _ctx: &mut Self::CTX,
        _e: Box<Error>,
    ) -> Result<bool> {
        self.circuit_breaker.record_failure();
        Ok(false)  // 不重试
    }
    
    async fn logging(
        &self,
        session: &mut Session,
        e: Option<&Error>,
        _ctx: &mut Self::CTX,
    ) {
        if e.is_none() {
            self.circuit_breaker.record_success();
        }
    }
}
```

## TLS 与安全

### TLS 终止

**配置 HTTPS 监听**:

```rust
use pingora::tls::ssl::{SslAcceptor, SslFiletype, SslMethod};

fn create_tls_server() -> Result<Server> {
    let mut server = Server::new(None)?;
    server.bootstrap();
    
    // 配置 TLS
    let mut acceptor = SslAcceptor::mozilla_intermediate(SslMethod::tls())?;
    acceptor.set_private_key_file("/path/to/private.key", SslFiletype::PEM)?;
    acceptor.set_certificate_chain_file("/path/to/cert.pem")?;
    
    let proxy = MyProxy {
        upstream_addr: "127.0.0.1:8080".to_string(),
    };
    
    let mut service = http_proxy_service(&server.configuration, proxy);
    
    // 添加 HTTPS 监听
    service.add_tls_with_acceptor(
        "0.0.0.0:443",
        None,
        acceptor.build(),
    )?;
    
    server.add_service(service);
    Ok(server)
}
```

**SNI 支持（Server Name Indication）**:

```rust
use std::collections::HashMap;

pub struct SniProxy {
    // 域名 -> 上游地址
    domain_mapping: HashMap<String, String>,
}

#[async_trait]
impl ProxyHttp for SniProxy {
    type CTX = ();
    
    fn new_ctx(&self) -> Self::CTX {
        ()
    }
    
    async fn upstream_peer(
        &self,
        session: &mut Session,
        _ctx: &mut Self::CTX,
    ) -> Result<Box<HttpPeer>> {
        // 从 TLS SNI 获取域名
        let sni = session
            .get_header("Host")
            .and_then(|h| h.to_str().ok())
            .unwrap_or("");
        
        let upstream_addr = self.domain_mapping
            .get(sni)
            .cloned()
            .unwrap_or_else(|| "127.0.0.1:8080".to_string());
        
        log::info!("SNI: {} -> {}", sni, upstream_addr);
        
        let peer = Box::new(HttpPeer::new(
            upstream_addr.parse()?,
            false,
            "".to_string(),
        ));
        Ok(peer)
    }
}
```

---

### 上游 TLS

**配置上游 HTTPS 连接**:

```rust
#[async_trait]
impl ProxyHttp for UpstreamTlsProxy {
    type CTX = ();
    
    fn new_ctx(&self) -> Self::CTX {
        ()
    }
    
    async fn upstream_peer(
        &self,
        _session: &mut Session,
        _ctx: &mut Self::CTX,
    ) -> Result<Box<HttpPeer>> {
        let mut peer = HttpPeer::new(
            "api.example.com:443".parse()?,
            true,  // 启用 TLS
            "api.example.com".to_string(),  // SNI
        );
        
        // 配置 TLS 选项
        peer.options.verify_cert = true;  // 验证证书
        peer.options.verify_hostname = true;  // 验证主机名
        
        Ok(Box::new(peer))
    }
}
```

---

### 安全头

**添加安全相关的 HTTP 头**:

```rust
#[async_trait]
impl ProxyHttp for SecurityHeadersProxy {
    type CTX = ();
    
    fn new_ctx(&self) -> Self::CTX {
        ()
    }
    
    async fn response_filter(
        &self,
        _session: &mut Session,
        upstream_response: &mut ResponseHeader,
        _ctx: &mut Self::CTX,
    ) -> Result<()> {
        // HSTS (HTTP Strict Transport Security)
        upstream_response.insert_header(
            "Strict-Transport-Security",
            "max-age=31536000; includeSubDomains; preload",
        )?;
        
        // XSS Protection
        upstream_response.insert_header("X-XSS-Protection", "1; mode=block")?;
        
        // Content Type Options
        upstream_response.insert_header("X-Content-Type-Options", "nosniff")?;
        
        // Frame Options
        upstream_response.insert_header("X-Frame-Options", "SAMEORIGIN")?;
        
        // CSP (Content Security Policy)
        upstream_response.insert_header(
            "Content-Security-Policy",
            "default-src 'self'; script-src 'self' 'unsafe-inline'",
        )?;
        
        // 移除敏感信息
        upstream_response.remove_header("Server");
        upstream_response.remove_header("X-Powered-By");
        
        Ok(())
    }
    
    async fn upstream_peer(
        &self,
        _session: &mut Session,
        _ctx: &mut Self::CTX,
    ) -> Result<Box<HttpPeer>> {
        let peer = Box::new(HttpPeer::new(
            "127.0.0.1:8080".parse()?,
            false,
            "".to_string(),
        ));
        Ok(peer)
    }
}
```

---

## 性能优化

### 配置优化

**服务器配置文件 (pingora.yaml)**:

```yaml
---
version: 1

# 工作线程数（通常 = CPU 核心数）
threads: 4

# 服务器选项
daemon: false
error_log: /var/log/pingora/error.log
pid_file: /var/run/pingora.pid

# 升级相关
upgrade_sock: /tmp/pingora_upgrade.sock

# 用户和组
user: nobody
group: nogroup

# 性能优化
# - SO_REUSEPORT: 允许多个进程绑定同一端口
# - TCP_NODELAY: 禁用 Nagle 算法，降低延迟
```

**代码中使用配置**:

```rust
use pingora::server::configuration::Opt;

fn main() {
    let opt = Opt {
        conf: Some("/etc/pingora/pingora.yaml".to_string()),
        ..Default::default()
    };
    
    let mut server = Server::new(Some(opt)).unwrap();
    // ...
}
```

---

### 连接池优化

**配置连接复用**:

```rust
use pingora::connectors::http::Connector;

fn create_connector() -> Connector {
    // 创建连接器，支持连接池
    let mut connector = Connector::new(Some(256));  // 最大 256 个连接
    
    // 配置 Keep-Alive
    connector.set_connect_timeout(Duration::from_secs(10));
    connector.set_read_timeout(Duration::from_secs(30));
    
    connector
}
```

---

### 零拷贝优化

Pingora 默认使用零拷贝技术，但可以进一步优化：

```rust
// 使用 Bytes 而不是 Vec<u8> 来避免拷贝
use bytes::Bytes;

#[async_trait]
impl ProxyHttp for ZeroCopyProxy {
    type CTX = ();
    
    fn new_ctx(&self) -> Self::CTX {
        ()
    }
    
    // Pingora 内部已经优化了零拷贝
    // 响应体直接从上游流式传输到客户端
    async fn upstream_peer(
        &self,
        _session: &mut Session,
        _ctx: &mut Self::CTX,
    ) -> Result<Box<HttpPeer>> {
        let peer = Box::new(HttpPeer::new(
            "127.0.0.1:8080".parse()?,
            false,
            "".to_string(),
        ));
        Ok(peer)
    }
}
```

---

## 生产环境部署

### Systemd 服务

**创建 systemd 服务文件 (/etc/systemd/system/pingora.service)**:

```ini
[Unit]
Description=Pingora HTTP Proxy
After=network.target
Documentation=https://github.com/cloudflare/pingora

[Service]
Type=simple
User=pingora
Group=pingora
WorkingDirectory=/opt/pingora
ExecStart=/opt/pingora/bin/pingora -c /etc/pingora/pingora.yaml
ExecReload=/bin/kill -HUP $MAINPID
Restart=always
RestartSec=5

# 资源限制
LimitNOFILE=1048576
LimitNPROC=512

# 安全加固
NoNewPrivileges=true
PrivateTmp=true
ProtectSystem=strict
ProtectHome=true
ReadWritePaths=/var/log/pingora /var/run

[Install]
WantedBy=multi-user.target
```

**启动和管理**:

```bash
# 创建用户和目录
sudo useradd -r -s /bin/false pingora
sudo mkdir -p /opt/pingora/bin /etc/pingora /var/log/pingora
sudo chown -R pingora:pingora /opt/pingora /var/log/pingora

# 部署二进制文件
sudo cp target/release/my-proxy /opt/pingora/bin/pingora
sudo chmod +x /opt/pingora/bin/pingora

# 启动服务
sudo systemctl daemon-reload
sudo systemctl start pingora
sudo systemctl enable pingora

# 查看状态
sudo systemctl status pingora

# 查看日志
sudo journalctl -u pingora -f

# 优雅重启（零停机）
sudo systemctl reload pingora
```

---

### Docker 部署

**Dockerfile**:

```dockerfile
FROM rust:1.75 as builder

WORKDIR /app
COPY . .
RUN cargo build --release --features proxy-pingora

FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

COPY --from=builder /app/target/release/my-proxy /usr/local/bin/pingora
COPY config/pingora.yaml /etc/pingora/pingora.yaml

RUN useradd -r -s /bin/false pingora
USER pingora

EXPOSE 80 443

CMD ["/usr/local/bin/pingora", "-c", "/etc/pingora/pingora.yaml"]
```

**docker-compose.yml**:

```yaml
version: '3.8'

services:
  pingora:
    build: .
    ports:
      - "80:80"
      - "443:443"
      - "9090:9090"  # Prometheus metrics
    volumes:
      - ./config:/etc/pingora
      - ./logs:/var/log/pingora
      - ./certs:/etc/certs:ro
    environment:
      - RUST_LOG=info
    restart: unless-stopped
    ulimits:
      nofile:
        soft: 1048576
        hard: 1048576
```

---

## 监控与可观测性

### Prometheus 指标

**集成 Prometheus**:

```rust
use prometheus::{Counter, Histogram, Registry, Encoder, TextEncoder};
use std::sync::Arc;

lazy_static::lazy_static! {
    static ref HTTP_REQUESTS_TOTAL: Counter = Counter::new(
        "http_requests_total",
        "Total number of HTTP requests"
    ).unwrap();
    
    static ref HTTP_REQUEST_DURATION: Histogram = Histogram::new(
        "http_request_duration_seconds",
        "HTTP request duration in seconds"
    ).unwrap();
    
    static ref UPSTREAM_FAILURES: Counter = Counter::new(
        "upstream_failures_total",
        "Total number of upstream failures"
    ).unwrap();
}

pub struct MonitoredProxy {
    upstream_addr: String,
}

#[async_trait]
impl ProxyHttp for MonitoredProxy {
    type CTX = Instant;
    
    fn new_ctx(&self) -> Self::CTX {
        Instant::now()
    }
    
    async fn request_filter(
        &self,
        _session: &mut Session,
        ctx: &mut Self::CTX,
    ) -> Result<bool> {
        HTTP_REQUESTS_TOTAL.inc();
        *ctx = Instant::now();
        Ok(false)
    }
    
    async fn upstream_peer(
        &self,
        _session: &mut Session,
        _ctx: &mut Self::CTX,
    ) -> Result<Box<HttpPeer>> {
        let peer = Box::new(HttpPeer::new(
            self.upstream_addr.parse()?,
            false,
            "".to_string(),
        ));
        Ok(peer)
    }
    
    async fn fail_to_proxy(
        &self,
        _session: &mut Session,
        _ctx: &mut Self::CTX,
        _e: Box<Error>,
    ) -> Result<bool> {
        UPSTREAM_FAILURES.inc();
        Ok(false)
    }
    
    async fn logging(
        &self,
        _session: &mut Session,
        _e: Option<&Error>,
        ctx: &mut Self::CTX,
    ) {
        let duration = ctx.elapsed().as_secs_f64();
        HTTP_REQUEST_DURATION.observe(duration);
    }
}

// Metrics 端点
async fn metrics_handler() -> String {
    let registry = Registry::new();
    registry.register(Box::new(HTTP_REQUESTS_TOTAL.clone())).unwrap();
    registry.register(Box::new(HTTP_REQUEST_DURATION.clone())).unwrap();
    registry.register(Box::new(UPSTREAM_FAILURES.clone())).unwrap();
    
    let encoder = TextEncoder::new();
    let mut buffer = vec![];
    encoder.encode(&registry.gather(), &mut buffer).unwrap();
    
    String::from_utf8(buffer).unwrap()
}
```

---

### 日志记录

**结构化日志**:

```rust
use slog::{Logger, Drain, o};

pub struct StructuredLoggingProxy {
    upstream_addr: String,
    logger: Logger,
}

#[async_trait]
impl ProxyHttp for StructuredLoggingProxy {
    type CTX = (Instant, String);
    
    fn new_ctx(&self) -> Self::CTX {
        (Instant::now(), uuid::Uuid::new_v4().to_string())
    }
    
    async fn request_filter(
        &self,
        session: &mut Session,
        ctx: &mut Self::CTX,
    ) -> Result<bool> {
        let (start_time, request_id) = ctx;
        
        slog::info!(self.logger, "接收请求";
            "request_id" => &request_id,
            "method" => session.req_header().method.as_str(),
            "uri" => session.req_header().uri.to_string(),
            "client_ip" => format!("{}", session.client_addr().unwrap()),
        );
        
        Ok(false)
    }
    
    async fn upstream_peer(
        &self,
        _session: &mut Session,
        _ctx: &mut Self::CTX,
    ) -> Result<Box<HttpPeer>> {
        let peer = Box::new(HttpPeer::new(
            self.upstream_addr.parse()?,
            false,
            "".to_string(),
        ));
        Ok(peer)
    }
    
    async fn logging(
        &self,
        session: &mut Session,
        e: Option<&Error>,
        ctx: &mut Self::CTX,
    ) {
        let (start_time, request_id) = ctx;
        let duration = start_time.elapsed().as_millis();
        let status = session.response_written()
            .map_or(0, |resp| resp.status.as_u16());
        
        slog::info!(self.logger, "请求完成";
            "request_id" => request_id,
            "status" => status,
            "duration_ms" => duration,
            "error" => e.is_some(),
        );
    }
}
```

---

## 高级特性

### WebSocket 代理

```rust
// Pingora 支持 WebSocket 代理
// WebSocket 连接会被透明地代理到上游
#[async_trait]
impl ProxyHttp for WebSocketProxy {
    type CTX = ();
    
    fn new_ctx(&self) -> Self::CTX {
        ()
    }
    
    async fn upstream_peer(
        &self,
        session: &mut Session,
        _ctx: &mut Self::CTX,
    ) -> Result<Box<HttpPeer>> {
        // 检查是否为 WebSocket 升级请求
        let is_websocket = session
            .req_header()
            .headers
            .get("Upgrade")
            .and_then(|v| v.to_str().ok())
            .map(|v| v.eq_ignore_ascii_case("websocket"))
            .unwrap_or(false);
        
        if is_websocket {
            log::info!("WebSocket 连接升级");
        }
        
        let peer = Box::new(HttpPeer::new(
            "127.0.0.1:8080".parse()?,
            false,
            "".to_string(),
        ));
        Ok(peer)
    }
}
```

---

### HTTP/2 支持

Pingora 原生支持 HTTP/2：

```rust
// HTTP/2 自动启用，无需特殊配置
// 只需确保 TLS 已配置（HTTP/2 通常需要 TLS）
```

---

## 故障排查

### 常见问题

**问题 1: 502 Bad Gateway**:

```bash
# 检查上游服务是否可达
curl -v http://127.0.0.1:8080/

# 检查 Pingora 日志
sudo journalctl -u pingora -n 100

# 解决方案：增加超时时间
```

**问题 2: 连接数过多**:

```bash
# 检查当前连接数
ss -s
netstat -an | grep ESTABLISHED | wc -l

# 解决方案：调整系统限制
sudo sysctl -w net.core.somaxconn=65535
sudo sysctl -w net.ipv4.ip_local_port_range="1024 65535"
sudo sysctl -w net.ipv4.tcp_tw_reuse=1
```

**问题 3: 性能不达预期**:

```bash
# 检查 CPU 使用率
top -H -p $(pgrep pingora)

# 检查工作线程数
# 应该 = CPU 核心数

# 检查是否启用连接复用
# 查看日志中的连接建立频率
```

---

## 总结

本指南涵盖了 Pingora 的完整实战内容：

### 核心功能

- ✅ 反向代理和请求转发
- ✅ 路由（路径、Host、加权）
- ✅ 负载均衡（轮询、加权、健康检查）
- ✅ 中间件（限流、缓存、熔断）
- ✅ TLS 终止和上游 TLS
- ✅ 监控和日志

### 性能特点

- ⚡ 零拷贝设计
- ⚡ 异步架构
- ⚡ 百万级并发
- ⚡ 极低延迟 (<1ms)

### 生产就绪

- ✅ Systemd 集成
- ✅ Docker 部署
- ✅ Prometheus 监控
- ✅ 结构化日志
- ✅ 优雅重启

---

**相关资源**:

- [Pingora GitHub](https://github.com/cloudflare/pingora)
- [Pingora 文档](https://github.com/cloudflare/pingora/tree/main/docs)
- [Cloudflare 博客](https://blog.cloudflare.com/pingora-open-source)

---

**更新日期**: 2025-10-24  
**文档版本**: 1.0  
**反馈**: 如有问题或建议，欢迎提 Issue
