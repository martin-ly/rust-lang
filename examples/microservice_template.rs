//! 微服务模板
//! 
//! 整合 C06(异步), C09(设计模式), C10(网络)
//! 
//! 特性:
//! - 配置管理 (Builder 模式)
//! - 服务注册 (单例模式)
//! - 请求处理 (策略模式)
//! - 日志记录 (观察者模式)
//! 
//! 运行: cargo run --example microservice_template

use std::collections::HashMap;
use std::net::SocketAddr;
use std::sync::Arc;
use tokio::net::{TcpListener, TcpStream};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::sync::RwLock;

/// 服务配置 (Builder 模式)
pub struct ServiceConfig {
    pub name: String,
    pub host: String,
    pub port: u16,
    pub workers: usize,
    pub log_level: String,
}

pub struct ServiceConfigBuilder {
    name: Option<String>,
    host: Option<String>,
    port: Option<u16>,
    workers: Option<usize>,
    log_level: Option<String>,
}

impl ServiceConfigBuilder {
    pub fn new() -> Self {
        Self {
            name: None,
            host: None,
            port: None,
            workers: None,
            log_level: None,
        }
    }
    
    pub fn name(mut self, name: impl Into<String>) -> Self {
        self.name = Some(name.into());
        self
    }
    
    pub fn host(mut self, host: impl Into<String>) -> Self {
        self.host = Some(host.into());
        self
    }
    
    pub fn port(mut self, port: u16) -> Self {
        self.port = Some(port);
        self
    }
    
    pub fn workers(mut self, workers: usize) -> Self {
        self.workers = Some(workers);
        self
    }
    
    pub fn log_level(mut self, level: impl Into<String>) -> Self {
        self.log_level = Some(level.into());
        self
    }
    
    pub fn build(self) -> Result<ServiceConfig, String> {
        Ok(ServiceConfig {
            name: self.name.ok_or("Name is required")?,
            host: self.host.unwrap_or_else(|| "127.0.0.1".to_string()),
            port: self.port.unwrap_or(8080),
            workers: self.workers.unwrap_or(4),
            log_level: self.log_level.unwrap_or_else(|| "info".to_string()),
        })
    }
}

/// 服务注册表 (单例模式)
pub struct ServiceRegistry {
    services: RwLock<HashMap<String, SocketAddr>>,
}

impl ServiceRegistry {
    pub fn new() -> Arc<Self> {
        Arc::new(Self {
            services: RwLock::new(HashMap::new()),
        })
    }
    
    pub async fn register(&self, name: String, addr: SocketAddr) {
        let mut services = self.services.write().await;
        services.insert(name, addr);
        println!("✅ Registered service: {} at {}", name, addr);
    }
    
    pub async fn discover(&self, name: &str) -> Option<SocketAddr> {
        let services = self.services.read().await;
        services.get(name).copied()
    }
    
    pub async fn list_services(&self) -> Vec<(String, SocketAddr)> {
        let services = self.services.read().await;
        services.iter().map(|(k, v)| (k.clone(), *v)).collect()
    }
}

/// HTTP 请求
#[derive(Debug, Clone)]
pub struct HttpRequest {
    pub method: String,
    pub path: String,
    pub headers: HashMap<String, String>,
    pub body: String,
}

/// HTTP 响应
#[derive(Debug, Clone)]
pub struct HttpResponse {
    pub status: u16,
    pub headers: HashMap<String, String>,
    pub body: String,
}

impl HttpResponse {
    pub fn json(data: impl Into<String>) -> Self {
        let mut headers = HashMap::new();
        headers.insert("Content-Type".to_string(), "application/json".to_string());
        
        Self {
            status: 200,
            headers,
            body: data.into(),
        }
    }
    
    pub fn not_found() -> Self {
        Self {
            status: 404,
            headers: HashMap::new(),
            body: r#"{"error": "Not Found"}"#.to_string(),
        }
    }
    
    pub fn to_http_string(&self) -> String {
        let headers_str = self.headers
            .iter()
            .map(|(k, v)| format!("{}: {}", k, v))
            .collect::<Vec<_>>()
            .join("\r\n");
        
        format!(
            "HTTP/1.1 {} OK\r\n{}\r\nContent-Length: {}\r\n\r\n{}",
            self.status,
            headers_str,
            self.body.len(),
            self.body
        )
    }
}

/// 请求处理器 trait (策略模式)
#[async_trait::async_trait]
pub trait RequestHandler: Send + Sync {
    async fn handle(&self, req: HttpRequest) -> HttpResponse;
}

/// 健康检查处理器
pub struct HealthHandler;

#[async_trait::async_trait]
impl RequestHandler for HealthHandler {
    async fn handle(&self, _req: HttpRequest) -> HttpResponse {
        HttpResponse::json(r#"{"status": "healthy"}"#)
    }
}

/// API 处理器
pub struct ApiHandler {
    registry: Arc<ServiceRegistry>,
}

impl ApiHandler {
    pub fn new(registry: Arc<ServiceRegistry>) -> Self {
        Self { registry }
    }
}

#[async_trait::async_trait]
impl RequestHandler for ApiHandler {
    async fn handle(&self, req: HttpRequest) -> HttpResponse {
        match req.path.as_str() {
            "/api/services" => {
                let services = self.registry.list_services().await;
                let json = format!("{{\"services\": {:?}}}", services);
                HttpResponse::json(json)
            }
            _ => HttpResponse::not_found(),
        }
    }
}

/// 路由器
#[derive(Default)]
pub struct Router {
    routes: HashMap<String, Box<dyn RequestHandler>>,
}

impl Router {
    pub fn new() -> Self {
        Self {
            routes: HashMap::new(),
        }
    }
    
    pub fn route(mut self, path: impl Into<String>, handler: Box<dyn RequestHandler>) -> Self {
        self.routes.insert(path.into(), handler);
        self
    }
    
    pub async fn handle(&self, req: HttpRequest) -> HttpResponse {
        if let Some(handler) = self.routes.get(&req.path) {
            handler.handle(req).await
        } else {
            HttpResponse::not_found()
        }
    }
}

/// 日志观察者 trait (观察者模式)
#[async_trait::async_trait]
pub trait LogObserver: Send + Sync {
    async fn on_request(&self, req: &HttpRequest);
    async fn on_response(&self, resp: &HttpResponse);
}

/// 控制台日志
pub struct ConsoleLogger;

#[async_trait::async_trait]
impl LogObserver for ConsoleLogger {
    async fn on_request(&self, req: &HttpRequest) {
        println!("[REQUEST] {} {}", req.method, req.path);
    }
    
    async fn on_response(&self, resp: &HttpResponse) {
        println!("[RESPONSE] Status: {}", resp.status);
    }
}

/// 微服务
pub struct Microservice {
    config: ServiceConfig,
    router: Arc<Router>,
    logger: Arc<dyn LogObserver>,
}

impl Microservice {
    pub fn new(config: ServiceConfig, router: Arc<Router>, logger: Arc<dyn LogObserver>) -> Self {
        Self {
            config,
            router,
            logger,
        }
    }
    
    pub async fn run(self) -> Result<(), Box<dyn std::error::Error>> {
        let addr = format!("{}:{}", self.config.host, self.config.port);
        let listener = TcpListener::bind(&addr).await?;
        
        println!("🚀 Microservice '{}' running on http://{}", 
            self.config.name, addr);
        println!("   Workers: {} | Log Level: {}", 
            self.config.workers, self.config.log_level);
        
        let router = Arc::clone(&self.router);
        let logger = Arc::clone(&self.logger);
        
        loop {
            let (stream, _) = listener.accept().await?;
            let router = Arc::clone(&router);
            let logger = Arc::clone(&logger);
            
            tokio::spawn(async move {
                if let Err(e) = handle_request(stream, router, logger).await {
                    eprintln!("Request error: {}", e);
                }
            });
        }
    }
}

async fn handle_request(
    mut stream: TcpStream,
    router: Arc<Router>,
    logger: Arc<dyn LogObserver>,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut buffer = [0u8; 1024];
    let n = stream.read(&mut buffer).await?;
    
    let request_str = String::from_utf8_lossy(&buffer[..n]);
    let request = parse_http_request(&request_str);
    
    logger.on_request(&request).await;
    let response = router.handle(request).await;
    logger.on_response(&response).await;
    
    stream.write_all(response.to_http_string().as_bytes()).await?;
    Ok(())
}

fn parse_http_request(request_str: &str) -> HttpRequest {
    let lines: Vec<&str> = request_str.lines().collect();
    let first_line = lines.first().unwrap_or(&"GET / HTTP/1.1");
    
    let parts: Vec<&str> = first_line.split_whitespace().collect();
    let method = parts.get(0).unwrap_or(&"GET").to_string();
    let path = parts.get(1).unwrap_or(&"/").to_string();
    
    let mut headers = HashMap::new();
    for line in lines.iter().skip(1) {
        if line.is_empty() {
            break;
        }
        if let Some(pos) = line.find(':') {
            let key = line[..pos].trim().to_string();
            let value = line[pos + 1..].trim().to_string();
            headers.insert(key, value);
        }
    }
    
    HttpRequest {
        method,
        path,
        headers,
        body: String::new(),
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🦀 Rust Microservice Template");
    println!("整合: 异步 + 设计模式 + 网络\n");
    
    // 构建配置
    let config = ServiceConfigBuilder::new()
        .name("api-gateway")
        .host("127.0.0.1")
        .port(8080)
        .workers(4)
        .log_level("info")
        .build()?;
    
    // 创建服务注册表
    let registry = ServiceRegistry::new();
    registry.register("auth-service".to_string(), "127.0.0.1:8081".parse()?).await;
    registry.register("user-service".to_string(), "127.0.0.1:8082".parse()?).await;
    
    // 构建路由
    let router = Arc::new(
        Router::new()
            .route("/health", Box::new(HealthHandler))
            .route("/api/services", Box::new(ApiHandler::new(Arc::clone(&registry))))
    );
    
    // 创建日志器
    let logger: Arc<dyn LogObserver> = Arc::new(ConsoleLogger);
    
    // 创建并运行服务
    let service = Microservice::new(config, router, logger);
    service.run().await
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_config_builder() {
        let config = ServiceConfigBuilder::new()
            .name("test")
            .port(3000)
            .build()
            .unwrap();
        
        assert_eq!(config.name, "test");
        assert_eq!(config.port, 3000);
    }
    
    #[tokio::test]
    async fn test_service_registry() {
        let registry = ServiceRegistry::new();
        let addr = "127.0.0.1:8080".parse().unwrap();
        
        registry.register("test".to_string(), addr).await;
        let found = registry.discover("test").await;
        
        assert_eq!(found, Some(addr));
    }
    
    #[test]
    fn test_http_response() {
        let resp = HttpResponse::json(r#"{"test": true}"#);
        assert_eq!(resp.status, 200);
        assert!(resp.body.contains("test"));
    }
}
