//! # 容器化微服务示例
//!
//! 本示例展示如何构建适合容器化部署的 Wasm 微服务
//!
//! ## 特性
//! - HTTP 服务器
//! - 健康检查端点
//! - Prometheus 指标暴露
//! - 优雅关闭
//! - 环境变量配置
//!
//! ## 编译
//! ```bash
//! cargo build --example 08_container_microservice --target wasm32-wasi --release
//! ```
//!
//! ## 运行（使用 WasmEdge）
//! ```bash
//! wasmedge --dir .:. target/wasm32-wasi/release/examples/08_container_microservice.wasm
//! ```
//!
//! ## Docker 运行
//! ```bash
//! docker run --runtime=io.containerd.wasmedge.v1 \
//!   --platform=wasi/wasm \
//!   -p 8080:8080 \
//!   my-wasm-microservice:latest
//! ```

use std::env;
use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;
use std::time::{SystemTime, UNIX_EPOCH};

/// 应用配置
#[allow(dead_code)]
#[derive(Debug, Clone)]
struct AppConfig {
    /// 服务器地址
    host: String,
    /// 服务器端口
    port: u16,
    /// 日志级别
    log_level: String,
    /// 最大连接数
    max_connections: usize,
}

impl AppConfig {
    /// 从环境变量加载配置
    fn from_env() -> Self {
        Self {
            host: env::var("HOST").unwrap_or_else(|_| "0.0.0.0".to_string()),
            port: env::var("PORT")
                .ok()
                .and_then(|p| p.parse().ok())
                .unwrap_or(8080),
            log_level: env::var("LOG_LEVEL").unwrap_or_else(|_| "info".to_string()),
            max_connections: env::var("MAX_CONNECTIONS")
                .ok()
                .and_then(|m| m.parse().ok())
                .unwrap_or(1000),
        }
    }
}

/// 应用指标
#[derive(Debug)]
struct AppMetrics {
    /// 总请求数
    total_requests: AtomicU64,
    /// 成功请求数
    successful_requests: AtomicU64,
    /// 失败请求数
    failed_requests: AtomicU64,
    /// 启动时间戳
    start_time: u64,
}

impl AppMetrics {
    fn new() -> Self {
        let start_time = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        Self {
            total_requests: AtomicU64::new(0),
            successful_requests: AtomicU64::new(0),
            failed_requests: AtomicU64::new(0),
            start_time,
        }
    }

    /// 记录请求
    fn record_request(&self, success: bool) {
        self.total_requests.fetch_add(1, Ordering::Relaxed);
        if success {
            self.successful_requests.fetch_add(1, Ordering::Relaxed);
        } else {
            self.failed_requests.fetch_add(1, Ordering::Relaxed);
        }
    }

    /// 生成 Prometheus 格式的指标
    fn to_prometheus(&self) -> String {
        let total = self.total_requests.load(Ordering::Relaxed);
        let successful = self.successful_requests.load(Ordering::Relaxed);
        let failed = self.failed_requests.load(Ordering::Relaxed);
        let uptime = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs()
            - self.start_time;

        format!(
            "# HELP http_requests_total Total number of HTTP requests\n\
             # TYPE http_requests_total counter\n\
             http_requests_total {}\n\
             \n\
             # HELP http_requests_successful Successful HTTP requests\n\
             # TYPE http_requests_successful counter\n\
             http_requests_successful {}\n\
             \n\
             # HELP http_requests_failed Failed HTTP requests\n\
             # TYPE http_requests_failed counter\n\
             http_requests_failed {}\n\
             \n\
             # HELP app_uptime_seconds Application uptime in seconds\n\
             # TYPE app_uptime_seconds gauge\n\
             app_uptime_seconds {}\n",
            total, successful, failed, uptime
        )
    }
}

/// HTTP 响应构建器
struct Response {
    status: u16,
    status_text: &'static str,
    body: String,
    content_type: &'static str,
}

#[allow(dead_code)]
impl Response {
    fn ok(body: String) -> Self {
        Self {
            status: 200,
            status_text: "OK",
            body,
            content_type: "text/plain",
        }
    }

    fn json(body: String) -> Self {
        Self {
            status: 200,
            status_text: "OK",
            body,
            content_type: "application/json",
        }
    }

    fn not_found() -> Self {
        Self {
            status: 404,
            status_text: "Not Found",
            body: "404 Not Found".to_string(),
            content_type: "text/plain",
        }
    }

    fn to_http(&self) -> String {
        format!(
            "HTTP/1.1 {} {}\r\n\
             Content-Type: {}\r\n\
             Content-Length: {}\r\n\
             Connection: close\r\n\
             \r\n\
             {}",
            self.status,
            self.status_text,
            self.content_type,
            self.body.len(),
            self.body
        )
    }
}

/// HTTP 请求解析
#[derive(Debug)]
struct Request {
    method: String,
    path: String,
    _headers: Vec<(String, String)>,
}

impl Request {
    fn parse(buffer: &[u8]) -> Option<Self> {
        let request_str = String::from_utf8_lossy(buffer);
        let mut lines = request_str.lines();

        // 解析请求行
        let request_line = lines.next()?;
        let parts: Vec<&str> = request_line.split_whitespace().collect();
        if parts.len() < 2 {
            return None;
        }

        let method = parts[0].to_string();
        let path = parts[1].to_string();

        // 解析 headers（简化版）
        let headers = vec![];

        Some(Self {
            method,
            path,
            _headers: headers,
        })
    }
}

/// 主应用
struct App {
    config: AppConfig,
    metrics: Arc<AppMetrics>,
    shutdown: Arc<AtomicBool>,
}

impl App {
    fn new() -> Self {
        let config = AppConfig::from_env();
        println!("[INFO] Configuration loaded: {:?}", config);

        Self {
            config,
            metrics: Arc::new(AppMetrics::new()),
            shutdown: Arc::new(AtomicBool::new(false)),
        }
    }

    /// 启动服务器
    fn run(&self) -> Result<(), Box<dyn std::error::Error>> {
        let addr = format!("{}:{}", self.config.host, self.config.port);
        let listener = TcpListener::bind(&addr)?;

        println!("[INFO] Server listening on http://{}", addr);
        println!("[INFO] Endpoints:");
        println!("  - GET  /           - Home page");
        println!("  - GET  /health     - Health check");
        println!("  - GET  /ready      - Readiness check");
        println!("  - GET  /metrics    - Prometheus metrics");
        println!("  - POST /api/echo   - Echo service");

        // 设置监听器为非阻塞（简化版，实际需要更复杂的实现）
        for stream in listener.incoming() {
            if self.shutdown.load(Ordering::Relaxed) {
                println!("[INFO] Shutdown signal received, stopping server");
                break;
            }

            match stream {
                Ok(stream) => {
                    let metrics = Arc::clone(&self.metrics);
                    self.handle_connection(stream, metrics);
                }
                Err(e) => {
                    eprintln!("[ERROR] Connection failed: {}", e);
                }
            }
        }

        Ok(())
    }

    /// 处理单个连接
    fn handle_connection(&self, mut stream: TcpStream, metrics: Arc<AppMetrics>) {
        let mut buffer = [0; 1024];

        match stream.read(&mut buffer) {
            Ok(_) => {
                if let Some(request) = Request::parse(&buffer) {
                    let response = self.route_request(&request, &metrics);
                    let success = response.status == 200;

                    if let Err(e) = stream.write_all(response.to_http().as_bytes()) {
                        eprintln!("[ERROR] Failed to write response: {}", e);
                        metrics.record_request(false);
                    } else {
                        metrics.record_request(success);
                    }
                } else {
                    eprintln!("[WARN] Failed to parse request");
                    metrics.record_request(false);
                }
            }
            Err(e) => {
                eprintln!("[ERROR] Failed to read from connection: {}", e);
                metrics.record_request(false);
            }
        }
    }

    /// 路由请求
    fn route_request(&self, request: &Request, metrics: &Arc<AppMetrics>) -> Response {
        println!("[INFO] {} {}", request.method, request.path);

        match (request.method.as_str(), request.path.as_str()) {
            ("GET", "/") => self.handle_home(),
            ("GET", "/health") => self.handle_health(),
            ("GET", "/ready") => self.handle_ready(),
            ("GET", "/metrics") => self.handle_metrics(metrics),
            ("POST", "/api/echo") => self.handle_echo(request),
            ("GET", path) if path.starts_with("/api/") => self.handle_api(path),
            _ => Response::not_found(),
        }
    }

    /// 主页
    fn handle_home(&self) -> Response {
        Response::json(
            r#"{
  "service": "Wasm Microservice",
  "version": "1.0.0",
  "status": "running",
  "runtime": "WasmEdge",
  "endpoints": [
    "GET /",
    "GET /health",
    "GET /ready",
    "GET /metrics",
    "POST /api/echo",
    "GET /api/info"
  ]
}"#
            .to_string(),
        )
    }

    /// 健康检查
    fn handle_health(&self) -> Response {
        Response::json(r#"{"status":"healthy","timestamp":0}"#.to_string())
    }

    /// 就绪检查
    fn handle_ready(&self) -> Response {
        // 在实际应用中，这里会检查依赖服务（数据库、缓存等）
        Response::json(r#"{"status":"ready"}"#.to_string())
    }

    /// Prometheus 指标
    fn handle_metrics(&self, metrics: &Arc<AppMetrics>) -> Response {
        let metrics_text = metrics.to_prometheus();
        Response {
            status: 200,
            status_text: "OK",
            body: metrics_text,
            content_type: "text/plain; version=0.0.4",
        }
    }

    /// Echo 服务
    fn handle_echo(&self, _request: &Request) -> Response {
        // 简化版：实际应该解析请求体
        Response::json(r#"{"echo":"Request body would be echoed here"}"#.to_string())
    }

    /// API 信息
    fn handle_api(&self, path: &str) -> Response {
        if path == "/api/info" {
            Response::json(format!(
                r#"{{"service":"Wasm Microservice","path":"{}","config":{{"host":"{}","port":{},"log_level":"{}"}}}}"#,
                path, self.config.host, self.config.port, self.config.log_level
            ))
        } else {
            Response::not_found()
        }
    }
}

fn main() {
    println!("[INFO] Starting Wasm Microservice...");
    println!("[INFO] Runtime: WasmEdge");
    println!("[INFO] Platform: wasm32-wasi");

    let app = App::new();

    if let Err(e) = app.run() {
        eprintln!("[ERROR] Application error: {}", e);
        std::process::exit(1);
    }

    println!("[INFO] Server stopped");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_config_from_env() {
        let config = AppConfig::from_env();
        assert_eq!(config.host, "0.0.0.0");
        assert_eq!(config.port, 8080);
    }

    #[test]
    fn test_metrics() {
        let metrics = AppMetrics::new();
        metrics.record_request(true);
        metrics.record_request(true);
        metrics.record_request(false);

        assert_eq!(metrics.total_requests.load(Ordering::Relaxed), 3);
        assert_eq!(metrics.successful_requests.load(Ordering::Relaxed), 2);
        assert_eq!(metrics.failed_requests.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn test_request_parse() {
        let raw = b"GET /health HTTP/1.1\r\nHost: localhost\r\n\r\n";
        let request = Request::parse(raw).unwrap();
        assert_eq!(request.method, "GET");
        assert_eq!(request.path, "/health");
    }

    #[test]
    fn test_response_builder() {
        let response = Response::ok("test".to_string());
        let http = response.to_http();
        assert!(http.contains("200 OK"));
        assert!(http.contains("test"));
    }
}

