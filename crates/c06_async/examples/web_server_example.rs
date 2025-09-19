//! Web服务器示例
//! 
//! 展示如何使用Tokio构建高性能异步Web服务器

use std::sync::Arc;
use std::time::Duration;
use anyhow::Result;
use tokio::net::{TcpListener, TcpStream};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::time::sleep;

/// HTTP请求结构
#[derive(Debug, Clone)]
pub struct HttpRequest {
    pub method: String,
    pub path: String,
    pub headers: std::collections::HashMap<String, String>,
    pub body: String,
}

/// HTTP响应结构
#[derive(Debug, Clone)]
pub struct HttpResponse {
    pub status_code: u16,
    pub status_text: String,
    pub headers: std::collections::HashMap<String, String>,
    pub body: String,
}

impl HttpResponse {
    pub fn new(status_code: u16, status_text: &str, body: &str) -> Self {
        let mut headers = std::collections::HashMap::new();
        headers.insert("Content-Type".to_string(), "text/html; charset=utf-8".to_string());
        headers.insert("Content-Length".to_string(), body.len().to_string());
        
        Self {
            status_code,
            status_text: status_text.to_string(),
            headers,
            body: body.to_string(),
        }
    }
    
    pub fn to_string(&self) -> String {
        let mut response = format!("HTTP/1.1 {} {}\r\n", self.status_code, self.status_text);
        
        for (key, value) in &self.headers {
            response.push_str(&format!("{}: {}\r\n", key, value));
        }
        
        response.push_str("\r\n");
        response.push_str(&self.body);
        response
    }
}

/// 路由处理器
#[derive(Clone)]
pub struct RouteHandler {
    pub path: String,
    pub handler: fn(&HttpRequest) -> Result<HttpResponse>,
}

/// 异步Web服务器
pub struct AsyncWebServer {
    listener: TcpListener,
    routes: Vec<RouteHandler>,
    request_count: Arc<tokio::sync::Mutex<u64>>,
}

impl AsyncWebServer {
    /// 创建新的Web服务器
    pub async fn new(addr: &str) -> Result<Self> {
        let listener = TcpListener::bind(addr).await?;
        println!("🚀 Web服务器启动在: {}", addr);
        
        Ok(Self {
            listener,
            routes: Vec::new(),
            request_count: Arc::new(tokio::sync::Mutex::new(0)),
        })
    }
    
    /// 添加路由
    pub fn add_route(&mut self, path: &str, handler: fn(&HttpRequest) -> Result<HttpResponse>) {
        self.routes.push(RouteHandler {
            path: path.to_string(),
            handler,
        });
    }
    
    /// 启动服务器
    pub async fn start(&self) -> Result<()> {
        println!("📡 等待连接...");
        
        loop {
            let (socket, addr) = self.listener.accept().await?;
            println!("🔗 新连接来自: {}", addr);
            
            let routes = self.routes.clone();
            let request_count = Arc::clone(&self.request_count);
            
            tokio::spawn(async move {
                if let Err(e) = Self::handle_connection(socket, routes, request_count).await {
                    eprintln!("❌ 处理连接时出错: {}", e);
                }
            });
        }
    }
    
    /// 处理单个连接
    async fn handle_connection(
        mut socket: TcpStream,
        routes: Vec<RouteHandler>,
        request_count: Arc<tokio::sync::Mutex<u64>>,
    ) -> Result<()> {
        let mut buffer = [0; 1024];
        
        loop {
            match socket.read(&mut buffer).await {
                Ok(0) => {
                    println!("🔌 连接关闭");
                    return Ok(());
                }
                Ok(n) => {
                    let request_str = String::from_utf8_lossy(&buffer[..n]);
                    println!("📨 收到请求:\n{}", request_str);
                    
                    // 解析HTTP请求
                    let request = Self::parse_request(&request_str)?;
                    
                    // 更新请求计数
                    {
                        let mut count = request_count.lock().await;
                        *count += 1;
                        println!("📊 总请求数: {}", *count);
                    }
                    
                    // 查找匹配的路由
                    let response = Self::find_route_handler(&request, &routes)?;
                    
                    // 发送响应
                    let response_str = response.to_string();
                    socket.write_all(response_str.as_bytes()).await?;
                    socket.flush().await?;
                    
                    println!("📤 响应已发送");
                }
                Err(e) => {
                    eprintln!("❌ 读取数据时出错: {}", e);
                    return Err(e.into());
                }
            }
        }
    }
    
    /// 解析HTTP请求
    fn parse_request(request_str: &str) -> Result<HttpRequest> {
        let lines: Vec<&str> = request_str.lines().collect();
        if lines.is_empty() {
            return Err(anyhow::anyhow!("空请求"));
        }
        
        // 解析请求行
        let request_line = lines[0];
        let parts: Vec<&str> = request_line.split_whitespace().collect();
        if parts.len() < 3 {
            return Err(anyhow::anyhow!("无效的请求行"));
        }
        
        let method = parts[0].to_string();
        let path = parts[1].to_string();
        
        // 解析头部
        let mut headers = std::collections::HashMap::new();
        let mut body_start = 1;
        
        for (i, line) in lines.iter().enumerate().skip(1) {
            if line.is_empty() {
                body_start = i + 1;
                break;
            }
            
            if let Some(colon_pos) = line.find(':') {
                let key = line[..colon_pos].trim().to_string();
                let value = line[colon_pos + 1..].trim().to_string();
                headers.insert(key, value);
            }
        }
        
        // 解析请求体
        let body = if body_start < lines.len() {
            lines[body_start..].join("\n")
        } else {
            String::new()
        };
        
        Ok(HttpRequest {
            method,
            path,
            headers,
            body,
        })
    }
    
    /// 查找匹配的路由处理器
    fn find_route_handler(request: &HttpRequest, routes: &[RouteHandler]) -> Result<HttpResponse> {
        for route in routes {
            if request.path == route.path {
                return (route.handler)(request);
            }
        }
        
        // 默认404响应
        Ok(HttpResponse::new(
            404,
            "Not Found",
            "<html><body><h1>404 - 页面未找到</h1></body></html>"
        ))
    }
}

/// 示例路由处理器

/// 首页处理器
fn home_handler(_request: &HttpRequest) -> Result<HttpResponse> {
    let html = r#"
    <!DOCTYPE html>
    <html>
    <head>
        <title>异步Web服务器</title>
        <meta charset="utf-8">
    </head>
    <body>
        <h1>🚀 欢迎使用异步Web服务器</h1>
        <p>这是一个使用Tokio构建的高性能异步Web服务器示例。</p>
        <ul>
            <li><a href="/api/status">API状态</a></li>
            <li><a href="/api/time">当前时间</a></li>
            <li><a href="/api/echo">回显测试</a></li>
        </ul>
    </body>
    </html>
    "#;
    
    Ok(HttpResponse::new(200, "OK", html))
}

/// API状态处理器
fn status_handler(_request: &HttpRequest) -> Result<HttpResponse> {
    let status = serde_json::json!({
        "status": "running",
        "server": "AsyncWebServer",
        "runtime": "tokio",
        "timestamp": chrono::Utc::now().to_rfc3339()
    });
    
    let mut response = HttpResponse::new(200, "OK", &status.to_string());
    response.headers.insert("Content-Type".to_string(), "application/json".to_string());
    
    Ok(response)
}

/// 时间处理器
fn time_handler(_request: &HttpRequest) -> Result<HttpResponse> {
    let now = chrono::Utc::now();
    let time_info = serde_json::json!({
        "timestamp": now.timestamp(),
        "datetime": now.to_rfc3339(),
        "timezone": "UTC"
    });
    
    let mut response = HttpResponse::new(200, "OK", &time_info.to_string());
    response.headers.insert("Content-Type".to_string(), "application/json".to_string());
    
    Ok(response)
}

/// 回显处理器
fn echo_handler(request: &HttpRequest) -> Result<HttpResponse> {
    let echo_data = serde_json::json!({
        "method": request.method,
        "path": request.path,
        "headers": request.headers,
        "body": request.body,
        "timestamp": chrono::Utc::now().to_rfc3339()
    });
    
    let mut response = HttpResponse::new(200, "OK", &echo_data.to_string());
    response.headers.insert("Content-Type".to_string(), "application/json".to_string());
    
    Ok(response)
}

/// 异步任务示例
async fn background_task(request_count: Arc<tokio::sync::Mutex<u64>>) {
    loop {
        sleep(Duration::from_secs(10)).await;
        let count = *request_count.lock().await;
        println!("📈 后台任务: 当前总请求数: {}", count);
    }
}

/// 主函数
#[tokio::main]
async fn main() -> Result<()> {
    println!("🚀 启动异步Web服务器示例");
    
    // 创建Web服务器
    let mut server = AsyncWebServer::new("127.0.0.1:8080").await?;
    
    // 添加路由
    server.add_route("/", home_handler);
    server.add_route("/api/status", status_handler);
    server.add_route("/api/time", time_handler);
    server.add_route("/api/echo", echo_handler);
    
    // 启动后台任务
    let request_count = Arc::clone(&server.request_count);
    tokio::spawn(background_task(request_count));
    
    println!("📋 可用路由:");
    println!("  GET  /           - 首页");
    println!("  GET  /api/status - API状态");
    println!("  GET  /api/time   - 当前时间");
    println!("  POST /api/echo   - 回显测试");
    println!("");
    println!("🌐 在浏览器中访问: http://127.0.0.1:8080");
    println!("🛑 按 Ctrl+C 停止服务器");
    
    // 启动服务器
    server.start().await?;
    
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_http_response_to_string() {
        let response = HttpResponse::new(200, "OK", "Hello, World!");
        let response_str = response.to_string();
        
        assert!(response_str.contains("HTTP/1.1 200 OK"));
        assert!(response_str.contains("Content-Type: text/html"));
        assert!(response_str.contains("Hello, World!"));
    }
    
    #[test]
    fn test_parse_request() {
        let request_str = "GET /api/status HTTP/1.1\r\nHost: localhost:8080\r\n\r\n";
        let request = AsyncWebServer::parse_request(request_str).unwrap();
        
        assert_eq!(request.method, "GET");
        assert_eq!(request.path, "/api/status");
        assert_eq!(request.headers.get("Host"), Some(&"localhost:8080".to_string()));
    }
    
    #[test]
    fn test_find_route_handler() {
        let routes = vec![
            RouteHandler {
                path: "/api/status".to_string(),
                handler: status_handler,
            }
        ];
        
        let request = HttpRequest {
            method: "GET".to_string(),
            path: "/api/status".to_string(),
            headers: std::collections::HashMap::new(),
            body: String::new(),
        };
        
        let response = AsyncWebServer::find_route_handler(&request, &routes).unwrap();
        assert_eq!(response.status_code, 200);
    }
    
    #[test]
    fn test_find_route_handler_404() {
        let routes = vec![
            RouteHandler {
                path: "/api/status".to_string(),
                handler: status_handler,
            }
        ];
        
        let request = HttpRequest {
            method: "GET".to_string(),
            path: "/nonexistent".to_string(),
            headers: std::collections::HashMap::new(),
            body: String::new(),
        };
        
        let response = AsyncWebServer::find_route_handler(&request, &routes).unwrap();
        assert_eq!(response.status_code, 404);
    }
}
