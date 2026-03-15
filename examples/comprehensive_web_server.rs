//! 综合 Web 服务器示例
//! 
//! 整合 C04(泛型), C06(异步), C09(设计模式), C10(网络)
//! 
//! 运行: cargo run --example comprehensive_web_server

use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use tokio::net::{TcpListener, TcpStream};
use tokio::io::{AsyncReadExt, AsyncWriteExt};

/// 泛型路由处理器
trait Handler<T>: Send + Sync {
    async fn handle(&self, req: Request) -> Response;
}

/// HTTP 请求
#[derive(Debug, Clone)]
struct Request {
    method: String,
    path: String,
    headers: HashMap<String, String>,
    body: String,
}

/// HTTP 响应
#[derive(Debug, Clone)]
struct Response {
    status: u16,
    headers: HashMap<String, String>,
    body: String,
}

impl Response {
    fn ok(body: impl Into<String>) -> Self {
        let mut headers = HashMap::new();
        headers.insert("Content-Type".to_string(), "text/plain".to_string());
        
        Self {
            status: 200,
            headers,
            body: body.into(),
        }
    }
    
    fn not_found() -> Self {
        Self {
            status: 404,
            headers: HashMap::new(),
            body: "Not Found".to_string(),
        }
    }
    
    fn to_string(&self) -> String {
        let headers_str: String = self.headers
            .iter()
            .map(|(k, v)| format!("{}: {}", k, v))
            .collect::<Vec<_>>()
            .join("\r\n");
        
        format!(
            "HTTP/1.1 {} OK\r\n{}\r\n\r\n{}",
            self.status,
            headers_str,
            self.body
        )
    }
}

/// 状态共享（单例模式）
type SharedState = Arc<RwLock<HashMap<String, String>>>;

/// 构建器模式的 Web 服务器
struct WebServer {
    host: String,
    port: u16,
    routes: HashMap<String, Box<dyn Fn(Request) -> Response + Send + Sync>>,
}

impl WebServer {
    fn builder() -> WebServerBuilder {
        WebServerBuilder::default()
    }
    
    async fn run(self) -> Result<(), Box<dyn std::error::Error>> {
        let addr = format!("{}:{}", self.host, self.port);
        let listener = TcpListener::bind(&addr).await?;
        
        println!("🚀 Server running on http://{}", addr);
        
        let routes = Arc::new(self.routes);
        
        loop {
            let (stream, _) = listener.accept().await?;
            let routes = Arc::clone(&routes);
            
            tokio::spawn(async move {
                if let Err(e) = handle_connection(stream, routes).await {
                    eprintln!("Connection error: {}", e);
                }
            });
        }
    }
}

/// Web 服务器构建器
#[derive(Default)]
struct WebServerBuilder {
    host: Option<String>,
    port: Option<u16>,
    routes: HashMap<String, Box<dyn Fn(Request) -> Response + Send + Sync>>,
}

impl WebServerBuilder {
    fn host(mut self, host: impl Into<String>) -> Self {
        self.host = Some(host.into());
        self
    }
    
    fn port(mut self, port: u16) -> Self {
        self.port = Some(port);
        self
    }
    
    fn route<F>(mut self, path: impl Into<String>, handler: F) -> Self
    where
        F: Fn(Request) -> Response + Send + Sync + 'static,
    {
        self.routes.insert(path.into(), Box::new(handler));
        self
    }
    
    fn build(self) -> Result<WebServer, String> {
        Ok(WebServer {
            host: self.host.unwrap_or_else(|| "127.0.0.1".to_string()),
            port: self.port.unwrap_or(8080),
            routes: self.routes,
        })
    }
}

async fn handle_connection(
    mut stream: TcpStream,
    routes: Arc<HashMap<String, Box<dyn Fn(Request) -> Response + Send + Sync>>>,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut buffer = [0u8; 1024];
    let n = stream.read(&mut buffer).await?;
    
    let request_str = String::from_utf8_lossy(&buffer[..n]);
    let request = parse_request(&request_str);
    
    let response = if let Some(handler) = routes.get(&request.path) {
        handler(request)
    } else {
        Response::not_found()
    };
    
    stream.write_all(response.to_string().as_bytes()).await?;
    Ok(())
}

fn parse_request(request_str: &str) -> Request {
    let lines: Vec<&str> = request_str.lines().collect();
    let first_line = lines.first().unwrap_or(&"GET / HTTP/1.1");
    
    let parts: Vec<&str> = first_line.split_whitespace().collect();
    let method = parts.get(0).unwrap_or(&"GET").to_string();
    let path = parts.get(1).unwrap_or(&"/").to_string();
    
    Request {
        method,
        path,
        headers: HashMap::new(),
        body: String::new(),
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🦀 Rust 综合 Web 服务器示例");
    println!("整合: 泛型 + 异步 + 设计模式 + 网络\n");
    
    let server = WebServer::builder()
        .host("127.0.0.1")
        .port(8080)
        .route("/", |_| {
            Response::ok("🦀 Welcome to Rust Web Server!")
        })
        .route("/api/hello", |_| {
            Response::ok("Hello, API!")
        })
        .route("/status", |_| {
            Response::ok("Server is running!")
        })
        .build()?;
    
    server.run().await
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_response_ok() {
        let response = Response::ok("test");
        assert_eq!(response.status, 200);
        assert_eq!(response.body, "test");
    }
    
    #[test]
    fn test_web_server_builder() {
        let server = WebServer::builder()
            .host("0.0.0.0")
            .port(3000)
            .route("/test", |_| Response::ok("test"))
            .build();
        
        assert!(server.is_ok());
    }
}
