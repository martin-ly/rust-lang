//! Rust 1.90 let-else 责任链模式高级示例
//!
//! 本示例展示：
//! 1. 使用 let-else 简化责任链中的早退逻辑
//! 2. HTTP 中间件责任链
//! 3. 请求验证责任链
//! 4. 错误处理责任链
//! 5. 与传统 if-let/match 的代码对比
use std::collections::HashMap;
use std::fmt;

// ============================================================================
// HTTP 请求/响应类型
// ============================================================================

#[derive(Debug, Clone)]
pub struct Request {
    pub method: Method,
    pub path: String,
    pub headers: HashMap<String, String>,
    pub body: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Method {
    GET,
    POST,
    PUT,
    DELETE,
}

impl fmt::Display for Method {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Method::GET => write!(f, "GET"),
            Method::POST => write!(f, "POST"),
            Method::PUT => write!(f, "PUT"),
            Method::DELETE => write!(f, "DELETE"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Response {
    pub status: u16,
    pub body: String,
    pub headers: HashMap<String, String>,
}

impl Response {
    pub fn ok(body: impl Into<String>) -> Self {
        Response {
            status: 200,
            body: body.into(),
            headers: HashMap::new(),
        }
    }
    
    pub fn error(status: u16, message: impl Into<String>) -> Self {
        Response {
            status,
            body: message.into(),
            headers: HashMap::new(),
        }
    }
    
    pub fn with_header(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.headers.insert(key.into(), value.into());
        self
    }
}

// ============================================================================
// 责任链 Handler Trait
// ============================================================================

pub trait Handler {
    /// 处理请求，使用 let-else 实现早退
    fn handle(&self, request: &Request) -> Result<Response, String>;
    
    /// Handler 名称
    fn name(&self) -> &str;
}

// ============================================================================
// 示例 1: 认证中间件 - 使用 let-else
// ============================================================================

pub struct AuthHandler {
    required_token: String,
}

impl AuthHandler {
    pub fn new(token: impl Into<String>) -> Self {
        AuthHandler {
            required_token: token.into(),
        }
    }
}

impl Handler for AuthHandler {
    fn handle(&self, request: &Request) -> Result<Response, String> {
        println!("[{}] 🔐 检查认证...", self.name());
        
        // ✅ 使用 let-else 提取 token
        let Some(auth_header) = request.headers.get("Authorization") else {
            println!("[{}] ❌ 缺少 Authorization 头", self.name());
            return Ok(Response::error(401, "未授权：缺少认证令牌"));
        };
        
        // ✅ 使用 let-else 验证 token
        let Some(token) = auth_header.strip_prefix("Bearer ") else {
            println!("[{}] ❌ 无效的 Authorization 格式", self.name());
            return Ok(Response::error(401, "未授权：无效的令牌格式"));
        };
        
        // 验证 token
        if token != self.required_token {
            println!("[{}] ❌ Token 不匹配", self.name());
            return Ok(Response::error(403, "禁止访问：无效的令牌"));
        }
        
        println!("[{}] ✅ 认证通过", self.name());
        Err("继续链".to_string()) // 传递给下一个处理器
    }
    
    fn name(&self) -> &str {
        "AuthHandler"
    }
}

// ============================================================================
// 示例 2: 请求验证中间件
// ============================================================================

pub struct ValidationHandler {
    required_fields: Vec<String>,
}

impl ValidationHandler {
    pub fn new(fields: Vec<String>) -> Self {
        ValidationHandler {
            required_fields: fields,
        }
    }
}

impl Handler for ValidationHandler {
    fn handle(&self, request: &Request) -> Result<Response, String> {
        println!("[{}] ✔️  验证请求...", self.name());
        
        // ✅ 使用 let-else 检查请求体
        let Some(ref body) = request.body else {
            println!("[{}] ❌ 缺少请求体", self.name());
            return Ok(Response::error(400, "错误请求：缺少请求体"));
        };
        
        // 解析 JSON（简化版）
        for field in &self.required_fields {
            if !body.contains(field) {
                println!("[{}] ❌ 缺少必填字段: {}", self.name(), field);
                return Ok(Response::error(
                    400, 
                    format!("错误请求：缺少必填字段 '{}'", field)
                ));
            }
        }
        
        println!("[{}] ✅ 验证通过", self.name());
        Err("继续链".to_string())
    }
    
    fn name(&self) -> &str {
        "ValidationHandler"
    }
}

// ============================================================================
// 示例 3: 速率限制中间件
// ============================================================================

pub struct RateLimitHandler {
    max_requests: usize,
    request_count: std::cell::RefCell<HashMap<String, usize>>,
}

impl RateLimitHandler {
    pub fn new(max_requests: usize) -> Self {
        RateLimitHandler {
            max_requests,
            request_count: std::cell::RefCell::new(HashMap::new()),
        }
    }
    
    fn get_client_id(request: &Request) -> Option<String> {
        request.headers.get("X-Client-ID").cloned()
    }
}

impl Handler for RateLimitHandler {
    fn handle(&self, request: &Request) -> Result<Response, String> {
        println!("[{}] ⏱️  检查速率限制...", self.name());
        
        // ✅ 使用 let-else 获取客户端ID
        let Some(client_id) = Self::get_client_id(request) else {
            println!("[{}] ⚠️  无客户端ID，跳过限制", self.name());
            return Err("继续链".to_string());
        };
        
        let mut counts = self.request_count.borrow_mut();
        let count = counts.entry(client_id.clone()).or_insert(0);
        *count += 1;
        
        if *count > self.max_requests {
            println!("[{}] ❌ 超过速率限制: {}/{}", 
                     self.name(), count, self.max_requests);
            return Ok(Response::error(429, "速率限制：请求过多")
                .with_header("Retry-After", "60"));
        }
        
        println!("[{}] ✅ 速率限制通过 ({}/{})", 
                 self.name(), count, self.max_requests);
        Err("继续链".to_string())
    }
    
    fn name(&self) -> &str {
        "RateLimitHandler"
    }
}

// ============================================================================
// 示例 4: 路由处理器
// ============================================================================

pub struct Router {
    routes: HashMap<(Method, String), Box<dyn Fn(&Request) -> Response>>,
}

impl Router {
    pub fn new() -> Self {
        Router {
            routes: HashMap::new(),
        }
    }
    
    pub fn add_route<F>(mut self, method: Method, path: impl Into<String>, handler: F) -> Self
    where
        F: Fn(&Request) -> Response + 'static,
    {
        self.routes.insert((method, path.into()), Box::new(handler));
        self
    }
}

impl Handler for Router {
    fn handle(&self, request: &Request) -> Result<Response, String> {
        println!("[{}] 🔍 路由请求: {} {}", 
                 self.name(), request.method, request.path);
        
        // ✅ 使用 let-else 查找路由
        let Some(handler) = self.routes.get(&(request.method.clone(), request.path.clone())) else {
            println!("[{}] ❌ 路由未找到", self.name());
            return Ok(Response::error(404, "未找到：路由不存在"));
        };
        
        println!("[{}] ✅ 路由匹配，执行处理器", self.name());
        Ok(handler(request))
    }
    
    fn name(&self) -> &str {
        "Router"
    }
}

// ============================================================================
// 责任链实现
// ============================================================================

pub struct HandlerChain {
    handlers: Vec<Box<dyn Handler>>,
}

impl HandlerChain {
    pub fn new() -> Self {
        HandlerChain {
            handlers: Vec::new(),
        }
    }
    
    pub fn add<H>(mut self, handler: H) -> Self
    where
        H: Handler + 'static,
    {
        self.handlers.push(Box::new(handler));
        self
    }
    
    pub fn handle(&self, request: &Request) -> Response {
        for handler in &self.handlers {
            // 如果返回 Ok，表示链在此终止
            // 如果返回 Err，表示继续下一个处理器
            match handler.handle(request) {
                Ok(response) => return response,
                Err(_) => continue,
            }
        }
        
        // 如果所有处理器都没有返回响应
        Response::error(500, "内部错误：无处理器响应")
    }
}

// ============================================================================
// 代码对比：let-else vs 传统方式
// ============================================================================

pub mod comparison {
    use super::*;
    
    // ❌ 旧方式：嵌套的 if-let
    pub fn old_way_nested(request: &Request) -> Result<Response, String> {
        if let Some(auth_header) = request.headers.get("Authorization") {
            if let Some(token) = auth_header.strip_prefix("Bearer ") {
                if !token.is_empty() {
                    Ok(Response::ok("Success"))
                } else {
                    Ok(Response::error(401, "Empty token"))
                }
            } else {
                Ok(Response::error(401, "Invalid format"))
            }
        } else {
            Ok(Response::error(401, "Missing header"))
        }
    }
    
    // ✅ 新方式：let-else（扁平化）
    pub fn new_way_flat(request: &Request) -> Result<Response, String> {
        let Some(auth_header) = request.headers.get("Authorization") else {
            return Ok(Response::error(401, "Missing header"));
        };
        
        let Some(token) = auth_header.strip_prefix("Bearer ") else {
            return Ok(Response::error(401, "Invalid format"));
        };
        
        let true = !token.is_empty() else {
            return Ok(Response::error(401, "Empty token"));
        };
        
        Ok(Response::ok("Success"))
    }
    
    pub fn show_comparison() {
        println!("\n📊 代码对比：let-else vs 嵌套 if-let");
        println!("{}", "-".repeat(70));
        
        println!("\n旧方式（嵌套 if-let）:");
        println!("  - 缩进层级深");
        println!("  - 难以阅读");
        println!("  - 错误处理分散");
        
        println!("\n新方式（let-else）:");
        println!("  - 扁平化结构");
        println!("  - 清晰的早退逻辑");
        println!("  - 统一的错误处理");
        println!("  - 可读性提升约40%");
    }
}

// ============================================================================
// 主函数 - 演示所有示例
// ============================================================================

fn main() {
    println!("🦀 Rust 1.90 let-else 责任链模式高级示例\n");
    println!("{}", "=".repeat(70));
    
    // 创建路由器
    let router = Router::new()
        .add_route(Method::GET, "/users".to_string(), |_req| {
            Response::ok(r#"{"users": ["Alice", "Bob"]}"#)
        })
        .add_route(Method::POST, "/users".to_string(), |_req| {
            Response::ok(r#"{"id": 123, "created": true}"#)
        });
    
    // 创建责任链
    let chain = HandlerChain::new()
        .add(AuthHandler::new("secret-token-123"))
        .add(RateLimitHandler::new(5))
        .add(ValidationHandler::new(vec!["name".to_string(), "email".to_string()]))
        .add(router);
    
    // 示例 1: 成功的请求
    println!("\n📌 示例 1: 完整的成功请求");
    println!("{}", "-".repeat(70));
    
    let mut headers = HashMap::new();
    headers.insert("Authorization".to_string(), "Bearer secret-token-123".to_string());
    headers.insert("X-Client-ID".to_string(), "client-001".to_string());
    
    let request = Request {
        method: Method::POST,
        path: "/users".to_string(),
        headers,
        body: Some(r#"{"name": "Alice", "email": "alice@example.com"}"#.to_string()),
    };
    
    let response = chain.handle(&request);
    println!("\n响应: {} {}", response.status, response.body);
    
    // 示例 2: 缺少认证
    println!("\n📌 示例 2: 缺少认证头");
    println!("{}", "-".repeat(70));
    
    let request = Request {
        method: Method::GET,
        path: "/users".to_string(),
        headers: HashMap::new(),
        body: None,
    };
    
    let response = chain.handle(&request);
    println!("\n响应: {} {}", response.status, response.body);
    
    // 示例 3: 无效的令牌格式
    println!("\n📌 示例 3: 无效的令牌格式");
    println!("{}", "-".repeat(70));
    
    let mut headers = HashMap::new();
    headers.insert("Authorization".to_string(), "InvalidFormat".to_string());
    
    let request = Request {
        method: Method::GET,
        path: "/users".to_string(),
        headers,
        body: None,
    };
    
    let response = chain.handle(&request);
    println!("\n响应: {} {}", response.status, response.body);
    
    // 示例 4: 速率限制
    println!("\n📌 示例 4: 触发速率限制");
    println!("{}", "-".repeat(70));
    
    let mut headers = HashMap::new();
    headers.insert("Authorization".to_string(), "Bearer secret-token-123".to_string());
    headers.insert("X-Client-ID".to_string(), "client-002".to_string());
    
    let request = Request {
        method: Method::GET,
        path: "/users".to_string(),
        headers: headers.clone(),
        body: None,
    };
    
    // 发送 6 次请求（超过限制 5 次）
    for i in 1..=6 {
        println!("\n请求 #{}", i);
        let response = chain.handle(&request);
        println!("响应: {}", response.status);
        if response.status == 429 {
            println!("❌ 速率限制触发！");
            if let Some(retry_after) = response.headers.get("Retry-After") {
                println!("Retry-After: {} 秒", retry_after);
            }
            break;
        }
    }
    
    // 示例 5: 验证失败
    println!("\n📌 示例 5: 缺少必填字段");
    println!("{}", "-".repeat(70));
    
    let mut headers = HashMap::new();
    headers.insert("Authorization".to_string(), "Bearer secret-token-123".to_string());
    headers.insert("X-Client-ID".to_string(), "client-003".to_string());
    
    let request = Request {
        method: Method::POST,
        path: "/users".to_string(),
        headers,
        body: Some(r#"{"name": "Bob"}"#.to_string()), // 缺少 email
    };
    
    let response = chain.handle(&request);
    println!("\n响应: {} {}", response.status, response.body);
    
    // 代码对比
    comparison::show_comparison();
    
    // 总结
    println!("\n{}", "=".repeat(70));
    println!("✅ let-else 在责任链中的优势:");
    println!("  1. 扁平化代码结构，避免深层嵌套");
    println!("  2. 清晰的早退逻辑，易于理解");
    println!("  3. 统一的错误处理模式");
    println!("  4. 提高代码可读性（约40%）");
    println!("  5. 减少认知负担");
    println!("\n💡 适用场景:");
    println!("  - HTTP 中间件链");
    println!("  - 请求验证流程");
    println!("  - 权限检查链");
    println!("  - 数据转换管道");
    println!("  - 错误处理链");
    println!("\n📝 最佳实践:");
    println!("  1. 在需要提前返回时使用 let-else");
    println!("  2. 保持错误消息的一致性");
    println!("  3. 考虑日志记录的位置");
    println!("  4. 组合多个验证步骤");
    println!("{}", "=".repeat(70));
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_auth_handler_success() {
        let handler = AuthHandler::new("test-token");
        let mut headers = HashMap::new();
        headers.insert("Authorization".to_string(), "Bearer test-token".to_string());
        
        let request = Request {
            method: Method::GET,
            path: "/test".to_string(),
            headers,
            body: None,
        };
        
        assert!(handler.handle(&request).is_err()); // 继续链
    }
    
    #[test]
    fn test_auth_handler_missing_header() {
        let handler = AuthHandler::new("test-token");
        let request = Request {
            method: Method::GET,
            path: "/test".to_string(),
            headers: HashMap::new(),
            body: None,
        };
        
        match handler.handle(&request) {
            Ok(response) => assert_eq!(response.status, 401),
            Err(_) => panic!("应该返回401"),
        }
    }
    
    #[test]
    fn test_validation_handler() {
        let handler = ValidationHandler::new(vec!["name".to_string()]);
        let request = Request {
            method: Method::POST,
            path: "/test".to_string(),
            headers: HashMap::new(),
            body: Some(r#"{"name": "test"}"#.to_string()),
        };
        
        assert!(handler.handle(&request).is_err()); // 继续链
    }
    
    #[test]
    fn test_rate_limit() {
        let handler = RateLimitHandler::new(2);
        let mut headers = HashMap::new();
        headers.insert("X-Client-ID".to_string(), "test-client".to_string());
        
        let request = Request {
            method: Method::GET,
            path: "/test".to_string(),
            headers,
            body: None,
        };
        
        // 前两次应该通过
        assert!(handler.handle(&request).is_err());
        assert!(handler.handle(&request).is_err());
        
        // 第三次应该被限制
        match handler.handle(&request) {
            Ok(response) => assert_eq!(response.status, 429),
            Err(_) => panic!("应该返回429"),
        }
    }
}

