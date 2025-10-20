// 🤖 AI辅助编程示例2：异步HTTP客户端
//
// 提示词：
// 场景：异步HTTP客户端
// 功能：发送GET/POST请求，支持超时和重试
// 使用：tokio + reqwest风格的API
// 错误处理：自定义Error类型

use std::time::Duration;
use thiserror::Error;

/// HTTP客户端错误类型
#[derive(Error, Debug)]
pub enum HttpError {
    #[error("Request timeout")]
    Timeout,
    
    #[error("Network error: {0}")]
    Network(String),
    
    #[error("Invalid URL: {0}")]
    InvalidUrl(String),
    
    #[error("HTTP error: {status}")]
    Http { status: u16 },
    
    #[error("Max retries exceeded")]
    MaxRetriesExceeded,
    
    #[error("Parse error: {0}")]
    Parse(String),
}

/// HTTP客户端配置
#[derive(Debug, Clone)]
pub struct ClientConfig {
    /// 请求超时时间
    pub timeout: Duration,
    /// 最大重试次数
    pub max_retries: u32,
    /// 重试延迟
    pub retry_delay: Duration,
    /// 自定义请求头
    pub headers: Vec<(String, String)>,
}

impl Default for ClientConfig {
    fn default() -> Self {
        Self {
            timeout: Duration::from_secs(30),
            max_retries: 3,
            retry_delay: Duration::from_millis(500),
            headers: Vec::new(),
        }
    }
}

/// 异步HTTP客户端
/// 
/// # 特性
/// - 支持GET/POST/PUT/DELETE方法
/// - 自动重试机制
/// - 超时控制
/// - 自定义请求头
/// 
/// # 示例
/// ```
/// let client = HttpClient::new(ClientConfig::default());
/// let response = client.get("https://api.example.com/users").await?;
/// println!("Response: {}", response.text);
/// ```
pub struct HttpClient {
    config: ClientConfig,
}

/// HTTP响应
#[derive(Debug, Clone)]
pub struct Response {
    pub status: u16,
    pub headers: Vec<(String, String)>,
    pub text: String,
}

impl HttpClient {
    /// 创建新的HTTP客户端
    pub fn new(config: ClientConfig) -> Self {
        Self { config }
    }

    /// 发送GET请求
    pub async fn get(&self, url: &str) -> Result<Response, HttpError> {
        self.request("GET", url, None).await
    }

    /// 发送POST请求
    pub async fn post(&self, url: &str, body: &str) -> Result<Response, HttpError> {
        self.request("POST", url, Some(body)).await
    }

    /// 发送PUT请求
    pub async fn put(&self, url: &str, body: &str) -> Result<Response, HttpError> {
        self.request("PUT", url, Some(body)).await
    }

    /// 发送DELETE请求
    pub async fn delete(&self, url: &str) -> Result<Response, HttpError> {
        self.request("DELETE", url, None).await
    }

    /// 内部请求实现（带重试机制）
    async fn request(
        &self,
        method: &str,
        url: &str,
        body: Option<&str>,
    ) -> Result<Response, HttpError> {
        let mut last_error = None;

        for attempt in 0..=self.config.max_retries {
            if attempt > 0 {
                // 重试延迟
                tokio::time::sleep(self.config.retry_delay).await;
                println!("🔄 重试 {}/{}", attempt, self.config.max_retries);
            }

            match self.do_request(method, url, body).await {
                Ok(response) => return Ok(response),
                Err(e) => {
                    last_error = Some(e);
                    // 某些错误不应重试
                    if let Some(HttpError::InvalidUrl(_)) = last_error {
                        break;
                    }
                }
            }
        }

        Err(last_error.unwrap_or(HttpError::MaxRetriesExceeded))
    }

    /// 执行单次请求
    async fn do_request(
        &self,
        method: &str,
        url: &str,
        body: Option<&str>,
    ) -> Result<Response, HttpError> {
        // 验证URL
        if !url.starts_with("http://") && !url.starts_with("https://") {
            return Err(HttpError::InvalidUrl(url.to_string()));
        }

        println!("🌐 {} {}", method, url);

        // 模拟网络请求（实际应用中使用reqwest）
        // 这里为了示例的独立性，使用模拟实现
        tokio::time::sleep(Duration::from_millis(100)).await;

        // 模拟响应
        let response = Response {
            status: 200,
            headers: vec![
                ("content-type".to_string(), "application/json".to_string()),
            ],
            text: format!(
                r#"{{"method": "{}", "url": "{}", "body": "{}"}}"#,
                method,
                url,
                body.unwrap_or("")
            ),
        };

        if response.status >= 400 {
            return Err(HttpError::Http {
                status: response.status,
            });
        }

        Ok(response)
    }
}

/// Builder模式构建HttpClient
pub struct HttpClientBuilder {
    config: ClientConfig,
}

impl HttpClientBuilder {
    pub fn new() -> Self {
        Self {
            config: ClientConfig::default(),
        }
    }

    pub fn timeout(mut self, timeout: Duration) -> Self {
        self.config.timeout = timeout;
        self
    }

    pub fn max_retries(mut self, max_retries: u32) -> Self {
        self.config.max_retries = max_retries;
        self
    }

    pub fn retry_delay(mut self, delay: Duration) -> Self {
        self.config.retry_delay = delay;
        self
    }

    pub fn header(mut self, key: String, value: String) -> Self {
        self.config.headers.push((key, value));
        self
    }

    pub fn build(self) -> HttpClient {
        HttpClient::new(self.config)
    }
}

impl Default for HttpClientBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_get_request() {
        let client = HttpClient::new(ClientConfig::default());
        let response = client.get("https://api.example.com/users").await.unwrap();
        
        assert_eq!(response.status, 200);
        assert!(response.text.contains("GET"));
    }

    #[tokio::test]
    async fn test_post_request() {
        let client = HttpClient::new(ClientConfig::default());
        let response = client
            .post("https://api.example.com/users", r#"{"name": "Alice"}"#)
            .await
            .unwrap();
        
        assert_eq!(response.status, 200);
        assert!(response.text.contains("POST"));
    }

    #[tokio::test]
    async fn test_builder_pattern() {
        let client = HttpClientBuilder::new()
            .timeout(Duration::from_secs(10))
            .max_retries(5)
            .header("Authorization".to_string(), "Bearer token".to_string())
            .build();
        
        assert_eq!(client.config.timeout, Duration::from_secs(10));
        assert_eq!(client.config.max_retries, 5);
    }

    #[tokio::test]
    async fn test_invalid_url() {
        let client = HttpClient::new(ClientConfig::default());
        let result = client.get("invalid-url").await;
        
        assert!(matches!(result, Err(HttpError::InvalidUrl(_))));
    }
}

#[tokio::main]
async fn main() -> Result<(), HttpError> {
    println!("🤖 AI辅助编程示例：异步HTTP客户端");
    println!("=====================================\n");

    // 1. 使用默认配置
    println!("1️⃣ 使用默认配置:");
    let client = HttpClient::new(ClientConfig::default());
    
    match client.get("https://api.example.com/users").await {
        Ok(response) => {
            println!("   ✅ GET请求成功");
            println!("   状态码: {}", response.status);
            println!("   响应: {}", response.text);
        }
        Err(e) => println!("   ❌ 错误: {}", e),
    }

    // 2. 使用Builder模式
    println!("\n2️⃣ 使用Builder模式:");
    let client = HttpClientBuilder::new()
        .timeout(Duration::from_secs(10))
        .max_retries(5)
        .retry_delay(Duration::from_millis(200))
        .header("Authorization".to_string(), "Bearer token123".to_string())
        .build();

    match client
        .post(
            "https://api.example.com/users",
            r#"{"name": "Alice", "email": "alice@example.com"}"#,
        )
        .await
    {
        Ok(response) => {
            println!("   ✅ POST请求成功");
            println!("   状态码: {}", response.status);
            println!("   响应: {}", response.text);
        }
        Err(e) => println!("   ❌ 错误: {}", e),
    }

    // 3. 测试错误处理
    println!("\n3️⃣ 测试错误处理:");
    match client.get("invalid-url").await {
        Ok(_) => println!("   不应该成功"),
        Err(e) => println!("   ✅ 正确捕获错误: {}", e),
    }

    println!("\n✅ 示例完成！");
    Ok(())
}

