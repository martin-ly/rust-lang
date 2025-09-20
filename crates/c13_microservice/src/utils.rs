//! 工具模块
//!
//! 提供常用的工具函数和宏，简化微服务开发。

use serde::{Deserialize, Serialize};
use std::time::{Duration, SystemTime, UNIX_EPOCH};
use uuid::Uuid;

/// 生成唯一ID
pub fn generate_id() -> String {
    Uuid::new_v4().to_string()
}

/// 获取当前时间戳（毫秒）
pub fn current_timestamp() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_millis() as u64
}

/// 获取当前时间戳（秒）
pub fn current_timestamp_secs() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs()
}

/// 格式化持续时间
pub fn format_duration(duration: Duration) -> String {
    let total_secs = duration.as_secs();
    let hours = total_secs / 3600;
    let minutes = (total_secs % 3600) / 60;
    let seconds = total_secs % 60;

    if hours > 0 {
        format!("{}h {}m {}s", hours, minutes, seconds)
    } else if minutes > 0 {
        format!("{}m {}s", minutes, seconds)
    } else {
        format!("{}s", seconds)
    }
}

/// 健康检查响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HealthCheck {
    pub status: String,
    pub timestamp: u64,
    pub version: String,
    pub uptime: u64,
    pub dependencies: Vec<DependencyStatus>,
}

/// 依赖状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DependencyStatus {
    pub name: String,
    pub status: String,
    pub response_time: Option<u64>,
    pub error: Option<String>,
}

impl HealthCheck {
    /// 创建健康检查响应
    pub fn new(version: String, uptime: u64) -> Self {
        Self {
            status: "healthy".to_string(),
            timestamp: current_timestamp_secs(),
            version,
            uptime,
            dependencies: Vec::new(),
        }
    }

    /// 添加依赖状态
    pub fn add_dependency(
        mut self,
        name: String,
        status: String,
        response_time: Option<u64>,
        error: Option<String>,
    ) -> Self {
        self.dependencies.push(DependencyStatus {
            name,
            status,
            response_time,
            error,
        });
        self
    }

    /// 检查是否有不健康的依赖
    pub fn is_healthy(&self) -> bool {
        self.dependencies.iter().all(|dep| dep.status == "healthy")
    }
}

/// 分页参数
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PaginationParams {
    pub page: u32,
    pub page_size: u32,
    pub total: Option<u64>,
}

impl PaginationParams {
    /// 创建分页参数
    pub fn new(page: u32, page_size: u32) -> Self {
        Self {
            page: page.max(1),
            page_size: page_size.clamp(1, 1000), // 限制最大页面大小
            total: None,
        }
    }

    /// 计算偏移量
    pub fn offset(&self) -> u64 {
        ((self.page - 1) * self.page_size) as u64
    }

    /// 计算总页数
    pub fn total_pages(&self) -> Option<u32> {
        self.total
            .map(|total| ((total as f64) / (self.page_size as f64)).ceil() as u32)
    }
}

/// 分页响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PaginatedResponse<T> {
    pub data: Vec<T>,
    pub pagination: PaginationParams,
}

impl<T> PaginatedResponse<T> {
    /// 创建分页响应
    pub fn new(data: Vec<T>, pagination: PaginationParams) -> Self {
        Self { data, pagination }
    }
}

/// 错误响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ErrorResponse {
    pub error: String,
    pub message: String,
    pub code: u32,
    pub timestamp: u64,
    pub request_id: Option<String>,
}

impl ErrorResponse {
    /// 创建错误响应
    pub fn new(error: String, message: String, code: u32) -> Self {
        Self {
            error,
            message,
            code,
            timestamp: current_timestamp_secs(),
            request_id: None,
        }
    }

    /// 设置请求ID
    pub fn with_request_id(mut self, request_id: String) -> Self {
        self.request_id = Some(request_id);
        self
    }
}

/// 成功响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SuccessResponse<T> {
    pub data: T,
    pub message: String,
    pub timestamp: u64,
    pub request_id: Option<String>,
}

impl<T> SuccessResponse<T> {
    /// 创建成功响应
    pub fn new(data: T, message: String) -> Self {
        Self {
            data,
            message,
            timestamp: current_timestamp_secs(),
            request_id: None,
        }
    }

    /// 设置请求ID
    pub fn with_request_id(mut self, request_id: String) -> Self {
        self.request_id = Some(request_id);
        self
    }
}

/// 重试配置
#[derive(Debug, Clone)]
pub struct RetryConfig {
    pub max_attempts: u32,
    pub initial_delay: Duration,
    pub max_delay: Duration,
    pub backoff_multiplier: f64,
}

impl Default for RetryConfig {
    fn default() -> Self {
        Self {
            max_attempts: 3,
            initial_delay: Duration::from_millis(100),
            max_delay: Duration::from_secs(5),
            backoff_multiplier: 2.0,
        }
    }
}

/// 执行重试操作
pub async fn retry<F, T, E>(config: RetryConfig, mut operation: F) -> Result<T, E>
where
    F: FnMut() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T, E>> + Send>>,
    E: std::fmt::Debug,
{
    let mut delay = config.initial_delay;

    for attempt in 1..=config.max_attempts {
        match operation().await {
            Ok(result) => return Ok(result),
            Err(e) => {
                if attempt == config.max_attempts {
                    return Err(e);
                }

                tokio::time::sleep(delay).await;
                delay = std::cmp::min(
                    Duration::from_millis(
                        (delay.as_millis() as f64 * config.backoff_multiplier) as u64,
                    ),
                    config.max_delay,
                );
            }
        }
    }

    unreachable!()
}

/// 超时执行操作
pub async fn with_timeout<F, T>(
    duration: Duration,
    future: F,
) -> Result<T, tokio::time::error::Elapsed>
where
    F: std::future::Future<Output = T>,
{
    tokio::time::timeout(duration, future).await
}

/// 字符串工具函数
pub mod string {
    /// 检查字符串是否为空或只包含空白字符
    pub fn is_blank(s: &str) -> bool {
        s.trim().is_empty()
    }

    /// 截断字符串到指定长度
    pub fn truncate(s: &str, max_len: usize) -> String {
        if s.len() <= max_len {
            s.to_string()
        } else {
            format!("{}...", &s[..max_len.saturating_sub(3)])
        }
    }

    /// 生成随机字符串
    pub fn random_string(length: usize) -> String {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let mut hasher = DefaultHasher::new();
        crate::utils::current_timestamp().hash(&mut hasher);
        let hash = hasher.finish();

        format!("{:x}", hash)[..length.min(16)].to_string()
    }
}

/// 时间工具函数
pub mod time {
    use super::*;

    /// 解析持续时间字符串
    pub fn parse_duration(s: &str) -> Option<Duration> {
        let s = s.trim();

        if let Some(stripped) = s.strip_suffix("ms") {
            stripped
                .parse::<u64>()
                .ok()
                .map(Duration::from_millis)
        } else if let Some(stripped) = s.strip_suffix("s") {
            stripped
                .parse::<u64>()
                .ok()
                .map(Duration::from_secs)
        } else if let Some(stripped) = s.strip_suffix("m") {
            stripped
                .parse::<u64>()
                .ok()
                .map(|m| Duration::from_secs(m * 60))
        } else if let Some(stripped) = s.strip_suffix("h") {
            stripped
                .parse::<u64>()
                .ok()
                .map(|h| Duration::from_secs(h * 3600))
        } else {
            s.parse::<u64>().ok().map(Duration::from_secs)
        }
    }

    /// 格式化时间戳为可读格式
    pub fn format_timestamp(timestamp: u64) -> String {
        let datetime = chrono::DateTime::from_timestamp(timestamp as i64, 0).unwrap_or_default();
        datetime.format("%Y-%m-%d %H:%M:%S").to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_generate_id() {
        let id1 = generate_id();
        let id2 = generate_id();
        assert_ne!(id1, id2);
        assert!(!id1.is_empty());
    }

    #[test]
    fn test_current_timestamp() {
        let ts1 = current_timestamp();
        let ts2 = current_timestamp();
        assert!(ts2 >= ts1);
    }

    #[test]
    fn test_format_duration() {
        assert_eq!(format_duration(Duration::from_secs(65)), "1m 5s");
        assert_eq!(format_duration(Duration::from_secs(3665)), "1h 1m 5s");
        assert_eq!(format_duration(Duration::from_secs(30)), "30s");
    }

    #[test]
    fn test_pagination_params() {
        let params = PaginationParams::new(2, 10);
        assert_eq!(params.offset(), 10);
        assert_eq!(params.page, 2);
        assert_eq!(params.page_size, 10);
    }

    #[test]
    fn test_health_check() {
        let health = HealthCheck::new("1.0.0".to_string(), 1000);
        assert_eq!(health.status, "healthy");
        assert_eq!(health.version, "1.0.0");
        assert!(health.is_healthy());
    }

    #[test]
    fn test_string_utils() {
        assert!(string::is_blank("  "));
        assert!(!string::is_blank("hello"));
        assert_eq!(string::truncate("hello world", 5), "he...");
    }

    #[test]
    fn test_time_utils() {
        assert_eq!(time::parse_duration("5s"), Some(Duration::from_secs(5)));
        assert_eq!(
            time::parse_duration("100ms"),
            Some(Duration::from_millis(100))
        );
        assert_eq!(time::parse_duration("2m"), Some(Duration::from_secs(120)));
    }
}
