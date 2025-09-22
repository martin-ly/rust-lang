//! CORS (Cross-Origin Resource Sharing) 模块
//!
//! 提供跨域资源共享配置和验证

use std::collections::HashSet;
use serde::{Deserialize, Serialize};
use thiserror::Error;

/// CORS配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CorsConfig {
    pub enabled: bool,
    pub allowed_origins: Vec<String>,
    pub allowed_methods: Vec<String>,
    pub allowed_headers: Vec<String>,
    pub exposed_headers: Vec<String>,
    pub allow_credentials: bool,
    pub max_age: u64,
    pub allow_wildcard: bool,
}

impl Default for CorsConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            allowed_origins: vec![
                "http://localhost:3000".to_string(),
                "http://localhost:8080".to_string(),
                "https://localhost:3000".to_string(),
                "https://localhost:8080".to_string(),
            ],
            allowed_methods: vec![
                "GET".to_string(),
                "POST".to_string(),
                "PUT".to_string(),
                "DELETE".to_string(),
                "OPTIONS".to_string(),
                "HEAD".to_string(),
                "PATCH".to_string(),
            ],
            allowed_headers: vec![
                "Content-Type".to_string(),
                "Authorization".to_string(),
                "X-Requested-With".to_string(),
                "Accept".to_string(),
                "Origin".to_string(),
            ],
            exposed_headers: vec![
                "X-Total-Count".to_string(),
                "X-Page-Count".to_string(),
            ],
            allow_credentials: true,
            max_age: 86400, // 24小时
            allow_wildcard: false,
        }
    }
}

/// CORS管理器
#[derive(Debug)]
pub struct CorsManager {
    config: CorsConfig,
    allowed_origins_set: HashSet<String>,
    allowed_methods_set: HashSet<String>,
    allowed_headers_set: HashSet<String>,
}

impl CorsManager {
    /// 创建新的CORS管理器
    pub fn new(config: CorsConfig) -> Self {
        let allowed_origins_set: HashSet<String> = config.allowed_origins.iter().cloned().collect();
        let allowed_methods_set: HashSet<String> = config.allowed_methods.iter().cloned().collect();
        let allowed_headers_set: HashSet<String> = config.allowed_headers.iter().cloned().collect();

        Self {
            config,
            allowed_origins_set,
            allowed_methods_set,
            allowed_headers_set,
        }
    }

    /// 验证CORS请求
    pub fn validate_request(
        &self,
        origin: &Option<String>,
        method: &str,
        path: &str,
    ) -> Result<CorsValidationResult, CorsError> {
        if !self.config.enabled {
            return Ok(CorsValidationResult::allowed());
        }

        // 验证Origin
        let origin_allowed = if let Some(origin) = origin {
            self.is_origin_allowed(origin)
        } else {
            // 同源请求或没有Origin头
            true
        };

        // 验证方法
        let method_allowed = self.is_method_allowed(method);

        // 验证路径（可以添加路径特定的CORS规则）
        let path_allowed = self.is_path_allowed(path);

        if !origin_allowed {
            return Err(CorsError::OriginNotAllowed(origin.clone().unwrap_or_default()));
        }

        if !method_allowed {
            return Err(CorsError::MethodNotAllowed(method.to_string()));
        }

        if !path_allowed {
            return Err(CorsError::PathNotAllowed(path.to_string()));
        }

        Ok(CorsValidationResult {
            allowed: true,
            origin: origin.clone(),
            method: method.to_string(),
            path: path.to_string(),
            allow_credentials: self.config.allow_credentials,
            max_age: self.config.max_age,
            allowed_headers: self.config.allowed_headers.clone(),
            exposed_headers: self.config.exposed_headers.clone(),
        })
    }

    /// 检查Origin是否被允许
    fn is_origin_allowed(&self, origin: &str) -> bool {
        if self.config.allow_wildcard && origin == "*" {
            return true;
        }

        // 精确匹配
        if self.allowed_origins_set.contains(origin) {
            return true;
        }

        // 通配符匹配
        if self.config.allow_wildcard {
            for allowed_origin in &self.config.allowed_origins {
                if self.matches_wildcard_pattern(origin, allowed_origin) {
                    return true;
                }
            }
        }

        false
    }

    /// 检查方法是否被允许
    fn is_method_allowed(&self, method: &str) -> bool {
        self.allowed_methods_set.contains(method)
    }

    /// 检查路径是否被允许
    fn is_path_allowed(&self, _path: &str) -> bool {
        // 这里可以添加路径特定的CORS规则
        // 例如某些路径不允许跨域访问
        true
    }

    /// 通配符模式匹配
    fn matches_wildcard_pattern(&self, origin: &str, pattern: &str) -> bool {
        if pattern.contains('*') {
            // 简单的通配符匹配实现
            let parts: Vec<&str> = pattern.split('*').collect();
            if parts.len() == 2 {
                let prefix = parts[0];
                let suffix = parts[1];
                origin.starts_with(prefix) && origin.ends_with(suffix)
            } else {
                false
            }
        } else {
            origin == pattern
        }
    }

    /// 生成CORS响应头
    pub fn generate_headers(&self, origin: &Option<String>) -> CorsHeaders {
        let mut headers = CorsHeaders::new();

        if !self.config.enabled {
            return headers;
        }

        // Access-Control-Allow-Origin
        if let Some(origin) = origin {
            if self.is_origin_allowed(origin) {
                headers.set_allow_origin(origin.clone());
            }
        } else if self.config.allow_wildcard {
            headers.set_allow_origin("*".to_string());
        }

        // Access-Control-Allow-Methods
        headers.set_allow_methods(self.config.allowed_methods.clone());

        // Access-Control-Allow-Headers
        headers.set_allow_headers(self.config.allowed_headers.clone());

        // Access-Control-Expose-Headers
        headers.set_expose_headers(self.config.exposed_headers.clone());

        // Access-Control-Allow-Credentials
        if self.config.allow_credentials {
            headers.set_allow_credentials(true);
        }

        // Access-Control-Max-Age
        headers.set_max_age(self.config.max_age);

        headers
    }

    /// 处理预检请求
    pub fn handle_preflight_request(
        &self,
        origin: &Option<String>,
        method: &str,
        headers: &Option<String>,
    ) -> Result<CorsPreflightResponse, CorsError> {
        if !self.config.enabled {
            return Ok(CorsPreflightResponse::allowed());
        }

        // 验证Origin
        if let Some(origin) = origin {
            if !self.is_origin_allowed(origin) {
                return Err(CorsError::OriginNotAllowed(origin.clone()));
            }
        }

        // 验证方法
        if !self.is_method_allowed(method) {
            return Err(CorsError::MethodNotAllowed(method.to_string()));
        }

        // 验证请求头
        if let Some(request_headers) = headers {
            let header_list: Vec<&str> = request_headers.split(',').map(|h| h.trim()).collect();
            for header in header_list {
                if !self.is_header_allowed(header) {
                    return Err(CorsError::HeaderNotAllowed(header.to_string()));
                }
            }
        }

        let cors_headers = self.generate_headers(origin);

        Ok(CorsPreflightResponse {
            allowed: true,
            headers: cors_headers,
        })
    }

    /// 检查请求头是否被允许
    fn is_header_allowed(&self, header: &str) -> bool {
        // 简单请求头总是被允许
        let simple_headers = vec![
            "accept",
            "accept-language",
            "content-language",
            "content-type",
        ];

        if simple_headers.contains(&header.to_lowercase().as_str()) {
            return true;
        }

        // 检查是否在允许列表中
        self.allowed_headers_set.contains(header)
    }

    /// 添加允许的Origin
    pub fn add_allowed_origin(&mut self, origin: String) {
        self.config.allowed_origins.push(origin.clone());
        self.allowed_origins_set.insert(origin);
    }

    /// 添加允许的方法
    pub fn add_allowed_method(&mut self, method: String) {
        self.config.allowed_methods.push(method.clone());
        self.allowed_methods_set.insert(method);
    }

    /// 添加允许的请求头
    pub fn add_allowed_header(&mut self, header: String) {
        self.config.allowed_headers.push(header.clone());
        self.allowed_headers_set.insert(header);
    }

    /// 获取CORS配置
    pub fn get_config(&self) -> &CorsConfig {
        &self.config
    }

    /// 获取CORS统计信息
    pub fn get_stats(&self) -> CorsStats {
        CorsStats {
            enabled: self.config.enabled,
            allowed_origins_count: self.config.allowed_origins.len(),
            allowed_methods_count: self.config.allowed_methods.len(),
            allowed_headers_count: self.config.allowed_headers.len(),
            allow_credentials: self.config.allow_credentials,
            max_age: self.config.max_age,
            allow_wildcard: self.config.allow_wildcard,
        }
    }
}

/// CORS验证结果
#[derive(Debug, Clone)]
pub struct CorsValidationResult {
    pub allowed: bool,
    pub origin: Option<String>,
    pub method: String,
    pub path: String,
    pub allow_credentials: bool,
    pub max_age: u64,
    pub allowed_headers: Vec<String>,
    pub exposed_headers: Vec<String>,
}

impl CorsValidationResult {
    /// 创建允许的结果
    pub fn allowed() -> Self {
        Self {
            allowed: true,
            origin: None,
            method: String::new(),
            path: String::new(),
            allow_credentials: false,
            max_age: 0,
            allowed_headers: Vec::new(),
            exposed_headers: Vec::new(),
        }
    }
}

/// CORS预检响应
#[derive(Debug, Clone)]
pub struct CorsPreflightResponse {
    pub allowed: bool,
    pub headers: CorsHeaders,
}

impl CorsPreflightResponse {
    /// 创建允许的预检响应
    pub fn allowed() -> Self {
        Self {
            allowed: true,
            headers: CorsHeaders::new(),
        }
    }
}

/// CORS响应头
#[derive(Debug, Clone)]
pub struct CorsHeaders {
    pub allow_origin: Option<String>,
    pub allow_methods: Vec<String>,
    pub allow_headers: Vec<String>,
    pub expose_headers: Vec<String>,
    pub allow_credentials: bool,
    pub max_age: u64,
}

impl CorsHeaders {
    /// 创建新的CORS响应头
    pub fn new() -> Self {
        Self {
            allow_origin: None,
            allow_methods: Vec::new(),
            allow_headers: Vec::new(),
            expose_headers: Vec::new(),
            allow_credentials: false,
            max_age: 0,
        }
    }

    /// 设置Access-Control-Allow-Origin
    pub fn set_allow_origin(&mut self, origin: String) {
        self.allow_origin = Some(origin);
    }

    /// 设置Access-Control-Allow-Methods
    pub fn set_allow_methods(&mut self, methods: Vec<String>) {
        self.allow_methods = methods;
    }

    /// 设置Access-Control-Allow-Headers
    pub fn set_allow_headers(&mut self, headers: Vec<String>) {
        self.allow_headers = headers;
    }

    /// 设置Access-Control-Expose-Headers
    pub fn set_expose_headers(&mut self, headers: Vec<String>) {
        self.expose_headers = headers;
    }

    /// 设置Access-Control-Allow-Credentials
    pub fn set_allow_credentials(&mut self, allow: bool) {
        self.allow_credentials = allow;
    }

    /// 设置Access-Control-Max-Age
    pub fn set_max_age(&mut self, max_age: u64) {
        self.max_age = max_age;
    }

    /// 转换为HTTP头部
    pub fn to_http_headers(&self) -> Vec<(String, String)> {
        let mut headers = Vec::new();

        if let Some(ref origin) = self.allow_origin {
            headers.push(("Access-Control-Allow-Origin".to_string(), origin.clone()));
        }

        if !self.allow_methods.is_empty() {
            headers.push((
                "Access-Control-Allow-Methods".to_string(),
                self.allow_methods.join(", "),
            ));
        }

        if !self.allow_headers.is_empty() {
            headers.push((
                "Access-Control-Allow-Headers".to_string(),
                self.allow_headers.join(", "),
            ));
        }

        if !self.expose_headers.is_empty() {
            headers.push((
                "Access-Control-Expose-Headers".to_string(),
                self.expose_headers.join(", "),
            ));
        }

        if self.allow_credentials {
            headers.push(("Access-Control-Allow-Credentials".to_string(), "true".to_string()));
        }

        if self.max_age > 0 {
            headers.push(("Access-Control-Max-Age".to_string(), self.max_age.to_string()));
        }

        headers
    }
}

/// CORS统计信息
#[derive(Debug, Clone)]
pub struct CorsStats {
    pub enabled: bool,
    pub allowed_origins_count: usize,
    pub allowed_methods_count: usize,
    pub allowed_headers_count: usize,
    pub allow_credentials: bool,
    pub max_age: u64,
    pub allow_wildcard: bool,
}

/// CORS错误
#[derive(Error, Debug, Clone)]
pub enum CorsError {
    #[error("Origin不被允许: {0}")]
    OriginNotAllowed(String),
    #[error("方法不被允许: {0}")]
    MethodNotAllowed(String),
    #[error("路径不被允许: {0}")]
    PathNotAllowed(String),
    #[error("请求头不被允许: {0}")]
    HeaderNotAllowed(String),
    #[error("CORS配置错误: {0}")]
    ConfigurationError(String),
}

/// CORS结果类型别名
pub type CorsResult<T> = Result<T, CorsError>;
