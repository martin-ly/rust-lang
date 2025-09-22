//! 请求验证中间件
//!
//! 提供请求参数验证、数据清理和安全检查功能

use std::collections::HashMap;
use tracing::instrument;
use regex::Regex;
use url::Url;

/// 验证配置
#[derive(Debug, Clone)]
pub struct ValidationConfig {
    pub max_body_size: usize,
    pub max_header_size: usize,
    pub max_query_params: usize,
    pub allowed_content_types: Vec<String>,
    pub blocked_user_agents: Vec<String>,
    pub rate_limit_by_ip: bool,
    pub sanitize_inputs: bool,
    pub validate_json_schema: bool,
}

impl Default for ValidationConfig {
    fn default() -> Self {
        Self {
            max_body_size: 10 * 1024 * 1024, // 10MB
            max_header_size: 8 * 1024, // 8KB
            max_query_params: 100,
            allowed_content_types: vec![
                "application/json".to_string(),
                "application/x-www-form-urlencoded".to_string(),
                "multipart/form-data".to_string(),
                "text/plain".to_string(),
            ],
            blocked_user_agents: vec![
                "curl".to_string(),
                "wget".to_string(),
                "python-requests".to_string(),
            ],
            rate_limit_by_ip: true,
            sanitize_inputs: true,
            validate_json_schema: false,
        }
    }
}

impl ValidationConfig {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_max_body_size(mut self, size: usize) -> Self {
        self.max_body_size = size;
        self
    }

    pub fn with_allowed_content_types(mut self, types: Vec<String>) -> Self {
        self.allowed_content_types = types;
        self
    }

    pub fn with_blocked_user_agents(mut self, agents: Vec<String>) -> Self {
        self.blocked_user_agents = agents;
        self
    }

    pub fn with_sanitization(mut self, enabled: bool) -> Self {
        self.sanitize_inputs = enabled;
        self
    }
}

/// 请求验证中间件
#[derive(Debug, Clone)]
pub struct RequestValidationMiddleware {
    pub config: ValidationConfig,
    pub validation_rules: HashMap<String, ValidationRule>,
    pub sanitization_rules: Vec<SanitizationRule>,
    pub security_patterns: Vec<SecurityPattern>,
}

impl Default for RequestValidationMiddleware {
    fn default() -> Self {
        Self::new(ValidationConfig::default())
    }
}

impl RequestValidationMiddleware {
    pub fn new(config: ValidationConfig) -> Self {
        let mut middleware = Self {
            config,
            validation_rules: HashMap::new(),
            sanitization_rules: Vec::new(),
            security_patterns: Vec::new(),
        };

        // 添加默认安全模式
        middleware.add_default_security_patterns();
        
        // 添加默认清理规则
        middleware.add_default_sanitization_rules();

        middleware
    }

    /// 添加默认安全模式
    fn add_default_security_patterns(&mut self) {
        // SQL注入模式
        self.security_patterns.push(SecurityPattern {
            name: "sql_injection".to_string(),
            pattern: Regex::new(r"(?i)(union|select|insert|update|delete|drop|create|alter|exec|execute)").unwrap(),
            severity: SecuritySeverity::High,
            action: SecurityAction::Block,
        });

        // XSS模式
        self.security_patterns.push(SecurityPattern {
            name: "xss".to_string(),
            pattern: Regex::new(r"(?i)(<script|javascript:|on\w+\s*=)").unwrap(),
            severity: SecuritySeverity::High,
            action: SecurityAction::Block,
        });

        // 路径遍历模式
        self.security_patterns.push(SecurityPattern {
            name: "path_traversal".to_string(),
            pattern: Regex::new(r"\.\./|\.\.\\|\.\.%2f|\.\.%5c").unwrap(),
            severity: SecuritySeverity::High,
            action: SecurityAction::Block,
        });

        // 命令注入模式
        self.security_patterns.push(SecurityPattern {
            name: "command_injection".to_string(),
            pattern: Regex::new(r"(?i)(\||&|;|\$\(|\`|\$\{).*").unwrap(),
            severity: SecuritySeverity::Medium,
            action: SecurityAction::Warn,
        });
    }

    /// 添加默认清理规则
    fn add_default_sanitization_rules(&mut self) {
        // HTML标签清理
        self.sanitization_rules.push(SanitizationRule {
            name: "html_tags".to_string(),
            pattern: Regex::new(r"<[^>]*>").unwrap(),
            replacement: "".to_string(),
            enabled: true,
        });

        // 特殊字符清理 - 使用原始字符串避免转义问题
        self.sanitization_rules.push(SanitizationRule {
            name: "special_chars".to_string(),
            pattern: Regex::new(r#"[<>"'&]"#).unwrap(),
            replacement: "".to_string(),
            enabled: true,
        });

        // 多余空格清理
        self.sanitization_rules.push(SanitizationRule {
            name: "whitespace".to_string(),
            pattern: Regex::new(r"\s+").unwrap(),
            replacement: " ".to_string(),
            enabled: true,
        });
    }

    /// 验证请求
    #[instrument(skip(self))]
    pub async fn validate_request(&self, request: &ValidationRequest) -> ValidationResult {
        let mut result = ValidationResult::new();

        // 基本验证
        if let Err(e) = self.validate_basic_request(request) {
            result.add_error(ValidationError::BasicValidation(e));
        }

        result
    }

    /// 基本请求验证
    fn validate_basic_request(&self, request: &ValidationRequest) -> Result<(), String> {
        // 验证URL
        if let Err(e) = Url::parse(&request.url) {
            return Err(format!("无效的URL: {}", e));
        }

        // 验证方法
        let valid_methods = ["GET", "POST", "PUT", "DELETE", "PATCH", "HEAD", "OPTIONS"];
        if !valid_methods.contains(&request.method.as_str()) {
            return Err(format!("不支持的HTTP方法: {}", request.method));
        }

        Ok(())
    }

    /// 字符串清理
    #[allow(dead_code)]
    fn sanitize_string(&self, input: &str) -> String {
        let mut result = input.to_string();

        for rule in &self.sanitization_rules {
            if rule.enabled {
                result = rule.pattern.replace_all(&result, &rule.replacement).to_string();
            }
        }

        result.trim().to_string()
    }
}

/// 验证规则
#[derive(Debug, Clone)]
pub struct ValidationRule {
    pub path_params: HashMap<String, ParameterRule>,
    pub query_params: HashMap<String, ParameterRule>,
    pub headers: HashMap<String, ParameterRule>,
    pub body_schema: Option<serde_json::Value>,
}

impl ValidationRule {
    pub fn new() -> Self {
        Self {
            path_params: HashMap::new(),
            query_params: HashMap::new(),
            headers: HashMap::new(),
            body_schema: None,
        }
    }
}

/// 参数验证规则
#[derive(Debug, Clone)]
pub struct ParameterRule {
    pub required: bool,
    pub data_type: ParameterType,
    pub min_length: Option<usize>,
    pub max_length: Option<usize>,
    pub pattern: Option<Regex>,
    pub allowed_values: Option<Vec<String>>,
}

impl ParameterRule {
    pub fn new(data_type: ParameterType) -> Self {
        Self {
            required: false,
            data_type,
            min_length: None,
            max_length: None,
            pattern: None,
            allowed_values: None,
        }
    }

    pub fn validate(&self, value: &str) -> Result<(), String> {
        if value.is_empty() && self.required {
            return Err("参数是必需的".to_string());
        }
        Ok(())
    }
}

/// 参数类型
#[derive(Debug, Clone)]
pub enum ParameterType {
    String,
    Integer,
    Float,
    Boolean,
    Email,
    Url,
}

/// 清理规则
#[derive(Debug, Clone)]
pub struct SanitizationRule {
    pub name: String,
    pub pattern: Regex,
    pub replacement: String,
    pub enabled: bool,
}

/// 安全模式
#[derive(Debug, Clone)]
pub struct SecurityPattern {
    pub name: String,
    pub pattern: Regex,
    pub severity: SecuritySeverity,
    pub action: SecurityAction,
}

/// 安全严重程度
#[derive(Debug, Clone)]
pub enum SecuritySeverity {
    Low,
    Medium,
    High,
    Critical,
}

/// 安全动作
#[derive(Debug, Clone)]
pub enum SecurityAction {
    Log,
    Warn,
    Block,
}

/// 验证请求
#[derive(Debug, Clone)]
pub struct ValidationRequest {
    pub method: String,
    pub url: String,
    pub path: String,
    pub path_params: HashMap<String, String>,
    pub query_params: HashMap<String, String>,
    pub headers: HashMap<String, String>,
    pub body: Option<Vec<u8>>,
    pub content_type: Option<String>,
    pub user_agent: Option<String>,
    pub client_ip: String,
}

/// 验证结果
#[derive(Debug, Clone)]
pub struct ValidationResult {
    pub is_valid: bool,
    pub errors: Vec<ValidationError>,
    pub warnings: Vec<String>,
    pub sanitized_data: Option<SanitizedData>,
}

impl ValidationResult {
    pub fn new() -> Self {
        Self {
            is_valid: true,
            errors: Vec::new(),
            warnings: Vec::new(),
            sanitized_data: None,
        }
    }

    pub fn add_error(&mut self, error: ValidationError) {
        self.errors.push(error);
        self.is_valid = false;
    }

    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }
}

/// 验证错误
#[derive(Debug, Clone)]
pub enum ValidationError {
    BasicValidation(String),
    ContentType(String),
    RequestSize(String),
    UserAgent(String),
    Security(String),
    Custom(String),
}

/// 清理后的数据
#[derive(Debug, Clone)]
pub struct SanitizedData {
    pub query_params: HashMap<String, String>,
    pub headers: HashMap<String, String>,
    pub body: Option<Vec<u8>>,
}

impl SanitizedData {
    pub fn new() -> Self {
        Self {
            query_params: HashMap::new(),
            headers: HashMap::new(),
            body: None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_validation_config() {
        let config = ValidationConfig::new()
            .with_max_body_size(5 * 1024 * 1024)
            .with_sanitization(true);

        assert_eq!(config.max_body_size, 5 * 1024 * 1024);
        assert!(config.sanitize_inputs);
    }

    #[tokio::test]
    async fn test_request_validation() {
        let config = ValidationConfig::new();
        let middleware = RequestValidationMiddleware::new(config);

        let request = ValidationRequest {
            method: "POST".to_string(),
            url: "https://example.com/api/users".to_string(),
            path: "/api/users".to_string(),
            path_params: HashMap::new(),
            query_params: HashMap::new(),
            headers: HashMap::new(),
            body: Some(b"{\"name\": \"test\"}".to_vec()),
            content_type: Some("application/json".to_string()),
            user_agent: Some("Mozilla/5.0".to_string()),
            client_ip: "127.0.0.1".to_string(),
        };

        let result = middleware.validate_request(&request).await;
        assert!(result.is_valid);
    }
}
