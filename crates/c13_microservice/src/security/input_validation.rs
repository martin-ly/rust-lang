//! 输入验证模块
//!
//! 提供输入验证、清理和安全检查功能

use std::collections::HashMap;
use regex::Regex;
// serde imports removed as they are not used
use thiserror::Error;

/// 输入验证器
#[derive(Debug)]
pub struct InputValidator {
    rules: Vec<ValidationRule>,
    sanitizers: Vec<Sanitizer>,
    xss_protection: XssProtection,
    sql_injection_protection: SqlInjectionProtection,
}

impl InputValidator {
    /// 创建新的输入验证器
    pub fn new() -> Self {
        let mut validator = Self {
            rules: Vec::new(),
            sanitizers: Vec::new(),
            xss_protection: XssProtection::new(),
            sql_injection_protection: SqlInjectionProtection::new(),
        };
        
        validator.add_default_rules();
        validator.add_default_sanitizers();
        validator
    }

    /// 添加默认验证规则
    fn add_default_rules(&mut self) {
        // 邮箱验证
        self.add_rule(ValidationRule::new(
            "email".to_string(),
            r"^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$".to_string(),
            ValidationType::Email,
        ));

        // 用户名验证
        self.add_rule(ValidationRule::new(
            "username".to_string(),
            r"^[a-zA-Z0-9_-]{3,20}$".to_string(),
            ValidationType::Username,
        ));

        // 密码验证
        self.add_rule(ValidationRule::new(
            "password".to_string(),
            r"^(?=.*[a-z])(?=.*[A-Z])(?=.*\d)(?=.*[@$!%*?&])[A-Za-z\d@$!%*?&]{8,}$".to_string(),
            ValidationType::Password,
        ));

        // URL验证
        self.add_rule(ValidationRule::new(
            "url".to_string(),
            r"^https?://[^\s/$.?#].[^\s]*$".to_string(),
            ValidationType::Url,
        ));

        // 手机号验证
        self.add_rule(ValidationRule::new(
            "phone".to_string(),
            r"^\+?[1-9]\d{1,14}$".to_string(),
            ValidationType::Phone,
        ));
    }

    /// 添加默认清理器
    fn add_default_sanitizers(&mut self) {
        // HTML标签清理
        self.add_sanitizer(Sanitizer::new(
            "html_tags".to_string(),
            r"<[^>]*>".to_string(),
            "".to_string(),
            SanitizationType::Remove,
        ));

        // 特殊字符清理
        self.add_sanitizer(Sanitizer::new(
            "special_chars".to_string(),
            r#"[<>"'&]"#.to_string(),
            "".to_string(),
            SanitizationType::Remove,
        ));

        // 多余空格清理
        self.add_sanitizer(Sanitizer::new(
            "whitespace".to_string(),
            r"\s+".to_string(),
            " ".to_string(),
            SanitizationType::Replace,
        ));
    }

    /// 添加验证规则
    pub fn add_rule(&mut self, rule: ValidationRule) {
        self.rules.push(rule);
    }

    /// 添加清理器
    pub fn add_sanitizer(&mut self, sanitizer: Sanitizer) {
        self.sanitizers.push(sanitizer);
    }

    /// 验证输入数据
    pub fn validate(&self, input: &ValidationInput) -> Result<ValidationResult, InputValidationError> {
        let mut result = ValidationResult::new();

        // 验证每个字段
        for (field_name, value) in &input.fields {
            match self.validate_field(field_name, value) {
                Ok(field_result) => {
                    result.add_field_result(field_name.clone(), field_result);
                }
                Err(e) => {
                    result.add_error(field_name.clone(), e);
                }
            }
        }

        // 验证查询参数
        for (param_name, value) in &input.query_params {
            match self.validate_query_param(param_name, value) {
                Ok(param_result) => {
                    result.add_query_param_result(param_name.clone(), param_result);
                }
                Err(e) => {
                    result.add_error(format!("query.{}", param_name), e);
                }
            }
        }

        // 验证路径参数
        for (param_name, value) in &input.path_params {
            match self.validate_path_param(param_name, value) {
                Ok(param_result) => {
                    result.add_path_param_result(param_name.clone(), param_result);
                }
                Err(e) => {
                    result.add_error(format!("path.{}", param_name), e);
                }
            }
        }

        // 验证请求体
        if let Some(body) = &input.body {
            match self.validate_body(body) {
                Ok(body_result) => {
                    result.set_body_result(body_result);
                }
                Err(e) => {
                    result.add_error("body".to_string(), e);
                }
            }
        }

        // XSS检查
        if let Err(e) = self.xss_protection.check(&input) {
            result.add_error("xss".to_string(), e);
        }

        // SQL注入检查
        if let Err(e) = self.sql_injection_protection.check(&input) {
            result.add_error("sql_injection".to_string(), e);
        }

        if result.has_errors() {
            Err(InputValidationError::ValidationFailed(result))
        } else {
            Ok(result)
        }
    }

    /// 验证字段
    fn validate_field(&self, field_name: &str, value: &str) -> Result<FieldValidationResult, InputValidationError> {
        let mut sanitized_value = value.to_string();

        // 应用清理器
        for sanitizer in &self.sanitizers {
            sanitized_value = sanitizer.sanitize(&sanitized_value);
        }

        // 应用验证规则
        for rule in &self.rules {
            if rule.matches_field(field_name) {
                if !rule.validate(&sanitized_value) {
                    return Err(InputValidationError::RuleViolation(
                        rule.name.clone(),
                        format!("字段 {} 不满足规则 {}", field_name, rule.name)
                    ));
                }
            }
        }

        Ok(FieldValidationResult {
            field_name: field_name.to_string(),
            original_value: value.to_string(),
            sanitized_value,
            is_valid: true,
            errors: Vec::new(),
        })
    }

    /// 验证查询参数
    fn validate_query_param(&self, param_name: &str, value: &str) -> Result<ParamValidationResult, InputValidationError> {
        let mut sanitized_value = value.to_string();

        // 应用清理器
        for sanitizer in &self.sanitizers {
            sanitized_value = sanitizer.sanitize(&sanitized_value);
        }

        // 检查长度限制
        if sanitized_value.len() > 1000 {
            return Err(InputValidationError::LengthExceeded(
                format!("查询参数 {} 长度超过限制", param_name)
            ));
        }

        Ok(ParamValidationResult {
            param_name: param_name.to_string(),
            original_value: value.to_string(),
            sanitized_value,
            is_valid: true,
        })
    }

    /// 验证路径参数
    fn validate_path_param(&self, param_name: &str, value: &str) -> Result<ParamValidationResult, InputValidationError> {
        let mut sanitized_value = value.to_string();

        // 应用清理器
        for sanitizer in &self.sanitizers {
            sanitized_value = sanitizer.sanitize(&sanitized_value);
        }

        // 检查路径遍历
        if sanitized_value.contains("..") || sanitized_value.contains("\\") {
            return Err(InputValidationError::PathTraversal(
                format!("路径参数 {} 包含路径遍历字符", param_name)
            ));
        }

        Ok(ParamValidationResult {
            param_name: param_name.to_string(),
            original_value: value.to_string(),
            sanitized_value,
            is_valid: true,
        })
    }

    /// 验证请求体
    fn validate_body(&self, body: &str) -> Result<BodyValidationResult, InputValidationError> {
        // 检查大小限制
        if body.len() > 10 * 1024 * 1024 { // 10MB
            return Err(InputValidationError::BodyTooLarge(
                "请求体大小超过10MB限制".to_string()
            ));
        }

        let mut sanitized_body = body.to_string();

        // 应用清理器
        for sanitizer in &self.sanitizers {
            sanitized_body = sanitizer.sanitize(&sanitized_body);
        }

        Ok(BodyValidationResult {
            original_size: body.len(),
            sanitized_size: sanitized_body.len(),
            sanitized_body,
            is_valid: true,
        })
    }

    /// 获取总检查次数
    pub fn get_total_checks(&self) -> usize {
        // 这里简化处理，实际应用中应该维护计数器
        0
    }
}

/// 验证规则
#[derive(Debug, Clone)]
pub struct ValidationRule {
    pub name: String,
    pub pattern: String,
    pub validation_type: ValidationType,
    pub regex: Option<Regex>,
}

impl ValidationRule {
    /// 创建新的验证规则
    pub fn new(name: String, pattern: String, validation_type: ValidationType) -> Self {
        let regex = Regex::new(&pattern).ok();
        Self {
            name,
            pattern,
            validation_type,
            regex,
        }
    }

    /// 检查是否匹配字段名
    pub fn matches_field(&self, field_name: &str) -> bool {
        match &self.validation_type {
            ValidationType::Email => field_name.to_lowercase().contains("email"),
            ValidationType::Username => field_name.to_lowercase().contains("username") || field_name.to_lowercase().contains("user"),
            ValidationType::Password => field_name.to_lowercase().contains("password") || field_name.to_lowercase().contains("pass"),
            ValidationType::Url => field_name.to_lowercase().contains("url") || field_name.to_lowercase().contains("link"),
            ValidationType::Phone => field_name.to_lowercase().contains("phone") || field_name.to_lowercase().contains("mobile"),
            ValidationType::Custom => true,
        }
    }

    /// 验证值
    pub fn validate(&self, value: &str) -> bool {
        if let Some(ref regex) = self.regex {
            regex.is_match(value)
        } else {
            true
        }
    }
}

/// 验证类型
#[derive(Debug, Clone)]
pub enum ValidationType {
    Email,
    Username,
    Password,
    Url,
    Phone,
    Custom,
}

/// 清理器
#[derive(Debug, Clone)]
pub struct Sanitizer {
    pub name: String,
    pub pattern: String,
    pub replacement: String,
    pub sanitization_type: SanitizationType,
    pub regex: Option<Regex>,
}

impl Sanitizer {
    /// 创建新的清理器
    pub fn new(name: String, pattern: String, replacement: String, sanitization_type: SanitizationType) -> Self {
        let regex = Regex::new(&pattern).ok();
        Self {
            name,
            pattern,
            replacement,
            sanitization_type,
            regex,
        }
    }

    /// 清理值
    pub fn sanitize(&self, value: &str) -> String {
        if let Some(ref regex) = self.regex {
            match self.sanitization_type {
                SanitizationType::Remove => regex.replace_all(value, "").to_string(),
                SanitizationType::Replace => regex.replace_all(value, &self.replacement).to_string(),
                SanitizationType::Escape => {
                    regex.replace_all(value, |caps: &regex::Captures| {
                        format!("&#x{:x};", caps[0].chars().next().unwrap() as u32)
                    }).to_string()
                }
            }
        } else {
            value.to_string()
        }
    }
}

/// 清理类型
#[derive(Debug, Clone)]
pub enum SanitizationType {
    Remove,
    Replace,
    Escape,
}

/// XSS保护
#[derive(Debug)]
pub struct XssProtection {
    patterns: Vec<Regex>,
}

impl XssProtection {
    /// 创建新的XSS保护
    pub fn new() -> Self {
        let mut protection = Self {
            patterns: Vec::new(),
        };
        protection.add_default_patterns();
        protection
    }

    /// 添加默认XSS模式
    fn add_default_patterns(&mut self) {
        let patterns = vec![
            r"(?i)<script[^>]*>.*?</script>",
            r"(?i)javascript:",
            r"(?i)on\w+\s*=",
            r"(?i)<iframe[^>]*>",
            r"(?i)<object[^>]*>",
            r"(?i)<embed[^>]*>",
            r"(?i)<link[^>]*>",
            r"(?i)<meta[^>]*>",
        ];

        for pattern in patterns {
            if let Ok(regex) = Regex::new(pattern) {
                self.patterns.push(regex);
            }
        }
    }

    /// 检查XSS
    pub fn check(&self, input: &ValidationInput) -> Result<(), InputValidationError> {
        let content = format!("{}", input);
        
        for pattern in &self.patterns {
            if pattern.is_match(&content) {
                return Err(InputValidationError::XssDetected(
                    "检测到潜在的XSS攻击".to_string()
                ));
            }
        }

        Ok(())
    }
}

/// SQL注入保护
#[derive(Debug)]
pub struct SqlInjectionProtection {
    patterns: Vec<Regex>,
}

impl SqlInjectionProtection {
    /// 创建新的SQL注入保护
    pub fn new() -> Self {
        let mut protection = Self {
            patterns: Vec::new(),
        };
        protection.add_default_patterns();
        protection
    }

    /// 添加默认SQL注入模式
    fn add_default_patterns(&mut self) {
        let patterns = vec![
            r"(?i)(union|select|insert|update|delete|drop|create|alter|exec|execute)\s+",
            r"(?i)(or|and)\s+1\s*=\s*1",
            r"(?i)(or|and)\s+true",
            r"(?i)--",
            r"(?i)/\*.*?\*/",
            r"(?i)'\s*(or|and)\s*'",
            r"(?i)\x00",
        ];

        for pattern in patterns {
            if let Ok(regex) = Regex::new(pattern) {
                self.patterns.push(regex);
            }
        }
    }

    /// 检查SQL注入
    pub fn check(&self, input: &ValidationInput) -> Result<(), InputValidationError> {
        let content = format!("{}", input);
        
        for pattern in &self.patterns {
            if pattern.is_match(&content) {
                return Err(InputValidationError::SqlInjectionDetected(
                    "检测到潜在的SQL注入攻击".to_string()
                ));
            }
        }

        Ok(())
    }
}

/// 验证输入
#[derive(Debug, Clone)]
pub struct ValidationInput {
    pub fields: HashMap<String, String>,
    pub query_params: HashMap<String, String>,
    pub path_params: HashMap<String, String>,
    pub headers: HashMap<String, String>,
    pub body: Option<String>,
}

impl std::fmt::Display for ValidationInput {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut content = String::new();
        
        for (_, value) in &self.fields {
            content.push_str(value);
            content.push(' ');
        }
        
        for (_, value) in &self.query_params {
            content.push_str(value);
            content.push(' ');
        }
        
        for (_, value) in &self.path_params {
            content.push_str(value);
            content.push(' ');
        }
        
        for (_, value) in &self.headers {
            content.push_str(value);
            content.push(' ');
        }
        
        if let Some(ref body) = self.body {
            content.push_str(body);
        }
        
        write!(f, "{}", content)
    }
}

/// 验证结果
#[derive(Debug, Clone)]
pub struct ValidationResult {
    pub field_results: HashMap<String, FieldValidationResult>,
    pub query_param_results: HashMap<String, ParamValidationResult>,
    pub path_param_results: HashMap<String, ParamValidationResult>,
    pub body_result: Option<BodyValidationResult>,
    pub errors: HashMap<String, InputValidationError>,
}

impl ValidationResult {
    /// 创建新的验证结果
    pub fn new() -> Self {
        Self {
            field_results: HashMap::new(),
            query_param_results: HashMap::new(),
            path_param_results: HashMap::new(),
            body_result: None,
            errors: HashMap::new(),
        }
    }

    /// 添加字段结果
    pub fn add_field_result(&mut self, field_name: String, result: FieldValidationResult) {
        self.field_results.insert(field_name, result);
    }

    /// 添加查询参数结果
    pub fn add_query_param_result(&mut self, param_name: String, result: ParamValidationResult) {
        self.query_param_results.insert(param_name, result);
    }

    /// 添加路径参数结果
    pub fn add_path_param_result(&mut self, param_name: String, result: ParamValidationResult) {
        self.path_param_results.insert(param_name, result);
    }

    /// 设置请求体结果
    pub fn set_body_result(&mut self, result: BodyValidationResult) {
        self.body_result = Some(result);
    }

    /// 添加错误
    pub fn add_error(&mut self, key: String, error: InputValidationError) {
        self.errors.insert(key, error);
    }

    /// 检查是否有错误
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }
}

/// 字段验证结果
#[derive(Debug, Clone)]
pub struct FieldValidationResult {
    pub field_name: String,
    pub original_value: String,
    pub sanitized_value: String,
    pub is_valid: bool,
    pub errors: Vec<String>,
}

/// 参数验证结果
#[derive(Debug, Clone)]
pub struct ParamValidationResult {
    pub param_name: String,
    pub original_value: String,
    pub sanitized_value: String,
    pub is_valid: bool,
}

/// 请求体验证结果
#[derive(Debug, Clone)]
pub struct BodyValidationResult {
    pub original_size: usize,
    pub sanitized_size: usize,
    pub sanitized_body: String,
    pub is_valid: bool,
}

/// 输入验证错误
#[derive(Error, Debug, Clone)]
pub enum InputValidationError {
    #[error("验证失败: {0:?}")]
    ValidationFailed(ValidationResult),
    #[error("规则违反: {0} - {1}")]
    RuleViolation(String, String),
    #[error("长度超限: {0}")]
    LengthExceeded(String),
    #[error("路径遍历: {0}")]
    PathTraversal(String),
    #[error("请求体过大: {0}")]
    BodyTooLarge(String),
    #[error("检测到XSS: {0}")]
    XssDetected(String),
    #[error("检测到SQL注入: {0}")]
    SqlInjectionDetected(String),
    #[error("正则表达式错误: {0}")]
    RegexError(String),
}

/// 输入验证结果类型别名
pub type InputValidationResult<T> = Result<T, InputValidationError>;
