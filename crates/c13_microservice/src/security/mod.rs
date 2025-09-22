//! 安全模块
//!
//! 提供OAuth2认证、HTTPS/TLS支持和输入验证功能

pub mod oauth2;
pub mod tls;
pub mod input_validation;
pub mod cors;
pub mod rate_limiting;

pub use oauth2::{
    OAuth2Config, OAuth2Provider, OAuth2Client, OAuth2Token, OAuth2User,
    OAuth2Error, OAuth2Manager,
};
pub use tls::{
    TlsConfig, TlsManager, CertificateInfo, TlsError, TlsVersion,
};
pub use input_validation::{
    InputValidator, ValidationRule, InputValidationError, ValidationInput,
    Sanitizer, XssProtection, SqlInjectionProtection,
};
pub use cors::{
    CorsConfig, CorsManager, CorsError,
};
pub use rate_limiting::{
    RateLimiter, RateLimitConfig, RateLimit, RateLimitError, RateLimitResult,
};

use std::collections::HashMap;
// use serde::{Deserialize, Serialize}; // 暂时未使用
use thiserror::Error;

/// 安全管理器
#[derive(Debug)]
pub struct SecurityManager {
    pub oauth2: Option<OAuth2Manager>,
    pub tls: Option<TlsManager>,
    pub cors: CorsManager,
    pub rate_limiter: RateLimiter,
    pub input_validator: InputValidator,
}

impl SecurityManager {
    /// 创建新的安全管理器
    pub fn new(config: SecurityConfig) -> Self {
        Self {
            oauth2: config.oauth2.map(OAuth2Manager::new),
            tls: config.tls.map(TlsManager::new),
            cors: CorsManager::new(config.cors),
            rate_limiter: RateLimiter::new(config.rate_limit),
            input_validator: InputValidator::new(),
        }
    }

    /// 验证请求的安全性
    pub async fn validate_request(&self, request: &SecurityRequest) -> SecurityResult {
        let mut results = Vec::new();

        // 输入验证
        let validation_input = ValidationInput {
            fields: request.input.query_params.clone(),
            query_params: request.input.query_params.clone(),
            path_params: request.input.path_params.clone(),
            headers: request.input.headers.clone(),
            body: request.input.body.clone(),
        };
        if let Err(e) = self.input_validator.validate(&validation_input) {
            results.push(SecurityCheckResult::InputValidationFailed(e));
        }

        // 速率限制
        match self.rate_limiter.check_limit(&request.client_id, &request.endpoint).await {
            Ok(rate_limit_result) => {
                if rate_limit_result.exceeded {
                    results.push(SecurityCheckResult::RateLimitExceeded(rate_limit_result));
                }
            }
            Err(e) => results.push(SecurityCheckResult::RateLimitError(e)),
        }

        // CORS检查
        if let Err(e) = self.cors.validate_request(&request.origin, &request.method, &request.path) {
            results.push(SecurityCheckResult::CorsViolation(e));
        }

        // TLS检查
        if let Some(tls_manager) = &self.tls {
            if !request.is_https && tls_manager.is_required() {
                results.push(SecurityCheckResult::TlsRequired);
            }
        }

        if results.is_empty() {
            SecurityResult::Allowed
        } else {
            SecurityResult::Blocked(results)
        }
    }

    /// 验证OAuth2令牌
    pub async fn validate_oauth2_token(&mut self, token: &str) -> Result<OAuth2User, SecurityError> {
        if let Some(oauth2_manager) = &mut self.oauth2 {
            oauth2_manager.validate_token(token).await.map_err(SecurityError::from)
        } else {
            Err(SecurityError::OAuth2NotConfigured)
        }
    }

    /// 获取安全统计信息
    pub async fn get_security_stats(&self) -> SecurityStats {
        SecurityStats {
            oauth2_enabled: self.oauth2.is_some(),
            tls_enabled: self.tls.is_some(),
            cors_enabled: true,
            rate_limiting_enabled: true,
            input_validation_enabled: true,
            total_requests_checked: self.input_validator.get_total_checks(),
            blocked_requests: self.rate_limiter.get_blocked_count().await,
        }
    }
}

/// 安全配置
#[derive(Debug, Clone)]
pub struct SecurityConfig {
    pub oauth2: Option<OAuth2Config>,
    pub tls: Option<TlsConfig>,
    pub cors: CorsConfig,
    pub rate_limit: RateLimitConfig,
}

impl Default for SecurityConfig {
    fn default() -> Self {
        Self {
            oauth2: None,
            tls: None,
            cors: CorsConfig::default(),
            rate_limit: RateLimitConfig::default(),
        }
    }
}

/// 安全请求
#[derive(Debug, Clone)]
pub struct SecurityRequest {
    pub client_id: String,
    pub endpoint: String,
    pub method: String,
    pub path: String,
    pub origin: Option<String>,
    pub input: InputData,
    pub is_https: bool,
}

/// 输入数据
#[derive(Debug, Clone)]
pub struct InputData {
    pub query_params: HashMap<String, String>,
    pub path_params: HashMap<String, String>,
    pub headers: HashMap<String, String>,
    pub body: Option<String>,
}

/// 安全验证结果
#[derive(Debug, Clone)]
pub enum SecurityResult {
    Allowed,
    Blocked(Vec<SecurityCheckResult>),
}

/// 安全检查结果
#[derive(Debug, Clone)]
pub enum SecurityCheckResult {
    InputValidationFailed(InputValidationError),
    RateLimitExceeded(RateLimitResult),
    RateLimitError(RateLimitError),
    CorsViolation(CorsError),
    TlsRequired,
    OAuth2Invalid,
}

/// 安全统计信息
#[derive(Debug, Clone)]
pub struct SecurityStats {
    pub oauth2_enabled: bool,
    pub tls_enabled: bool,
    pub cors_enabled: bool,
    pub rate_limiting_enabled: bool,
    pub input_validation_enabled: bool,
    pub total_requests_checked: usize,
    pub blocked_requests: usize,
}

/// 安全错误
#[derive(Error, Debug)]
pub enum SecurityError {
    #[error("OAuth2未配置")]
    OAuth2NotConfigured,
    #[error("TLS错误: {0}")]
    TlsError(#[from] TlsError),
    #[error("CORS错误: {0}")]
    CorsError(#[from] CorsError),
    #[error("速率限制错误: {0}")]
    RateLimitError(#[from] RateLimitError),
    #[error("输入验证错误: {0}")]
    InputValidationError(#[from] InputValidationError),
    #[error("OAuth2错误: {0}")]
    OAuth2Error(#[from] OAuth2Error),
}

/// 安全结果类型别名
pub type SecurityResultType<T> = Result<T, SecurityError>;
