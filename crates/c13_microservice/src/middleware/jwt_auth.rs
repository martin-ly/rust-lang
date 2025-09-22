//! JWT认证中间件
//!
//! 提供基于JWT的认证和授权功能

use std::collections::HashMap;
use std::time::{Duration, SystemTime, UNIX_EPOCH};
use tracing::{error, info, warn, instrument};
use serde::{Deserialize, Serialize};
use jsonwebtoken::{decode, encode, Algorithm, DecodingKey, EncodingKey, Header, Validation};

/// JWT配置
#[derive(Debug, Clone)]
pub struct JwtConfig {
    pub secret: String,
    pub algorithm: Algorithm,
    pub expiration_duration: Duration,
    pub issuer: Option<String>,
    pub audience: Option<String>,
    pub leeway: u64, // 允许的时间偏差（秒）
}

impl Default for JwtConfig {
    fn default() -> Self {
        Self {
            secret: "your-secret-key".to_string(),
            algorithm: Algorithm::HS256,
            expiration_duration: Duration::from_secs(3600), // 1小时
            issuer: None,
            audience: None,
            leeway: 60, // 1分钟
        }
    }
}

impl JwtConfig {
    pub fn new(secret: String) -> Self {
        Self {
            secret,
            ..Default::default()
        }
    }

    pub fn with_expiration(mut self, duration: Duration) -> Self {
        self.expiration_duration = duration;
        self
    }

    pub fn with_issuer(mut self, issuer: String) -> Self {
        self.issuer = Some(issuer);
        self
    }

    pub fn with_audience(mut self, audience: String) -> Self {
        self.audience = Some(audience);
        self
    }

    pub fn with_algorithm(mut self, algorithm: Algorithm) -> Self {
        self.algorithm = algorithm;
        self
    }
}

/// JWT声明
#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct Claims {
    pub sub: String,    // 主题（通常是用户ID）
    pub exp: u64,       // 过期时间
    pub iat: u64,       // 签发时间
    pub iss: Option<String>, // 签发者
    pub aud: Option<String>, // 受众
    pub roles: Vec<String>,  // 用户角色
    pub permissions: Vec<String>, // 用户权限
    pub custom: HashMap<String, serde_json::Value>, // 自定义声明
}

impl Claims {
    pub fn new(subject: String) -> Self {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        Self {
            sub: subject,
            exp: now + 3600, // 默认1小时过期
            iat: now,
            iss: None,
            aud: None,
            roles: Vec::new(),
            permissions: Vec::new(),
            custom: HashMap::new(),
        }
    }

    pub fn with_expiration(mut self, exp: u64) -> Self {
        self.exp = exp;
        self
    }

    pub fn with_issuer(mut self, issuer: String) -> Self {
        self.iss = Some(issuer);
        self
    }

    pub fn with_audience(mut self, audience: String) -> Self {
        self.aud = Some(audience);
        self
    }

    pub fn with_roles(mut self, roles: Vec<String>) -> Self {
        self.roles = roles;
        self
    }

    pub fn with_permissions(mut self, permissions: Vec<String>) -> Self {
        self.permissions = permissions;
        self
    }

    pub fn add_custom_claim(mut self, key: String, value: serde_json::Value) -> Self {
        self.custom.insert(key, value);
        self
    }

    /// 检查是否过期
    pub fn is_expired(&self) -> bool {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        self.exp < now
    }

    /// 检查是否有指定角色
    pub fn has_role(&self, role: &str) -> bool {
        self.roles.contains(&role.to_string())
    }

    /// 检查是否有指定权限
    pub fn has_permission(&self, permission: &str) -> bool {
        self.permissions.contains(&permission.to_string())
    }

    /// 检查是否有任意一个角色
    pub fn has_any_role(&self, roles: &[&str]) -> bool {
        roles.iter().any(|&role| self.has_role(role))
    }

    /// 检查是否有任意一个权限
    pub fn has_any_permission(&self, permissions: &[&str]) -> bool {
        permissions.iter().any(|&permission| self.has_permission(permission))
    }
}

/// JWT认证中间件
#[derive(Debug, Clone)]
pub struct JwtAuthMiddleware {
    pub config: JwtConfig,
    pub skip_paths: Vec<String>,
    pub required_roles: Option<Vec<String>>,
    pub required_permissions: Option<Vec<String>>,
    pub validate_expiration: bool,
    pub validate_issuer: bool,
    pub validate_audience: bool,
}

impl Default for JwtAuthMiddleware {
    fn default() -> Self {
        Self::new(JwtConfig::default())
    }
}

impl JwtAuthMiddleware {
    pub fn new(config: JwtConfig) -> Self {
        Self {
            config,
            skip_paths: vec![
                "/health".to_string(),
                "/healthz".to_string(),
                "/metrics".to_string(),
                "/docs".to_string(),
                "/openapi.json".to_string(),
            ],
            required_roles: None,
            required_permissions: None,
            validate_expiration: true,
            validate_issuer: false,
            validate_audience: false,
        }
    }

    pub fn with_skip_paths(mut self, paths: Vec<String>) -> Self {
        self.skip_paths = paths;
        self
    }

    pub fn with_required_roles(mut self, roles: Vec<String>) -> Self {
        self.required_roles = Some(roles);
        self
    }

    pub fn with_required_permissions(mut self, permissions: Vec<String>) -> Self {
        self.required_permissions = Some(permissions);
        self
    }

    pub fn with_expiration_validation(mut self, enabled: bool) -> Self {
        self.validate_expiration = enabled;
        self
    }

    pub fn with_issuer_validation(mut self, enabled: bool) -> Self {
        self.validate_issuer = enabled;
        self
    }

    pub fn with_audience_validation(mut self, enabled: bool) -> Self {
        self.validate_audience = enabled;
        self
    }

    /// 生成JWT令牌
    #[instrument(skip(self))]
    pub fn generate_token(&self, claims: &Claims) -> Result<String, JwtError> {
        let header = Header::new(self.config.algorithm);
        let encoding_key = EncodingKey::from_secret(self.config.secret.as_ref());

        match encode(&header, claims, &encoding_key) {
            Ok(token) => {
                info!("JWT令牌生成成功，用户: {}", claims.sub);
                Ok(token)
            }
            Err(e) => {
                error!("JWT令牌生成失败: {}", e);
                Err(JwtError::TokenGeneration(e.to_string()))
            }
        }
    }

    /// 验证JWT令牌
    #[instrument(skip(self))]
    pub fn validate_token(&self, token: &str) -> Result<Claims, JwtError> {
        let decoding_key = DecodingKey::from_secret(self.config.secret.as_ref());
        
        let mut validation = Validation::new(self.config.algorithm);
        validation.leeway = self.config.leeway;

        if self.validate_expiration {
            validation.validate_exp = true;
        } else {
            validation.validate_exp = false;
        }

        if self.validate_issuer {
            if let Some(ref issuer) = self.config.issuer {
                validation.iss = Some(std::collections::HashSet::from([issuer.clone()]));
            }
        }

        if self.validate_audience {
            if let Some(ref audience) = self.config.audience {
                validation.aud = Some(std::collections::HashSet::from([audience.clone()]));
            }
        }

        match decode::<Claims>(token, &decoding_key, &validation) {
            Ok(token_data) => {
                let claims = token_data.claims;
                
                if self.validate_expiration && claims.is_expired() {
                    return Err(JwtError::TokenExpired);
                }

                info!("JWT令牌验证成功，用户: {}", claims.sub);
                Ok(claims)
            }
            Err(e) => {
                error!("JWT令牌验证失败: {}", e);
                Err(match e.kind() {
                    jsonwebtoken::errors::ErrorKind::ExpiredSignature => JwtError::TokenExpired,
                    jsonwebtoken::errors::ErrorKind::InvalidSignature => JwtError::InvalidSignature,
                    jsonwebtoken::errors::ErrorKind::InvalidToken => JwtError::InvalidToken,
                    _ => JwtError::ValidationError(e.to_string()),
                })
            }
        }
    }

    /// 检查路径是否需要跳过认证
    pub fn should_skip_path(&self, path: &str) -> bool {
        self.skip_paths.iter().any(|skip_path| path.starts_with(skip_path))
    }

    /// 验证用户角色
    pub fn validate_roles(&self, claims: &Claims) -> Result<(), JwtError> {
        if let Some(ref required_roles) = self.required_roles {
            if !claims.has_any_role(required_roles.iter().map(|s| s.as_str()).collect::<Vec<_>>().as_slice()) {
                warn!("用户 {} 缺少必需角色: {:?}", claims.sub, required_roles);
                return Err(JwtError::InsufficientRoles);
            }
        }
        Ok(())
    }

    /// 验证用户权限
    pub fn validate_permissions(&self, claims: &Claims) -> Result<(), JwtError> {
        if let Some(ref required_permissions) = self.required_permissions {
            if !claims.has_any_permission(required_permissions.iter().map(|s| s.as_str()).collect::<Vec<_>>().as_slice()) {
                warn!("用户 {} 缺少必需权限: {:?}", claims.sub, required_permissions);
                return Err(JwtError::InsufficientPermissions);
            }
        }
        Ok(())
    }

    /// 处理认证请求
    pub async fn authenticate_request(&self, path: &str, token: Option<&str>) -> AuthResult {
        // 检查是否需要跳过认证
        if self.should_skip_path(path) {
            return AuthResult::Skipped;
        }

        // 检查是否有令牌
        let token = match token {
            Some(t) => t,
            None => {
                warn!("请求路径 {} 需要认证但未提供令牌", path);
                return AuthResult::Unauthorized("缺少认证令牌".to_string());
            }
        };

        // 验证令牌
        let claims = match self.validate_token(token) {
            Ok(claims) => claims,
            Err(e) => {
                return AuthResult::Unauthorized(format!("令牌验证失败: {}", e));
            }
        };

        // 验证角色
        if let Err(e) = self.validate_roles(&claims) {
            return AuthResult::Forbidden(format!("角色验证失败: {}", e));
        }

        // 验证权限
        if let Err(e) = self.validate_permissions(&claims) {
            return AuthResult::Forbidden(format!("权限验证失败: {}", e));
        }

        AuthResult::Authenticated(claims)
    }
}

/// JWT错误类型
#[derive(Debug, thiserror::Error)]
pub enum JwtError {
    #[error("令牌生成失败: {0}")]
    TokenGeneration(String),
    
    #[error("令牌验证失败: {0}")]
    ValidationError(String),
    
    #[error("令牌已过期")]
    TokenExpired,
    
    #[error("无效的签名")]
    InvalidSignature,
    
    #[error("无效的令牌")]
    InvalidToken,
    
    #[error("角色不足")]
    InsufficientRoles,
    
    #[error("权限不足")]
    InsufficientPermissions,
}

/// 认证结果
#[derive(Debug, Clone)]
pub enum AuthResult {
    Authenticated(Claims),
    Unauthorized(String),
    Forbidden(String),
    Skipped,
}

impl AuthResult {
    pub fn is_authenticated(&self) -> bool {
        matches!(self, AuthResult::Authenticated(_))
    }

    pub fn is_authorized(&self) -> bool {
        matches!(self, AuthResult::Authenticated(_) | AuthResult::Skipped)
    }

    pub fn get_claims(&self) -> Option<&Claims> {
        match self {
            AuthResult::Authenticated(claims) => Some(claims),
            _ => None,
        }
    }

    pub fn get_error_message(&self) -> Option<&str> {
        match self {
            AuthResult::Unauthorized(msg) | AuthResult::Forbidden(msg) => Some(msg),
            _ => None,
        }
    }
}

/// JWT用户信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct JwtUser {
    pub id: String,
    pub username: String,
    pub email: Option<String>,
    pub roles: Vec<String>,
    pub permissions: Vec<String>,
    pub metadata: HashMap<String, serde_json::Value>,
}

impl From<Claims> for JwtUser {
    fn from(claims: Claims) -> Self {
        Self {
            id: claims.sub.clone(),
            username: claims.sub,
            email: claims.custom.get("email").and_then(|v| v.as_str()).map(|s| s.to_string()),
            roles: claims.roles,
            permissions: claims.permissions,
            metadata: claims.custom,
        }
    }
}

/// JWT认证管理器
#[derive(Debug, Clone)]
pub struct JwtAuthManager {
    pub auth_middleware: JwtAuthMiddleware,
    pub token_blacklist: std::collections::HashSet<String>,
}

impl JwtAuthManager {
    pub fn new(config: JwtConfig) -> Self {
        Self {
            auth_middleware: JwtAuthMiddleware::new(config),
            token_blacklist: std::collections::HashSet::new(),
        }
    }

    /// 生成用户令牌
    pub fn generate_user_token(&self, user: &JwtUser) -> Result<String, JwtError> {
        let claims = Claims::new(user.id.clone())
            .with_roles(user.roles.clone())
            .with_permissions(user.permissions.clone())
            .add_custom_claim("username".to_string(), serde_json::Value::String(user.username.clone()));

        let claims = if let Some(ref email) = user.email {
            claims.add_custom_claim("email".to_string(), serde_json::Value::String(email.clone()))
        } else {
            claims
        };

        let claims = user.metadata.iter().fold(claims, |acc, (key, value)| {
            acc.add_custom_claim(key.clone(), value.clone())
        });

        self.auth_middleware.generate_token(&claims)
    }

    /// 撤销令牌
    pub fn revoke_token(&mut self, token: &str) {
        self.token_blacklist.insert(token.to_string());
        info!("令牌已撤销");
    }

    /// 检查令牌是否被撤销
    pub fn is_token_revoked(&self, token: &str) -> bool {
        self.token_blacklist.contains(token)
    }

    /// 验证请求
    pub async fn authenticate_request(&self, path: &str, token: Option<&str>) -> AuthResult {
        // 检查令牌是否被撤销
        if let Some(t) = token {
            if self.is_token_revoked(t) {
                return AuthResult::Unauthorized("令牌已被撤销".to_string());
            }
        }

        self.auth_middleware.authenticate_request(path, token).await
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_jwt_config() {
        let config = JwtConfig::new("test-secret".to_string())
            .with_expiration(Duration::from_secs(7200))
            .with_issuer("test-app".to_string());

        assert_eq!(config.secret, "test-secret");
        assert_eq!(config.expiration_duration.as_secs(), 7200);
        assert_eq!(config.issuer, Some("test-app".to_string()));
    }

    #[test]
    fn test_claims() {
        let claims = Claims::new("user123".to_string())
            .with_roles(vec!["admin".to_string(), "user".to_string()])
            .with_permissions(vec!["read".to_string(), "write".to_string()]);

        assert_eq!(claims.sub, "user123");
        assert!(claims.has_role("admin"));
        assert!(claims.has_permission("read"));
        assert!(claims.has_any_role(&["admin", "guest"]));
        assert!(!claims.has_any_role(&["guest", "visitor"]));
    }

    #[tokio::test]
    async fn test_jwt_auth_middleware() {
        let config = JwtConfig::new("test-secret".to_string());
        let middleware = JwtAuthMiddleware::new(config)
            .with_required_roles(vec!["admin".to_string()])
            .with_skip_paths(vec!["/public".to_string()]);

        // 测试跳过路径
        assert!(middleware.should_skip_path("/public/data"));
        assert!(!middleware.should_skip_path("/private/data"));

        // 测试令牌生成和验证
        let claims = Claims::new("test-user".to_string())
            .with_roles(vec!["admin".to_string()]);

        let token = middleware.generate_token(&claims).unwrap();
        let validated_claims = middleware.validate_token(&token).unwrap();

        assert_eq!(validated_claims.sub, "test-user");
        assert!(validated_claims.has_role("admin"));
    }

    #[tokio::test]
    async fn test_jwt_auth_manager() {
        let config = JwtConfig::new("test-secret".to_string());
        let mut manager = JwtAuthManager::new(config);

        let user = JwtUser {
            id: "user123".to_string(),
            username: "testuser".to_string(),
            email: Some("test@example.com".to_string()),
            roles: vec!["admin".to_string()],
            permissions: vec!["read".to_string()],
            metadata: HashMap::new(),
        };

        let token = manager.generate_user_token(&user).unwrap();
        
        // 测试令牌撤销
        manager.revoke_token(&token);
        assert!(manager.is_token_revoked(&token));

        // 测试认证请求
        let result = manager.authenticate_request("/api/data", Some(&token)).await;
        assert!(!result.is_authorized());
    }
}
