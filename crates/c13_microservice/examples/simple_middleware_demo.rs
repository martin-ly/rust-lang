//! 简单中间件演示
//!
//! 演示JWT认证、请求验证、缓存等中间件的基本功能

use std::collections::HashMap;
use tracing::{info, warn, error};

use c13_microservice::{
    middleware::{
        JwtAuthMiddleware, JwtConfig, JwtAuthManager, JwtUser,
        RequestValidationMiddleware, ValidationConfig, ValidationRequest,
        HttpCacheMiddleware, CacheConfig, HttpCacheRequest, HttpCacheResponse,
    },
    error::Result,
};

/// 演示服务器配置
#[derive(Debug, Clone)]
pub struct DemoServerConfig {
    pub jwt_config: JwtConfig,
    pub validation_config: ValidationConfig,
    pub cache_config: CacheConfig,
}

impl Default for DemoServerConfig {
    fn default() -> Self {
        Self {
            jwt_config: JwtConfig::default(),
            validation_config: ValidationConfig::new(),
            cache_config: CacheConfig::default(),
        }
    }
}

/// 演示服务器
#[derive(Debug)]
pub struct DemoServer {
    _config: DemoServerConfig,
    jwt_manager: JwtAuthManager,
    jwt_middleware: JwtAuthMiddleware,
    validation_middleware: RequestValidationMiddleware,
    cache_middleware: HttpCacheMiddleware,
}

impl DemoServer {
    pub fn new(config: DemoServerConfig) -> Self {
        let jwt_manager = JwtAuthManager::new(config.jwt_config.clone());
        let jwt_middleware = jwt_manager.auth_middleware.clone();
        let validation_middleware = RequestValidationMiddleware::new(config.validation_config.clone());
        let cache_middleware = HttpCacheMiddleware::new(config.cache_config.clone());

        Self {
            _config: config,
            jwt_manager,
            jwt_middleware,
            validation_middleware,
            cache_middleware,
        }
    }

    /// 启动演示服务器
    pub async fn start(&self) -> Result<()> {
        info!("启动简单中间件演示服务器");

        // 演示JWT认证
        self.demonstrate_jwt_auth().await?;

        // 演示请求验证
        self.demonstrate_request_validation().await?;

        // 演示缓存功能
        self.demonstrate_caching().await?;

        info!("简单中间件演示完成");
        Ok(())
    }

    /// 演示JWT认证功能
    async fn demonstrate_jwt_auth(&self) -> Result<()> {
        info!("=== JWT认证演示 ===");

        // 创建用户
        let user = JwtUser {
            id: "user123".to_string(),
            username: "john_doe".to_string(),
            email: Some("john@example.com".to_string()),
            roles: vec!["admin".to_string(), "user".to_string()],
            permissions: vec!["read".to_string(), "write".to_string()],
            metadata: HashMap::new(),
        };

        // 生成JWT令牌
        let token_result = self.jwt_manager.generate_user_token(&user);
        match token_result {
            Ok(token) => {
                info!("生成的JWT令牌: {}", token);

                // 验证JWT令牌
                let auth_result = self.jwt_middleware.authenticate_request("/api/protected", Some(&token)).await;
                match auth_result {
                    c13_microservice::middleware::AuthResult::Authenticated(claims) => {
                        info!("JWT验证成功:");
                        info!("  用户ID: {}", claims.sub);
                        info!("  角色: {:?}", claims.roles);
                        info!("  权限: {:?}", claims.permissions);
                        info!("  是否过期: {}", claims.is_expired());
                        info!("  是否有admin角色: {}", claims.has_role("admin"));
                        info!("  是否有write权限: {}", claims.has_permission("write"));
                    }
                    c13_microservice::middleware::AuthResult::Unauthorized(msg) => {
                        error!("JWT验证失败: {}", msg);
                    }
                    c13_microservice::middleware::AuthResult::Forbidden(msg) => {
                        error!("JWT权限不足: {}", msg);
                    }
                    c13_microservice::middleware::AuthResult::Skipped => {
                        info!("JWT认证被跳过");
                    }
                }
            }
            Err(e) => {
                error!("生成JWT令牌失败: {}", e);
                return Err(e.into());
            }
        }

        Ok(())
    }

    /// 演示请求验证功能
    async fn demonstrate_request_validation(&self) -> Result<()> {
        info!("=== 请求验证演示 ===");

        // 创建测试请求
        let valid_request = ValidationRequest {
            method: "POST".to_string(),
            url: "https://api.example.com/users".to_string(),
            path: "/users".to_string(),
            path_params: HashMap::new(),
            query_params: {
                let mut params = HashMap::new();
                params.insert("page".to_string(), "1".to_string());
                params.insert("limit".to_string(), "10".to_string());
                params
            },
            headers: {
                let mut headers = HashMap::new();
                headers.insert("Content-Type".to_string(), "application/json".to_string());
                headers.insert("Authorization".to_string(), "Bearer token123".to_string());
                headers
            },
            body: Some(b"{\"name\": \"John Doe\", \"email\": \"john@example.com\"}".to_vec()),
            content_type: Some("application/json".to_string()),
            user_agent: Some("Mozilla/5.0".to_string()),
            client_ip: "192.168.1.100".to_string(),
        };

        // 验证有效请求
        let result = self.validation_middleware.validate_request(&valid_request).await;
        if result.is_valid {
            info!("有效请求验证通过");
        } else {
            warn!("请求验证失败: {:?}", result.errors);
        }

        // 测试恶意请求
        let mut malicious_request = valid_request.clone();
        malicious_request.query_params.insert("script".to_string(), "<script>alert('xss')</script>".to_string());
        
        let result = self.validation_middleware.validate_request(&malicious_request).await;
        if !result.is_valid {
            info!("恶意请求正确被拦截: {:?}", result.errors);
        } else {
            warn!("恶意请求未被检测到");
        }

        Ok(())
    }

    /// 演示缓存功能
    async fn demonstrate_caching(&self) -> Result<()> {
        info!("=== 缓存功能演示 ===");

        // 创建缓存请求
        let _cache_request = HttpCacheRequest {
            method: "GET".to_string(),
            path: "/api/users".to_string(),
            query_params: {
                let mut params = HashMap::new();
                params.insert("page".to_string(), "1".to_string());
                params.insert("limit".to_string(), "10".to_string());
                params
            },
            headers: HashMap::new(),
        };

        // 创建模拟响应
        let mock_response = HttpCacheResponse {
            status_code: 200,
            headers: {
                let mut headers = HashMap::new();
                headers.insert("Content-Type".to_string(), "application/json".to_string());
                headers.insert("Cache-Control".to_string(), "public, max-age=300".to_string());
                headers
            },
            body: b"{\"users\": [{\"id\": 1, \"name\": \"John Doe\"}]}".to_vec(),
            created_at: std::time::Instant::now(),
        };

        // 检查是否应该缓存
        if self.cache_middleware.should_cache_response(&mock_response) {
            info!("响应应该被缓存");
        } else {
            info!("响应不应该被缓存");
        }

        // 缓存功能演示完成
        info!("缓存功能演示完成");

        Ok(())
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::INFO)
        .init();

    info!("简单中间件演示开始");

    // 创建并启动演示服务器
    let config = DemoServerConfig::default();
    let server = DemoServer::new(config);
    
    match server.start().await {
        Ok(_) => {
            info!("演示成功完成");
        }
        Err(e) => {
            error!("演示失败: {}", e);
            return Err(e);
        }
    }

    Ok(())
}
