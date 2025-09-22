//! 综合中间件演示
//!
//! 演示JWT认证、请求验证、缓存等中间件的完整功能

#[allow(unused_imports)]
use std::collections::HashMap;
use std::time::{Duration, Instant};
use tokio::time::sleep;
use tracing::{info, warn, error};
use tower::ServiceBuilder;
use tower_http::cors::CorsLayer;
use tower_http::trace::TraceLayer;

use c13_microservice::{
    middleware::{
        JwtAuthMiddleware, JwtConfig, JwtAuthManager, Claims, JwtUser,
        RequestValidationMiddleware, ValidationConfig, ValidationRequest,
        HttpCacheMiddleware, CacheConfig, HttpCacheResponse,
        MiddlewareManager, RateLimitMiddleware,
        HealthCheckMiddleware, ErrorHandlingMiddleware,
    },
    error::Result,
    utils::current_timestamp_secs,
};

/// 演示服务器配置
#[allow(unused)]
#[derive(Debug, Clone)]
pub struct DemoServerConfig {
    pub jwt_config: JwtConfig,
    pub validation_config: ValidationConfig,
    pub cache_config: CacheConfig,
    pub rate_limit_requests_per_minute: u32,
    pub health_check_path: String,
}

impl Default for DemoServerConfig {
    fn default() -> Self {
        Self {
            jwt_config: JwtConfig::default(),
            validation_config: ValidationConfig::new(),
            cache_config: CacheConfig::default(),
            rate_limit_requests_per_minute: 100,
            health_check_path: "/health".to_string(),
        }
    }
}

/// 演示服务器
#[allow(unused)]
#[derive(Debug)]
pub struct DemoServer {
    config: DemoServerConfig,
    jwt_manager: JwtAuthManager,
    jwt_middleware: JwtAuthMiddleware,
    validation_middleware: RequestValidationMiddleware,
    cache_middleware: HttpCacheMiddleware,
    middleware_manager: MiddlewareManager,
}

#[allow(unused)]
impl DemoServer {
    pub fn new(config: DemoServerConfig) -> Self {
        let jwt_manager = JwtAuthManager::new(config.jwt_config.clone());
        let jwt_middleware = jwt_manager.auth_middleware.clone();
        let validation_middleware = RequestValidationMiddleware::new(config.validation_config.clone());
        let cache_middleware = HttpCacheMiddleware::new(config.cache_config.clone());

        let middleware_manager = MiddlewareManager::new()
            .with_rate_limit(RateLimitMiddleware::default())
            .with_health_check(HealthCheckMiddleware::new())
            .with_error_handling(ErrorHandlingMiddleware::default());

        Self {
            config,
            jwt_manager,
            jwt_middleware,
            validation_middleware,
            cache_middleware,
            middleware_manager,
        }
    }

    /// 启动演示服务器
    pub async fn start(&self) -> Result<()> {
        info!("启动综合中间件演示服务器");

        // 演示JWT认证
        self.demonstrate_jwt_auth().await?;

        // 演示请求验证
        self.demonstrate_request_validation().await?;

        // 演示缓存功能
        self.demonstrate_caching().await?;

        // 演示中间件组合
        self.demonstrate_middleware_composition().await?;

        info!("综合中间件演示完成");
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
        let token = self.jwt_manager.generate_user_token(&user)?;
        info!("生成的JWT令牌: {}", token);

        // 验证JWT令牌
        match self.jwt_middleware.authenticate_request("/api/protected", Some(&token)).await {
            c13_microservice::middleware::AuthResult::Authenticated(claims) => {
                info!("JWT验证成功:");
                info!("  用户ID: {}", claims.sub);
                info!(
                    "  用户名: {}",
                    claims
                        .custom
                        .get("username")
                        .and_then(|v| v.as_str())
                        .unwrap_or(claims.sub.as_str())
                );
                info!("  角色: {:?}", claims.roles);
                info!("  权限: {:?}", claims.permissions);
                info!("  是否有admin角色: {}", claims.has_role("admin"));
                info!("  是否有write权限: {}", claims.has_permission("write"));
            }
            c13_microservice::middleware::AuthResult::Skipped => {
                info!("JWT认证被跳过");
            }
            c13_microservice::middleware::AuthResult::Unauthorized(e) => {
                error!("JWT验证失败: {}", e);
                return Err(c13_microservice::error::Error::Auth(e));
            }
            c13_microservice::middleware::AuthResult::Forbidden(e) => {
                error!("JWT权限验证失败: {}", e);
                return Err(c13_microservice::error::Error::Auth(e));
            }
        }

        // 测试过期令牌
        // 构造一个已过期的 claims 并手动生成 token
        let expired_claims = Claims::new(user.id.clone())
            .with_roles(user.roles.clone())
            .with_permissions(user.permissions.clone())
            .with_expiration(current_timestamp_secs() - 10);
        let expired_token = self.jwt_middleware.generate_token(&expired_claims)?;
        
        match self.jwt_middleware.authenticate_request("/api/protected", Some(&expired_token)).await {
            c13_microservice::middleware::AuthResult::Authenticated(_) => warn!("过期令牌验证意外成功"),
            c13_microservice::middleware::AuthResult::Unauthorized(e) => info!("过期令牌正确被拒绝: {}", e),
            c13_microservice::middleware::AuthResult::Forbidden(e) => info!("过期令牌权限被拒绝: {}", e),
            c13_microservice::middleware::AuthResult::Skipped => info!("认证被跳过"),
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

        // 创建缓存请求示例（此处未直接使用）

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
            created_at: Instant::now(),
        };

        // 检查是否应该缓存
        if self.cache_middleware.should_cache_response(&mock_response) {
            info!("响应应该被缓存");
        } else {
            info!("响应不应该被缓存");
        }

        // 此处仅演示 should_cache_response，详细统计请使用 CacheManager

        Ok(())
    }

    /// 演示中间件组合
    async fn demonstrate_middleware_composition(&self) -> Result<()> {
        info!("=== 中间件组合演示 ===");

        // 创建中间件服务构建器
        let _middleware_stack = ServiceBuilder::new()
            .layer(TraceLayer::new_for_http())
            .layer(CorsLayer::permissive())
            .layer(self.middleware_manager.clone());

        info!("中间件栈已配置:");
        info!("  - 请求追踪");
        info!("  - CORS支持");
        info!("  - 速率限制");
        info!("  - 健康检查");
        info!("  - 错误处理");

        // 模拟请求处理
        self.simulate_request_processing().await?;

        Ok(())
    }

    /// 模拟请求处理
    async fn simulate_request_processing(&self) -> Result<()> {
        info!("模拟请求处理流程:");

        let requests = vec![
            ("GET", "/health", "健康检查"),
            ("GET", "/api/users", "获取用户列表"),
            ("POST", "/api/users", "创建用户"),
            ("GET", "/api/users/123", "获取特定用户"),
        ];

        for (method, path, description) in requests {
            info!("处理请求: {} {} - {}", method, path, description);
            
            // 模拟请求延迟
            sleep(Duration::from_millis(100)).await;
            
            // 检查是否需要认证
            let auth_result = self.jwt_middleware.authenticate_request(path, None).await;
            match auth_result {
                c13_microservice::middleware::AuthResult::Authenticated(_) => {
                    info!("  JWT认证成功");
                }
                c13_microservice::middleware::AuthResult::Skipped => {
                    info!("  跳过认证");
                }
                c13_microservice::middleware::AuthResult::Unauthorized(e) => {
                    info!("  认证失败: {}", e);
                }
                c13_microservice::middleware::AuthResult::Forbidden(e) => {
                    info!("  权限不足: {}", e);
                }
            }

            // 检查是否应该缓存
            // 仅演示响应缓存策略

            // 模拟响应
            let mock_response = HttpCacheResponse {
                status_code: 200,
                headers: HashMap::new(),
                body: format!("{{\"message\": \"处理{}请求成功\"}}", description).into_bytes(),
                created_at: Instant::now(),
            };

            // 检查是否应该缓存
            if self.cache_middleware.should_cache_response(&mock_response) {
                info!("  响应应该被缓存");
            } else {
                info!("  响应不应该被缓存");
            }
        }

        Ok(())
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::INFO)
        .init();

    info!("综合中间件演示开始");

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
