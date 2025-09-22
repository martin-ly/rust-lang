//! API服务器模块
//! 
//! 提供HTTP API服务器功能

use axum::{
    extract::{Path, Query, State},
    http::StatusCode,
    response::Json,
    routing::{get, post, put, delete},
    Router,
};
use std::sync::Arc;
use std::collections::HashMap;
use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};

use super::types::*;
use super::middleware::*;
use super::handlers::*;

/// 应用状态
#[derive(Debug, Clone)]
pub struct AppState {
    pub config: AppConfig,
    pub auth: Arc<dyn AuthService>,
    pub rate_limiter: RateLimiter,
    pub cors: Arc<dyn CorsService>,
    pub health_checker: Arc<dyn HealthChecker>,
    pub metrics: Arc<dyn MetricsCollector>,
    pub error_tracker: Arc<dyn ErrorTracker>,
}

/// 应用配置
#[derive(Debug, Clone)]
pub struct AppConfig {
    pub host: String,
    pub port: u16,
    pub request_timeout: std::time::Duration,
    pub max_request_size: u64,
    pub allowed_content_types: Vec<String>,
    pub cors_origins: Vec<String>,
    pub rate_limit_requests: u32,
    pub rate_limit_window: std::time::Duration,
}

impl Default for AppConfig {
    fn default() -> Self {
        Self {
            host: "0.0.0.0".to_string(),
            port: 8080,
            request_timeout: std::time::Duration::from_secs(30),
            max_request_size: 10 * 1024 * 1024, // 10MB
            allowed_content_types: vec![
                "application/json".to_string(),
                "application/x-www-form-urlencoded".to_string(),
                "multipart/form-data".to_string(),
            ],
            cors_origins: vec!["*".to_string()],
            rate_limit_requests: 100,
            rate_limit_window: std::time::Duration::from_secs(60),
        }
    }
}

/// 认证服务接口
#[async_trait::async_trait]
pub trait AuthService: Send + Sync {
    async fn validate_token(&self, token: &str) -> bool;
    async fn get_user(&self, token: &str) -> Option<UserInfo>;
}

/// CORS服务接口
#[async_trait::async_trait]
pub trait CorsService: Send + Sync {
    fn is_allowed_origin(&self, origin: &str) -> bool;
}

/// 健康检查服务接口
#[async_trait::async_trait]
pub trait HealthChecker: Send + Sync {
    async fn is_healthy(&self) -> bool;
}

/// 指标收集服务接口
#[async_trait::async_trait]
pub trait MetricsCollector: Send + Sync {
    async fn record_request(&self, method: &str, path: &str, status: u16, duration: std::time::Duration);
}

/// 错误跟踪服务接口
#[async_trait::async_trait]
pub trait ErrorTracker: Send + Sync {
    async fn record_error(&self, status: u16, path: &str, method: &str);
}

/// API服务器
#[derive(Debug)]
pub struct ApiServer {
    config: AppConfig,
    state: Arc<AppState>,
    router: Router,
}

impl ApiServer {
    /// 创建新的API服务器
    pub fn new(config: AppConfig) -> Self {
        let state = Arc::new(AppState {
            config: config.clone(),
            auth: Arc::new(DefaultAuthService),
            rate_limiter: RateLimiter::new(config.rate_limit_requests, config.rate_limit_window),
            cors: Arc::new(DefaultCorsService::new(config.cors_origins.clone())),
            health_checker: Arc::new(DefaultHealthChecker),
            metrics: Arc::new(DefaultMetricsCollector),
            error_tracker: Arc::new(DefaultErrorTracker),
        });

        let router = Self::create_router(state.clone());

        Self {
            config,
            state,
            router,
        }
    }

    /// 创建路由
    fn create_router(state: Arc<AppState>) -> Router {
        Router::new()
            // 健康检查路由
            .route("/health", get(handlers::health_check))
            .route("/health/detailed", get(handlers::detailed_health_check))

            // 系统信息路由
            .route("/system/info", get(handlers::get_system_info))
            .route("/system/metrics", get(handlers::get_system_metrics))
            .route("/system/config", get(handlers::get_system_config))
            .route("/system/config", put(handlers::update_system_config))

            // 模型管理路由
            .route("/models", get(handlers::list_models).post(handlers::create_model))
            .route("/models/:id", get(handlers::get_model).put(handlers::update_model).delete(handlers::delete_model))
            .route("/models/:id/load", post(handlers::load_model))
            .route("/models/:id/unload", post(handlers::unload_model))
            .route("/models/:id/status", get(handlers::get_model_status))

            // 推理路由
            .route("/inference", post(handlers::run_inference))
            .route("/inference/batch", post(handlers::run_batch_inference))
            .route("/inference/async", post(handlers::run_async_inference))
            .route("/inference/results/:id", get(handlers::get_inference_result))
            .route("/inference/warmup/:id", post(handlers::warmup_model))
            .route("/inference/status", get(handlers::get_inference_status))

            // 训练路由
            .route("/train", post(handlers::start_training))
            .route("/train/:id/status", get(handlers::get_training_status))
            .route("/train/:id/stop", post(handlers::stop_training))
            .route("/train/:id/logs", get(handlers::get_training_logs))

            // 数据集管理路由
            .route("/datasets", get(handlers::list_datasets).post(handlers::upload_dataset))
            .route("/datasets/:id", get(handlers::get_dataset).delete(handlers::delete_dataset))
            .route("/datasets/:id/download", get(handlers::download_dataset))

            // 缓存管理路由
            .route("/cache", get(handlers::list_caches).post(handlers::create_cache))
            .route("/cache/:name", get(handlers::get_cache_stats).delete(handlers::clear_cache))
            .route("/cache/:name/:key", get(handlers::get_cache_value).put(handlers::set_cache_value).delete(handlers::delete_cache_value))
            .route("/cache/:name/warmup", post(handlers::warmup_cache))
            .route("/cache/:name/cleanup", post(handlers::cleanup_cache))

            // 存储管理路由
            .route("/storage/upload", post(handlers::upload_file))
            .route("/storage/download", get(handlers::download_file))
            .route("/storage/delete", delete(handlers::delete_file))
            .route("/storage/list", get(handlers::list_files))
            .route("/storage/copy", post(handlers::copy_file))
            .route("/storage/move", post(handlers::move_file))
            .route("/storage/metadata/:key", get(handlers::get_file_metadata))
            .route("/storage/stats", get(handlers::get_storage_stats))
            .route("/storage/health", get(handlers::get_storage_health))
            .route("/storage/cleanup", post(handlers::cleanup_storage))

            // 消息队列路由
            .route("/messaging/queues", get(handlers::list_queues).post(handlers::create_queue))
            .route("/messaging/queues/:name", get(handlers::get_queue_stats).delete(handlers::delete_queue))
            .route("/messaging/publish", post(handlers::publish_message))
            .route("/messaging/subscribe", post(handlers::subscribe_message))
            .route("/messaging/unsubscribe", post(handlers::unsubscribe_message))
            .route("/messaging/messages/:queue_name/:message_id", get(handlers::get_message).delete(handlers::delete_message))
            .route("/messaging/cleanup", post(handlers::cleanup_messages))
            .route("/messaging/retry", post(handlers::retry_failed_messages))
            .route("/messaging/dead_letter", post(handlers::move_to_dead_letter))

            // WebSocket路由
            .route("/ws", get(handlers::websocket_handler))

            // 认证路由
            .route("/auth/login", post(handlers::login))
            .route("/auth/logout", post(handlers::logout))
            .route("/auth/validate", post(handlers::validate_token))
            .route("/auth/refresh", post(handlers::refresh_token))

            // 用户管理路由
            .route("/users", get(handlers::list_users).post(handlers::create_user))
            .route("/users/:id", get(handlers::get_user).put(handlers::update_user).delete(handlers::delete_user))
            .route("/users/:id/roles", get(handlers::get_user_roles).put(handlers::update_user_roles))

            // 批量操作路由
            .route("/batch/operations", post(handlers::batch_operations))
            .route("/batch/operations/:id", get(handlers::get_batch_operation_status))

            // 搜索路由
            .route("/search", get(handlers::search))
            .route("/search/suggestions", get(handlers::get_search_suggestions))

            // 配置管理路由
            .route("/config", get(handlers::get_config).put(handlers::update_config))
            .route("/config/:key", get(handlers::get_config_value).put(handlers::update_config_value).delete(handlers::delete_config_value))

            // 日志路由
            .route("/logs", get(handlers::get_logs))
            .route("/logs/:level", get(handlers::get_logs_by_level))

            // 中间件
            .layer(axum::middleware::from_fn_with_state(
                state.clone(),
                middleware::request_id_middleware,
            ))
            .layer(axum::middleware::from_fn_with_state(
                state.clone(),
                middleware::logging_middleware,
            ))
            .layer(axum::middleware::from_fn_with_state(
                state.clone(),
                middleware::metrics_middleware,
            ))
            .layer(axum::middleware::from_fn_with_state(
                state.clone(),
                middleware::security_headers_middleware,
            ))
            .layer(axum::middleware::from_fn_with_state(
                state.clone(),
                middleware::cache_control_middleware,
            ))
            .layer(axum::middleware::from_fn_with_state(
                state.clone(),
                middleware::request_validation_middleware,
            ))
            .layer(axum::middleware::from_fn_with_state(
                state.clone(),
                middleware::cors_middleware,
            ))
            .layer(axum::middleware::from_fn_with_state(
                state.clone(),
                middleware::rate_limit_middleware,
            ))
            .layer(axum::middleware::from_fn_with_state(
                state.clone(),
                middleware::auth_middleware,
            ))
            .layer(axum::middleware::from_fn_with_state(
                state.clone(),
                middleware::health_check_middleware,
            ))
            .layer(axum::middleware::from_fn_with_state(
                state.clone(),
                middleware::timeout_middleware,
            ))
            .layer(axum::middleware::from_fn_with_state(
                state.clone(),
                middleware::compression_middleware,
            ))
            .layer(axum::middleware::from_fn_with_state(
                state.clone(),
                middleware::error_handling_middleware,
            ))
            .with_state(state)
    }

    /// 启动服务器
    pub async fn start(&self) -> Result<(), Box<dyn std::error::Error>> {
        let listener = tokio::net::TcpListener::bind(format!("{}:{}", self.config.host, self.config.port)).await?;
        
        tracing::info!("API服务器启动在 {}:{}", self.config.host, self.config.port);
        
        axum::serve(listener, self.router.clone()).await?;
        
        Ok(())
    }

    /// 获取服务器配置
    pub fn get_config(&self) -> &AppConfig {
        &self.config
    }

    /// 获取应用状态
    pub fn get_state(&self) -> &Arc<AppState> {
        &self.state
    }
}

/// 默认认证服务实现
#[derive(Debug)]
pub struct DefaultAuthService;

#[async_trait::async_trait]
impl AuthService for DefaultAuthService {
    async fn validate_token(&self, _token: &str) -> bool {
        // 默认实现：总是返回true
        // 在实际应用中，这里应该验证JWT令牌或其他认证机制
        true
    }

    async fn get_user(&self, _token: &str) -> Option<UserInfo> {
        // 默认实现：返回一个默认用户
        Some(UserInfo {
            id: "default".to_string(),
            username: "default".to_string(),
            email: Some("default@example.com".to_string()),
            roles: vec!["user".to_string()],
            created_at: Utc::now(),
            last_login: Some(Utc::now()),
        })
    }
}

/// 默认CORS服务实现
#[derive(Debug)]
pub struct DefaultCorsService {
    allowed_origins: Vec<String>,
}

impl DefaultCorsService {
    pub fn new(allowed_origins: Vec<String>) -> Self {
        Self { allowed_origins }
    }
}

#[async_trait::async_trait]
impl CorsService for DefaultCorsService {
    fn is_allowed_origin(&self, origin: &str) -> bool {
        self.allowed_origins.contains(&"*".to_string()) || self.allowed_origins.contains(&origin.to_string())
    }
}

/// 默认健康检查服务实现
#[derive(Debug)]
pub struct DefaultHealthChecker;

#[async_trait::async_trait]
impl HealthChecker for DefaultHealthChecker {
    async fn is_healthy(&self) -> bool {
        // 默认实现：总是返回true
        // 在实际应用中，这里应该检查数据库连接、外部服务等
        true
    }
}

/// 默认指标收集服务实现
#[derive(Debug)]
pub struct DefaultMetricsCollector;

#[async_trait::async_trait]
impl MetricsCollector for DefaultMetricsCollector {
    async fn record_request(&self, method: &str, path: &str, status: u16, duration: std::time::Duration) {
        tracing::info!(
            "Request: {} {} - Status: {} - Duration: {:?}",
            method,
            path,
            status,
            duration
        );
    }
}

/// 默认错误跟踪服务实现
#[derive(Debug)]
pub struct DefaultErrorTracker;

#[async_trait::async_trait]
impl ErrorTracker for DefaultErrorTracker {
    async fn record_error(&self, status: u16, path: &str, method: &str) {
        tracing::error!(
            "Error: {} {} - Status: {}",
            method,
            path,
            status
        );
    }
}