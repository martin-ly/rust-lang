//! API模块
//! 
//! 提供REST API的实现

pub mod handlers;
pub mod middleware;
pub mod routes;
pub mod server;

pub use handlers::*;
pub use middleware::*;
pub use routes::*;
pub use server::*;

use axum::{
    extract::{Path, Query, State},
    http::StatusCode,
    response::Json,
    routing::{get, post, put, delete},
    Router,
};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;

/// API响应结构
#[derive(Debug, Serialize, Deserialize)]
pub struct ApiResponse<T> {
    pub success: bool,
    pub data: Option<T>,
    pub error: Option<String>,
    pub message: Option<String>,
}

impl<T> ApiResponse<T> {
    /// 创建成功响应
    pub fn success(data: T) -> Self {
        Self {
            success: true,
            data: Some(data),
            error: None,
            message: None,
        }
    }

    /// 创建错误响应
    pub fn error(message: String) -> Self {
        Self {
            success: false,
            data: None,
            error: Some(message),
            message: None,
        }
    }

    /// 创建带消息的成功响应
    pub fn success_with_message(data: T, message: String) -> Self {
        Self {
            success: true,
            data: Some(data),
            error: None,
            message: Some(message),
        }
    }
}

/// 分页参数
#[derive(Debug, Deserialize)]
pub struct PaginationParams {
    pub page: Option<u32>,
    pub limit: Option<u32>,
    pub offset: Option<u32>,
}

impl Default for PaginationParams {
    fn default() -> Self {
        Self {
            page: Some(1),
            limit: Some(20),
            offset: Some(0),
        }
    }
}

/// 排序参数
#[derive(Debug, Deserialize)]
pub struct SortParams {
    pub sort_by: Option<String>,
    pub sort_order: Option<String>, // "asc" or "desc"
}

/// 过滤参数
#[derive(Debug, Deserialize)]
pub struct FilterParams {
    pub search: Option<String>,
    pub filters: Option<HashMap<String, String>>,
}

/// 查询参数组合
#[derive(Debug, Deserialize)]
pub struct QueryParams {
    #[serde(flatten)]
    pub pagination: PaginationParams,
    #[serde(flatten)]
    pub sort: SortParams,
    #[serde(flatten)]
    pub filter: FilterParams,
}

/// 健康检查响应
#[derive(Debug, Serialize, Deserialize)]
pub struct HealthResponse {
    pub status: String,
    pub version: String,
    pub timestamp: String,
    pub uptime: u64,
    pub services: HashMap<String, String>,
}

/// 统计信息响应
#[derive(Debug, Serialize, Deserialize)]
pub struct StatsResponse {
    pub total_users: u64,
    pub total_models: u64,
    pub total_training_jobs: u64,
    pub total_inference_requests: u64,
    pub active_sessions: u64,
    pub cache_hit_rate: f64,
    pub memory_usage: u64,
    pub cpu_usage: f64,
}

/// 错误类型
#[derive(Debug, thiserror::Error)]
pub enum ApiError {
    #[error("未找到资源: {0}")]
    NotFound(String),
    
    #[error("参数错误: {0}")]
    BadRequest(String),
    
    #[error("未授权: {0}")]
    Unauthorized(String),
    
    #[error("禁止访问: {0}")]
    Forbidden(String),
    
    #[error("内部服务器错误: {0}")]
    InternalServerError(String),
    
    #[error("服务不可用: {0}")]
    ServiceUnavailable(String),
    
    #[error("请求超时: {0}")]
    RequestTimeout(String),
    
    #[error("请求过多: {0}")]
    TooManyRequests(String),
}

impl ApiError {
    /// 获取HTTP状态码
    pub fn status_code(&self) -> StatusCode {
        match self {
            ApiError::NotFound(_) => StatusCode::NOT_FOUND,
            ApiError::BadRequest(_) => StatusCode::BAD_REQUEST,
            ApiError::Unauthorized(_) => StatusCode::UNAUTHORIZED,
            ApiError::Forbidden(_) => StatusCode::FORBIDDEN,
            ApiError::InternalServerError(_) => StatusCode::INTERNAL_SERVER_ERROR,
            ApiError::ServiceUnavailable(_) => StatusCode::SERVICE_UNAVAILABLE,
            ApiError::RequestTimeout(_) => StatusCode::REQUEST_TIMEOUT,
            ApiError::TooManyRequests(_) => StatusCode::TOO_MANY_REQUESTS,
        }
    }
}

/// 将ApiError转换为JSON响应
impl axum::response::IntoResponse for ApiError {
    fn into_response(self) -> axum::response::Response {
        let status = self.status_code();
        let response = ApiResponse::<()>::error(self.to_string());
        (status, Json(response)).into_response()
    }
}