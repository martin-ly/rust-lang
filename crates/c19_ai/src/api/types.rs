//! API类型定义
//! 
//! 定义API请求和响应的数据结构

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use chrono::{DateTime, Utc};

/// 健康检查响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HealthResponse {
    pub status: String,
    pub timestamp: DateTime<Utc>,
    pub version: String,
}

/// 模型信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModelInfo {
    pub id: String,
    pub name: String,
    pub version: String,
    pub framework: String,
    pub status: String,
    pub created_at: DateTime<Utc>,
}

/// 创建模型请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CreateModelRequest {
    pub name: String,
    pub version: String,
    pub framework: String,
    pub config: Option<serde_json::Value>,
}

/// 更新模型请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UpdateModelRequest {
    pub name: Option<String>,
    pub version: Option<String>,
    pub framework: Option<String>,
    pub config: Option<serde_json::Value>,
}

/// 预测请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PredictRequest {
    pub model_id: String,
    pub input: serde_json::Value,
    pub parameters: Option<HashMap<String, serde_json::Value>>,
}

/// 预测响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PredictResponse {
    pub id: String,
    pub model_id: String,
    pub predictions: Vec<f64>,
    pub confidence: f64,
    pub processing_time_ms: u64,
    pub timestamp: DateTime<Utc>,
}

/// 批量预测请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchPredictRequest {
    pub model_id: String,
    pub inputs: Vec<serde_json::Value>,
    pub parameters: Option<HashMap<String, serde_json::Value>>,
}

/// 异步预测响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AsyncPredictResponse {
    pub id: String,
    pub model_id: String,
    pub status: String,
    pub estimated_completion_time: DateTime<Utc>,
    pub timestamp: DateTime<Utc>,
}

/// 推理状态响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InferenceStatusResponse {
    pub id: String,
    pub status: String,
    pub result: Option<PredictResponse>,
    pub error: Option<String>,
    pub timestamp: DateTime<Utc>,
}

/// 开始训练请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StartTrainingRequest {
    pub model_id: String,
    pub dataset_id: String,
    pub config: serde_json::Value,
}

/// 训练状态响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TrainingStatusResponse {
    pub id: String,
    pub status: String,
    pub progress: f64,
    pub current_epoch: u32,
    pub total_epochs: u32,
    pub metrics: HashMap<String, f64>,
    pub timestamp: DateTime<Utc>,
}

/// 数据集信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DatasetInfo {
    pub id: String,
    pub name: String,
    pub size: u64,
    pub created_at: DateTime<Utc>,
}

/// 上传数据集请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UploadDatasetRequest {
    pub name: String,
    pub description: Option<String>,
    pub tags: Option<Vec<String>>,
}

/// 缓存统计响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheStatsResponse {
    pub total_entries: u64,
    pub hit_rate: f64,
    pub memory_usage: u64,
    pub timestamp: DateTime<Utc>,
}

/// 存储统计响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StorageStatsResponse {
    pub total_files: u64,
    pub total_size: u64,
    pub available_space: u64,
    pub timestamp: DateTime<Utc>,
}

/// 文件信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FileInfo {
    pub id: String,
    pub name: String,
    pub size: u64,
    pub content_type: String,
    pub created_at: DateTime<Utc>,
}

/// 上传文件请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UploadFileRequest {
    pub name: String,
    pub content_type: Option<String>,
    pub metadata: Option<HashMap<String, String>>,
}

/// 发布消息请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PublishMessageRequest {
    pub topic: String,
    pub payload: serde_json::Value,
    pub headers: Option<HashMap<String, String>>,
}

/// 订阅请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SubscribeRequest {
    pub topic: String,
    pub filter: Option<HashMap<String, String>>,
}

/// 队列信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QueueInfo {
    pub name: String,
    pub message_count: u64,
    pub consumer_count: u32,
    pub created_at: DateTime<Utc>,
}

/// 系统信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SystemInfo {
    pub version: String,
    pub uptime: u64,
    pub memory_usage: u64,
    pub cpu_usage: f64,
    pub timestamp: DateTime<Utc>,
}

/// 系统指标
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SystemMetrics {
    pub requests_per_second: f64,
    pub average_response_time: f64,
    pub error_rate: f64,
    pub active_connections: u32,
    pub timestamp: DateTime<Utc>,
}

/// 操作结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OperationResult {
    pub success: bool,
    pub message: String,
    pub timestamp: DateTime<Utc>,
}

/// API错误响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ErrorResponse {
    pub error: String,
    pub message: String,
    pub timestamp: DateTime<Utc>,
    pub request_id: Option<String>,
}

/// 分页参数
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PaginationParams {
    pub page: Option<u32>,
    pub limit: Option<u32>,
    pub sort: Option<String>,
    pub order: Option<String>,
}

/// 分页响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PaginatedResponse<T> {
    pub data: Vec<T>,
    pub total: u64,
    pub page: u32,
    pub limit: u32,
    pub total_pages: u32,
}

/// 搜索参数
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SearchParams {
    pub query: Option<String>,
    pub filters: Option<HashMap<String, String>>,
    pub pagination: Option<PaginationParams>,
}

/// 批量操作请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchOperationRequest {
    pub operation: String,
    pub ids: Vec<String>,
    pub parameters: Option<HashMap<String, serde_json::Value>>,
}

/// 批量操作响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchOperationResponse {
    pub successful: Vec<String>,
    pub failed: Vec<BatchOperationError>,
    pub total_processed: usize,
}

/// 批量操作错误
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchOperationError {
    pub id: String,
    pub error: String,
}

/// 配置更新请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConfigUpdateRequest {
    pub key: String,
    pub value: serde_json::Value,
    pub description: Option<String>,
}

/// 配置信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConfigInfo {
    pub key: String,
    pub value: serde_json::Value,
    pub description: Option<String>,
    pub updated_at: DateTime<Utc>,
}

/// 用户信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UserInfo {
    pub id: String,
    pub username: String,
    pub email: Option<String>,
    pub roles: Vec<String>,
    pub created_at: DateTime<Utc>,
    pub last_login: Option<DateTime<Utc>>,
}

/// 认证请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuthRequest {
    pub username: String,
    pub password: String,
}

/// 认证响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuthResponse {
    pub token: String,
    pub expires_at: DateTime<Utc>,
    pub user: UserInfo,
}

/// 令牌验证请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TokenValidationRequest {
    pub token: String,
}

/// 令牌验证响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TokenValidationResponse {
    pub valid: bool,
    pub user: Option<UserInfo>,
    pub expires_at: Option<DateTime<Utc>>,
}