//! 健康检查和监控端点
//! 
//! 提供系统健康状态、性能指标和监控功能

use super::{ApiResponse, ApiError};
use crate::config::ConfigManager;
use crate::auth::manager::AuthManager;
use crate::database::DatabaseManager;
use crate::cache::manager::CacheManager;
use crate::storage::manager::StorageManager;
use axum::{
    extract::State,
    response::Json,
};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{SystemTime, UNIX_EPOCH};
use tokio::time::Instant;

/// 应用状态
#[derive(Clone)]
pub struct AppState {
    pub config_manager: Arc<ConfigManager>,
    pub auth_manager: Arc<AuthManager>,
    pub db_manager: Arc<DatabaseManager>,
    pub cache_manager: Arc<CacheManager>,
    pub storage_manager: Arc<StorageManager>,
    pub start_time: SystemTime,
}

/// 健康检查响应
#[derive(Debug, Serialize)]
pub struct HealthResponse {
    pub status: String,
    pub version: String,
    pub timestamp: String,
    pub uptime: u64,
    pub services: HashMap<String, ServiceStatus>,
}

/// 服务状态
#[derive(Debug, Serialize)]
pub struct ServiceStatus {
    pub status: String,
    pub response_time_ms: Option<u64>,
    pub last_check: String,
    pub error: Option<String>,
}

/// 详细健康检查响应
#[derive(Debug, Serialize)]
pub struct DetailedHealthResponse {
    pub overall_status: String,
    pub version: String,
    pub timestamp: String,
    pub uptime: u64,
    pub services: HashMap<String, ServiceStatus>,
    pub system_info: SystemInfo,
}

/// 系统信息
#[derive(Debug, Serialize)]
pub struct SystemInfo {
    pub memory_usage: MemoryInfo,
    pub cpu_usage: f64,
    pub disk_usage: DiskInfo,
    pub network_info: NetworkInfo,
}

/// 内存信息
#[derive(Debug, Serialize)]
pub struct MemoryInfo {
    pub total: u64,
    pub used: u64,
    pub free: u64,
    pub available: u64,
}

/// 磁盘信息
#[derive(Debug, Serialize)]
pub struct DiskInfo {
    pub total: u64,
    pub used: u64,
    pub free: u64,
    pub usage_percent: f64,
}

/// 网络信息
#[derive(Debug, Serialize)]
pub struct NetworkInfo {
    pub connections: u32,
    pub bytes_sent: u64,
    pub bytes_received: u64,
}

/// 性能指标响应
#[derive(Debug, Serialize)]
pub struct MetricsResponse {
    pub timestamp: String,
    pub metrics: HashMap<String, MetricValue>,
}

/// 指标值
#[derive(Debug, Serialize)]
#[serde(untagged)]
pub enum MetricValue {
    Counter(u64),
    Gauge(f64),
    Histogram(Vec<f64>),
    Timer(u64),
}

/// 基础健康检查
pub async fn health_check(State(state): State<AppState>) -> Result<Json<ApiResponse<HealthResponse>>, ApiError> {
    let start_time = Instant::now();
    let uptime = SystemTime::now()
        .duration_since(state.start_time)
        .unwrap_or_default()
        .as_secs();

    let mut services = HashMap::new();
    
    // 检查数据库连接
    let db_status = check_database(&state.db_manager).await;
    services.insert("database".to_string(), db_status);
    
    // 检查缓存服务
    let cache_status = check_cache(&state.cache_manager).await;
    services.insert("cache".to_string(), cache_status);
    
    // 检查存储服务
    let storage_status = check_storage(&state.storage_manager).await;
    services.insert("storage".to_string(), storage_status);

    // 检查认证服务
    let auth_status = check_auth(&state.auth_manager).await;
    services.insert("auth".to_string(), auth_status);

    // 检查配置服务
    let config_status = check_config(&state.config_manager).await;
    services.insert("config".to_string(), config_status);

    let overall_status = if services.values().any(|s| s.status == "unhealthy") {
        "degraded"
    } else if services.values().any(|s| s.status == "degraded") {
        "degraded"
    } else {
        "healthy"
    };

    let health = HealthResponse {
        status: overall_status.to_string(),
        version: "0.3.0".to_string(),
        timestamp: chrono::Utc::now().to_rfc3339(),
        uptime,
        services,
    };

    Ok(Json(ApiResponse::success(health)))
}

/// 详细健康检查
pub async fn detailed_health_check(State(state): State<AppState>) -> Result<Json<ApiResponse<DetailedHealthResponse>>, ApiError> {
    let uptime = SystemTime::now()
        .duration_since(state.start_time)
        .unwrap_or_default()
        .as_secs();

    let mut services = HashMap::new();
    
    // 检查所有服务
    let db_status = check_database(&state.db_manager).await;
    services.insert("database".to_string(), db_status);
    
    let cache_status = check_cache(&state.cache_manager).await;
    services.insert("cache".to_string(), cache_status);
    
    let storage_status = check_storage(&state.storage_manager).await;
    services.insert("storage".to_string(), storage_status);

    let auth_status = check_auth(&state.auth_manager).await;
    services.insert("auth".to_string(), auth_status);

    let config_status = check_config(&state.config_manager).await;
    services.insert("config".to_string(), config_status);

    let overall_status = if services.values().any(|s| s.status == "unhealthy") {
        "unhealthy"
    } else if services.values().any(|s| s.status == "degraded") {
        "degraded"
    } else {
        "healthy"
    };

    // 获取系统信息
    let system_info = get_system_info().await;

    let health = DetailedHealthResponse {
        overall_status: overall_status.to_string(),
        version: "0.3.0".to_string(),
        timestamp: chrono::Utc::now().to_rfc3339(),
        uptime,
        services,
        system_info,
    };

    Ok(Json(ApiResponse::success(health)))
}

/// 性能指标
pub async fn get_metrics(State(state): State<AppState>) -> Result<Json<ApiResponse<MetricsResponse>>, ApiError> {
    let mut metrics = HashMap::new();

    // 缓存指标
    if let Ok(cache_stats) = state.cache_manager.get_all_stats().await {
        metrics.insert("cache.hit_rate".to_string(), MetricValue::Gauge(cache_stats.hit_rate));
        metrics.insert("cache.miss_rate".to_string(), MetricValue::Gauge(cache_stats.miss_rate));
        metrics.insert("cache.total_requests".to_string(), MetricValue::Counter(cache_stats.total_requests));
        metrics.insert("cache.total_hits".to_string(), MetricValue::Counter(cache_stats.total_hits));
        metrics.insert("cache.total_misses".to_string(), MetricValue::Counter(cache_stats.total_misses));
    }

    // 数据库指标
    if let Ok(db_stats) = state.db_manager.get_connection_stats().await {
        metrics.insert("database.active_connections".to_string(), MetricValue::Gauge(db_stats.active_connections as f64));
        metrics.insert("database.total_connections".to_string(), MetricValue::Counter(db_stats.total_connections));
        metrics.insert("database.failed_connections".to_string(), MetricValue::Counter(db_stats.failed_connections));
    }

    // 存储指标
    if let Ok(storage_stats) = state.storage_manager.get_all_stats().await {
        metrics.insert("storage.total_files".to_string(), MetricValue::Counter(storage_stats.total_files));
        metrics.insert("storage.total_size".to_string(), MetricValue::Counter(storage_stats.total_size));
        metrics.insert("storage.operations_count".to_string(), MetricValue::Counter(storage_stats.operations_count));
    }

    // 系统指标
    let system_info = get_system_info().await;
    metrics.insert("system.memory_usage".to_string(), MetricValue::Gauge(system_info.memory_usage.used as f64));
    metrics.insert("system.cpu_usage".to_string(), MetricValue::Gauge(system_info.cpu_usage));
    metrics.insert("system.disk_usage".to_string(), MetricValue::Gauge(system_info.disk_usage.usage_percent));

    let response = MetricsResponse {
        timestamp: chrono::Utc::now().to_rfc3339(),
        metrics,
    };

    Ok(Json(ApiResponse::success(response)))
}

/// 检查数据库服务
async fn check_database(db_manager: &DatabaseManager) -> ServiceStatus {
    let start_time = Instant::now();
    let timestamp = chrono::Utc::now().to_rfc3339();

    match db_manager.get_connection_stats().await {
        Ok(stats) => {
            let response_time = start_time.elapsed().as_millis() as u64;
            let status = if stats.active_connections > 0 { "healthy" } else { "degraded" };
            
            ServiceStatus {
                status: status.to_string(),
                response_time_ms: Some(response_time),
                last_check: timestamp,
                error: None,
            }
        }
        Err(e) => {
            let response_time = start_time.elapsed().as_millis() as u64;
            ServiceStatus {
                status: "unhealthy".to_string(),
                response_time_ms: Some(response_time),
                last_check: timestamp,
                error: Some(e.to_string()),
            }
        }
    }
}

/// 检查缓存服务
async fn check_cache(cache_manager: &CacheManager) -> ServiceStatus {
    let start_time = Instant::now();
    let timestamp = chrono::Utc::now().to_rfc3339();

    match cache_manager.get_all_stats().await {
        Ok(_stats) => {
            let response_time = start_time.elapsed().as_millis() as u64;
            ServiceStatus {
                status: "healthy".to_string(),
                response_time_ms: Some(response_time),
                last_check: timestamp,
                error: None,
            }
        }
        Err(e) => {
            let response_time = start_time.elapsed().as_millis() as u64;
            ServiceStatus {
                status: "unhealthy".to_string(),
                response_time_ms: Some(response_time),
                last_check: timestamp,
                error: Some(e.to_string()),
            }
        }
    }
}

/// 检查存储服务
async fn check_storage(storage_manager: &StorageManager) -> ServiceStatus {
    let start_time = Instant::now();
    let timestamp = chrono::Utc::now().to_rfc3339();

    match storage_manager.get_all_stats().await {
        Ok(_stats) => {
            let response_time = start_time.elapsed().as_millis() as u64;
            ServiceStatus {
                status: "healthy".to_string(),
                response_time_ms: Some(response_time),
                last_check: timestamp,
                error: None,
            }
        }
        Err(e) => {
            let response_time = start_time.elapsed().as_millis() as u64;
            ServiceStatus {
                status: "unhealthy".to_string(),
                response_time_ms: Some(response_time),
                last_check: timestamp,
                error: Some(e.to_string()),
            }
        }
    }
}

/// 检查认证服务
async fn check_auth(auth_manager: &AuthManager) -> ServiceStatus {
    let start_time = Instant::now();
    let timestamp = chrono::Utc::now().to_rfc3339();

    // 简单的健康检查 - 尝试获取用户统计
    match auth_manager.get_user_stats().await {
        Ok(_stats) => {
            let response_time = start_time.elapsed().as_millis() as u64;
            ServiceStatus {
                status: "healthy".to_string(),
                response_time_ms: Some(response_time),
                last_check: timestamp,
                error: None,
            }
        }
        Err(e) => {
            let response_time = start_time.elapsed().as_millis() as u64;
            ServiceStatus {
                status: "unhealthy".to_string(),
                response_time_ms: Some(response_time),
                last_check: timestamp,
                error: Some(e.to_string()),
            }
        }
    }
}

/// 检查配置服务
async fn check_config(config_manager: &ConfigManager) -> ServiceStatus {
    let start_time = Instant::now();
    let timestamp = chrono::Utc::now().to_rfc3339();

    // 简单的健康检查 - 尝试获取配置
    match config_manager.get_all().await {
        Ok(_configs) => {
            let response_time = start_time.elapsed().as_millis() as u64;
            ServiceStatus {
                status: "healthy".to_string(),
                response_time_ms: Some(response_time),
                last_check: timestamp,
                error: None,
            }
        }
        Err(e) => {
            let response_time = start_time.elapsed().as_millis() as u64;
            ServiceStatus {
                status: "unhealthy".to_string(),
                response_time_ms: Some(response_time),
                last_check: timestamp,
                error: Some(e.to_string()),
            }
        }
    }
}

/// 获取系统信息
async fn get_system_info() -> SystemInfo {
    // 这里应该使用系统监控库，如 sysinfo
    // 为了演示，我们返回模拟数据
    SystemInfo {
        memory_usage: MemoryInfo {
            total: 8 * 1024 * 1024 * 1024, // 8GB
            used: 2 * 1024 * 1024 * 1024,  // 2GB
            free: 6 * 1024 * 1024 * 1024,  // 6GB
            available: 6 * 1024 * 1024 * 1024, // 6GB
        },
        cpu_usage: 25.5,
        disk_usage: DiskInfo {
            total: 500 * 1024 * 1024 * 1024, // 500GB
            used: 100 * 1024 * 1024 * 1024,  // 100GB
            free: 400 * 1024 * 1024 * 1024,  // 400GB
            usage_percent: 20.0,
        },
        network_info: NetworkInfo {
            connections: 150,
            bytes_sent: 1024 * 1024 * 1024, // 1GB
            bytes_received: 2 * 1024 * 1024 * 1024, // 2GB
        },
    }
}
