//! API v1 路由
//! 
//! 定义v1版本的API端点

use axum::{
    routing::{get, post, put, delete},
    Router,
};
use crate::api::handlers::*;

/// 创建v1 API路由
pub fn create_v1_routes() -> Router {
    Router::new()
        // 健康检查
        .route("/health", get(health::HealthHandler::health_check))
        .route("/health/detailed", get(health::HealthHandler::detailed_health))
        .route("/ready", get(health::HealthHandler::readiness))
        .route("/live", get(health::HealthHandler::liveness))
        
        // 模型管理
        .route("/models", get(models::ModelHandler::list_models))
        .route("/models", post(models::ModelHandler::create_model))
        .route("/models/stats", get(models::ModelHandler::get_model_stats))
        .route("/models/search", get(models::ModelHandler::search_models))
        .route("/models/export", post(models::ModelHandler::export_models))
        .route("/models/batch", post(models::ModelHandler::batch_operation))
        .route("/models/:id", get(models::ModelHandler::get_model))
        .route("/models/:id", put(models::ModelHandler::update_model))
        .route("/models/:id", delete(models::ModelHandler::delete_model))
        
        // 训练任务
        .route("/training/jobs", get(training::TrainingHandler::list_training_jobs))
        .route("/training/jobs", post(training::TrainingHandler::create_training_job))
        .route("/training/jobs/stats", get(training::TrainingHandler::get_training_stats))
        .route("/training/jobs/batch", post(training::TrainingHandler::batch_operation))
        .route("/training/jobs/:id", get(training::TrainingHandler::get_training_job))
        .route("/training/jobs/:id/cancel", post(training::TrainingHandler::cancel_training_job))
        .route("/training/jobs/:id/restart", post(training::TrainingHandler::restart_training_job))
        .route("/training/jobs/:id/delete", delete(training::TrainingHandler::delete_training_job))
        .route("/training/jobs/:id/logs", get(training::TrainingHandler::get_training_job_logs))
        .route("/training/jobs/:id/metrics", get(training::TrainingHandler::get_training_job_metrics))
        .route("/training/jobs/:id/output", get(training::TrainingHandler::get_training_job_output))
        
        // 推理服务
        .route("/inference", post(inference::InferenceHandler::inference))
        .route("/inference/batch", post(inference::InferenceHandler::batch_inference))
        .route("/inference/history", get(inference::InferenceHandler::get_inference_history))
        .route("/inference/stats", get(inference::InferenceHandler::get_inference_stats))
        .route("/inference/models", get(inference::InferenceHandler::get_available_models))
        .route("/inference/queue", get(inference::InferenceHandler::get_inference_queue_status))
        .route("/inference/models/:id/performance", get(inference::InferenceHandler::get_model_performance))
        .route("/inference/models/:id/warmup", post(inference::InferenceHandler::warmup_model))
        
        // 数据集管理
        .route("/datasets", get(datasets::DatasetHandler::list_datasets))
        .route("/datasets", post(datasets::DatasetHandler::create_dataset))
        .route("/datasets/stats", get(datasets::DatasetHandler::get_dataset_stats))
        .route("/datasets/:id", get(datasets::DatasetHandler::get_dataset))
        .route("/datasets/:id", delete(datasets::DatasetHandler::delete_dataset))
        
        // 指标管理
        .route("/metrics", get(metrics::MetricsHandler::list_metrics))
        .route("/metrics", post(metrics::MetricsHandler::record_metric))
        .route("/metrics/stats", get(metrics::MetricsHandler::get_metrics_stats))
        .route("/metrics/trend", get(metrics::MetricsHandler::get_metrics_trend))
        
        // 系统管理
        .route("/system/status", get(system::SystemHandler::get_system_status))
        .route("/system/stats", get(system::SystemHandler::get_system_statistics))
        .route("/system/config", get(system::SystemHandler::get_system_config))
        .route("/system/config", put(system::SystemHandler::update_system_config))
        .route("/system/logs", get(system::SystemHandler::get_system_logs))
        .route("/system/restart", post(system::SystemHandler::restart_system))
        .route("/system/resources", get(system::SystemHandler::get_resource_usage))
        .route("/system/version", get(system::SystemHandler::get_version_info))
        
        // 日志管理
        .route("/logs", post(logs::LogHandler::query_logs))
        .route("/logs/stats", get(logs::LogHandler::get_log_stats))
        .route("/logs/export", post(logs::LogHandler::export_logs))
        
        // 配置管理
        .route("/config", get(config::ConfigHandler::list_configs))
        .route("/config/:key", get(config::ConfigHandler::get_config))
        .route("/config/:key", put(config::ConfigHandler::update_config))
        .route("/config/:key", delete(config::ConfigHandler::delete_config))
        .route("/config/reset", post(config::ConfigHandler::reset_configs))
}
