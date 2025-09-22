// 模型监控模块
use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};
use uuid::Uuid;

/// 模型监控指标
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModelMetrics {
    pub id: Uuid,
    pub model_id: String,
    pub timestamp: DateTime<Utc>,
    pub accuracy: f64,
    pub latency: f64,
    pub throughput: f64,
    pub memory_usage: f64,
}

impl ModelMetrics {
    pub fn new(model_id: String) -> Self {
        Self {
            id: Uuid::new_v4(),
            model_id,
            timestamp: Utc::now(),
            accuracy: 0.0,
            latency: 0.0,
            throughput: 0.0,
            memory_usage: 0.0,
        }
    }
}
