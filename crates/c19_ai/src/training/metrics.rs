// 训练指标模块
use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};
use uuid::Uuid;

/// 训练指标
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TrainingMetrics {
    pub id: Uuid,
    pub job_id: String,
    pub timestamp: DateTime<Utc>,
    pub loss: f64,
    pub accuracy: f64,
}

impl TrainingMetrics {
    pub fn new(job_id: String) -> Self {
        Self {
            id: Uuid::new_v4(),
            job_id,
            timestamp: Utc::now(),
            loss: 0.0,
            accuracy: 0.0,
        }
    }
}

impl Default for TrainingMetrics {
    fn default() -> Self {
        Self {
            id: Uuid::new_v4(),
            job_id: "default".to_string(),
            timestamp: Utc::now(),
            loss: 0.0,
            accuracy: 0.0,
        }
    }
}

impl TrainingMetrics {
    pub fn record_metric(&mut self, name: &str, value: f64) {
        match name {
            "loss" => self.loss = value,
            "accuracy" => self.accuracy = value,
            _ => {} // Ignore unknown metrics
        }
    }
}
