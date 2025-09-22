// 训练调度器模块
use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};
use uuid::Uuid;

/// 训练调度器
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TrainingScheduler {
    pub id: Uuid,
    pub name: String,
    pub created_at: DateTime<Utc>,
}

impl TrainingScheduler {
    pub fn new(name: String) -> Self {
        Self {
            id: Uuid::new_v4(),
            name,
            created_at: Utc::now(),
        }
    }
}
