// 模型版本管理模块
use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};
use uuid::Uuid;

/// 模型版本
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModelVersion {
    pub id: Uuid,
    pub model_id: String,
    pub version: String,
    pub created_at: DateTime<Utc>,
    pub metadata: serde_json::Value,
}

impl ModelVersion {
    pub fn new(model_id: String, version: String) -> Self {
        Self {
            id: Uuid::new_v4(),
            model_id,
            version,
            created_at: Utc::now(),
            metadata: serde_json::Value::Null,
        }
    }
}
