// 数据验证器模块
use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};
use uuid::Uuid;

/// 数据验证器
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DataValidator {
    pub id: Uuid,
    pub name: String,
    pub created_at: DateTime<Utc>,
}

impl DataValidator {
    pub fn new(name: String) -> Self {
        Self {
            id: Uuid::new_v4(),
            name,
            created_at: Utc::now(),
        }
    }
}
