// 数据质量模块
use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};
use uuid::Uuid;

/// 数据质量评估器
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DataQuality {
    pub id: Uuid,
    pub name: String,
    pub created_at: DateTime<Utc>,
}

impl DataQuality {
    pub fn new(name: String) -> Self {
        Self {
            id: Uuid::new_v4(),
            name,
            created_at: Utc::now(),
        }
    }
}
