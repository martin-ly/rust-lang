// 数据库模型模块
use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};
use uuid::Uuid;

/// 数据库模型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DatabaseModel {
    pub id: Uuid,
    pub name: String,
    pub created_at: DateTime<Utc>,
}

impl DatabaseModel {
    pub fn new(name: String) -> Self {
        Self {
            id: Uuid::new_v4(),
            name,
            created_at: Utc::now(),
        }
    }
}
