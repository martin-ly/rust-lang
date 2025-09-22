// 数据库迁移模块
use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};
use uuid::Uuid;

/// 数据库迁移
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DatabaseMigration {
    pub id: Uuid,
    pub version: String,
    pub created_at: DateTime<Utc>,
}

impl DatabaseMigration {
    pub fn new(version: String) -> Self {
        Self {
            id: Uuid::new_v4(),
            version,
            created_at: Utc::now(),
        }
    }
}
