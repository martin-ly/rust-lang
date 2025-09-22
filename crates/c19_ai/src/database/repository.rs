// 数据库仓库模块
use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};
use uuid::Uuid;

/// 数据库仓库
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DatabaseRepository {
    pub id: Uuid,
    pub name: String,
    pub created_at: DateTime<Utc>,
}

impl DatabaseRepository {
    pub fn new(name: String) -> Self {
        Self {
            id: Uuid::new_v4(),
            name,
            created_at: Utc::now(),
        }
    }
}
