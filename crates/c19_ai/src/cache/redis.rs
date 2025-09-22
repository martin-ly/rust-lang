// Redis缓存模块
use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};
use uuid::Uuid;

/// Redis缓存
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RedisCache {
    pub id: Uuid,
    pub name: String,
    pub created_at: DateTime<Utc>,
}

impl RedisCache {
    pub fn new(name: String) -> Self {
        Self {
            id: Uuid::new_v4(),
            name,
            created_at: Utc::now(),
        }
    }
}
