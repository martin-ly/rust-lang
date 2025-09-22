// 数据性能分析器模块
use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};
use uuid::Uuid;

/// 数据性能分析器
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DataProfiler {
    pub id: Uuid,
    pub name: String,
    pub created_at: DateTime<Utc>,
}

impl DataProfiler {
    pub fn new(name: String) -> Self {
        Self {
            id: Uuid::new_v4(),
            name,
            created_at: Utc::now(),
        }
    }
}
