// 模型部署模块
use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};
use uuid::Uuid;

/// 模型部署
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModelDeployment {
    pub id: Uuid,
    pub model_id: String,
    pub environment: String,
    pub status: DeploymentStatus,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DeploymentStatus {
    Pending,
    Deploying,
    Active,
    Failed,
    Stopped,
}

impl ModelDeployment {
    pub fn new(model_id: String, environment: String) -> Self {
        Self {
            id: Uuid::new_v4(),
            model_id,
            environment,
            status: DeploymentStatus::Pending,
            created_at: Utc::now(),
            updated_at: Utc::now(),
        }
    }
}
