use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};
use uuid::Uuid;

/// 用户会话
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Session {
    pub id: Uuid,
    pub user_id: Uuid,
    pub token: String,
    pub refresh_token: String,
    pub expires_at: DateTime<Utc>,
    pub created_at: DateTime<Utc>,
    pub last_accessed: DateTime<Utc>,
    pub ip_address: Option<String>,
    pub user_agent: Option<String>,
    pub client_info: Option<String>,
    pub is_active: bool,
}

impl Session {
    pub fn new(user_id: Uuid, token: String, expires_at: DateTime<Utc>) -> Self {
        Self {
            id: Uuid::new_v4(),
            user_id,
            token: token.clone(),
            refresh_token: token,
            expires_at,
            created_at: Utc::now(),
            last_accessed: Utc::now(),
            ip_address: None,
            user_agent: None,
            client_info: None,
            is_active: true,
        }
    }
}
