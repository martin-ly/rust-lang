use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};
use uuid::Uuid;

/// OAuth Provider
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum OAuthProvider {
    Google,
    GitHub,
    Microsoft,
    Apple,
    Custom(String),
}

/// OAuth Token
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OAuthToken {
    pub id: Uuid,
    pub user_id: Uuid,
    pub provider: OAuthProvider,
    pub access_token: String,
    pub refresh_token: Option<String>,
    pub expires_at: Option<DateTime<Utc>>,
    pub scope: Vec<String>,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

impl OAuthToken {
    pub fn new(
        user_id: Uuid,
        provider: OAuthProvider,
        access_token: String,
        refresh_token: Option<String>,
        expires_at: Option<DateTime<Utc>>,
        scope: Vec<String>,
    ) -> Self {
        Self {
            id: Uuid::new_v4(),
            user_id,
            provider,
            access_token,
            refresh_token,
            expires_at,
            scope,
            created_at: Utc::now(),
            updated_at: Utc::now(),
        }
    }
}
