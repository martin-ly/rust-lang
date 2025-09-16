//! 模型提供商
//!
//! 提供不同 LLM 提供商的接口

use anyhow::Result;
use serde::{Deserialize, Serialize};

/// 提供商类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ProviderType {
    OpenAI,
    Anthropic,
    Google,
    Local,
}

/// 提供商配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProviderConfig {
    pub provider_type: ProviderType,
    pub api_key: Option<String>,
    pub base_url: Option<String>,
}

/// 提供商客户端 trait
pub trait ProviderClient {
    async fn list_models(&self) -> Result<Vec<String>>;
    async fn is_available(&self) -> Result<bool>;
}
