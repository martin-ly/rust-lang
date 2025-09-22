//! 提供商管理
//! 
//! 提供大语言模型提供商的管理和配置功能

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use uuid::Uuid;
use chrono::{DateTime, Utc};

/// 提供商信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Provider {
    pub id: String,
    pub name: String,
    pub description: Option<String>,
    pub provider_type: ProviderType,
    pub base_url: String,
    pub api_version: Option<String>,
    pub authentication: AuthenticationConfig,
    pub rate_limits: RateLimits,
    pub supported_models: Vec<String>,
    pub capabilities: Vec<ProviderCapability>,
    pub status: ProviderStatus,
    pub metadata: HashMap<String, serde_json::Value>,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

/// 提供商类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ProviderType {
    OpenAI,
    Anthropic,
    Google,
    Azure,
    AWS,
    HuggingFace,
    Local,
    Custom(String),
}

/// 认证配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuthenticationConfig {
    pub auth_type: AuthType,
    pub api_key: Option<String>,
    pub api_secret: Option<String>,
    pub access_token: Option<String>,
    pub refresh_token: Option<String>,
    pub client_id: Option<String>,
    pub client_secret: Option<String>,
    pub organization_id: Option<String>,
    pub project_id: Option<String>,
    pub region: Option<String>,
    pub endpoint: Option<String>,
    pub custom_headers: HashMap<String, String>,
}

/// 认证类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AuthType {
    ApiKey,
    BearerToken,
    OAuth2,
    AwsSignature,
    AzureKey,
    Custom(String),
}

/// 速率限制
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RateLimits {
    pub requests_per_minute: Option<usize>,
    pub requests_per_hour: Option<usize>,
    pub requests_per_day: Option<usize>,
    pub tokens_per_minute: Option<usize>,
    pub tokens_per_hour: Option<usize>,
    pub tokens_per_day: Option<usize>,
    pub concurrent_requests: Option<usize>,
    pub burst_limit: Option<usize>,
}

/// 提供商能力
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ProviderCapability {
    Chat,
    Completion,
    Embedding,
    FunctionCalling,
    Vision,
    CodeGeneration,
    Reasoning,
    Multimodal,
    Streaming,
    BatchProcessing,
    Custom(String),
}

/// 提供商状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ProviderStatus {
    Active,
    Inactive,
    Maintenance,
    Error,
    RateLimited,
    Custom(String),
}

/// 提供商管理器
#[derive(Debug)]
pub struct ProviderManager {
    providers: HashMap<String, Provider>,
    active_providers: HashMap<String, String>,
    provider_stats: HashMap<String, ProviderStats>,
    rate_limit_tracker: HashMap<String, RateLimitTracker>,
}

/// 提供商统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProviderStats {
    pub provider_id: String,
    pub total_requests: usize,
    pub successful_requests: usize,
    pub failed_requests: usize,
    pub total_tokens: usize,
    pub total_cost: f64,
    pub average_response_time: f64,
    pub last_request: Option<DateTime<Utc>>,
    pub uptime: f64,
    pub error_rate: f64,
    pub success_rate: f64,
}

/// 速率限制跟踪器
#[derive(Debug, Clone)]
pub struct RateLimitTracker {
    pub provider_id: String,
    pub request_counts: HashMap<String, usize>,
    pub token_counts: HashMap<String, usize>,
    pub last_reset: DateTime<Utc>,
    pub window_size: std::time::Duration,
}

/// 提供商配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProviderConfig {
    pub name: String,
    pub description: Option<String>,
    pub provider_type: ProviderType,
    pub base_url: String,
    pub api_version: Option<String>,
    pub authentication: AuthenticationConfig,
    pub rate_limits: RateLimits,
    pub supported_models: Vec<String>,
    pub capabilities: Vec<ProviderCapability>,
    pub metadata: HashMap<String, serde_json::Value>,
}

impl ProviderManager {
    /// 创建新的提供商管理器
    pub fn new() -> Self {
        Self {
            providers: HashMap::new(),
            active_providers: HashMap::new(),
            provider_stats: HashMap::new(),
            rate_limit_tracker: HashMap::new(),
        }
    }

    /// 注册提供商
    pub fn register_provider(&mut self, config: ProviderConfig) -> Result<()> {
        let provider = Provider {
            id: Uuid::new_v4().to_string(),
            name: config.name,
            description: config.description,
            provider_type: config.provider_type,
            base_url: config.base_url,
            api_version: config.api_version,
            authentication: config.authentication,
            rate_limits: config.rate_limits,
            supported_models: config.supported_models,
            capabilities: config.capabilities,
            status: ProviderStatus::Active,
            metadata: config.metadata,
            created_at: Utc::now(),
            updated_at: Utc::now(),
        };

        let provider_id = provider.id.clone();
        self.providers.insert(provider_id.clone(), provider);

        // 初始化统计信息
        self.provider_stats.insert(provider_id.clone(), ProviderStats {
            provider_id: provider_id.clone(),
            total_requests: 0,
            successful_requests: 0,
            failed_requests: 0,
            total_tokens: 0,
            total_cost: 0.0,
            average_response_time: 0.0,
            last_request: None,
            uptime: 100.0,
            error_rate: 0.0,
            success_rate: 100.0,
        });

        // 初始化速率限制跟踪器
        self.rate_limit_tracker.insert(provider_id, RateLimitTracker {
            provider_id: provider_id.clone(),
            request_counts: HashMap::new(),
            token_counts: HashMap::new(),
            last_reset: Utc::now(),
            window_size: std::time::Duration::from_secs(60),
        });

        Ok(())
    }

    /// 获取提供商
    pub fn get_provider(&self, provider_id: &str) -> Option<&Provider> {
        self.providers.get(provider_id)
    }

    /// 获取所有提供商
    pub fn get_all_providers(&self) -> Vec<&Provider> {
        self.providers.values().collect()
    }

    /// 按类型获取提供商
    pub fn get_providers_by_type(&self, provider_type: &ProviderType) -> Vec<&Provider> {
        self.providers.values()
            .filter(|provider| std::mem::discriminant(&provider.provider_type) == std::mem::discriminant(provider_type))
            .collect()
    }

    /// 按状态获取提供商
    pub fn get_providers_by_status(&self, status: &ProviderStatus) -> Vec<&Provider> {
        self.providers.values()
            .filter(|provider| std::mem::discriminant(&provider.status) == std::mem::discriminant(status))
            .collect()
    }

    /// 按能力获取提供商
    pub fn get_providers_by_capability(&self, capability: &ProviderCapability) -> Vec<&Provider> {
        self.providers.values()
            .filter(|provider| provider.capabilities.contains(capability))
            .collect()
    }

    /// 按模型获取提供商
    pub fn get_providers_by_model(&self, model_id: &str) -> Vec<&Provider> {
        self.providers.values()
            .filter(|provider| provider.supported_models.contains(&model_id.to_string()))
            .collect()
    }

    /// 获取提供商统计信息
    pub fn get_provider_stats(&self, provider_id: &str) -> Option<&ProviderStats> {
        self.provider_stats.get(provider_id)
    }

    /// 获取所有提供商统计信息
    pub fn get_all_provider_stats(&self) -> Vec<&ProviderStats> {
        self.provider_stats.values().collect()
    }

    /// 记录请求
    pub fn record_request(&mut self, provider_id: &str, success: bool, tokens: usize, cost: f64, response_time: f64) {
        if let Some(stats) = self.provider_stats.get_mut(provider_id) {
            stats.total_requests += 1;
            if success {
                stats.successful_requests += 1;
            } else {
                stats.failed_requests += 1;
            }
            stats.total_tokens += tokens;
            stats.total_cost += cost;
            stats.last_request = Some(Utc::now());
            
            // 更新平均响应时间
            stats.average_response_time = (stats.average_response_time * (stats.total_requests - 1) as f64 + response_time) / stats.total_requests as f64;
            
            // 更新成功率
            stats.success_rate = (stats.successful_requests as f64 / stats.total_requests as f64) * 100.0;
            stats.error_rate = (stats.failed_requests as f64 / stats.total_requests as f64) * 100.0;
        }
    }

    /// 获取提供商数量
    pub fn provider_count(&self) -> usize {
        self.providers.len()
    }

    /// 获取活跃提供商数量
    pub fn active_provider_count(&self) -> usize {
        self.providers.values()
            .filter(|provider| provider.status == ProviderStatus::Active)
            .count()
    }
}

impl Default for ProviderManager {
    fn default() -> Self {
        Self::new()
    }
}