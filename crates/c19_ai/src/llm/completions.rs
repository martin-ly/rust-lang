//! 文本补全功能
//!
//! 提供文本补全和生成功能

use anyhow::Result;
use serde::{Deserialize, Serialize};

/// 补全请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompletionRequest {
    pub prompt: String,
    pub max_tokens: Option<u32>,
    pub temperature: Option<f32>,
    pub stop_sequences: Option<Vec<String>>,
}

/// 补全响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompletionResponse {
    pub text: String,
    pub usage: Option<TokenUsage>,
}

/// 令牌使用统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TokenUsage {
    pub prompt_tokens: u32,
    pub completion_tokens: u32,
    pub total_tokens: u32,
}

/// 补全客户端 trait
pub trait CompletionClient {
    async fn complete(&self, request: CompletionRequest) -> Result<CompletionResponse>;
}
