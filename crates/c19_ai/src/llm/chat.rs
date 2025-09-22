//! 聊天接口
//! 
//! 提供与大语言模型的聊天对话功能

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use uuid::Uuid;
use chrono::{DateTime, Utc};

/// 聊天会话
#[derive(Debug, Clone)]
pub struct ChatSession {
    pub id: Uuid,
    pub user_id: Option<String>,
    pub model_id: String,
    pub messages: Vec<ChatMessage>,
    pub config: ChatConfig,
    pub metadata: HashMap<String, serde_json::Value>,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

/// 聊天消息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ChatMessage {
    pub id: Uuid,
    pub role: MessageRole,
    pub content: String,
    pub timestamp: DateTime<Utc>,
    pub metadata: HashMap<String, serde_json::Value>,
}

/// 消息角色
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MessageRole {
    System,
    User,
    Assistant,
    Function,
}

/// 聊天配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ChatConfig {
    pub temperature: f64,
    pub max_tokens: Option<usize>,
    pub top_p: Option<f64>,
    pub top_k: Option<usize>,
    pub frequency_penalty: Option<f64>,
    pub presence_penalty: Option<f64>,
    pub stop_sequences: Vec<String>,
    pub stream: bool,
    pub system_prompt: Option<String>,
}

impl Default for ChatConfig {
    fn default() -> Self {
        Self {
            temperature: 0.7,
            max_tokens: Some(1000),
            top_p: Some(1.0),
            top_k: None,
            frequency_penalty: Some(0.0),
            presence_penalty: Some(0.0),
            stop_sequences: vec![],
            stream: false,
            system_prompt: None,
        }
    }
}

/// 聊天请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ChatRequest {
    pub session_id: Option<Uuid>,
    pub model_id: String,
    pub messages: Vec<ChatMessage>,
    pub config: ChatConfig,
    pub user_id: Option<String>,
}

/// 聊天响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ChatResponse {
    pub id: Uuid,
    pub session_id: Uuid,
    pub message: ChatMessage,
    pub usage: TokenUsage,
    pub finish_reason: FinishReason,
    pub model: String,
    pub timestamp: DateTime<Utc>,
}

/// 令牌使用情况
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TokenUsage {
    pub prompt_tokens: usize,
    pub completion_tokens: usize,
    pub total_tokens: usize,
}

/// 完成原因
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum FinishReason {
    Stop,
    Length,
    ContentFilter,
    FunctionCall,
    ToolCall,
    Other(String),
}

/// 流式聊天响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StreamChatResponse {
    pub id: Uuid,
    pub session_id: Uuid,
    pub delta: String,
    pub finish_reason: Option<FinishReason>,
    pub usage: Option<TokenUsage>,
    pub timestamp: DateTime<Utc>,
}

/// 聊天管理器
#[derive(Debug)]
pub struct ChatManager {
    sessions: HashMap<Uuid, ChatSession>,
    providers: HashMap<String, Box<dyn ChatProvider>>,
    default_config: ChatConfig,
}

/// 聊天提供商接口
#[async_trait::async_trait]
pub trait ChatProvider: Send + Sync {
    async fn chat(&self, request: ChatRequest) -> Result<ChatResponse>;
    async fn stream_chat(&self, request: ChatRequest) -> Result<Vec<StreamChatResponse>>;
    async fn get_models(&self) -> Result<Vec<String>>;
    async fn get_model_info(&self, model_id: &str) -> Result<ModelInfo>;
}

/// 模型信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModelInfo {
    pub id: String,
    pub name: String,
    pub provider: String,
    pub description: Option<String>,
    pub max_tokens: Option<usize>,
    pub context_length: Option<usize>,
    pub capabilities: Vec<ModelCapability>,
    pub pricing: Option<PricingInfo>,
}

/// 模型能力
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ModelCapability {
    Chat,
    Completion,
    Embedding,
    FunctionCalling,
    Vision,
    CodeGeneration,
    Reasoning,
    Custom(String),
}

/// 定价信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PricingInfo {
    pub input_price_per_1k_tokens: f64,
    pub output_price_per_1k_tokens: f64,
    pub currency: String,
}

/// 函数调用
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionCall {
    pub name: String,
    pub arguments: HashMap<String, serde_json::Value>,
}

/// 工具调用
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ToolCall {
    pub id: String,
    pub function: FunctionCall,
}

/// 聊天会话统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ChatSessionStats {
    pub session_id: Uuid,
    pub message_count: usize,
    pub total_tokens: usize,
    pub total_cost: f64,
    pub duration: std::time::Duration,
    pub created_at: DateTime<Utc>,
    pub last_activity: DateTime<Utc>,
}

impl ChatSession {
    /// 创建新的聊天会话
    pub fn new(user_id: Option<String>, model_id: String, config: ChatConfig) -> Self {
        Self {
            id: Uuid::new_v4(),
            user_id,
            model_id,
            messages: Vec::new(),
            config,
            metadata: HashMap::new(),
            created_at: Utc::now(),
            updated_at: Utc::now(),
        }
    }

    /// 添加消息
    pub fn add_message(&mut self, role: MessageRole, content: String) {
        let message = ChatMessage {
            id: Uuid::new_v4(),
            role,
            content,
            timestamp: Utc::now(),
            metadata: HashMap::new(),
        };
        self.messages.push(message);
        self.updated_at = Utc::now();
    }

    /// 添加系统消息
    pub fn add_system_message(&mut self, content: String) {
        self.add_message(MessageRole::System, content);
    }

    /// 添加用户消息
    pub fn add_user_message(&mut self, content: String) {
        self.add_message(MessageRole::User, content);
    }

    /// 添加助手消息
    pub fn add_assistant_message(&mut self, content: String) {
        self.add_message(MessageRole::Assistant, content);
    }

    /// 获取最后一条消息
    pub fn get_last_message(&self) -> Option<&ChatMessage> {
        self.messages.last()
    }

    /// 获取消息数量
    pub fn message_count(&self) -> usize {
        self.messages.len()
    }

    /// 清空消息历史
    pub fn clear_messages(&mut self) {
        self.messages.clear();
        self.updated_at = Utc::now();
    }

    /// 设置元数据
    pub fn set_metadata(&mut self, key: String, value: serde_json::Value) {
        self.metadata.insert(key, value);
        self.updated_at = Utc::now();
    }

    /// 获取元数据
    pub fn get_metadata(&self, key: &str) -> Option<&serde_json::Value> {
        self.metadata.get(key)
    }

    /// 更新配置
    pub fn update_config(&mut self, config: ChatConfig) {
        self.config = config;
        self.updated_at = Utc::now();
    }
}

impl ChatManager {
    /// 创建新的聊天管理器
    pub fn new() -> Self {
        Self {
            sessions: HashMap::new(),
            providers: HashMap::new(),
            default_config: ChatConfig::default(),
        }
    }

    /// 注册聊天提供商
    pub fn register_provider(&mut self, name: String, provider: Box<dyn ChatProvider>) {
        self.providers.insert(name, provider);
    }

    /// 创建聊天会话
    pub fn create_session(&mut self, user_id: Option<String>, model_id: String, config: Option<ChatConfig>) -> ChatSession {
        let config = config.unwrap_or_else(|| self.default_config.clone());
        let session = ChatSession::new(user_id, model_id, config);
        let session_id = session.id;
        self.sessions.insert(session_id, session);
        self.sessions.get(&session_id).unwrap().clone()
    }

    /// 获取聊天会话
    pub fn get_session(&self, session_id: &Uuid) -> Option<&ChatSession> {
        self.sessions.get(session_id)
    }

    /// 获取用户的所有会话
    pub fn get_user_sessions(&self, user_id: &str) -> Vec<&ChatSession> {
        self.sessions
            .values()
            .filter(|session| session.user_id.as_ref() == Some(user_id))
            .collect()
    }

    /// 删除聊天会话
    pub fn delete_session(&mut self, session_id: &Uuid) -> Option<ChatSession> {
        self.sessions.remove(session_id)
    }

    /// 发送聊天消息
    pub async fn send_message(&mut self, session_id: &Uuid, content: String) -> Result<ChatResponse> {
        let session = self.sessions.get_mut(session_id)
            .ok_or_else(|| anyhow::anyhow!("Session not found"))?;

        // 添加用户消息
        session.add_user_message(content);

        // 创建聊天请求
        let request = ChatRequest {
            session_id: Some(*session_id),
            model_id: session.model_id.clone(),
            messages: session.messages.clone(),
            config: session.config.clone(),
            user_id: session.user_id.clone(),
        };

        // 获取提供商
        let provider = self.get_provider_for_model(&session.model_id)?;

        // 发送请求
        let response = provider.chat(request).await?;

        // 添加助手消息到会话
        session.add_assistant_message(response.message.content.clone());

        Ok(response)
    }

    /// 流式发送聊天消息
    pub async fn stream_message(&mut self, session_id: &Uuid, content: String) -> Result<Vec<StreamChatResponse>> {
        let session = self.sessions.get_mut(session_id)
            .ok_or_else(|| anyhow::anyhow!("Session not found"))?;

        // 添加用户消息
        session.add_user_message(content);

        // 创建聊天请求
        let request = ChatRequest {
            session_id: Some(*session_id),
            model_id: session.model_id.clone(),
            messages: session.messages.clone(),
            config: session.config.clone(),
            user_id: session.user_id.clone(),
        };

        // 获取提供商
        let provider = self.get_provider_for_model(&session.model_id)?;

        // 发送流式请求
        let responses = provider.stream_chat(request).await?;

        // 合并所有流式响应内容
        let full_content = responses.iter()
            .map(|r| r.delta.clone())
            .collect::<Vec<_>>()
            .join("");

        // 添加助手消息到会话
        session.add_assistant_message(full_content);

        Ok(responses)
    }

    /// 获取提供商
    fn get_provider_for_model(&self, model_id: &str) -> Result<&dyn ChatProvider> {
        // 简化实现：根据模型ID推断提供商
        // 实际实现应该维护模型到提供商的映射
        if model_id.starts_with("gpt-") {
            self.providers.get("openai")
                .map(|p| p.as_ref())
                .ok_or_else(|| anyhow::anyhow!("OpenAI provider not found"))
        } else if model_id.starts_with("claude-") {
            self.providers.get("anthropic")
                .map(|p| p.as_ref())
                .ok_or_else(|| anyhow::anyhow!("Anthropic provider not found"))
        } else {
            Err(anyhow::anyhow!("Unknown model: {}", model_id))
        }
    }

    /// 获取会话统计信息
    pub fn get_session_stats(&self, session_id: &Uuid) -> Option<ChatSessionStats> {
        if let Some(session) = self.sessions.get(session_id) {
            let duration = Utc::now().signed_duration_since(session.created_at).to_std().unwrap_or_default();
            Some(ChatSessionStats {
                session_id: *session_id,
                message_count: session.messages.len(),
                total_tokens: 0, // TODO: 计算总令牌数
                total_cost: 0.0, // TODO: 计算总成本
                duration,
                created_at: session.created_at,
                last_activity: session.updated_at,
            })
        } else {
            None
        }
    }

    /// 清理过期会话
    pub fn cleanup_expired_sessions(&mut self, max_age: std::time::Duration) -> usize {
        let cutoff_time = Utc::now() - chrono::Duration::from_std(max_age).unwrap_or_default();
        let mut to_remove = Vec::new();

        for (session_id, session) in &self.sessions {
            if session.updated_at < cutoff_time {
                to_remove.push(*session_id);
            }
        }

        for session_id in to_remove {
            self.sessions.remove(&session_id);
        }

        to_remove.len()
    }

    /// 获取所有会话
    pub fn get_all_sessions(&self) -> Vec<&ChatSession> {
        self.sessions.values().collect()
    }

    /// 获取会话数量
    pub fn session_count(&self) -> usize {
        self.sessions.len()
    }
}

impl Default for ChatManager {
    fn default() -> Self {
        Self::new()
    }
}

/// 预定义聊天配置
pub struct PresetChatConfigs;

impl PresetChatConfigs {
    /// 获取创意写作配置
    pub fn creative_writing() -> ChatConfig {
        ChatConfig {
            temperature: 0.9,
            max_tokens: Some(2000),
            top_p: Some(0.9),
            top_k: Some(50),
            frequency_penalty: Some(0.1),
            presence_penalty: Some(0.1),
            stop_sequences: vec![],
            stream: false,
            system_prompt: Some("You are a creative writing assistant. Help users with creative writing tasks, story development, character creation, and other creative endeavors.".to_string()),
        }
    }

    /// 获取代码生成配置
    pub fn code_generation() -> ChatConfig {
        ChatConfig {
            temperature: 0.1,
            max_tokens: Some(4000),
            top_p: Some(0.95),
            top_k: Some(40),
            frequency_penalty: Some(0.0),
            presence_penalty: Some(0.0),
            stop_sequences: vec!["```".to_string()],
            stream: false,
            system_prompt: Some("You are a helpful coding assistant. Provide clear, well-commented code solutions and explanations.".to_string()),
        }
    }

    /// 获取问答配置
    pub fn qa() -> ChatConfig {
        ChatConfig {
            temperature: 0.3,
            max_tokens: Some(1000),
            top_p: Some(0.9),
            top_k: Some(40),
            frequency_penalty: Some(0.0),
            presence_penalty: Some(0.0),
            stop_sequences: vec![],
            stream: false,
            system_prompt: Some("You are a helpful assistant. Provide accurate, concise answers to user questions.".to_string()),
        }
    }

    /// 获取对话配置
    pub fn conversation() -> ChatConfig {
        ChatConfig {
            temperature: 0.7,
            max_tokens: Some(1500),
            top_p: Some(0.9),
            top_k: Some(50),
            frequency_penalty: Some(0.1),
            presence_penalty: Some(0.1),
            stop_sequences: vec![],
            stream: false,
            system_prompt: Some("You are a friendly, helpful assistant. Engage in natural conversation with users.".to_string()),
        }
    }
}