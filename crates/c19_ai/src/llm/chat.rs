//! 聊天对话功能
//!
//! 提供与 LLM 进行对话的接口

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// 聊天消息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ChatMessage {
    /// 消息角色
    pub role: MessageRole,
    /// 消息内容
    pub content: String,
    /// 消息元数据
    pub metadata: Option<HashMap<String, serde_json::Value>>,
}

/// 消息角色
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MessageRole {
    /// 系统消息
    System,
    /// 用户消息
    User,
    /// 助手消息
    Assistant,
    /// 工具消息
    Tool,
}

/// 聊天会话
#[derive(Debug, Clone)]
pub struct ChatSession {
    /// 会话 ID
    pub id: String,
    /// 消息历史
    pub messages: Vec<ChatMessage>,
    /// 会话配置
    pub config: ChatConfig,
    /// 会话元数据
    pub metadata: HashMap<String, serde_json::Value>,
}

/// 聊天配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ChatConfig {
    /// 模型名称
    pub model: String,
    /// 温度参数
    pub temperature: Option<f32>,
    /// 最大令牌数
    pub max_tokens: Option<u32>,
    /// 停止序列
    pub stop_sequences: Option<Vec<String>>,
    /// 系统提示
    pub system_prompt: Option<String>,
    /// 流式响应
    pub stream: bool,
}

/// 聊天响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ChatResponse {
    /// 响应消息
    pub message: ChatMessage,
    /// 使用统计
    pub usage: Option<TokenUsage>,
    /// 响应元数据
    pub metadata: HashMap<String, serde_json::Value>,
}

/// 令牌使用统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TokenUsage {
    /// 提示令牌数
    pub prompt_tokens: u32,
    /// 完成令牌数
    pub completion_tokens: u32,
    /// 总令牌数
    pub total_tokens: u32,
}

/// 聊天客户端 trait
pub trait ChatClient {
    /// 发送聊天消息
    async fn chat(&self, session: &mut ChatSession, message: String) -> Result<ChatResponse>;

    /// 流式聊天
    async fn chat_stream(
        &self,
        session: &mut ChatSession,
        message: String,
    ) -> Result<Box<dyn Iterator<Item = Result<String>>>>;

    /// 获取可用模型列表
    async fn list_models(&self) -> Result<Vec<String>>;
}

impl ChatSession {
    /// 创建新的聊天会话
    pub fn new(id: String, config: ChatConfig) -> Self {
        Self {
            id,
            messages: Vec::new(),
            config,
            metadata: HashMap::new(),
        }
    }

    /// 添加消息
    pub fn add_message(&mut self, message: ChatMessage) {
        self.messages.push(message);
    }

    /// 添加系统消息
    pub fn add_system_message(&mut self, content: String) {
        let message = ChatMessage {
            role: MessageRole::System,
            content,
            metadata: None,
        };
        self.add_message(message);
    }

    /// 添加用户消息
    pub fn add_user_message(&mut self, content: String) {
        let message = ChatMessage {
            role: MessageRole::User,
            content,
            metadata: None,
        };
        self.add_message(message);
    }

    /// 添加助手消息
    pub fn add_assistant_message(&mut self, content: String) {
        let message = ChatMessage {
            role: MessageRole::Assistant,
            content,
            metadata: None,
        };
        self.add_message(message);
    }

    /// 获取会话摘要
    pub fn get_summary(&self) -> ChatSessionSummary {
        ChatSessionSummary {
            id: self.id.clone(),
            message_count: self.messages.len(),
            model: self.config.model.clone(),
            created_at: self
                .metadata
                .get("created_at")
                .and_then(|v| v.as_str())
                .unwrap_or("unknown")
                .to_string(),
        }
    }
}

/// 聊天会话摘要
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ChatSessionSummary {
    pub id: String,
    pub message_count: usize,
    pub model: String,
    pub created_at: String,
}

impl Default for ChatConfig {
    fn default() -> Self {
        Self {
            model: "gpt-3.5-turbo".to_string(),
            temperature: Some(0.7),
            max_tokens: Some(1000),
            stop_sequences: None,
            system_prompt: None,
            stream: false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_chat_session_creation() {
        let config = ChatConfig::default();
        let session = ChatSession::new("test-session".to_string(), config);

        assert_eq!(session.id, "test-session");
        assert_eq!(session.messages.len(), 0);
    }

    #[test]
    fn test_add_messages() {
        let mut session = ChatSession::new("test-session".to_string(), ChatConfig::default());

        session.add_user_message("Hello".to_string());
        session.add_assistant_message("Hi there!".to_string());

        assert_eq!(session.messages.len(), 2);
        assert!(matches!(session.messages[0].role, MessageRole::User));
        assert!(matches!(session.messages[1].role, MessageRole::Assistant));
    }
}
