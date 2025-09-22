//! 文本补全接口
//! 
//! 提供与大语言模型的文本补全功能

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use uuid::Uuid;
use chrono::{DateTime, Utc};

/// 补全请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompletionRequest {
    pub id: Option<Uuid>,
    pub model: String,
    pub prompt: String,
    pub config: CompletionConfig,
    pub user_id: Option<String>,
    pub metadata: HashMap<String, serde_json::Value>,
}

/// 补全配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompletionConfig {
    pub temperature: f64,
    pub max_tokens: Option<usize>,
    pub top_p: Option<f64>,
    pub top_k: Option<usize>,
    pub frequency_penalty: Option<f64>,
    pub presence_penalty: Option<f64>,
    pub stop_sequences: Vec<String>,
    pub stream: bool,
    pub echo: bool,
    pub logprobs: Option<usize>,
    pub best_of: Option<usize>,
    pub suffix: Option<String>,
}

impl Default for CompletionConfig {
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
            echo: false,
            logprobs: None,
            best_of: None,
            suffix: None,
        }
    }
}

/// 补全响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompletionResponse {
    pub id: Uuid,
    pub model: String,
    pub choices: Vec<CompletionChoice>,
    pub usage: TokenUsage,
    pub created: DateTime<Utc>,
    pub metadata: HashMap<String, serde_json::Value>,
}

/// 补全选择
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompletionChoice {
    pub index: usize,
    pub text: String,
    pub finish_reason: FinishReason,
    pub logprobs: Option<LogProbs>,
}

/// 对数概率
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LogProbs {
    pub tokens: Vec<String>,
    pub token_logprobs: Vec<Option<f64>>,
    pub top_logprobs: Vec<Option<HashMap<String, f64>>>,
    pub text_offset: Vec<usize>,
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
    Other(String),
}

/// 流式补全响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StreamCompletionResponse {
    pub id: Uuid,
    pub model: String,
    pub choices: Vec<StreamCompletionChoice>,
    pub created: DateTime<Utc>,
}

/// 流式补全选择
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StreamCompletionChoice {
    pub index: usize,
    pub delta: CompletionDelta,
    pub finish_reason: Option<FinishReason>,
}

/// 补全增量
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompletionDelta {
    pub text: String,
    pub logprobs: Option<LogProbs>,
}

/// 补全管理器
#[derive(Debug)]
pub struct CompletionManager {
    providers: HashMap<String, Box<dyn CompletionProvider>>,
    default_config: CompletionConfig,
    request_history: HashMap<Uuid, CompletionRequest>,
}

/// 补全提供商接口
#[async_trait::async_trait]
pub trait CompletionProvider: Send + Sync {
    async fn complete(&self, request: CompletionRequest) -> Result<CompletionResponse>;
    async fn stream_complete(&self, request: CompletionRequest) -> Result<Vec<StreamCompletionResponse>>;
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
    Completion,
    Chat,
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

/// 补全统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompletionStats {
    pub total_requests: usize,
    pub total_tokens: usize,
    pub total_cost: f64,
    pub average_tokens_per_request: f64,
    pub success_rate: f64,
    pub error_rate: f64,
    pub last_updated: DateTime<Utc>,
}

/// 补全模板
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompletionTemplate {
    pub id: String,
    pub name: String,
    pub description: String,
    pub template: String,
    pub config: CompletionConfig,
    pub variables: Vec<TemplateVariable>,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

/// 模板变量
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TemplateVariable {
    pub name: String,
    pub description: String,
    pub required: bool,
    pub default_value: Option<String>,
    pub variable_type: VariableType,
}

/// 变量类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum VariableType {
    String,
    Number,
    Boolean,
    List,
    Object,
}

impl CompletionManager {
    /// 创建新的补全管理器
    pub fn new() -> Self {
        Self {
            providers: HashMap::new(),
            default_config: CompletionConfig::default(),
            request_history: HashMap::new(),
        }
    }

    /// 注册补全提供商
    pub fn register_provider(&mut self, name: String, provider: Box<dyn CompletionProvider>) {
        self.providers.insert(name, provider);
    }

    /// 执行文本补全
    pub async fn complete(&mut self, request: CompletionRequest) -> Result<CompletionResponse> {
        let request_id = request.id.unwrap_or_else(Uuid::new_v4);
        let mut request = request;
        request.id = Some(request_id);

        // 保存请求历史
        self.request_history.insert(request_id, request.clone());

        // 获取提供商
        let provider = self.get_provider_for_model(&request.model)?;

        // 执行补全
        let response = provider.complete(request).await?;

        Ok(response)
    }

    /// 流式执行文本补全
    pub async fn stream_complete(&mut self, request: CompletionRequest) -> Result<Vec<StreamCompletionResponse>> {
        let request_id = request.id.unwrap_or_else(Uuid::new_v4);
        let mut request = request;
        request.id = Some(request_id);

        // 保存请求历史
        self.request_history.insert(request_id, request.clone());

        // 获取提供商
        let provider = self.get_provider_for_model(&request.model)?;

        // 执行流式补全
        let responses = provider.stream_complete(request).await?;

        Ok(responses)
    }

    /// 使用模板执行补全
    pub async fn complete_with_template(
        &mut self,
        template_id: &str,
        variables: HashMap<String, String>,
        model: String,
        user_id: Option<String>,
    ) -> Result<CompletionResponse> {
        // 获取模板
        let template = self.get_template(template_id)?;

        // 渲染模板
        let prompt = self.render_template(&template, variables)?;

        // 创建请求
        let request = CompletionRequest {
            id: Some(Uuid::new_v4()),
            model,
            prompt,
            config: template.config.clone(),
            user_id,
            metadata: HashMap::new(),
        };

        // 执行补全
        self.complete(request).await
    }

    /// 获取提供商
    fn get_provider_for_model(&self, model_id: &str) -> Result<&dyn CompletionProvider> {
        // 简化实现：根据模型ID推断提供商
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

    /// 获取模板
    fn get_template(&self, template_id: &str) -> Result<CompletionTemplate> {
        // 简化实现：返回预定义模板
        match template_id {
            "code_completion" => Ok(CompletionTemplate {
                id: "code_completion".to_string(),
                name: "代码补全".to_string(),
                description: "用于代码补全的模板".to_string(),
                template: "请补全以下代码：\n\n{{code}}\n\n补全后的代码：".to_string(),
                config: CompletionConfig {
                    temperature: 0.1,
                    max_tokens: Some(1000),
                    top_p: Some(0.95),
                    top_k: Some(40),
                    frequency_penalty: Some(0.0),
                    presence_penalty: Some(0.0),
                    stop_sequences: vec!["```".to_string()],
                    stream: false,
                    echo: false,
                    logprobs: None,
                    best_of: None,
                    suffix: None,
                },
                variables: vec![TemplateVariable {
                    name: "code".to_string(),
                    description: "要补全的代码".to_string(),
                    required: true,
                    default_value: None,
                    variable_type: VariableType::String,
                }],
                created_at: Utc::now(),
                updated_at: Utc::now(),
            }),
            "text_summary" => Ok(CompletionTemplate {
                id: "text_summary".to_string(),
                name: "文本摘要".to_string(),
                description: "用于文本摘要的模板".to_string(),
                template: "请为以下文本生成摘要：\n\n{{text}}\n\n摘要：".to_string(),
                config: CompletionConfig {
                    temperature: 0.3,
                    max_tokens: Some(500),
                    top_p: Some(0.9),
                    top_k: Some(40),
                    frequency_penalty: Some(0.0),
                    presence_penalty: Some(0.0),
                    stop_sequences: vec![],
                    stream: false,
                    echo: false,
                    logprobs: None,
                    best_of: None,
                    suffix: None,
                },
                variables: vec![TemplateVariable {
                    name: "text".to_string(),
                    description: "要摘要的文本".to_string(),
                    required: true,
                    default_value: None,
                    variable_type: VariableType::String,
                }],
                created_at: Utc::now(),
                updated_at: Utc::now(),
            }),
            _ => Err(anyhow::anyhow!("Template not found: {}", template_id)),
        }
    }

    /// 渲染模板
    fn render_template(&self, template: &CompletionTemplate, variables: HashMap<String, String>) -> Result<String> {
        let mut prompt = template.template.clone();

        for variable in &template.variables {
            let value = variables.get(&variable.name)
                .or_else(|| variable.default_value.as_ref())
                .ok_or_else(|| anyhow::anyhow!("Missing required variable: {}", variable.name))?;

            prompt = prompt.replace(&format!("{{{{{}}}}}", variable.name), value);
        }

        Ok(prompt)
    }

    /// 获取请求历史
    pub fn get_request_history(&self, request_id: &Uuid) -> Option<&CompletionRequest> {
        self.request_history.get(request_id)
    }

    /// 获取所有请求历史
    pub fn get_all_request_history(&self) -> Vec<&CompletionRequest> {
        self.request_history.values().collect()
    }

    /// 清理请求历史
    pub fn cleanup_request_history(&mut self, max_age: std::time::Duration) -> usize {
        let cutoff_time = Utc::now() - chrono::Duration::from_std(max_age).unwrap_or_default();
        let mut to_remove = Vec::new();

        for (request_id, request) in &self.request_history {
            // 简化实现：假设请求时间在元数据中
            if let Some(created_at) = request.metadata.get("created_at") {
                if let Ok(created_at) = created_at.as_str() {
                    if let Ok(created_at) = DateTime::parse_from_rfc3339(created_at) {
                        if created_at.with_timezone(&Utc) < cutoff_time {
                            to_remove.push(*request_id);
                        }
                    }
                }
            }
        }

        for request_id in to_remove {
            self.request_history.remove(&request_id);
        }

        to_remove.len()
    }

    /// 获取统计信息
    pub fn get_stats(&self) -> CompletionStats {
        let total_requests = self.request_history.len();
        let total_tokens = 0; // TODO: 计算总令牌数
        let total_cost = 0.0; // TODO: 计算总成本
        let average_tokens_per_request = if total_requests > 0 {
            total_tokens as f64 / total_requests as f64
        } else {
            0.0
        };

        CompletionStats {
            total_requests,
            total_tokens,
            total_cost,
            average_tokens_per_request,
            success_rate: 1.0, // TODO: 计算成功率
            error_rate: 0.0,   // TODO: 计算错误率
            last_updated: Utc::now(),
        }
    }
}

impl Default for CompletionManager {
    fn default() -> Self {
        Self::new()
    }
}

/// 预定义补全配置
pub struct PresetCompletionConfigs;

impl PresetCompletionConfigs {
    /// 获取代码补全配置
    pub fn code_completion() -> CompletionConfig {
        CompletionConfig {
            temperature: 0.1,
            max_tokens: Some(1000),
            top_p: Some(0.95),
            top_k: Some(40),
            frequency_penalty: Some(0.0),
            presence_penalty: Some(0.0),
            stop_sequences: vec!["```".to_string()],
            stream: false,
            echo: false,
            logprobs: None,
            best_of: None,
            suffix: None,
        }
    }

    /// 获取创意写作配置
    pub fn creative_writing() -> CompletionConfig {
        CompletionConfig {
            temperature: 0.9,
            max_tokens: Some(2000),
            top_p: Some(0.9),
            top_k: Some(50),
            frequency_penalty: Some(0.1),
            presence_penalty: Some(0.1),
            stop_sequences: vec![],
            stream: false,
            echo: false,
            logprobs: None,
            best_of: None,
            suffix: None,
        }
    }

    /// 获取问答配置
    pub fn qa() -> CompletionConfig {
        CompletionConfig {
            temperature: 0.3,
            max_tokens: Some(1000),
            top_p: Some(0.9),
            top_k: Some(40),
            frequency_penalty: Some(0.0),
            presence_penalty: Some(0.0),
            stop_sequences: vec![],
            stream: false,
            echo: false,
            logprobs: None,
            best_of: None,
            suffix: None,
        }
    }

    /// 获取翻译配置
    pub fn translation() -> CompletionConfig {
        CompletionConfig {
            temperature: 0.2,
            max_tokens: Some(1000),
            top_p: Some(0.9),
            top_k: Some(40),
            frequency_penalty: Some(0.0),
            presence_penalty: Some(0.0),
            stop_sequences: vec![],
            stream: false,
            echo: false,
            logprobs: None,
            best_of: None,
            suffix: None,
        }
    }
}