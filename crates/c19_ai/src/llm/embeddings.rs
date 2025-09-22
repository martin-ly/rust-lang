//! 嵌入接口
//! 
//! 提供与大语言模型的文本嵌入功能

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use uuid::Uuid;
use chrono::{DateTime, Utc};

/// 嵌入请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EmbeddingRequest {
    pub id: Option<Uuid>,
    pub model: String,
    pub input: EmbeddingInput,
    pub config: EmbeddingConfig,
    pub user_id: Option<String>,
    pub metadata: HashMap<String, serde_json::Value>,
}

/// 嵌入输入
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum EmbeddingInput {
    Text(String),
    Texts(Vec<String>),
    Tokens(Vec<usize>),
    TokenBatches(Vec<Vec<usize>>),
}

/// 嵌入配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EmbeddingConfig {
    pub dimensions: Option<usize>,
    pub encoding_format: EncodingFormat,
    pub normalize: bool,
    pub batch_size: Option<usize>,
    pub max_retries: Option<usize>,
    pub timeout: Option<std::time::Duration>,
}

impl Default for EmbeddingConfig {
    fn default() -> Self {
        Self {
            dimensions: None,
            encoding_format: EncodingFormat::Float,
            normalize: false,
            batch_size: Some(100),
            max_retries: Some(3),
            timeout: Some(std::time::Duration::from_secs(30)),
        }
    }
}

/// 编码格式
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum EncodingFormat {
    Float,
    Base64,
}

/// 嵌入响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EmbeddingResponse {
    pub id: Uuid,
    pub model: String,
    pub data: Vec<EmbeddingData>,
    pub usage: TokenUsage,
    pub created: DateTime<Utc>,
    pub metadata: HashMap<String, serde_json::Value>,
}

/// 嵌入数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EmbeddingData {
    pub index: usize,
    pub embedding: Embedding,
    pub input_text: Option<String>,
    pub metadata: HashMap<String, serde_json::Value>,
}

/// 嵌入向量
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Embedding {
    pub values: Vec<f32>,
    pub dimensions: usize,
    pub encoding_format: EncodingFormat,
}

impl Embedding {
    /// 创建新的嵌入向量
    pub fn new(values: Vec<f32>, encoding_format: EncodingFormat) -> Self {
        let dimensions = values.len();
        Self {
            values,
            dimensions,
            encoding_format,
        }
    }

    /// 计算余弦相似度
    pub fn cosine_similarity(&self, other: &Embedding) -> Result<f32> {
        if self.dimensions != other.dimensions {
            return Err(anyhow::anyhow!("Dimension mismatch"));
        }

        let dot_product: f32 = self.values
            .iter()
            .zip(other.values.iter())
            .map(|(a, b)| a * b)
            .sum();

        let norm_a: f32 = self.values.iter().map(|x| x * x).sum::<f32>().sqrt();
        let norm_b: f32 = other.values.iter().map(|x| x * x).sum::<f32>().sqrt();

        if norm_a == 0.0 || norm_b == 0.0 {
            return Ok(0.0);
        }

        Ok(dot_product / (norm_a * norm_b))
    }

    /// 计算欧几里得距离
    pub fn euclidean_distance(&self, other: &Embedding) -> Result<f32> {
        if self.dimensions != other.dimensions {
            return Err(anyhow::anyhow!("Dimension mismatch"));
        }

        let distance: f32 = self.values
            .iter()
            .zip(other.values.iter())
            .map(|(a, b)| (a - b).powi(2))
            .sum::<f32>()
            .sqrt();

        Ok(distance)
    }

    /// 计算点积
    pub fn dot_product(&self, other: &Embedding) -> Result<f32> {
        if self.dimensions != other.dimensions {
            return Err(anyhow::anyhow!("Dimension mismatch"));
        }

        let dot_product: f32 = self.values
            .iter()
            .zip(other.values.iter())
            .map(|(a, b)| a * b)
            .sum();

        Ok(dot_product)
    }

    /// 标准化向量
    pub fn normalize(&mut self) {
        let norm: f32 = self.values.iter().map(|x| x * x).sum::<f32>().sqrt();
        if norm > 0.0 {
            for value in &mut self.values {
                *value /= norm;
            }
        }
    }

    /// 获取标准化副本
    pub fn normalized(&self) -> Self {
        let mut normalized = self.clone();
        normalized.normalize();
        normalized
    }
}

/// 令牌使用情况
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TokenUsage {
    pub prompt_tokens: usize,
    pub total_tokens: usize,
}

/// 嵌入管理器
#[derive(Debug)]
pub struct EmbeddingManager {
    providers: HashMap<String, Box<dyn EmbeddingProvider>>,
    default_config: EmbeddingConfig,
    request_history: HashMap<Uuid, EmbeddingRequest>,
    embedding_cache: HashMap<String, Embedding>,
}

/// 嵌入提供商接口
#[async_trait::async_trait]
pub trait EmbeddingProvider: Send + Sync {
    async fn embed(&self, request: EmbeddingRequest) -> Result<EmbeddingResponse>;
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
    pub dimensions: Option<usize>,
    pub capabilities: Vec<ModelCapability>,
    pub pricing: Option<PricingInfo>,
}

/// 模型能力
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ModelCapability {
    Embedding,
    Completion,
    Chat,
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

/// 相似度搜索结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SimilaritySearchResult {
    pub text: String,
    pub embedding: Embedding,
    pub similarity_score: f32,
    pub metadata: HashMap<String, serde_json::Value>,
}

/// 嵌入统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EmbeddingStats {
    pub total_requests: usize,
    pub total_tokens: usize,
    pub total_cost: f64,
    pub average_tokens_per_request: f64,
    pub cache_hit_rate: f64,
    pub success_rate: f64,
    pub error_rate: f64,
    pub last_updated: DateTime<Utc>,
}

/// 嵌入索引
#[derive(Debug, Clone)]
pub struct EmbeddingIndex {
    pub id: String,
    pub name: String,
    pub model: String,
    pub embeddings: Vec<(String, Embedding)>,
    pub metadata: HashMap<String, serde_json::Value>,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

impl EmbeddingIndex {
    /// 创建新的嵌入索引
    pub fn new(id: String, name: String, model: String) -> Self {
        Self {
            id,
            name,
            model,
            embeddings: Vec::new(),
            metadata: HashMap::new(),
            created_at: Utc::now(),
            updated_at: Utc::now(),
        }
    }

    /// 添加嵌入
    pub fn add_embedding(&mut self, text: String, embedding: Embedding) {
        self.embeddings.push((text, embedding));
        self.updated_at = Utc::now();
    }

    /// 搜索相似嵌入
    pub fn search_similar(&self, query_embedding: &Embedding, top_k: usize) -> Result<Vec<SimilaritySearchResult>> {
        let mut results: Vec<SimilaritySearchResult> = self.embeddings
            .iter()
            .map(|(text, embedding)| {
                let similarity_score = query_embedding.cosine_similarity(embedding).unwrap_or(0.0);
                SimilaritySearchResult {
                    text: text.clone(),
                    embedding: embedding.clone(),
                    similarity_score,
                    metadata: HashMap::new(),
                }
            })
            .collect();

        // 按相似度排序
        results.sort_by(|a, b| b.similarity_score.partial_cmp(&a.similarity_score).unwrap_or(std::cmp::Ordering::Equal));

        // 返回前k个结果
        results.truncate(top_k);
        Ok(results)
    }

    /// 获取嵌入数量
    pub fn size(&self) -> usize {
        self.embeddings.len()
    }

    /// 清空索引
    pub fn clear(&mut self) {
        self.embeddings.clear();
        self.updated_at = Utc::now();
    }
}

impl EmbeddingManager {
    /// 创建新的嵌入管理器
    pub fn new() -> Self {
        Self {
            providers: HashMap::new(),
            default_config: EmbeddingConfig::default(),
            request_history: HashMap::new(),
            embedding_cache: HashMap::new(),
        }
    }

    /// 注册嵌入提供商
    pub fn register_provider(&mut self, name: String, provider: Box<dyn EmbeddingProvider>) {
        self.providers.insert(name, provider);
    }

    /// 生成文本嵌入
    pub async fn embed(&mut self, request: EmbeddingRequest) -> Result<EmbeddingResponse> {
        let request_id = request.id.unwrap_or_else(Uuid::new_v4);
        let mut request = request;
        request.id = Some(request_id);

        // 检查缓存
        if let Some(cached_embedding) = self.get_cached_embedding(&request) {
            return Ok(self.create_response_from_cache(request_id, &request, cached_embedding));
        }

        // 保存请求历史
        self.request_history.insert(request_id, request.clone());

        // 获取提供商
        let provider = self.get_provider_for_model(&request.model)?;

        // 执行嵌入
        let response = provider.embed(request.clone()).await?;

        // 缓存结果
        self.cache_embeddings(&request, &response);

        Ok(response)
    }

    /// 批量生成文本嵌入
    pub async fn embed_batch(&mut self, texts: Vec<String>, model: String, config: Option<EmbeddingConfig>) -> Result<EmbeddingResponse> {
        let config = config.unwrap_or_else(|| self.default_config.clone());
        let request = EmbeddingRequest {
            id: Some(Uuid::new_v4()),
            model,
            input: EmbeddingInput::Texts(texts),
            config,
            user_id: None,
            metadata: HashMap::new(),
        };

        self.embed(request).await
    }

    /// 搜索相似嵌入
    pub async fn search_similar(
        &mut self,
        query: String,
        model: String,
        index: &EmbeddingIndex,
        top_k: usize,
        config: Option<EmbeddingConfig>,
    ) -> Result<Vec<SimilaritySearchResult>> {
        // 生成查询嵌入
        let query_request = EmbeddingRequest {
            id: Some(Uuid::new_v4()),
            model,
            input: EmbeddingInput::Text(query),
            config: config.unwrap_or_else(|| self.default_config.clone()),
            user_id: None,
            metadata: HashMap::new(),
        };

        let query_response = self.embed(query_request).await?;
        let query_embedding = &query_response.data[0].embedding;

        // 在索引中搜索
        index.search_similar(query_embedding, top_k)
    }

    /// 创建嵌入索引
    pub async fn create_index(
        &mut self,
        id: String,
        name: String,
        texts: Vec<String>,
        model: String,
        config: Option<EmbeddingConfig>,
    ) -> Result<EmbeddingIndex> {
        // 生成嵌入
        let response = self.embed_batch(texts.clone(), model.clone(), config).await?;

        // 创建索引
        let mut index = EmbeddingIndex::new(id, name, model);
        for (i, embedding_data) in response.data.iter().enumerate() {
            if i < texts.len() {
                index.add_embedding(texts[i].clone(), embedding_data.embedding.clone());
            }
        }

        Ok(index)
    }

    /// 获取提供商
    fn get_provider_for_model(&self, model_id: &str) -> Result<&dyn EmbeddingProvider> {
        // 简化实现：根据模型ID推断提供商
        if model_id.starts_with("text-embedding-") {
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

    /// 获取缓存的嵌入
    fn get_cached_embedding(&self, request: &EmbeddingRequest) -> Option<&Embedding> {
        match &request.input {
            EmbeddingInput::Text(text) => {
                let cache_key = format!("{}:{}", request.model, text);
                self.embedding_cache.get(&cache_key)
            }
            _ => None, // 简化实现：只缓存单个文本
        }
    }

    /// 缓存嵌入
    fn cache_embeddings(&mut self, request: &EmbeddingRequest, response: &EmbeddingResponse) {
        match &request.input {
            EmbeddingInput::Text(text) => {
                if let Some(embedding_data) = response.data.first() {
                    let cache_key = format!("{}:{}", request.model, text);
                    self.embedding_cache.insert(cache_key, embedding_data.embedding.clone());
                }
            }
            _ => {} // 简化实现：只缓存单个文本
        }
    }

    /// 从缓存创建响应
    fn create_response_from_cache(&self, request_id: Uuid, request: &EmbeddingRequest, embedding: &Embedding) -> EmbeddingResponse {
        let embedding_data = EmbeddingData {
            index: 0,
            embedding: embedding.clone(),
            input_text: match &request.input {
                EmbeddingInput::Text(text) => Some(text.clone()),
                _ => None,
            },
            metadata: HashMap::new(),
        };

        EmbeddingResponse {
            id: request_id,
            model: request.model.clone(),
            data: vec![embedding_data],
            usage: TokenUsage {
                prompt_tokens: 0, // 缓存命中，无令牌消耗
                total_tokens: 0,
            },
            created: Utc::now(),
            metadata: HashMap::new(),
        }
    }

    /// 获取请求历史
    pub fn get_request_history(&self, request_id: &Uuid) -> Option<&EmbeddingRequest> {
        self.request_history.get(request_id)
    }

    /// 获取所有请求历史
    pub fn get_all_request_history(&self) -> Vec<&EmbeddingRequest> {
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

    /// 清理嵌入缓存
    pub fn cleanup_embedding_cache(&mut self, max_size: usize) -> usize {
        if self.embedding_cache.len() <= max_size {
            return 0;
        }

        let to_remove = self.embedding_cache.len() - max_size;
        let keys_to_remove: Vec<String> = self.embedding_cache.keys().take(to_remove).cloned().collect();

        for key in keys_to_remove {
            self.embedding_cache.remove(&key);
        }

        to_remove
    }

    /// 获取统计信息
    pub fn get_stats(&self) -> EmbeddingStats {
        let total_requests = self.request_history.len();
        let total_tokens = 0; // TODO: 计算总令牌数
        let total_cost = 0.0; // TODO: 计算总成本
        let average_tokens_per_request = if total_requests > 0 {
            total_tokens as f64 / total_requests as f64
        } else {
            0.0
        };

        let cache_hit_rate = 0.0; // TODO: 计算缓存命中率

        EmbeddingStats {
            total_requests,
            total_tokens,
            total_cost,
            average_tokens_per_request,
            cache_hit_rate,
            success_rate: 1.0, // TODO: 计算成功率
            error_rate: 0.0,   // TODO: 计算错误率
            last_updated: Utc::now(),
        }
    }

    /// 获取缓存大小
    pub fn cache_size(&self) -> usize {
        self.embedding_cache.len()
    }

    /// 清空缓存
    pub fn clear_cache(&mut self) {
        self.embedding_cache.clear();
    }
}

impl Default for EmbeddingManager {
    fn default() -> Self {
        Self::new()
    }
}

/// 预定义嵌入配置
pub struct PresetEmbeddingConfigs;

impl PresetEmbeddingConfigs {
    /// 获取默认配置
    pub fn default() -> EmbeddingConfig {
        EmbeddingConfig::default()
    }

    /// 获取高维配置
    pub fn high_dimensional() -> EmbeddingConfig {
        EmbeddingConfig {
            dimensions: Some(1536),
            encoding_format: EncodingFormat::Float,
            normalize: true,
            batch_size: Some(100),
            max_retries: Some(3),
            timeout: Some(std::time::Duration::from_secs(30)),
        }
    }

    /// 获取低维配置
    pub fn low_dimensional() -> EmbeddingConfig {
        EmbeddingConfig {
            dimensions: Some(384),
            encoding_format: EncodingFormat::Float,
            normalize: true,
            batch_size: Some(200),
            max_retries: Some(3),
            timeout: Some(std::time::Duration::from_secs(30)),
        }
    }

    /// 获取批量处理配置
    pub fn batch_processing() -> EmbeddingConfig {
        EmbeddingConfig {
            dimensions: None,
            encoding_format: EncodingFormat::Float,
            normalize: false,
            batch_size: Some(1000),
            max_retries: Some(5),
            timeout: Some(std::time::Duration::from_secs(60)),
        }
    }
}